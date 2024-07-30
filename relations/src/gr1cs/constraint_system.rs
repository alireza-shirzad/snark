use ark_ff::Field;
use ark_std::{
    any::{Any, TypeId},
    boxed::Box,
    cell::{Ref, RefCell, RefMut},
    collections::BTreeMap,
    format,
    rc::Rc,
    string::String,
    string::ToString,
    vec,
    vec::Vec,
    log2
};


use crate::{utils::{
    error::SynthesisError,
    impl_lc::LinearCombination,
    variable::{Matrix, Variable},
}};

use super::{impl_lc::LcIndex, predicate::{self, LocalPredicate, LocalPredicateType}};

/// Computations are expressed in terms of generalized rank-1 constraint systems (GR1CS).
/// The `generate_constraints` method is called to generate constraints for
/// both CRS generation and for proving.
// TODO: Think: should we replace this with just a closure?
pub trait ConstraintSynthesizer<F: Field> {
    /// Drives generation of new constraints inside `cs`.
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> crate::utils::Result<()>;
}

/// An Generalized Rank-One `ConstraintSystem`. Enforces constraints of the form
/// `L_i(<M_1j, z>, <M_2j, z>,..., <M_tj, z>)`, where `M_ij`s are linear
/// combinations over variables, and `z` is the concrete assignment to these
/// variables.
#[derive(Debug, Clone)]
pub struct ConstraintSystem<F: Field> {
    /// The mode in which the constraint system is operating. `self` can either
    /// be in setup mode (i.e., `self.mode == SynthesisMode::Setup`) or in
    /// proving mode (i.e., `self.mode == SynthesisMode::Prove`). If we are
    /// in proving mode, then we have the additional option of whether or
    /// not to construct the A, B, and C matrices of the constraint system
    /// (see below).
    pub mode: SynthesisMode,
    /// The number of variables that are "public inputs" to the constraint
    /// system.
    pub num_instance_variables: usize,
    /// The number of variables that are "private inputs" to the constraint
    /// system.
    pub num_witness_variables: usize,
    /// The number of constraints in the constraint system.
    pub num_constraints: usize,
    /// The number of linear combinations
    pub num_linear_combinations: usize,
    /// The number of predicates
    pub num_local_predicates: usize,

    /// The parameter we aim to minimize in this constraint system (either the
    /// number of constraints or their total weight).
    pub optimization_goal: OptimizationGoal,

    /// Assignments to the public input variables. This is empty if `self.mode
    /// == SynthesisMode::Setup`.
    pub instance_assignment: Vec<F>,
    /// Assignments to the private input variables. This is empty if `self.mode
    /// == SynthesisMode::Setup`.
    pub witness_assignment: Vec<F>,

    pub local_predicates: BTreeMap<String, LocalPredicate<F>>,
    lc_map: BTreeMap<LcIndex, LinearCombination<F>>,
    lc_assignment_cache: Rc<RefCell<BTreeMap<LcIndex, F>>>,


}

impl<F: Field> ConstraintSystem<F> {
    /// Construct an empty `ConstraintSystem`.
    pub fn new() -> Self {
        Self {
            mode: SynthesisMode::Prove { construct_matrices: true },
            num_instance_variables: 1,
            num_witness_variables: 0,
            num_constraints: 0,
            num_linear_combinations: 0,
            num_local_predicates: 0,
            optimization_goal: OptimizationGoal::Constraints,
            instance_assignment: vec![F::one()],
            witness_assignment: Vec::new(),
            local_predicates: BTreeMap::new(),
            lc_map: BTreeMap::new(),
            lc_assignment_cache: Rc::new(RefCell::new(BTreeMap::new())),

        }
    }

    /// Create a new `ConstraintSystemRef<F>`.
    pub fn new_ref() -> ConstraintSystemRef<F> {
        ConstraintSystemRef::new(Self::new())
    }

    /// Set `self.mode` to `mode`.
    pub fn set_mode(&mut self, mode: SynthesisMode) {
        self.mode = mode;
    }

    /// Check whether `self.mode == SynthesisMode::Setup`.
    pub fn is_in_setup_mode(&self) -> bool {
        self.mode == SynthesisMode::Setup
    }

    /// Check whether this constraint system aims to optimize weight,
    /// number of constraints, or neither.
    pub fn optimization_goal(&self) -> OptimizationGoal {
        self.optimization_goal
    }

    /// Specify whether this constraint system should aim to optimize weight,
    /// number of constraints, or neither.
    pub fn set_optimization_goal(&mut self, goal: OptimizationGoal) {
        // `set_optimization_goal` should only be executed before any constraint or value is created.
        assert_eq!(self.num_instance_variables, 1);
        assert_eq!(self.num_witness_variables, 0);
        assert_eq!(self.num_constraints, 0);
        assert_eq!(self.num_linear_combinations, 0);

        self.optimization_goal = goal;
    }

    /// Check whether or not `self` will construct matrices.
    pub fn should_construct_matrices(&self) -> bool {
        match self.mode {
            SynthesisMode::Setup => true,
            SynthesisMode::Prove { construct_matrices } => construct_matrices,
        }
    }

    /// Return a variable representing the constant "zero" inside the constraint
    /// system.
    #[inline]
    pub fn zero() -> Variable {
        Variable::Zero
    }

    /// Return a variable representing the constant "one" inside the constraint
    /// system.
    #[inline]
    pub fn one() -> Variable {
        Variable::One
    }

    /// Obtain a variable representing a new public instance input.
    #[inline]
    pub fn new_input_variable<Func>(&mut self, f: Func) -> crate::utils::Result<Variable>
    where
        Func: FnOnce() -> crate::utils::Result<F>,
    {
        let index = self.num_instance_variables;
        self.num_instance_variables += 1;

        if !self.is_in_setup_mode() {
            self.instance_assignment.push(f()?);
        }
        Ok(Variable::Instance(index))
    }

    /// Obtain a variable representing a new private witness input.
    #[inline]
    pub fn new_witness_variable<Func>(&mut self, f: Func) -> crate::utils::Result<Variable>
    where
        Func: FnOnce() -> crate::utils::Result<F>,
    {
        let index = self.num_witness_variables;
        self.num_witness_variables += 1;

        if !self.is_in_setup_mode() {
            self.witness_assignment.push(f()?);
        }
        Ok(Variable::Witness(index))
    }

    pub fn register_predicate(
        &mut self,
        label: &str,
        local_predicate: LocalPredicate<F>,
    ) -> crate::utils::Result<()> {
        self.local_predicates
            .insert(String::from(label), local_predicate);
        self.num_local_predicates += 1;
        Ok(())
    }



    /// Obtain a variable representing a linear combination.
    #[inline]
    pub fn new_lc(&mut self, lc: LinearCombination<F>) -> crate::r1cs::Result<Variable> {
        let index = LcIndex(self.num_linear_combinations);
        let var = Variable::SymbolicLc(index);

        self.lc_map.insert(index, lc);

        self.num_linear_combinations += 1;
        Ok(var)
    }


    /// Enforce a R1CS constraint with the name `name`.
    #[inline]
    pub fn enforce_constraint(
        &mut self,
        linear_combinations: Vec<LinearCombination<F>>,
        predicate_name: &str,
    ) -> crate::utils::Result<()> {
        if self.should_construct_matrices() {
            let mut indices:Vec<LcIndex> = Vec::new();
            for lc in linear_combinations {
                let index = self.new_lc(lc)?.get_lc_index().unwrap();
                indices.push(index);
            }
            let mut predicate = self.local_predicates.get_mut(predicate_name).unwrap();
            predicate.enforce_constraint(indices)?;
        }
        self.num_constraints += 1;

        Ok(())
    }

    pub fn to_index(&self) -> Option<super::index::Index<F>> {
        if let SynthesisMode::Prove {
            construct_matrices: false,
        } = self.mode
        {
            None
        } else {
            let mut index = super::index::Index::<F> {
                n: self.num_instance_variables,
                k: self.num_witness_variables + self.num_instance_variables,
                c: self.num_local_predicates,
                predicates: Vec::new(),
            };

            for (label, predicate) in self.local_predicates.iter() {
                index.add_predicate(predicate, &self.lc_map);
            }

            Some(index)
        }
    }




    /// Obtain the assignment corresponding to the `Variable` `v`.
    pub fn assigned_value(&self, v: Variable) -> Option<F> {
        match v {
            Variable::One => Some(F::one()),
            Variable::Zero => Some(F::zero()),
            Variable::Witness(idx) => self.witness_assignment.get(idx).copied(),
            Variable::Instance(idx) => self.instance_assignment.get(idx).copied(),
            Variable::SymbolicLc(idx) => {
                let value = self.lc_assignment_cache.borrow().get(&idx).copied();
                if value.is_some() {
                    value
                } else {
                    let value = self.eval_lc(idx)?;
                    self.lc_assignment_cache.borrow_mut().insert(idx, value);
                    Some(value)
                }
            },
        }
    }

    fn eval_lc(&self, lc: LcIndex) -> Option<F> {
        let lc = self.lc_map.get(&lc)?;
        let mut acc = F::zero();
        for (coeff, var) in lc.iter() {
            acc += *coeff * self.assigned_value(*var)?;
        }
        Some(acc)
    }

    /// If `self` is satisfied, outputs `Ok(true)`.
    /// If `self` is unsatisfied, outputs `Ok(false)`.
    /// If `self.is_in_setup_mode()`, outputs `Err(())`.
    pub fn is_satisfied(&self) -> crate::utils::Result<bool> {
        self.which_is_unsatisfied().map(|s| s.is_none())
    }

    /// If `self` is satisfied, outputs `Ok(None)`.
    /// If `self` is unsatisfied, outputs `Some(i)`, where `i` is the index of
    /// the first unsatisfied constraint. If `self.is_in_setup_mode()`, outputs
    /// `Err(())`.
    pub fn which_is_unsatisfied(&self) -> crate::utils::Result<Option<String>> {
        if self.is_in_setup_mode() {
            Err(SynthesisError::AssignmentMissing)
        } else {
            for (label, predicate) in self.local_predicates.iter() {
                    self.which_predicate_is_unsatisfied(&predicate)?;
            }
            Ok(None)
        }
    }

        /// Finalize the constraint system (either by outlining or inlining,
    /// if an optimization goal is set).
    pub fn finalize(&mut self) {
        match self.optimization_goal {
            OptimizationGoal::None => self.inline_all_lcs(),
            OptimizationGoal::Constraints => self.inline_all_lcs(),
            // OptimizationGoal::Weight => self.outline_lcs(),
        };
    }

        /// Naively inlines symbolic linear combinations into the linear
    /// combinations that use them.
    ///
    /// Useful for standard pairing-based SNARKs where addition gates are cheap.
    /// For example, in the SNARKs such as [\[Groth16\]](https://eprint.iacr.org/2016/260) and
    /// [\[Groth-Maller17\]](https://eprint.iacr.org/2017/540), addition gates
    /// do not contribute to the size of the multi-scalar multiplication, which
    /// is the dominating cost.
    pub fn inline_all_lcs(&mut self) {
        // Only inline when a matrix representing R1CS is needed.
        if !self.should_construct_matrices() {
            return;
        }

        // A dummy closure is used, which means that
        // - it does not modify the inlined LC.
        // - it does not add new witness variables.
        self.transform_lc_map(&mut |_, _, _| (0, None));
    }



    /// Count the number of times each LC is used within other LCs in the
    /// constraint system
    fn lc_num_times_used(&self, count_sinks: bool) -> Vec<usize> {
        let mut num_times_used = vec![0; self.lc_map.len()];

        // Iterate over every lc in constraint system
        for (index, lc) in self.lc_map.iter() {
            num_times_used[index.0] += count_sinks as usize;

            // Increment the counter for each lc that this lc has a direct dependency on.
            for &(_, var) in lc.iter() {
                if var.is_lc() {
                    let lc_index = var.get_lc_index().expect("should be lc");
                    num_times_used[lc_index.0] += 1;
                }
            }
        }
        num_times_used
    }


        /// Transform the map of linear combinations.
    /// Specifically, allow the creation of additional witness assignments.
    ///
    /// This method is used as a subroutine of `inline_all_lcs` and `outline_lcs`.
    ///
    /// The transformer function is given a references of this constraint system (&self),
    /// number of times used, and a mutable reference of the linear combination to be transformed.
    ///     (&ConstraintSystem<F>, usize, &mut LinearCombination<F>)
    ///
    /// The transformer function returns the number of new witness variables needed
    /// and a vector of new witness assignments (if not in the setup mode).
    ///     (usize, Option<Vec<F>>)
    pub fn transform_lc_map(
        &mut self,
        transformer: &mut dyn FnMut(
            &ConstraintSystem<F>,
            usize,
            &mut LinearCombination<F>,
        ) -> (usize, Option<Vec<F>>),
    ) {
        // `transformed_lc_map` stores the transformed linear combinations.
        let mut transformed_lc_map = BTreeMap::<_, LinearCombination<F>>::new();
        let mut num_times_used = self.lc_num_times_used(false);

        // This loop goes through all the LCs in the map, starting from
        // the early ones. The transformer function is applied to the
        // inlined LC, where new witness variables can be created.
        for (&index, lc) in &self.lc_map {
            let mut transformed_lc = LinearCombination::new();

            // Inline the LC, unwrapping symbolic LCs that may constitute it,
            // and updating them according to transformations in prior iterations.
            for &(coeff, var) in lc.iter() {
                if var.is_lc() {
                    let lc_index = var.get_lc_index().expect("should be lc");

                    // If `var` is a `SymbolicLc`, fetch the corresponding
                    // inlined LC, and substitute it in.
                    //
                    // We have the guarantee that `lc_index` must exist in
                    // `transformed_lc` since a LC can only depend on other
                    // LCs with lower indices, which we have transformed.
                    //
                    let lc = transformed_lc_map
                        .get(&lc_index)
                        .expect("should be inlined");
                    transformed_lc.extend((lc * coeff).0.into_iter());

                    // Delete linear combinations that are no longer used.
                    //
                    // Deletion is safe for both outlining and inlining:
                    // * Inlining: the LC is substituted directly into all use sites, and so once it
                    //   is fully inlined, it is redundant.
                    //
                    // * Outlining: the LC is associated with a new variable `w`, and a new
                    //   constraint of the form `lc_data * 1 = w`, where `lc_data` is the actual
                    //   data in the linear combination. Furthermore, we replace its entry in
                    //   `new_lc_map` with `(1, w)`. Once `w` is fully inlined, then we can delete
                    //   the entry from `new_lc_map`
                    //
                    num_times_used[lc_index.0] -= 1;
                    if num_times_used[lc_index.0] == 0 {
                        // This lc is not used any more, so remove it.
                        transformed_lc_map.remove(&lc_index);
                    }
                } else {
                    // Otherwise, it's a concrete variable and so we
                    // substitute it in directly.
                    transformed_lc.push((coeff, var));
                }
            }
            transformed_lc.compactify();

            // Call the transformer function.
            let (num_new_witness_variables, new_witness_assignments) =
                transformer(&self, num_times_used[index.0], &mut transformed_lc);

            // Insert the transformed LC.
            transformed_lc_map.insert(index, transformed_lc);

            // Update the witness counter.
            self.num_witness_variables += num_new_witness_variables;

            // Supply additional witness assignments if not in the
            // setup mode and if new witness variables are created.
            if !self.is_in_setup_mode() && num_new_witness_variables > 0 {
                assert!(new_witness_assignments.is_some());
                if let Some(new_witness_assignments) = new_witness_assignments {
                    assert_eq!(new_witness_assignments.len(), num_new_witness_variables);
                    self.witness_assignment
                        .extend_from_slice(&new_witness_assignments);
                }
            }
        }
        // Replace the LC map.
        self.lc_map = transformed_lc_map;
    }


    pub fn which_predicate_is_unsatisfied(
        &self,
        predicate: &LocalPredicate<F>,
    ) -> crate::utils::Result<Option<String>> {
        for i in 0..predicate.num_constraints {
            let mut point: Vec<F> = Vec::new();
            for argument in predicate.constraints.iter() {
                point.push(
                    self.eval_lc(argument[i])
                        .ok_or(SynthesisError::AssignmentMissing)?,
                );
            }

            let result = match &predicate.predicate_type {
                LocalPredicateType::Polynomial(poly) => poly.evaluate(&point),
                _ => Err(SynthesisError::NotImplemented),
            }?;

            if result != F::zero() {
                panic!("Constraint {} is unsatisfied", i)
            }
        }
        Ok(None)
    }





}


/// A shared reference to a constraint system that can be stored in high level
/// variables.
#[derive(Debug, Clone)]
pub enum ConstraintSystemRef<F: Field> {
    /// Represents the case where we *don't* need to allocate variables or
    /// enforce constraints. Encountered when operating over constant
    /// values.
    None,
    /// Represents the case where we *do* allocate variables or enforce
    /// constraints.
    CS(Rc<RefCell<ConstraintSystem<F>>>),
}

impl<F: Field> PartialEq for ConstraintSystemRef<F> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::None, Self::None) => true,
            (..) => false,
        }
    }
}

impl<F: Field> Eq for ConstraintSystemRef<F> {}

/// A namespaced `ConstraintSystemRef`.
#[derive(Debug, Clone)]
pub struct Namespace<F: Field> {
    inner: ConstraintSystemRef<F>,
    id: Option<tracing::Id>,
}

impl<F: Field> From<ConstraintSystemRef<F>> for Namespace<F> {
    fn from(other: ConstraintSystemRef<F>) -> Self {
        Self {
            inner: other,
            id: None,
        }
    }
}

impl<F: Field> Namespace<F> {
    /// Construct a new `Namespace`.
    pub fn new(inner: ConstraintSystemRef<F>, id: Option<tracing::Id>) -> Self {
        Self { inner, id }
    }

    /// Obtain the inner `ConstraintSystemRef<F>`.
    pub fn cs(&self) -> ConstraintSystemRef<F> {
        self.inner.clone()
    }

    /// Manually leave the namespace.
    pub fn leave_namespace(self) {
        drop(self)
    }
}

impl<F: Field> Drop for Namespace<F> {
    fn drop(&mut self) {
        if let Some(id) = self.id.as_ref() {
            tracing::dispatcher::get_default(|dispatch| dispatch.exit(id))
        }
        let _ = self.inner;
    }
}

impl<F: Field> ConstraintSystemRef<F> {
    /// Returns `self` if `!self.is_none()`, otherwise returns `other`.
    pub fn or(self, other: Self) -> Self {
        match self {
            ConstraintSystemRef::None => other,
            _ => self,
        }
    }

    /// Returns `true` is `self == ConstraintSystemRef::None`.
    pub fn is_none(&self) -> bool {
        matches!(self, ConstraintSystemRef::None)
    }

    /// Construct a `ConstraintSystemRef` from a `ConstraintSystem`.
    #[inline]
    pub fn new(inner: ConstraintSystem<F>) -> Self {
        Self::CS(Rc::new(RefCell::new(inner)))
    }

    fn inner(&self) -> Option<&Rc<RefCell<ConstraintSystem<F>>>> {
        match self {
            Self::CS(a) => Some(a),
            Self::None => None,
        }
    }

    /// Consumes self to return the inner `ConstraintSystem<F>`. Returns
    /// `None` if `Self::CS` is `None` or if any other references to
    /// `Self::CS` exist.  
    pub fn into_inner(self) -> Option<ConstraintSystem<F>> {
        match self {
            Self::CS(a) => Rc::try_unwrap(a).ok().map(|s| s.into_inner()),
            Self::None => None,
        }
    }

    /// Obtain an immutable reference to the underlying `ConstraintSystem`.
    ///
    /// # Panics
    /// This method panics if `self` is already mutably borrowed.
    #[inline]
    pub fn borrow(&self) -> Option<Ref<'_, ConstraintSystem<F>>> {
        self.inner().map(|cs| cs.borrow())
    }

    /// Obtain a mutable reference to the underlying `ConstraintSystem`.
    ///
    /// # Panics
    /// This method panics if `self` is already mutably borrowed.
    #[inline]
    pub fn borrow_mut(&self) -> Option<RefMut<'_, ConstraintSystem<F>>> {
        self.inner().map(|cs| cs.borrow_mut())
    }

    /// Set `self.mode` to `mode`.
    /// Sets the mode if there exists an underlying ConstrainSystem
    pub fn set_mode(&self, mode: SynthesisMode) {
        self.inner().map_or((), |cs| cs.borrow_mut().set_mode(mode))
    }

    /// Check whether `self.mode == SynthesisMode::Setup`.
    /// Returns true if 1- There is an underlying ConstraintSystem and
    /// 2- It's in setup mode
    #[inline]
    pub fn is_in_setup_mode(&self) -> bool {
        self.inner()
            .map_or(false, |cs| cs.borrow().is_in_setup_mode())
    }

    /// Returns the number of constraints.
    #[inline]
    pub fn num_constraints(&self) -> usize {
        self.inner().map_or(0, |cs| cs.borrow().num_constraints)
    }

    /// Returns the number of instance variables.
    #[inline]
    pub fn num_instance_variables(&self) -> usize {
        self.inner()
            .map_or(0, |cs| cs.borrow().num_instance_variables)
    }

    /// Returns the number of witness variables.
    #[inline]
    pub fn num_witness_variables(&self) -> usize {
        self.inner()
            .map_or(0, |cs| cs.borrow().num_witness_variables)
    }

    /// Returns the number of local predicates
    #[inline]
    pub fn num_local_predicates(&self) -> usize {
        self.inner()
            .map_or(0, |cs| cs.borrow().num_local_predicates)
    }

    /// Check whether this constraint system aims to optimize weight,
    /// number of constraints, or neither.
    #[inline]
    pub fn optimization_goal(&self) -> OptimizationGoal {
        self.inner().map_or(OptimizationGoal::Constraints, |cs| {
            cs.borrow().optimization_goal()
        })
    }

    /// Specify whether this constraint system should aim to optimize weight,
    /// number of constraints, or neither.
    #[inline]
    pub fn set_optimization_goal(&self, goal: OptimizationGoal) {
        self.inner()
            .map_or((), |cs| cs.borrow_mut().set_optimization_goal(goal))
    }

    /// Check whether or not `self` will construct matrices.
    #[inline]
    pub fn should_construct_matrices(&self) -> bool {
        self.inner()
            .map_or(false, |cs| cs.borrow().should_construct_matrices())
    }

    /// Obtain a variable representing a new public instance input
    /// This function takes a closure, this closure returns `Result<F>`
    /// Internally, this function calls new_input_variable of the constraint system to which it's pointing
    #[inline]
    pub fn new_input_variable<Func>(&self, f: Func) -> crate::utils::Result<Variable>
    where
        Func: FnOnce() -> crate::utils::Result<F>,
    {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| {
                if !self.is_in_setup_mode() {
                    // This is needed to avoid double-borrows, because `f`
                    // might itself mutably borrow `cs` (eg: `f = || g.value()`).
                    let value = f();
                    cs.borrow_mut().new_input_variable(|| value)
                } else {
                    cs.borrow_mut().new_input_variable(f)
                }
            })
    }

    /// Obtain a variable representing a new private witness input.
    #[inline]
    pub fn new_witness_variable<Func>(&self, f: Func) -> crate::utils::Result<Variable>
    where
        Func: FnOnce() -> crate::utils::Result<F>,
    {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| {
                if !self.is_in_setup_mode() {
                    // This is needed to avoid double-borrows, because `f`
                    // might itself mutably borrow `cs` (eg: `f = || g.value()`).
                    let value = f();
                    cs.borrow_mut().new_witness_variable(|| value)
                } else {
                    cs.borrow_mut().new_witness_variable(f)
                }
            })
    }

    /// Finalize the constraint system (either by outlining or inlining,
    /// if an optimization goal is set).
    pub fn finalize(&self) {
        if let Some(cs) = self.inner() {
            cs.borrow_mut().finalize()
        }
    }

    /// Obtain a variable representing a linear combination.
    #[inline]
    pub fn new_lc(&self, lc: LinearCombination<F>) -> crate::gr1cs::Result<Variable> {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| cs.borrow_mut().new_lc(lc))
    }


    /// Enforce a R1CS constraint with the name `name`.
    #[inline]
    pub fn enforce_constraint(
        &self,
        linear_combinations: Vec<LinearCombination<F>>,
        predicate_name: &str,
    ) -> crate::utils::Result<()> {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| {
                cs.borrow_mut()
                    .enforce_constraint(linear_combinations, predicate_name)
            })
    }

    #[inline]
    pub fn to_index(&self) -> Option<super::index::Index<F>> {
        self.inner().and_then(|cs| cs.borrow().to_index())
    }


    /// Naively inlines symbolic linear combinations into the linear
    /// combinations that use them.
    ///
    /// Useful for standard pairing-based SNARKs where addition gates are cheap.
    /// For example, in the SNARKs such as [\[Groth16\]](https://eprint.iacr.org/2016/260) and
    /// [\[Groth-Maller17\]](https://eprint.iacr.org/2017/540), addition gates
    /// do not contribute to the size of the multi-scalar multiplication, which
    /// is the dominating cost.
    pub fn inline_all_lcs(&self) {
        if let Some(cs) = self.inner() {
            cs.borrow_mut().inline_all_lcs()
        }
    }


    /// Obtain the assignment corresponding to the `Variable` `v`.
    pub fn assigned_value(&self, v: Variable) -> Option<F> {
        self.inner().and_then(|cs| cs.borrow().assigned_value(v))
    }


    pub fn register_predicate(
        &mut self,
        label: &str,
        local_predicate: LocalPredicate<F>,
    ) -> crate::utils::Result<()> {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| cs.borrow_mut().register_predicate(label, local_predicate));
        Ok(())
    }

    /// If `self` is satisfied, outputs `Ok(true)`.
    /// If `self` is unsatisfied, outputs `Ok(false)`.
    /// If `self.is_in_setup_mode()` or if `self == None`, outputs `Err(())`.
    pub fn is_satisfied(&self) -> crate::utils::Result<bool> {
        self.inner()
            .map_or(Err(SynthesisError::AssignmentMissing), |cs| {
                cs.borrow().is_satisfied()
            })
    }

    /// If `self` is satisfied, outputs `Ok(None)`.
    /// If `self` is unsatisfied, outputs `Some(i)`, where `i` is the index of
    /// the first unsatisfied constraint.
    /// If `self.is_in_setup_mode()` or `self == None`, outputs `Err(())`.
    pub fn which_is_unsatisfied(&self) -> crate::utils::Result<Option<String>> {
        self.inner()
            .map_or(Err(SynthesisError::AssignmentMissing), |cs| {
                cs.borrow().which_is_unsatisfied()
            })
    }
}

/// Defines the mode of operation of a `ConstraintSystem`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum SynthesisMode {
    /// Indicate to the `ConstraintSystem` that it should only generate
    /// constraint matrices and not populate the variable assignments.
    Setup,
    /// Indicate to the `ConstraintSystem` that it populate the variable
    /// assignments. If additionally `construct_matrices == true`, then generate
    /// the matrices as in the `Setup` case.
    Prove {
        /// If `construct_matrices == true`, then generate
        /// the matrices as in the `Setup` case.
        construct_matrices: bool,
    },
}

/// Defines the parameter to optimize for a `ConstraintSystem`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum OptimizationGoal {
    /// Make no attempt to optimize.
    None,
    /// Minimize the number of constraints.
    Constraints,
}




