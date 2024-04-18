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


use crate::{r1cs, utils::{
    error::SynthesisError,
    impl_lc::LinearCombination,
    variable::{Matrix, Variable},
}};

use super::predicate::{self, LocalPredicate, LocalPredicateType};

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

}

impl<F: Field> ConstraintSystem<F> {
    /// Construct an empty `ConstraintSystem`.
    pub fn new() -> Self {
        Self {
            mode: SynthesisMode::Prove {
                construct_matrices: true,
            },
            num_instance_variables: 1,
            num_witness_variables: 0,
            num_constraints: 0,
            num_linear_combinations: 0,
            num_local_predicates: 0,
            optimization_goal: OptimizationGoal::Constraints,
            instance_assignment: vec![F::one()],
            witness_assignment: Vec::new(),
            local_predicates: BTreeMap::new(),

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

    /// Enforce a R1CS constraint with the name `name`.
    #[inline]
    pub fn enforce_constraint(
        &mut self,
        linear_combinations: Vec<LinearCombination<F>>,
        predicate_name: &str,
    ) -> crate::utils::Result<()> {
        if self.should_construct_matrices() {
            let predicate = self.local_predicates.get_mut(predicate_name).unwrap();
            predicate.enforce_constraint(linear_combinations)?;
        }
        self.num_constraints += 1;

        Ok(())
    }

    pub fn to_index(&self) -> Option<Index<F>> {
        if let SynthesisMode::Prove {
            construct_matrices: false,
        } = self.mode
        {
            None
        } else {
            let mut index = Index::<F> {
                n: self.num_instance_variables,
                k: self.num_witness_variables + self.num_instance_variables,
                c: self.num_local_predicates,
                predicates: Vec::new(),
            };

            for (label, predicate) in self.local_predicates.iter() {
                index.add_predicate(predicate);
            }

            Some(index)
        }
    }

    /// Obtain a variable representing a linear combination.
    #[inline]
    pub fn new_lc(&mut self, lc: LinearCombination<F>) -> crate::gr1cs::Result<Variable> {
        // TODO: Should be changed!
        let var = Variable::SymbolicLc(crate::gr1cs::LcIndex(2));
        Ok(var)
    }


    /// Obtain the assignment corresponding to the `Variable` `v`.
    pub fn assigned_value(&self, v: Variable) -> Option<F> {
        match v {
            Variable::One => Some(F::one()),
            Variable::Zero => Some(F::zero()),
            Variable::Witness(idx) => self.witness_assignment.get(idx).copied(),
            Variable::Instance(idx) => self.instance_assignment.get(idx).copied(),
            Variable::SymbolicLc(idx) => {
                //TODO
                Some(F::one())
            },
        }
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
                predicate
                    .which_is_unsatisfied(&self.witness_assignment, &self.instance_assignment)?;
            }
            Ok(None)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Index<F: Field> {
    pub n: usize,
    pub k: usize,
    pub c: usize,
    pub predicates: Vec<Predicate<F>>,
}
impl<F: Field> Index<F> {
    pub fn get_t_max(&self) -> usize {
        self.predicates
            .iter()
            .map(|predicate| predicate.get_t())
            .max()
            .unwrap()
    }

    pub fn get_max_degree(&self) -> usize {
        let mut predicates_max_degree:usize = 0;
        for predicate in &self.predicates{
            let predicate_degree:usize = match predicate.predicate_type {
            LocalPredicateType::Polynomial(ref poly) => poly.get_degree(),
            _=> panic!("Not implemented")
            };
            predicates_max_degree = ark_std::cmp::max(predicates_max_degree, predicate_degree);
        }
        
        predicates_max_degree
    }

    pub fn get_m_total(&self) -> usize {
        self.predicates.iter().map(|predicate| predicate.get_m()).sum()
    }
    pub fn get_v_total(&self) -> usize {
        log2(self.get_m_total() as usize) as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Predicate<F: Field> {
    pub m: usize,
    pub t: usize,
    pub matrices: Vec<Matrix<F>>,
    pub predicate_type: predicate::LocalPredicateType<F>,
}

impl<F: Field> Predicate<F> {
    pub fn get_m(&self) -> usize {
        self.m
    }


    pub fn get_t(&self) -> usize {
        self.t
    }

    pub fn get_matrices(&self) -> &[Matrix<F>] {
        &self.matrices
    }
}

impl<F: Field> Index<F> {
    pub fn add_predicate(
        &mut self,
        local_predicate: &LocalPredicate<F>,
    ) -> crate::utils::Result<()> {

        let mut predicate_matrices: Vec<Matrix<F>> = vec![Matrix::new(); local_predicate.arity];
        let predicate_constraints: &Vec<Vec<LinearCombination<F>>> = local_predicate.get_constraints();
        // std::dbg!(predicate_constraints.len());

        for (argument_index, argument_constraints) in predicate_constraints.iter().enumerate() {
            for argument_constraint in argument_constraints {
                predicate_matrices[argument_index].push(self.make_row(argument_constraint))
            }
        }

        self.predicates.push(Predicate {
            m: local_predicate.num_constraints,
            t: local_predicate.arity,
            matrices: predicate_matrices,
            predicate_type: local_predicate.predicate_type.clone(),
        });
        Ok(())
    }

    #[inline]
    fn make_row(&self, l: &LinearCombination<F>) -> Vec<(F, usize)> {
        let num_input = self.n;
        l.0.iter()
            .filter_map(|(coeff, var)| {
                if coeff.is_zero() {
                    None
                } else {
                    Some((
                        *coeff,
                        var.get_index_unchecked(num_input).expect("no symbolic LCs"),
                    ))
                }
            })
            .collect()
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
    pub fn to_index(&self) -> Option<Index<F>> {
        self.inner().and_then(|cs| cs.borrow().to_index())
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

#[cfg(test)]
mod tests {

    use ark_test_curves::bls12_381::Fr;
    use crate::gr1cs::{sample::*, ConstraintSystem};

    use super::ConstraintSynthesizer;
    // / Let's test the following scenario
    // / L_1(X_1, X_2, X_3, X_4) with matrices: (M_11, M_12, M_13, M_14)
    // / L_2(X_1, X_2) with matrices: (M_21, M_22)
    // M_11 = [
    //     0,0,0,0,1
    //     4,0,2,0,2
    // ]
    // M_12 = [
    //     2,3,0,0,0
    //     1,1,1,1,1
    // ]
    // M_13 = [
    //     0,5,1,1,0
    //     1,1,0,0,0
    // ]
    // M_14 = [
    //     4,0,1,1,1
    //     0,0,1,2,6
    // ]
    // #[test]
    // fn matrix_generation() -> crate::utils::Result<()> {
    //     let mut cs = ConstraintSystem::<Fr>::new_ref();

    //     let a = cs.new_input_variable(|| Ok(Fr::from(1u8))).unwrap();
    //     let b = cs.new_input_variable(|| Ok(Fr::from(1u8))).unwrap();
    //     let c = cs.new_witness_variable(|| Ok(Fr::from(2u8))).unwrap();
    //     let d = cs.new_witness_variable(|| Ok(Fr::from(3u8))).unwrap();
    //     let e = cs.new_witness_variable(|| Ok(Fr::from(2u8))).unwrap();

    //     let mut local_predicate_1 = LocalPredicate::new_poly_predicate(4, Vec::new()).unwrap();

    //     cs.register_predicate("poly-predicate-1", local_predicate_1);
    //     let predicate1_constraint1 = vec![
    //         lc!() + e,
    //         lc!() + (Fr::from(2u8), a) + (Fr::from(3u8), b),
    //         lc!() + (Fr::from(5u8), b) + c + d,
    //         lc!() + (Fr::from(4u8), a) + c + d + e,
    //     ];
    //     let predicate1_constraint2 = vec![
    //         lc!() + (Fr::from(4u8), a) + (Fr::from(2u8), c) + (Fr::from(2u8), e),
    //         lc!() + a + b + c + d + e,
    //         lc!() + a + b,
    //         lc!() + c + (Fr::from(2u8), d) + (Fr::from(6u8), e),
    //     ];
    //     cs.enforce_constraint(predicate1_constraint1, "poly-predicate-1");

    //     let index = cs.to_index().unwrap();

    //         assert_eq!(
    //             vec![
    //                 vec![
    //                     vec![(Fr::one(), 4)],
    //                     vec![(Fr::from(4u8), 0), (Fr::from(2u8), 2), (Fr::from(2u8), 4)]
    //                 ],
    //                 vec![
    //                     vec![(Fr::from(2u8), 0), (Fr::from(3u8), 1)],
    //                     vec![
    //                         (Fr::one(), 0),
    //                         (Fr::one(), 1),
    //                         (Fr::one(), 2),
    //                         (Fr::one(), 3),
    //                         (Fr::one(), 4),
    //                     ]
    //                 ],
    //                 vec![
    //                     vec![(Fr::from(5u8), 1), (Fr::one(), 2), (Fr::one(), 3)],
    //                     vec![(Fr::one(), 0), (Fr::one(), 1)]
    //                 ],
    //                 vec![
    //                     vec![
    //                         (Fr::from(4u8), 0),
    //                         (Fr::one(), 2),
    //                         (Fr::one(), 3),
    //                         (Fr::one(), 4)
    //                     ],
    //                     vec![(Fr::one(), 2), (Fr::from(2u8), 3), (Fr::from(6u8), 4)]
    //                 ]
    //             ],
    //             index
    //             .predicates[0]
    //             .matrices
    //         );
    //         Ok(())
    // }

    // Let's test whether GR1CS accepts on a valid (winess,instance) pair
    // The circuit consists of three gates (A,B,C)
    // Gate A has 3 inputs: calculates y=x1x2+3x3^2
    // Gate B has 2 inputs: calculates y=7x2+x1^3
    // Gate C has 2 inputs and is a multiplication gate
    // The circuit topology is described in the following:
    // w4 = A(x1,x2,x3)
    // w5 = B(x4,w1)
    // w6 = C(w2w3)
    // w7 = w4+w5
    // w8 = B(w5,w6)
    // x5 = C(w7,w8)
    // #[test]
    // fn matrix_satisfaction() -> crate::utils::Result<()> {
    //     let dummy_circuit = DummyCircuit_1;
    //     let cs = ConstraintSystem::<Fr>::new_ref();
    //     dummy_circuit.generate_constraints(cs)?;
    //     assert!(cs.is_satisfied().unwrap());
    //     Ok(())
    // }
}



