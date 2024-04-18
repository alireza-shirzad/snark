
use crate::utils::error::SynthesisError;
use crate::utils::impl_lc::LinearCombination;
use crate::utils::polynomial::Polynomial;
use crate::utils::variable::*;

use ark_ff::Field;
use ark_std::vec::Vec;
use ark_std::{string::String};

#[cfg(feature = "std")]
use crate::gr1cs::trace::ConstraintTrace;

/// The types of local predicates used in GR1CS
/// For now we only add polynomial and lookup predicates
#[derive(Clone,Debug, PartialEq, Eq)]
pub enum LocalPredicateType<F> {
    /// Indicates that the local predicate is a polynomial predicate
    Polynomial(Polynomial<F>),
    /// Indicates that the local predicatea lookup predicate
    Lookup,
}


pub const MUL: &str = "multiplication";


pub type PredicateArgument<F> = Vec<LinearCombination<F>>;

#[derive(Debug, Clone)]
pub struct LocalPredicate<F: Field> {
    /// The arity that this local predicate supports
    /// In L(x_1,...,x_t), t is called the arity
    pub arity: usize,

    /// The type of the local predicate
    /// Whether it is a polynomial predicate or a look up predicate or ...
    pub predicate_type: LocalPredicateType<F>,

    /// The number of constraints expressed in this predicate
    /// The sum of these `num_constraints` for all predicates will add up to
    /// the total number of constraints in the system
    pub num_constraints: usize,


    /// The constraints of this predicate
    /// each vector in `constraints` corresponds to an argument of the local predicate
    /// Hence, `self.constraints.len()` should always equal `self.arity`
    constraints: Vec<PredicateArgument<F>>,
}

impl<F: Field> LocalPredicate<F> {
    pub fn new(arity: usize, predicate_type: LocalPredicateType<F>) -> Self {
        Self {
            arity,
            predicate_type,
            num_constraints: 0,
            constraints: vec![Vec::new();arity],

        }
    }

    pub fn new_poly_predicate(
        arity: usize,
        terms: Vec<(F, Vec<usize>)>,
    ) -> crate::utils::Result<Self> {
        let polynomial = Polynomial::new(arity, terms)?;
        Ok(Self::new(arity, LocalPredicateType::Polynomial(polynomial)))
    }

    pub fn enforce_constraint(
        &mut self,
        constraint_lcs: Vec<LinearCombination<F>>,
    ) -> crate::utils::Result<()> {
        if self.arity != constraint_lcs.len() {
            return Err(SynthesisError::ArityMismatch);
        }
        self.num_constraints += 1;
        for i in 0..self.arity {
            self.constraints[i].push(constraint_lcs[i].clone());
        }
        Ok(())
    }
    pub fn which_is_unsatisfied(
        &self,
        witness_assignment: &Vec<F>,
        instance_assignment: &Vec<F>,
    ) -> crate::utils::Result<Option<String>> {
        for i in 0..self.num_constraints {
            let mut point: Vec<F> = Vec::new();
            for argument in self.constraints.iter() {
                point.push(
                    self.eval_lc(&argument[i], witness_assignment, instance_assignment)
                        .ok_or(SynthesisError::AssignmentMissing)?,
                );
            }

            let result = match &self.predicate_type {
                LocalPredicateType::Polynomial(poly) => poly.evaluate(&point),
                _ => Err(SynthesisError::NotImplemented),
            }?;

            if result != F::zero() {
                panic!("Constraint {} is unsatisfied", i)
                // let trace;
                // #[cfg(feature = "std")]
                // {
                //     trace = self.constraint_traces[i].as_ref().map_or_else(
                //         || {
                //             eprintln!("Constraint trace requires enabling `ConstraintLayer`");
                //             format!("{}", i)
                //         },
                //         |t| format!("{}", t),
                //     );
                // }
                // #[cfg(not(feature = "std"))]
                // {
                //     trace = format!("{}", i);
                // }
                // return Ok(Some(trace));
            }
        }
        Ok(None)
    }

    // Getter method for `constraints`
    pub fn get_constraints(&self) -> &Vec<Vec<LinearCombination<F>>> {
        &self.constraints
    }

    fn eval_lc(
        &self,
        lc: &LinearCombination<F>,
        witness_assignment: &Vec<F>,
        instance_assignment: &Vec<F>,
    ) -> Option<F> {
        let mut acc = F::zero();
        for (coeff, var) in lc.iter() {
            acc += *coeff * self.assigned_value(*var, witness_assignment, instance_assignment)?;
        }
        Some(acc)
    }

    /// Obtain the assignment corresponding to the `Variable` `v`.
    pub fn assigned_value(
        &self,
        v: Variable,
        witness_assignment: &Vec<F>,
        instance_assignment: &Vec<F>,
    ) -> Option<F> {
        match v {
            Variable::One => Some(F::one()),
            Variable::Zero => Some(F::zero()),
            Variable::Witness(idx) => witness_assignment.get(idx).copied(),
            Variable::Instance(idx) => instance_assignment.get(idx).copied(),
            Variable::SymbolicLc(idx) => None,
        }
    }
}
