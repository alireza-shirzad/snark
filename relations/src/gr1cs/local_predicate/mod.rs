//! This module contains the implementation of a general local predicate, defined in https://eprint.iacr.org/2024/1245
//! A local predicate is a function from t (arity) variables to a boolean
//! variable A local predicate can be as simple as f(a,b,c)=a.b-c=0 or as
//! complex as a lookup table

pub mod polynomial_constraint;

use super::{
    Constraint, ConstraintSystem, ConstraintSystemRef, LcIndex, LinearCombination, Matrix,
};
use crate::utils::{error::SynthesisError::ArityMismatch, variable::Variable::SymbolicLc};
use ark_ff::Field;
use ark_std::vec::Vec;
use polynomial_constraint::PolynomialPredicate;

/// A predicate is a function that decides (outputs boolean) on a vector of
/// field elements
pub trait Predicate<F> {
    /// Evaluate the predicate on t (arity) variables
    fn evaluate(&self, variables: &[F]) -> bool;

    /// Get the arity of the predicate, i.e. the number of variables it takes
    fn arity(&self) -> usize;
}

/// GR1CS can potentially support different types of predicates
/// For now, we only support polynomial predicates
/// In the future, we can add other types of predicates, e.g. lookup table
#[derive(Debug, Clone)]
pub enum LocalPredicate<F: Field> {
    Polynomial(PolynomialPredicate<F>),
    // Add other predicates in the future, e.g. lookup table
}

impl<F: Field> Predicate<F> for LocalPredicate<F> {
    fn evaluate(&self, variables: &[F]) -> bool {
        match self {
            LocalPredicate::Polynomial(p) => p.evaluate(variables),
            // TODO: Add other predicates in the future, e.g. lookup table
        }
    }

    fn arity(&self) -> usize {
        match self {
            LocalPredicate::Polynomial(p) => p.arity(),
            // TODO: Add other predicates in the future, e.g. lookup table
        }
    }
}

/// A constraint system that enforces a predicate
#[derive(Debug, Clone)]
pub struct PredicateConstraintSystem<F: Field> {
    /// The list of linear combinations for each arguments of the predicate
    /// The length of this list is equal to the arity of the predicate
    /// Each element in the list has size equal to the number of constraints
    argument_lcs: Vec<Vec<LcIndex>>,

    /// The number of constraints enforced by this predicate
    num_constraints: usize,

    /// The local predicate acting on constraints
    local_predicate: LocalPredicate<F>,
}

impl<F: Field> PredicateConstraintSystem<F> {
    /// Create a new predicate constraint system with a specific predicate
    fn new(local_predicate: LocalPredicate<F>) -> Self {
        Self {
            argument_lcs: vec![Vec::new(); local_predicate.arity()],
            local_predicate,
            num_constraints: 0,
        }
    }

    /// Create new polynomial predicate constraint system
    pub fn new_polynomial_predicate(arity: usize, terms: Vec<(F, Vec<(usize, usize)>)>) -> Self {
        Self::new(LocalPredicate::Polynomial(PolynomialPredicate::new(
            arity, terms,
        )))
    }

    /// creates an R1CS predicate which is a special kind of polynomial
    /// predicate
    pub fn new_r1cs_predicate() -> crate::utils::Result<Self> {
        Ok(Self::new_polynomial_predicate(
            3,
            vec![
                (F::from(1u8), vec![(0, 1), (1, 1)]),
                (F::from(-1i8), vec![(2, 1)]),
            ],
        ))
    }

    /// Get the arity of the local predicate in this predicate constraint system
    pub fn get_arity(&self) -> usize {
        self.local_predicate.arity()
    }

    /// Get the number of constraints enforced by this predicate
    pub fn num_constraints(&self) -> usize {
        self.num_constraints
    }

    /// Get the vector of constrints enforced by this predicate
    /// Each constraint is a list of linear combinations with size equal to the
    /// arity
    pub fn get_constraints(&self) -> &Vec<Constraint> {
        &self.argument_lcs
    }

    /// Get a reference to the local predicate in this predicate constraint
    /// system
    pub fn get_local_predicate(&self) -> &LocalPredicate<F> {
        &self.local_predicate
    }

    /// Enforce a constraint in this predicate constraint system
    /// The constraint is a list of linear combinations with size equal to the
    /// arity
    pub fn enforce_constraint(&mut self, constraint: Constraint) -> crate::utils::Result<()> {
        if constraint.len() != self.get_arity() {
            return Err(ArityMismatch);
        }

        for (i, lc_index) in constraint.iter().enumerate() {
            self.argument_lcs[i].push(*lc_index);
        }

        self.num_constraints += 1;
        Ok(())
    }

    fn iter_constraints(&self) -> impl Iterator<Item = Constraint> + '_ {
        // Transpose the `argument_lcs` to iterate over constraints
        let num_constraints = self.num_constraints;

        (0..num_constraints).map(move |i| {
            (0..self.get_arity())
                .map(|j| self.argument_lcs[j][i])
                .collect::<Vec<LcIndex>>()
        })
    }

    /// Check if the constraints enforced by this predicate are satisfied
    /// i.e. L(x_1, x_2, ..., x_n) = 0
    pub fn which_constraint_is_unsatisfied(&self, cs: &ConstraintSystem<F>) -> Option<usize> {
        for (i, constraint) in self.iter_constraints().enumerate() {
            let variables: Vec<F> = constraint
                .iter()
                .map(|lc_index| cs.assigned_value(SymbolicLc(*lc_index)).unwrap())
                .collect();
            let result = self.local_predicate.evaluate(&variables);
            if result {
                return Some(i);
            }
        }
        None
    }

    /// Create the set of matrices for this predicate constraint system
    pub fn to_matrices(&self, cs: &ConstraintSystem<F>) -> Vec<Matrix<F>> {
        let mut matrices: Vec<Matrix<F>> = vec![Vec::new(); self.get_arity()];
        for constraint in self.iter_constraints() {
            for (matrix_ind, lc_index) in constraint.iter().enumerate() {
                let lc: LinearCombination<F> = cs.get_lc(*lc_index).unwrap();
                let row: Vec<(F, usize)> = cs.make_row(&lc);
                matrices[matrix_ind].push(row);
            }
        }
        matrices
    }
}
