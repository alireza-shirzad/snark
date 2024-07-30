
use crate::utils::error::SynthesisError;
use crate::utils::impl_lc::LinearCombination;
use crate::utils::polynomial::Polynomial;
use crate::utils::variable::*;

use ark_ff::Field;
use ark_std::vec::Vec;
use ark_std::{string::String};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};


use super::impl_lc::LcIndex;

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


pub type PredicateArgument = Vec<LcIndex>;

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
    pub constraints: Vec<PredicateArgument>,
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
        constraint_lcs: Vec<LcIndex>,
    ) -> crate::utils::Result<()> {
        if self.arity != constraint_lcs.len() {
            return Err(SynthesisError::ArityMismatch);
        }
        self.num_constraints += 1;
        for i in 0..self.arity {
            self.constraints[i].push(constraint_lcs[i]);
        }
        Ok(())
    }


    // Getter method for `constraints`
    pub fn get_constraints(&self) -> &Vec<Vec<LcIndex>> {
        &self.constraints
    }


}
