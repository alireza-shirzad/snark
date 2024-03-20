use core::result;

use crate::utils::error::SynthesisError;
use crate::utils::impl_lc::LinearCombination;
use crate::utils::variable::*;

use ark_ff::Field;
use ark_std::vec::Vec;
use ark_std::{string::String};

#[cfg(feature = "std")]
use crate::gr1cs::trace::ConstraintTrace;

/// The types of local predicates used in GR1CS
/// For now we only add polynomial and lookup predicates
#[derive(Debug, Clone)]
pub enum LocalPredicateType<F> {
    /// Indicates that the local predicate is a polynomial predicate
    Polynomial(Polynomial<F>),
    /// Indicates that the local predicatea lookup predicate
    Lookup,
}

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

    #[cfg(feature = "std")]
    constraint_traces: Vec<Option<ConstraintTrace>>,

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
            #[cfg(feature = "std")]
            constraint_traces: Vec::new(),
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
                let trace;
                #[cfg(feature = "std")]
                {
                    trace = self.constraint_traces[i].as_ref().map_or_else(
                        || {
                            eprintln!("Constraint trace requires enabling `ConstraintLayer`");
                            format!("{}", i)
                        },
                        |t| format!("{}", t),
                    );
                }
                #[cfg(not(feature = "std"))]
                {
                    trace = format!("{}", i);
                }
                return Ok(Some(trace));
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

#[derive(Debug, Clone)]
pub struct Polynomial<F> {
    arity: usize,
    terms: Vec<Term<F>>,
}
impl<F: Field> Polynomial<F> {
    pub fn new(arity: usize, terms: Vec<(F, Vec<usize>)>) -> crate::utils::Result<Self> {
        let mut inner_terms: Vec<Term<F>> = Vec::new();
        for term in terms {
            if term.1.len() != arity {
                return Err(SynthesisError::ArityMismatch);
            }
            inner_terms.push(Term {
                coefficient: term.0,
                exponents: term.1,
            });
        }
        Ok(Self {
            arity,
            terms: inner_terms,
        })
    }
    pub fn evaluate(&self, point: &EvaluationPoint<F>) -> crate::utils::Result<F> {
        let mut result = F::zero();
        for term in self.terms.iter() {
            result = result + term.compute(&point)?;
        }
        Ok(result)
    }
}

#[derive(Debug, Clone)]
struct Term<F> {
    coefficient: F,
    exponents: Vec<usize>,
}

impl<F: Field> Term<F> {
    pub fn compute(&self, point: &EvaluationPoint<F>) -> crate::utils::Result<F> {
        if point.len() != self.exponents.len() {
    
            return Err(SynthesisError::ArityMismatch);
        }
        let mut result: F = self.coefficient;
        for (index, exponent) in self.exponents.iter().enumerate() {
            let exponent: usize = *exponent;
            result = result * point[index].pow([exponent as u64])
        }
        Ok(result)
    }
}

pub type EvaluationPoint<F> = Vec<F>;

#[cfg(test)]
mod tests {
    use crate::gr1cs::*;
    use ark_ff::{One, Zero};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn polynomial_tests() -> crate::utils::Result<()> {
        // P(X_1,X_2,X_3) = 4X_1X_2^5 + X_1X_3 + 3X_2^3 + 6
        let polynomial = predicate::Polynomial::<Fr>::new(
            3,
            vec![
                (Fr::from(4u8), vec![1, 5, 0]),
                (Fr::from(1u8), vec![1, 0, 3]),
                (Fr::from(3u8), vec![0, 3, 0]),
                (Fr::from(6u8), vec![0, 0, 0]),
            ],
        )?;

        // Test on point (0,0,0)
        assert_eq!(
            Fr::from(6u8),
            polynomial
                .evaluate(&vec![Fr::zero(), Fr::zero(), Fr::zero()])
                .unwrap()
        );
        // Test on point (1,1,1)
        assert_eq!(
            Fr::from(14u8),
            polynomial
                .evaluate(&vec![Fr::one(), Fr::one(), Fr::one()])
                .unwrap()
        );
        // Test on point (10,3,5)
        assert_eq!(
            Fr::from(11057u16),
            polynomial
                .evaluate(&vec![Fr::from(10u8), Fr::from(3u8), Fr::from(5u8)])
                .unwrap()
        );

        // Test on point (1,10,3,5) with wrong arity
        assert_eq!(
            Err(error::SynthesisError::ArityMismatch),
            polynomial.evaluate(&vec![
                Fr::from(1u8),
                Fr::from(10u8),
                Fr::from(3u8),
                Fr::from(5u8)
            ])
        );
        Ok(())
    }
}
