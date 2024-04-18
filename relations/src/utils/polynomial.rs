
use crate::utils::error::SynthesisError;

use ark_ff::Field;
use ark_std::vec::Vec;



#[derive(Clone,Debug, PartialEq, Eq)]
pub struct Polynomial<F> {
    pub arity: usize,
    pub terms: Vec<Term<F>>,
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

    pub fn get_degree(&self) -> usize {
        self.terms.iter().map(|term| term.get_degree()).max().unwrap()
    }

}

#[derive(Clone,Debug, PartialEq, Eq)]
pub struct Term<F> {
    pub coefficient: F,
    pub exponents: Vec<usize>,
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
    fn get_degree(&self) -> usize {
        self.exponents.iter().sum()
    }
}

pub type EvaluationPoint<F> = Vec<F>;

#[cfg(test)]
mod tests {
    use crate::utils::polynomial::*;
    use ark_ff::{One, Zero};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn polynomial_tests() -> crate::utils::Result<()> {
        // P(X_1,X_2,X_3) = 4X_1X_2^5 + X_1X_3 + 3X_2^3 + 6
        let polynomial = Polynomial::<Fr>::new(
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
            Err(crate::utils::error::SynthesisError::ArityMismatch),
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
