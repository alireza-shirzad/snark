use ark_ff::Field;
use ark_std::log2;
use ark_std::vec::Vec;
use ark_std::collections::BTreeMap;
use crate::gr1cs::predicate::LocalPredicate;
use crate::utils::variable::Matrix;

use super::impl_lc::{LcIndex, LinearCombination};
use super::predicate::{self, LocalPredicateType};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Write};

#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize)]
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

impl <F:Field> CanonicalSerialize for Predicate<F> {
    // We only have to implement the `serialize_with_mode` method; the other methods 
    // have default implementations that call the latter.
    //
    // Notice that `serialize_with_mode` takes `mode: Compress` as an argument. This 
    // is used to indicate whether we want to serialize with or without compression.
    fn serialize_with_mode<W: Write>(&self, mut writer: W, mode: Compress) -> Result<(), SerializationError> {
        self.m.serialize_with_mode(&mut writer, mode)?;
        self.t.serialize_with_mode(&mut writer, mode)?;
        self.matrices.serialize_with_mode(&mut writer, mode)?;
        Ok(())
    }

    fn serialized_size(&self, mode: Compress) -> usize {
        self.m.serialized_size(mode) + self.t.serialized_size(mode) + self.matrices.serialized_size(mode)
    }
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
        lc_map:&BTreeMap<LcIndex, LinearCombination<F>>
    ) -> crate::utils::Result<()> {

        let mut predicate_matrices: Vec<Matrix<F>> = vec![Matrix::new(); local_predicate.arity];
        let predicate_constraints: &Vec<Vec<LcIndex>> = &local_predicate.constraints;

        for (argument_index, argument_constraints) in predicate_constraints.iter().enumerate() {
            for argument_constraint in argument_constraints {
                let argument_lc: &LinearCombination<F> = lc_map.get(argument_constraint).expect("no symbolic LCs");
                predicate_matrices[argument_index].push(self.make_row(argument_lc));
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
        // std::dbg!(&l);
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