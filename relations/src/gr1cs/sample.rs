use super::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
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
};

use crate::{lc, utils::{
    error::SynthesisError,
    impl_lc::LinearCombination,
    variable::{Matrix, Variable},
}};

use super::predicate::{self, LocalPredicate};

#[derive(Clone, Debug)]
pub struct DummyCircuit_1;

impl<F: Field+ core::convert::From<i8>> ConstraintSynthesizer<F> for DummyCircuit_1 {
    fn generate_constraints(self, mut cs: ConstraintSystemRef<F>) -> crate::utils::Result<()> {

        let x1 = cs.new_input_variable(|| Ok(F::from(1u8))).unwrap();
        let x2 = cs.new_input_variable(|| Ok(F::from(2u8))).unwrap();
        let x3 = cs.new_input_variable(|| Ok(F::from(3u8))).unwrap();
        let x4 = cs.new_input_variable(|| Ok(F::from(0u8))).unwrap();
        let x5 = cs.new_input_variable(|| Ok(F::from(1255254u32))).unwrap();
        let w1 = cs.new_witness_variable(|| Ok(F::from(4u8))).unwrap();
        let w2 = cs.new_witness_variable(|| Ok(F::from(2u8))).unwrap();
        let w3 = cs.new_witness_variable(|| Ok(F::from(5u8))).unwrap();
        let w4 = cs.new_witness_variable(|| Ok(F::from(29u8))).unwrap();
        let w5 = cs.new_witness_variable(|| Ok(F::from(28u8))).unwrap();
        let w6 = cs.new_witness_variable(|| Ok(F::from(10u8))).unwrap();
        let w7 = cs.new_witness_variable(|| Ok(F::from(57u8))).unwrap();
        let w8 = cs.new_witness_variable(|| Ok(F::from(22022u32))).unwrap();
    
        let mut local_predicate_a = LocalPredicate::new_poly_predicate(
            4,
            vec![
                (F::from(1u8), vec![1, 1, 0, 0]),
                (F::from(3u8), vec![0, 0, 2, 0]),
                (F::from(-1i8), vec![0, 0, 0, 1]),
            ],
        )
        .unwrap();
        let mut local_predicate_b = LocalPredicate::new_poly_predicate(
            3,
            vec![
                (F::from(7u8), vec![0, 1, 0]),
                (F::from(1u8), vec![3, 0, 0]),
                (F::from(-1i8), vec![0, 0, 1]),
            ],
        )
        .unwrap();
        let mut local_predicate_c = LocalPredicate::new_poly_predicate(
            3,
            vec![
                (F::from(1u8), vec![1, 1, 0]),
                (F::from(-1i8), vec![0, 0, 1]),
            ],
        )
        .unwrap();
    
        cs.register_predicate("poly-predicate-A", local_predicate_a);
        cs.register_predicate("poly-predicate-B", local_predicate_b);
        cs.register_predicate("poly-predicate-C", local_predicate_c);
    
        let predicate_a_constraint_1 = vec![lc!() + x1, lc!() + x2, lc!() + x3, lc!() + w4];
        let predicate_b_constraint_1 = vec![lc!() + x4, lc!() + w1, lc!() + w5];
        let predicate_c_constraint_1 = vec![lc!() + w2, lc!() + w3, lc!() + w6];
        let predicate_b_constraint_2 = vec![lc!() + w5, lc!() + w6, lc!() + w8];
        let predicate_c_constraint_2 = vec![lc!() + w5 + w4, lc!() + w8, lc!() + x5];
    
        cs.enforce_constraint(predicate_a_constraint_1, "poly-predicate-A");
        cs.enforce_constraint(predicate_b_constraint_1, "poly-predicate-B");
        cs.enforce_constraint(predicate_c_constraint_1, "poly-predicate-C");
        cs.enforce_constraint(predicate_b_constraint_2, "poly-predicate-B");
        cs.enforce_constraint(predicate_c_constraint_2, "poly-predicate-C");
        Ok(())
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{One, Zero};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn test_dummy_circuit_1() {
        let c = DummyCircuit_1;
        let cs = ConstraintSystem::<Fr>::new_ref();
        c.generate_constraints(cs.clone()).unwrap();
        let cs = cs.borrow().unwrap();
        let index = cs.to_index().unwrap();
        let max_deg = index.get_max_degree();    }
}