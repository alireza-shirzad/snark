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

use crate::{
    lc,
    utils::{
        error::SynthesisError,
        impl_lc::LinearCombination,
        variable::{Matrix, Variable},
    },
};

use super::predicate::{self, LocalPredicate};

#[derive(Clone, Debug)]
pub struct DummyCircuit_1;
pub struct DummyCircuit_2;

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
impl<F: Field + core::convert::From<i8>> ConstraintSynthesizer<F> for DummyCircuit_2 {
    fn generate_constraints(self, mut cs: ConstraintSystemRef<F>) -> crate::utils::Result<()> {
        let a = cs.new_input_variable(|| Ok(F::from(1u8))).unwrap();
        let b = cs.new_input_variable(|| Ok(F::from(1u8))).unwrap();
        let c = cs.new_witness_variable(|| Ok(F::from(2u8))).unwrap();
        let d = cs.new_witness_variable(|| Ok(F::from(3u8))).unwrap();
        let e = cs.new_witness_variable(|| Ok(F::from(2u8))).unwrap();

        let mut local_predicate_1 = LocalPredicate::new_poly_predicate(4, Vec::new()).unwrap();

        cs.register_predicate("poly-predicate-1", local_predicate_1);
        let predicate1_constraint1 = vec![
            lc!() + e,
            lc!() + (F::from(2u8), a) + (F::from(3u8), b),
            lc!() + (F::from(5u8), b) + c + d,
            lc!() + (F::from(4u8), a) + c + d + e,
        ];
        let predicate1_constraint2 = vec![
            lc!() + (F::from(4u8), a) + (F::from(2u8), c) + (F::from(2u8), e),
            lc!() + a + b + c + d + e,
            lc!() + a + b,
            lc!() + c + (F::from(2u8), d) + (F::from(6u8), e),
        ];
        cs.enforce_constraint(predicate1_constraint1, "poly-predicate-1");

        let index = cs.to_index().unwrap();

        assert_eq!(
            vec![
                vec![
                    vec![(F::one(), 4)],
                    vec![(F::from(4u8), 0), (F::from(2u8), 2), (F::from(2u8), 4)]
                ],
                vec![
                    vec![(F::from(2u8), 0), (F::from(3u8), 1)],
                    vec![
                        (F::one(), 0),
                        (F::one(), 1),
                        (F::one(), 2),
                        (F::one(), 3),
                        (F::one(), 4),
                    ]
                ],
                vec![
                    vec![(F::from(5u8), 1), (F::one(), 2), (F::one(), 3)],
                    vec![(F::one(), 0), (F::one(), 1)]
                ],
                vec![
                    vec![
                        (F::from(4u8), 0),
                        (F::one(), 2),
                        (F::one(), 3),
                        (F::one(), 4)
                    ],
                    vec![(F::one(), 2), (F::from(2u8), 3), (F::from(6u8), 4)]
                ]
            ],
            index.predicates[0].matrices
        );
        Ok(())
    }
}

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
impl<F: Field + core::convert::From<i8>> ConstraintSynthesizer<F> for DummyCircuit_1 {
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
        assert!(cs.is_satisfied().unwrap());
    }


    #[test]
    fn test_dummy_circuit_2() {
        let c = DummyCircuit_2;
        let cs = ConstraintSystem::<Fr>::new_ref();
        c.generate_constraints(cs.clone()).unwrap();
        let cs = cs.borrow().unwrap();
        let index = cs.to_index().unwrap();
    }
}
