use ark_std::vec::Vec;
pub use ark_ff::{Field, ToConstraintField};
use core::cmp::Ordering;



/// A sparse representation of constraint matrices.
/// Column numbers start from zero
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

pub fn transpose<F: Field>(matrix: &Matrix<F>) -> Matrix<F> {
    // First, find the maximum column index to know the size of the transposed matrix
    let max_cols = matrix.iter().flat_map(|row| row.iter().map(|&(_, col)| col + 1)).max().unwrap_or(0);

    // Initialize the transposed matrix with empty vectors
    let mut transposed: Matrix<F> = vec![Vec::new(); max_cols];

    // Iterate through each row and each element in the row
    for (row_index, row) in matrix.iter().enumerate() {
        for &(value, col_index) in row {
            // Add the element to the new row (which is originally a column) in the transposed matrix
            transposed[col_index].push((value, row_index));
        }
    }

    // Return the transposed matrix
    transposed
}

use crate::utils::impl_lc::LcIndex;

use super::impl_lc::LinearCombination;


/// Represents the different kinds of variables present in a constraint system.
#[derive(Copy, Clone, PartialEq, Debug, Eq)]
pub enum Variable {
    /// Represents the "zero" constant.
    Zero,
    /// Represents of the "one" constant.
    One,
    /// Represents a public instance variable.
    Instance(usize),
    /// Represents a private witness variable.
    Witness(usize),
    /// Represents of a linear combination.
    SymbolicLc(LcIndex),
    
}

impl Variable {
    /// Is `self` the zero variable?
    #[inline]
    pub fn is_zero(&self) -> bool {
        matches!(self, Variable::Zero)
    }

    /// Is `self` the one variable?
    #[inline]
    pub fn is_one(&self) -> bool {
        matches!(self, Variable::One)
    }

    /// Is `self` an instance variable?
    #[inline]
    pub fn is_instance(&self) -> bool {
        matches!(self, Variable::Instance(_))
    }

    /// Is `self` a witness variable?
    #[inline]
    pub fn is_witness(&self) -> bool {
        matches!(self, Variable::Witness(_))
    }

    /// Is `self` a linear combination?
    #[inline]
    pub fn is_lc(&self) -> bool {
        matches!(self, Variable::SymbolicLc(_))
    }

    /// Get the `LcIndex` in `self` if `self.is_lc()`.
    #[inline]
    pub fn get_lc_index(&self) -> Option<LcIndex> {
        match self {
            Variable::SymbolicLc(index) => Some(*index),
            _ => None,
        }
    }

    /// Returns `Some(usize)` if `!self.is_lc()`, and `None` otherwise.
    #[inline]
    pub fn get_index_unchecked(&self, witness_offset: usize) -> Option<usize> {
        match self {
            // The one variable always has index 0
            Variable::One => Some(0),
            Variable::Instance(i) => Some(*i),
            Variable::Witness(i) => Some(witness_offset + *i),
            _ => None,
        }
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Variable::*;
        match (self, other) {
            (Zero, Zero) => Some(Ordering::Equal),
            (One, One) => Some(Ordering::Equal),
            (Zero, _) => Some(Ordering::Less),
            (One, _) => Some(Ordering::Less),
            (_, Zero) => Some(Ordering::Greater),
            (_, One) => Some(Ordering::Greater),

            (Instance(i), Instance(j)) | (Witness(i), Witness(j)) => i.partial_cmp(j),
            (Instance(_), Witness(_)) => Some(Ordering::Less),
            (Witness(_), Instance(_)) => Some(Ordering::Greater),

            (SymbolicLc(i), SymbolicLc(j)) => i.partial_cmp(j),
            (_, SymbolicLc(_)) => Some(Ordering::Less),
            (SymbolicLc(_), _) => Some(Ordering::Greater),
        }
    }
}

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}
