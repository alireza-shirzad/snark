//! Core interface for working with Generalized Rank-1 Constraint Systems (GR1CS).

#[macro_use]
pub mod constraint_system;
pub mod predicate;
use crate::utils::error;

#[cfg(feature = "std")]
mod trace;

#[cfg(feature = "std")]
pub use crate::gr1cs::trace::{ConstraintLayer, ConstraintTrace, TraceStep, TracingMode};

use ark_std::vec::Vec;
pub use ark_ff::{Field};


use core::cmp::Ordering;




