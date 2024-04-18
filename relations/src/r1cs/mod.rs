//! Core interface for working with Rank-1 Constraint Systems (R1CS).



#[macro_use]
mod constraint_system;
#[cfg(feature = "std")]
mod trace;

#[cfg(feature = "std")]
pub use crate::r1cs::trace::{ConstraintLayer, ConstraintTrace, TraceStep, TracingMode};

pub use tracing::info_span;
pub use ark_ff::{Field, ToConstraintField};
pub use constraint_system::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace,
    OptimizationGoal, SynthesisMode
};


pub use crate::utils::error;
pub use crate::utils::error::SynthesisError;

pub use crate::utils::variable::*;
pub use crate::utils::*;

pub use crate::utils::impl_lc::*;

/// Generate a `Namespace` with name `name` from `ConstraintSystem` `cs`.
/// `name` must be a `&'static str`.
#[macro_export]
macro_rules! ns {
    ($cs:expr, $name:expr) => {{
        let span = $crate::r1cs::info_span!(target: "r1cs", $name);
        let id = span.id();
        let _enter_guard = span.enter();
        core::mem::forget(_enter_guard);
        core::mem::forget(span);
        $crate::r1cs::Namespace::new($cs.clone(), id)
    }};
}

