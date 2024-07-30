//! Core interface for working with Generalized Rank-1 Constraint Systems (GR1CS).

#[macro_use]
pub mod constraint_system;
pub mod predicate;
pub mod sample;
pub mod index;
mod Index;


pub use tracing::info_span;
pub use constraint_system::{
     ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace,
    OptimizationGoal, SynthesisMode,
};
pub use crate::utils::error;
pub use crate::utils::error::SynthesisError;

pub use crate::utils::variable::*;
pub use crate::utils::*;

pub use crate::utils::impl_lc::*;


pub use predicate::MUL;


/// Generate a `Namespace` with name `name` from `ConstraintSystem` `cs`.
/// `name` must be a `&'static str`.
#[macro_export]
macro_rules! gns {
    ($cs:expr, $name:expr) => {{
        let span = $crate::gr1cs::info_span!(target: "gr1cs", $name);
        let id = span.id();
        let _enter_guard = span.enter();
        core::mem::forget(_enter_guard);
        core::mem::forget(span);
        $crate::gr1cs::Namespace::new($cs.clone(), id)
    }};
}
