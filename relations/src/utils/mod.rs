pub mod variable;
pub mod error;
pub mod impl_lc;


/// A result type specialized to `SynthesisError`.
pub type Result<T> = core::result::Result<T, error::SynthesisError>;