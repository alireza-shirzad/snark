use core::fmt;

use crate::gr1cs::LcIndex;

/// This is an error that could occur during circuit synthesis contexts,
/// such as CRS generation, proving or verification.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum SynthesisError {
    /// During synthesis, we tried to allocate a variable when
    /// `ConstraintSystemRef` was `None`.
    MissingCS,
    /// During synthesis, we lacked knowledge of a variable assignment.
    AssignmentMissing,
    /// During synthesis, we divided by zero.
    DivisionByZero,
    /// During synthesis, we constructed an unsatisfiable constraint system.
    Unsatisfiable,
    /// During synthesis, our polynomials ended up being too high of degree
    PolynomialDegreeTooLarge,
    /// During proof generation, we encountered an identity in the CRS
    UnexpectedIdentity,
    /// During verification, our verifying key was malformed.
    MalformedVerifyingKey,
    /// During CRS generation, we observed an unconstrained auxiliary variable
    UnconstrainedVariable,
    /// The string does not match to any predicate
    PredicateNotFound,
    /// The predicate expects a different arity
    ArityMismatch,
    /// The LcIndex provided does not correspond to any Linear Combination
    LcNotFound(LcIndex),
    /// The variable type is not expected for the operation
    UnexpectedVariable,
}

impl ark_std::error::Error for SynthesisError {}

impl fmt::Display for SynthesisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            SynthesisError::MissingCS => write!(f, "the constraint system was `None`"),
            SynthesisError::AssignmentMissing => {
                write!(f, "an assignment for a variable could not be computed")
            },
            SynthesisError::DivisionByZero => write!(f, "division by zero"),
            SynthesisError::Unsatisfiable => write!(f, "unsatisfiable constraint system"),
            SynthesisError::PolynomialDegreeTooLarge => write!(f, "polynomial degree is too large"),
            SynthesisError::UnexpectedIdentity => {
                write!(f, "encountered an identity element in the CRS")
            },
            SynthesisError::MalformedVerifyingKey => write!(f, "malformed verifying key"),
            SynthesisError::UnconstrainedVariable => {
                write!(f, "auxiliary variable was unconstrained")
            },
            SynthesisError::ArityMismatch => {
                write!(f, "The Arity for the predicate does not match the input")
            },
            SynthesisError::PredicateNotFound => {
                write!(f, "The predicate was not found in the constraint system")
            },
            SynthesisError::LcNotFound(ind) => {
                write!(
                    f,
                    "The LcIndex {} does not correspond to any Linear Combination",
                    ind.0
                )
            },
            SynthesisError::UnexpectedVariable => {
                write!(f, "Variable type is not expected for the operation")
            },
        }
    }
}
