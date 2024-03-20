use core::fmt;

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
    /// During Constraint Enforcing, The number of linear combinations did not match the predicate arity
    ArityMismatch,
    /// Returns not implemented errors
    NotImplemented,
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
            SynthesisError::UnconstrainedVariable => {
                write!(f, "Number of linear combinations should match the predicate arity")
            },
            SynthesisError::ArityMismatch => {
                write!(f, "The Arity of the constraints provided does not match the arity supported by the local predicate")
            },
            SynthesisError::NotImplemented => {
                write!(f, "This function has not been implemented yet")
            },
        }
    }
}
