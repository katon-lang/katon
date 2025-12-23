use std::fmt;

use crate::ast::Type;

#[derive(Debug, Clone, PartialEq)]
pub enum CheckError {
    UseAfterMove { var: String },
    TypeMismatch { expected: Type, found: Type },
    InvalidIndex { base_ty: Type },
    UndefinedVariable { var: String },
    UndefinedArray { var: String },
    AssignToMoved { var: String },
    VerificationError { kind: VerificationError },
    TypeError { msg: String },
    InternalError(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VerificationError {
    PreconditionNotSatisfied,
    PostconditionNotProven,
    InvariantNotEstablished,
    InvariantNotPreserved,
    AssertionMayFail,
    DivisionByZero,
    ArrayIndexOutOfBounds,
    UndefinedBehavior(String),
}

impl CheckError {
    pub fn is_verification_error(&self) -> bool {
        matches!(self, CheckError::VerificationError { .. })
    }

    pub fn is_internal(&self) -> bool {
        matches!(self, CheckError::InternalError(_))
    }
}

impl fmt::Display for VerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerificationError::PreconditionNotSatisfied => write!(f, "precondition may not hold"),

            VerificationError::PostconditionNotProven => {
                write!(f, "postcondition could not be proven")
            }

            VerificationError::InvariantNotEstablished => {
                write!(f, "loop invariant does not hold on entry")
            }

            VerificationError::InvariantNotPreserved => {
                write!(f, "loop invariant is not preserved by the loop body")
            }

            VerificationError::AssertionMayFail => write!(f, "assertion may fail"),

            VerificationError::DivisionByZero => write!(f, "possible division by zero"),

            VerificationError::ArrayIndexOutOfBounds => {
                write!(f, "array index may be out of bounds")
            }

            VerificationError::UndefinedBehavior(msg) => write!(f, "undefined behavior: {}", msg),
        }
    }
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckError::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "mismatched types\nexpected: {:?}\n   found: {:?}",
                    expected, found
                )
            }
            CheckError::InvalidIndex { base_ty } => {
                write!(f, "cannot index into a value of type `{:?}`", base_ty)
            }
            CheckError::TypeError { msg } => {
                write!(f, "{}", msg) // Here 'msg' is actually the custom message
            }
            CheckError::UndefinedVariable { var } => {
                write!(f, "cannot find value `{}` in this scope", var)
            }
            CheckError::UseAfterMove { var } => {
                write!(f, "use of moved value: '{}'", var)
            }
            CheckError::UndefinedArray { var } => write!(f, "array `{}` is undefined", var),
            CheckError::VerificationError { kind } => {
                write!(f, "verification failed: {}", kind)
            }
            CheckError::InternalError(msg) => write!(f, "internal compiler error: {}", msg),
            _ => write!(f, "{:?}", self),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    pub error: CheckError,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(start <= end);
        Span { start, end }
    }

    /// Dummy span for tests, desugaring, or generated code
    pub fn dummy() -> Self {
        Span { start: 0, end: 0 }
    }

    /// Length in bytes
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    // 0..0 is both empty and dummy
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // 5..5 is empty but not dummy
    pub fn is_dummy(&self) -> bool {
        self.start == 0 && self.end == 0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }

    pub fn dummy(node: T) -> Self {
        Self {
            node,
            span: Span::dummy(),
        }
    }
}

impl Diagnostic {
    pub fn emit(&self, source: &str) {
        let line_num = source[..self.span.start].lines().count() + 1;
        let snippet = &source[self.span.start..self.span.end];

        let kind = match self.error {
            CheckError::VerificationError { .. } => "verification error",
            _ => "error",
        };

        println!("{}: {}", kind, self.error);
        println!(" --> line {}", line_num);
        println!("  |");
        println!("{:3} | {}", line_num, snippet);
        println!("  | {}", "^".repeat(self.span.len().max(1)));
        println!("  |");
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.error {
            CheckError::UseAfterMove { var } => {
                write!(
                    f,
                    "Borrow error: use of moved value '{}'\n  at {:?}",
                    var, self.span
                )
            }
            CheckError::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "Type error: expected '{}', found '{}'\n  at {:?}",
                    expected, found, self.span
                )
            }
            CheckError::InvalidIndex { base_ty } => {
                write!(
                    f,
                    "Type error: cannot index into value of type '{}'\n  at {:?}",
                    base_ty, self.span
                )
            }
            CheckError::UndefinedVariable { var } => {
                write!(f, "Variable '{}' undefined\n at {:?}", var, self.span)
            }
            CheckError::AssignToMoved { var } => {
                write!(
                    f,
                    "Borrow Error: Cannot assign to moved or uninitialized '{}'\n at {:?}",
                    var, self.span
                )
            }
            CheckError::UndefinedArray { var } => {
                write!(f, "Array '{}' undefined\n at {:?}", var, self.span)
            }
            CheckError::TypeError { msg } => {
                write!(f, "Type error: {}\n at {:?}", msg, self.span)
            }
            CheckError::VerificationError { kind } => {
                write!(f, "Verification error: {}\n at {:?}", kind, self.span)
            }
            CheckError::InternalError(msg) => {
                write!(f, "internal compiler error: {}", msg)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_error_is_detected() {
        let err = CheckError::VerificationError {
            kind: VerificationError::AssertionMayFail,
        };

        assert!(err.is_verification_error());
        assert!(!err.is_internal());
    }

    #[test]
    fn test_internal_error_is_detected() {
        let err = CheckError::InternalError("ICE".into());

        assert!(err.is_internal());
        assert!(!err.is_verification_error());
    }

    #[test]
    fn test_verification_error_display_messages() {
        let cases = vec![
            (
                VerificationError::PreconditionNotSatisfied,
                "precondition may not hold",
            ),
            (
                VerificationError::PostconditionNotProven,
                "postcondition could not be proven",
            ),
            (
                VerificationError::InvariantNotEstablished,
                "loop invariant does not hold on entry",
            ),
            (
                VerificationError::InvariantNotPreserved,
                "loop invariant is not preserved by the loop body",
            ),
            (VerificationError::AssertionMayFail, "assertion may fail"),
            (
                VerificationError::DivisionByZero,
                "possible division by zero",
            ),
            (
                VerificationError::ArrayIndexOutOfBounds,
                "array index may be out of bounds",
            ),
        ];

        for (err, expected) in cases {
            assert_eq!(err.to_string(), expected);
        }
    }

    #[test]
    fn test_undefined_behavior_includes_message() {
        let err = VerificationError::UndefinedBehavior("null dereference".into());
        assert_eq!(err.to_string(), "undefined behavior: null dereference");
    }

    #[test]
    fn test_use_after_move_display() {
        let err = CheckError::UseAfterMove { var: "x".into() };

        assert_eq!(err.to_string(), "use of moved value: 'x'");
    }

    #[test]
    fn test_undefined_variable_display() {
        let err = CheckError::UndefinedVariable { var: "y".into() };

        assert_eq!(err.to_string(), "cannot find value `y` in this scope");
    }

    #[test]
    fn test_verification_error_wrapped_display() {
        let err = CheckError::VerificationError {
            kind: VerificationError::DivisionByZero,
        };

        assert_eq!(
            err.to_string(),
            "verification failed: possible division by zero"
        );
    }

    #[test]
    fn test_span_length_and_empty() {
        let s = Span::new(10, 15);
        assert_eq!(s.len(), 5);
        assert!(!s.is_empty());
        assert!(!s.is_dummy());
    }

    #[test]
    fn test_dummy_span_is_empty_and_dummy() {
        let s = Span::dummy();
        assert_eq!(s.len(), 0);
        assert!(s.is_empty());
        assert!(s.is_dummy());
    }

    #[test]
    fn test_spanned_dummy_uses_dummy_span() {
        let spanned = Spanned::dummy(42);
        assert_eq!(spanned.node, 42);
        assert!(spanned.span.is_dummy());
    }

    #[test]
    fn test_diagnostic_display_verification_error() {
        let diag = Diagnostic {
            error: CheckError::VerificationError {
                kind: VerificationError::AssertionMayFail,
            },
            span: Span::new(3, 7),
        };

        let msg = diag.to_string();

        assert!(msg.contains("Verification error"));
        assert!(msg.contains("assertion may fail"));
    }

    #[test]
    fn test_diagnostic_display_type_error() {
        let diag = Diagnostic {
            error: CheckError::TypeError {
                msg: "expected int".into(),
            },
            span: Span::new(0, 1),
        };

        let msg = diag.to_string();

        assert!(msg.contains("Type error"));
        assert!(msg.contains("expected int"));
    }
}
