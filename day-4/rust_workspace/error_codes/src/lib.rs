/* 
    In the real linux kernel, this is defined in the C bindings, but we isolate it here.
    addapted from Linux Foundation presentation: 
    "Mentorship Series - Rust for Linux: Code Documentation & Tests."
    Youtube: https://www.youtube.com/watch?v=J8yoUQKEY5g
    time: 47:34
*/

pub const MAX_ERROR_CODE: i32 = 4095; 

/// A pure Rust wrapper that represents a valid Linux kernel error.
pub struct ErrorCode {
    value: i32,
}

impl ErrorCode {
    /// Creates an `ErrorCode` from a raw integer.
    pub fn from_code(code: i32) -> Result<Self, ()> {
        // We ensure the code is strictly positive and within bounds.
        // (Note: The kernel handles negative C errnos by negating them first).
        if code <= 0 || code > MAX_ERROR_CODE {
            return Err(());
        }
        
        // INVARIANT: The check above ensures the mathematical type invariant holds.
        Ok(ErrorCode { value: code })
    }

    /// Safely extracts the raw error code.
    pub fn to_code(self) -> i32 {
        self.value
    }
}


/*------------------------------------------------------------------------------
    Unit Tests
------------------------------------------------------------------------------*/


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_code_roundtrips() {
        let ec = ErrorCode::from_code(42).unwrap();
        assert_eq!(ec.to_code(), 42);
    }

    #[test]
    fn zero_is_rejected() {
        assert!(ErrorCode::from_code(0).is_err());
    }

    #[test]
    fn negative_is_rejected() {
        assert!(ErrorCode::from_code(-1).is_err());
    }

    #[test]
    fn max_error_code_is_accepted() {
        assert!(ErrorCode::from_code(MAX_ERROR_CODE).is_ok());
    }

    #[test]
    fn above_max_is_rejected() {
        assert!(ErrorCode::from_code(MAX_ERROR_CODE + 1).is_err());
    }
}

