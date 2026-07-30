// In the real kernel, this is defined in the C bindings, but we isolate it here.
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

