// src/lib.rs

// The prime modulus: 2^31 - 1
pub const PRIME: u32 = 2147483647; 

pub struct M31 {
    pub value: u32,
}

pub fn add_m31(a: M31, b: M31) -> M31 {
    let mut sum = a.value + b.value;
    
    // If the sum exceeds the prime, wrap it around the field
    if sum >= PRIME {
        sum -= PRIME;
    }
    
    M31 { value: sum }
}


/*------------------------------------------------------------------------------
    Unit Tests
------------------------------------------------------------------------------*/


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_wraparound() {
        let r = add_m31(M31 { value: 2 }, M31 { value: 3 });
        assert_eq!(r.value, 5);
    }

    #[test]
    fn wraps_at_prime() {
        let r = add_m31(M31 { value: PRIME - 1 }, M31 { value: 1 });
        assert_eq!(r.value, 0);
    }

    #[test]
    fn wraps_past_prime() {
        let r = add_m31(M31 { value: PRIME - 1 }, M31 { value: 3 });
        assert_eq!(r.value, 2);
    }
}
