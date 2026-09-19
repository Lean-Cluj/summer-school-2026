pub fn affine_encrypt<const N: usize>(mut data: [u8; N], a: u8, b: u8) -> [u8; N] {
    let mut i: usize = 0;
    while i < N {
        data[i] = data[i].wrapping_mul(a).wrapping_add(b);
        i += 1;
    }
    data
}


/*------------------------------------------------------------------------------
    Unit Tests
------------------------------------------------------------------------------*/


#[cfg(test)]
mod tests {
    use super::*;

    // A key (a, b) = (3, 7). `a` must be odd to be invertible modulo 256.
    const A: u8 = 3;
    const B: u8 = 7;

    // Decrypting is `affine_encrypt` again, with a different (a, b) pair:
    // a_inv is the multiplicative inverse of a modulo 256
    // (3 * 171 = 513 = 2 * 256 + 1), and b_inv = -(a_inv * b) mod 256
    // (171 * 7 = 1197 = 4 * 256 + 173, so b_inv = 256 - 173 = 83).
    const A_INV: u8 = 171;
    const B_INV: u8 = 83;

    #[test]
    fn empty_array() {
        let data: [u8; 0] = [];
        assert_eq!(affine_encrypt(data, A, B), data);
    }

    #[test]
    fn known_value_no_wraparound() {
        // (3 * 5 + 7) mod 256 = 22
        assert_eq!(affine_encrypt([5], A, B), [22]);
    }

    #[test]
    fn known_value_with_wraparound() {
        // 3 * 250 = 750, 750 mod 256 = 238, 238 + 7 = 245
        assert_eq!(affine_encrypt([250], A, B), [245]);
    }

    #[test]
    fn multiple_elements() {
        assert_eq!(affine_encrypt([5, 250], A, B), [22, 245]);
    }

    #[test]
    fn applying_twice_with_the_inverse_key_decrypts() {
        let data = [0, 1, 5, 42, 128, 200, 250, 254, 255];
        let encrypted = affine_encrypt(data, A, B);
        assert_ne!(encrypted, data);
        let decrypted = affine_encrypt(encrypted, A_INV, B_INV);
        assert_eq!(decrypted, data);
    }
}
