pub fn xor_encrypt<const N: usize>(mut data: [u8; N], key: u8) -> [u8; N] {
    let mut i: usize = 0;
    while i < N {
        data[i] = data[i] ^ key;
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

    #[test]
    fn identity_with_zero_key() {
        let data = [1, 2, 3, 4, 5];
        assert_eq!(xor_encrypt(data, 0), data);
    }

    #[test]
    fn involution() {
        let data = [0, 1, 2, 3, 255, 128, 42];
        let key = 0xAB;
        let encrypted = xor_encrypt(data, key);
        assert_ne!(encrypted, data);
        assert_eq!(xor_encrypt(encrypted, key), data);
    }

    #[test]
    fn empty_array() {
        let data: [u8; 0] = [];
        assert_eq!(xor_encrypt(data, 0x42), data);
    }
}