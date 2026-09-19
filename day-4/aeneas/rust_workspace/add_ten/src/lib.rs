pub fn add_ten(x: u32) -> u32 {
    x + 10
}

/*------------------------------------------------------------------------------
    Unit Tests
------------------------------------------------------------------------------*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        assert_eq!(add_ten(0), 10);
        assert_eq!(add_ten(5), 15);
        assert_eq!(add_ten(32), 42);
    }
}
