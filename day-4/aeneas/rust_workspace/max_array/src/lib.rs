pub fn max_element<const N: usize>(data: [u8; N]) -> u8 {
    let mut max: u8 = data[0];
    let mut i: usize = 1;
    while i < N {
        if data[i] > max {
            max = data[i];
        }
        i += 1;
    }
    max
}


/*------------------------------------------------------------------------------
    Unit Tests
------------------------------------------------------------------------------*/


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_element() {
        assert_eq!(max_element([7]), 7);
    }

    #[test]
    fn max_in_middle() {
        assert_eq!(max_element([3, 1, 9, 2, 9, 5]), 9);
    }

    #[test]
    fn max_at_start() {
        assert_eq!(max_element([200, 10, 20]), 200);
    }
}
