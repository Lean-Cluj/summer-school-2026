pub enum Light { Red, Green, Yellow }

pub fn next_light(current: Light) -> Light {
    match current {
        Light::Red => Light::Green,
        Light::Green => Light::Yellow,
        Light::Yellow => Light::Red,
    }
}


/*------------------------------------------------------------------------------
    Unit Tests
------------------------------------------------------------------------------*/


#[cfg(test)]
mod tests {
    use super::*;

    // No `PartialEq`/`Debug` derive on `Light` (would add code Aeneas has to
    // translate), so assertions are written with `matches!` instead.
    #[test]
    fn cycle() {
        assert!(matches!(next_light(Light::Red), Light::Green));
        assert!(matches!(next_light(Light::Green), Light::Yellow));
        assert!(matches!(next_light(Light::Yellow), Light::Red));
    }

    #[test]
    fn full_loop_returns_to_start() {
        let l = next_light(next_light(next_light(Light::Red)));
        assert!(matches!(l, Light::Red));
    }
}
