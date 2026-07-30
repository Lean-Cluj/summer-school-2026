pub enum Light { Red, Green, Yellow }

pub fn next_light(current: Light) -> Light {
    match current {
        Light::Red => Light::Green,
        Light::Green => Light::Yellow,
        Light::Yellow => Light::Red,
    }
}
