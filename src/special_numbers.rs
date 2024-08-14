#[allow(dead_code)]
pub trait SpecialNumbers {
    const SQRT_TWO : Self;
    const PI : Self;
    const SQRT_PI : Self;
}

impl SpecialNumbers for f64 {
    const SQRT_TWO : Self = std::f64::consts::SQRT_2;

    const PI : Self = std::f64::consts::PI;

    const SQRT_PI : Self = todo!();
}