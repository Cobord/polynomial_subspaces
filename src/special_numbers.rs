#[allow(dead_code)]
pub trait SpecialNumbers {
    const SQRT_TWO: Self;
    const PI: Self;
    const SQRT_PI: Self;
}

impl SpecialNumbers for f64 {
    const SQRT_TWO: Self = std::f64::consts::SQRT_2;

    const PI: Self = std::f64::consts::PI;

    const SQRT_PI: Self = 2.0 / std::f64::consts::FRAC_2_SQRT_PI;
}

impl SpecialNumbers for f32 {
    const SQRT_TWO: Self = std::f32::consts::SQRT_2;

    const PI: Self = std::f32::consts::PI;

    const SQRT_PI: Self = 2.0 / std::f32::consts::FRAC_2_SQRT_PI;
}
