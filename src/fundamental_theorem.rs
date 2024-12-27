use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub};

use crate::generic_polynomial::{DegreeType, Generic1DPoly, SmallIntegers};

pub enum FindZeroError {
    EverythingIsAZeroForZeroPolynomial,
    AbelRuffiniUnsolvability(DegreeType),
}

pub trait FundamentalTheorem<T>: Generic1DPoly<T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + DivAssign<T>,
{
    /// give those solutions that are within T without needing an extension
    /// `zero_pred` is there to determine if a T is 0 or not
    /// `my_sqrt` gives the square root if it existed within T without needing an extension
    /// `my_cube_root` gives a cube root if it existed within T without needing an extension
    ///     and if applicable a cube root of unity
    /// # Errors
    /// either it was the zero polynomial and everything is a zero not a small `Vec<(T, usize)>`
    ///     for x-values and multiplicities
    /// or the polynomial was not exactly solvable in radicals due to Galois considerations
    fn find_zeros(
        &self,
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, FindZeroError>;
}

pub(crate) fn quadratic_solve<T>(
    constant_term: T,
    linear_coeff: T,
    quadratic_coeff: T,
    zero_pred: &impl Fn(&T) -> bool,
    my_sqrt: &impl Fn(&T) -> Option<T>,
) -> Vec<(T, usize)>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + From<SmallIntegers>
        + Sub<Output = T>
        + DivAssign<T>,
{
    let two_t: T = 2.into();
    let four_t: T = 4.into();
    let discriminant = linear_coeff.clone() * linear_coeff.clone()
        - four_t * constant_term.clone() * quadratic_coeff;
    if zero_pred(&discriminant) {
        let mut only_answer = -linear_coeff;
        only_answer /= constant_term * two_t;
        vec![(only_answer, 1)]
    } else {
        #[allow(clippy::collapsible_else_if)]
        if let Some(sqrt_discriminant) = my_sqrt(&discriminant) {
            let two_a = constant_term * two_t;
            let mut answer_1 = -(linear_coeff.clone() + sqrt_discriminant.clone());
            answer_1 /= two_a.clone();
            let mut answer_2 = -linear_coeff;
            answer_2 += sqrt_discriminant;
            answer_2 /= two_a;
            vec![(answer_1, 0), (answer_2, 0)]
        } else {
            vec![]
        }
    }
}

#[allow(clippy::needless_pass_by_value)]
pub(crate) fn cubic_solve<T>(
    _constant_term: T,
    _linear_coeff: T,
    _quadratic_coeff: T,
    _cubic_coeff: T,
    _zero_pred: &impl Fn(&T) -> bool,
    _my_sqrt: &impl Fn(&T) -> Option<T>,
    _my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
) -> Result<Vec<(T, usize)>, FindZeroError>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + From<SmallIntegers>
        + Sub<Output = T>
        + DivAssign<T>,
{
    todo!();
}

#[allow(clippy::too_many_arguments, clippy::needless_pass_by_value)]
pub(crate) fn quartic_solve<T>(
    _constant_term: T,
    _linear_coeff: T,
    _quadratic_coeff: T,
    _cubic_coeff: T,
    _quartic_coeff: T,
    _zero_pred: &impl Fn(&T) -> bool,
    _my_sqrt: &impl Fn(&T) -> Option<T>,
    _my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
) -> Result<Vec<(T, usize)>, FindZeroError>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign<T>
        + Add<Output = T>
        + Mul<Output = T>
        + From<SmallIntegers>
        + Sub<Output = T>
        + DivAssign<T>,
{
    todo!();
}
