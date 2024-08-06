use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::ops::DivAssign;

pub enum FindZeroError {
    EverythingIsAZeroForZeroPolynomial,
    AbelRuffiniUnsolvability,
}

pub type DegreeType = u8;
pub type SmallIntegers = i8;

// TODO
// may make T Copy, but I like not having that at first
// so I can make the arithmetic I am doing with it
// not have to use those copies, having to put clone
// provides the painfulness to make aware of that happening

pub trait Generic1DPoly<T>:
    Sized
    + AddAssign<T>
    + Add<T, Output = Self>
    + Add<Output = Self>
    + SubAssign<T>
    + Sub<T, Output = Self>
    + Sub<Output = Self>
    + MulAssign<T>
    + Mul<T, Output = Self>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>,
{
    fn create_zero_poly() -> Self;
    fn create_monomial(
        degree: DegreeType,
        zero_pred: &impl Fn(&T) -> bool,
        surely_fits: bool,
    ) -> Option<Self>;
    #[allow(dead_code)]
    fn evaluate_at(&self, t: T) -> T;
    fn evaluate_at_zero(&self) -> T;
    #[allow(dead_code)]
    fn evaluate_at_one(&self) -> T;
    #[allow(dead_code)]
    fn evaluate_at_neg_one(&self) -> T;
    #[allow(dead_code)]
    fn is_zero_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool;
    #[allow(dead_code)]
    fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool;
    fn polynomial_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<DegreeType>;
    #[allow(dead_code)]
    fn differentiate(self) -> Self;
    /// take the product of these two polynomials
    /// the type of Self constrains the allowed terms
    /// if sure_will_cancel then even if we seem to be breaking those constraints
    /// then ignore that problem because we are told it will cancel out and that term
    /// will be 0 anyway
    fn truncating_product(
        &self,
        rhs: &Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<Self>;
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
    #[allow(dead_code)]
    fn find_zeros(
        &self,
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> T,
    ) -> Result<Vec<(T, usize)>, FindZeroError>;
}

pub(crate) fn quadratic_solve<T>(
    constant_term: T,
    linear_coeff: T,
    quadratic_coeff: T,
    zero_pred: &impl Fn(&T) -> bool,
    my_sqrt: &impl Fn(&T) -> Option<T>,
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
    let two_t: T = 2.into();
    let four_t: T = 4.into();
    let discriminant = linear_coeff.clone() * linear_coeff.clone()
        - four_t * constant_term.clone() * quadratic_coeff;
    if zero_pred(&discriminant) {
        let mut only_answer = -linear_coeff;
        only_answer /= constant_term * two_t;
        Ok(vec![(only_answer, 1)])
    } else {
        #[allow(clippy::collapsible_else_if)]
        if let Some(sqrt_discriminant) = my_sqrt(&discriminant) {
            let two_a = constant_term * two_t;
            let mut answer_1 = -(linear_coeff.clone() + sqrt_discriminant.clone());
            answer_1 /= two_a.clone();
            let mut answer_2 = -linear_coeff;
            answer_2 += sqrt_discriminant;
            answer_2 /= two_a;
            Ok(vec![(answer_1, 0), (answer_2, 0)])
        } else {
            Ok(vec![])
        }
    }
}

pub(crate) fn cubic_solve<T>(
    _constant_term: T,
    _linear_coeff: T,
    _quadratic_coeff: T,
    _cubic_coeff: T,
    _zero_pred: &impl Fn(&T) -> bool,
    _my_sqrt: &impl Fn(&T) -> Option<T>,
    _my_cube_root: &impl Fn(&T) -> T,
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

#[allow(clippy::too_many_arguments)]
pub(crate) fn quartic_solve<T>(
    _constant_term: T,
    _linear_coeff: T,
    _quadratic_coeff: T,
    _cubic_coeff: T,
    _quartic_coeff: T,
    _zero_pred: &impl Fn(&T) -> bool,
    _my_sqrt: &impl Fn(&T) -> Option<T>,
    _my_cube_root: &impl Fn(&T) -> T,
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

#[allow(dead_code)]
pub fn test_same_polynomial<const N: usize, T, P, Q>(
    p: P,
    q: Q,
    degree: DegreeType,
    t_points: [T; N],
    small_enough: &impl Fn(&T) -> bool,
) where
    P: Generic1DPoly<T>,
    Q: Generic1DPoly<T>,
    T: Clone
        + Neg<Output = T>
        + AddAssign<T>
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign<T>
        + From<SmallIntegers>
        + Sub<Output = T>
        + std::fmt::Display,
{
    let p_at_t = p.evaluate_at_zero();
    let q_at_t = q.evaluate_at_zero();
    let diff = p_at_t.clone() - q_at_t.clone();
    assert!(small_enough(&diff), "{p_at_t} {q_at_t} {degree} 0");
    for t_point in t_points {
        let p_at_t = p.evaluate_at(t_point.clone());
        let q_at_t = q.evaluate_at(t_point.clone());
        let diff = p_at_t.clone() - q_at_t.clone();
        assert!(small_enough(&diff), "{p_at_t} {q_at_t} {degree} {t_point}");
    }
    let p_at_t = p.evaluate_at_one();
    let q_at_t = q.evaluate_at_one();
    let diff = p_at_t.clone() - q_at_t.clone();
    assert!(small_enough(&diff), "{p_at_t} {q_at_t} {degree} 1");
}
