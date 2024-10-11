#[cfg(feature = "pade")]
use crate::generic_polynomial::{
    DegreeType, DifferentiateError, Generic1DPoly, MonomialError, PointSpecifier, SmallIntegers,
};
#[cfg(feature = "pade")]
use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub};
#[cfg(feature = "pade")]
use std::marker::PhantomData;

#[allow(clippy::module_name_repetitions)]
#[cfg(feature = "pade")]
pub struct PadeApproximant<T, P, Q>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign<T>
        + Add<T, Output = T>
        + Mul<T, Output = T>
        + MulAssign<T>
        + From<SmallIntegers>
        + Sub<T, Output = T>
        + DivAssign<T>,
    P: Generic1DPoly<T>,
    Q: Generic1DPoly<T>,
{
    numerator_poly: P,
    denominator_poly: Q,
    dummy_t: PhantomData<T>,
}

#[cfg(feature = "pade")]
impl<T, P, Q> PadeApproximant<T, P, Q>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign<T>
        + Add<T, Output = T>
        + Mul<T, Output = T>
        + MulAssign<T>
        + From<SmallIntegers>
        + Sub<T, Output = T>
        + DivAssign<T>,
    P: Generic1DPoly<T>,
    Q: Generic1DPoly<T>,
{
    #[allow(dead_code)]
    fn create_zero_pade() -> Self {
        let numerator_poly = P::create_zero_poly();
        Self::create_polynomial(numerator_poly)
    }

    fn create_polynomial(numerator_poly: P) -> Self {
        let denominator_poly =
            Q::create_monomial(1, &|_| false, false).expect("The zero subspace for denominator");
        Self {
            numerator_poly,
            denominator_poly,
            dummy_t: PhantomData,
        }
    }

    fn evaluate_at(&self, t: T, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at(t.clone());
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at(t);
            answer /= den;
            Some(answer)
        }
    }

    fn evaluate_at_zero(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at_zero();
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at_zero();
            answer /= den;
            Some(answer)
        }
    }

    fn evaluate_at_one(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at_one();
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at_one();
            answer /= den;
            Some(answer)
        }
    }

    fn evaluate_at_neg_one(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at_neg_one();
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at_neg_one();
            answer /= den;
            Some(answer)
        }
    }

    #[allow(dead_code)]
    fn is_zero_pade(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.numerator_poly.is_zero_polynomial(zero_pred)
    }

    #[allow(dead_code)]
    fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.numerator_poly.is_constant_polynomial(zero_pred)
            && self.denominator_poly.is_constant_polynomial(zero_pred)
    }

    #[allow(dead_code)]
    fn pade_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<(DegreeType, DegreeType)> {
        let den_degree = self.numerator_poly.polynomial_degree(zero_pred);
        assert!(den_degree.is_some(), "Denominator is 0");
        
        let num_degree = self.numerator_poly.polynomial_degree(zero_pred);
        num_degree.map(|n| (n, den_degree.unwrap()))
    }

    #[allow(dead_code)]
    fn evaluate_at_specifier(
        &self,
        around_here: PointSpecifier<T>,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Option<T> {
        match around_here {
            PointSpecifier::NegOne => self.evaluate_at_neg_one(zero_pred),
            PointSpecifier::Zero => self.evaluate_at_zero(zero_pred),
            PointSpecifier::One => self.evaluate_at_one(zero_pred),
            PointSpecifier::General(t) => self.evaluate_at(t, zero_pred),
        }
    }

    #[allow(dead_code)]
    fn linear_approx_pade(
        self,
        around_here: PointSpecifier<T>,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<(T, T), Result<DifferentiateError, MonomialError>> {
        let denominator_value = self
            .denominator_poly
            .evaluate_at_specifier(around_here.clone());
        if zero_pred(&denominator_value) {
            return Err(Ok(DifferentiateError::CantComputeDerivative));
        }
        let (a, b) = self
            .numerator_poly
            .linear_approx(around_here.clone())
            .map_err(Ok)?;
        let (c, d) = self
            .denominator_poly
            .linear_approx(around_here)
            .map_err(Ok)?;
        let mut zeroth_order = a.clone();
        zeroth_order /= c.clone();
        let c_squared = c.clone() * c.clone();
        let mut first_order = b * c - a * d;
        first_order /= c_squared;
        Ok((zeroth_order, first_order))
    }
}
