use crate::generic_polynomial::{
    DegreeType, DifferentiateError, Generic1DPoly, MonomialError, PointSpecifier, SmallIntegers,
};
use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub};
use std::marker::PhantomData;

#[allow(clippy::module_name_repetitions)]
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
    #[must_use]
    pub fn create_zero_pade() -> Self {
        let numerator_poly = P::create_zero_poly();
        Self::create_polynomial(numerator_poly)
    }

    /// # Panics
    /// does not panic because 1 is not the 0 polynomial but `create_monomial` does not know that
    pub fn create_polynomial(numerator_poly: P) -> Self {
        let denominator_poly =
            Q::create_monomial(1, &|_| false, false).expect("The zero subspace for denominator");
        Self {
            numerator_poly,
            denominator_poly,
            dummy_t: PhantomData,
        }
    }

    pub fn evaluate_at(&self, t: T, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at(t.clone());
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at(t);
            answer /= den;
            Some(answer)
        }
    }

    pub fn evaluate_at_zero(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at_zero();
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at_zero();
            answer /= den;
            Some(answer)
        }
    }

    pub fn evaluate_at_one(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at_one();
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at_one();
            answer /= den;
            Some(answer)
        }
    }

    pub fn evaluate_at_neg_one(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<T> {
        let den = self.denominator_poly.evaluate_at_neg_one();
        if zero_pred(&den) {
            None
        } else {
            let mut answer = self.numerator_poly.evaluate_at_neg_one();
            answer /= den;
            Some(answer)
        }
    }

    pub fn is_zero_pade(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.numerator_poly.is_zero_polynomial(zero_pred)
    }

    pub fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.numerator_poly.is_constant_polynomial(zero_pred)
            && self.denominator_poly.is_constant_polynomial(zero_pred)
    }

    /// # Panics
    /// if the denominator is the zero polynomial
    pub fn pade_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<(DegreeType, DegreeType)> {
        let den_degree = self.numerator_poly.polynomial_degree(zero_pred);
        assert!(den_degree.is_some(), "Denominator is 0");

        let num_degree = self.numerator_poly.polynomial_degree(zero_pred);
        num_degree.map(|n| (n, den_degree.unwrap()))
    }

    pub fn evaluate_at_specifier(
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

    /// first order approximation around the given point
    /// # Errors
    /// it might fail because the subspace of numerator and denominator polynomials
    /// does not have to be closed under `d/dx` operator
    /// so building the approximation with quotient rule would fail when trying
    /// to differentiate them at the specified point
    /// it is also possible the denominator evaluates to 0 at that point
    pub fn linear_approx_pade(
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
