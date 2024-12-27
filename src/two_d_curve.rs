#[cfg(feature = "bezier")]
use bezier_rs::Bezier;

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::{marker::PhantomData, ops::DivAssign};

use crate::generic_polynomial::{
    DifferentiateError, FindZeroError, FundamentalTheorem, Generic1DPoly, MonomialError,
    PointSpecifier, SmallIntegers,
};
#[cfg(any(feature = "GADT", feature = "bezier"))]
use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;

/// T is the type being used to represent the real numbers
/// have two polynomials which can be used as functions from T to T
/// so used for an R -> R^2 curve
pub struct TwoPolynomials<T, P: Generic1DPoly<T>>
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
    x: P,
    y: P,
    dummy_t: PhantomData<T>,
}

/// Bezier curves go to two `SymmetricBasisPolynomial`'s where the real numbers are being used as f64
/// and we only need at most 4 coefficients because we are only interested in up to cubic Bezier's
/// so we can constrain the const generic there to be only 4
#[cfg(feature = "bezier")]
impl From<Bezier> for TwoPolynomials<f64, SymmetricalBasisPolynomial<4, f64>> {
    #[must_use]
    fn from(value: Bezier) -> Self {
        let p0 = value.start;
        let pn = value.end;
        let (x_poly, y_poly) = match value.handles {
            bezier_rs::BezierHandles::Linear => {
                // p0.x*(1-t) + pn.x*t
                let x_poly = SymmetricalBasisPolynomial {
                    coeffs: [p0.x, pn.x, 0., 0.],
                };
                // p0.y*(1-t) + pn.y*t
                let y_poly = SymmetricalBasisPolynomial {
                    coeffs: [p0.y, pn.y, 0., 0.],
                };
                (x_poly, y_poly)
            }
            bezier_rs::BezierHandles::Quadratic { handle: p1 } => {
                // (C)*t + (A)*(1-t) + (-A-C+2*B)*t*(1-t)*t + (-A-C+2*B)*t*(1-t)*(1-t) == A*(1-t)^2 + B*2*t*(1-t) + C*t^2
                // p0.x*(1-t)^2 + p1.x*2*t*(1-t) + pn.x*t^2
                //
                let temp: f64 = 2. * p1.x - (p0.x + pn.x);
                let x_poly = SymmetricalBasisPolynomial {
                    coeffs: [p0.x, pn.x, temp, temp],
                };
                let temp: f64 = 2. * p1.y - (p0.y + pn.y);
                let y_poly = SymmetricalBasisPolynomial {
                    coeffs: [p0.y, pn.y, temp, temp],
                };
                (x_poly, y_poly)
            }
            bezier_rs::BezierHandles::Cubic {
                handle_start: p1,
                handle_end: p2,
            } => {
                //A*(1-t)^3 + 3*B*t*(1-t)^2 + 3*C*t^2*(1-t)+D*t^3
                //E*(1-t)+F*t+G*t*(1-t)^2+H*t^2*(1-t)
                //[{e: a, f: d, g: -2*a + 3*b - d, h: -a + 3*c - 2*d}]
                let g = 3. * p1.x - 2. * p0.x - pn.x;
                let h = 3. * p2.x - 2. * pn.x - p0.x;
                let x_poly = SymmetricalBasisPolynomial {
                    coeffs: [p0.x, pn.x, g, h],
                };
                let g = 3. * p1.y - 2. * p0.y - pn.y;
                let h = 3. * p2.y - 2. * pn.y - p0.y;
                let y_poly = SymmetricalBasisPolynomial {
                    coeffs: [p0.y, pn.y, g, h],
                };
                (x_poly, y_poly)
            }
        };
        TwoPolynomials {
            x: x_poly,
            y: y_poly,
            dummy_t: PhantomData,
        }
    }
}

#[cfg(feature = "GADT")]
impl<const N: usize, T> TwoPolynomials<T, SymmetricalBasisPolynomial<N, T>>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign<T>
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign<T>
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PartialEq<T>,
{
    fn norm_squared(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Option<
        SymmetricalBasisPolynomial<
            { 2 * SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound() + 2 },
            T,
        >,
    > {
        let new_self_x = self
            .x
            .try_convert_degree::<{
                2*SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_self_y = self
            .y
            .try_convert_degree::<{
                2*SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;

        let x1x2 = new_self_x.truncating_product(&new_self_x, zero_pred, true)?;
        let y1y2 = new_self_y.truncating_product(&new_self_y, zero_pred, true)?;
        Some(x1x2 + y1y2)
    }

    fn dot_generic<const M: usize>(
        self,
        other: TwoPolynomials<T, SymmetricalBasisPolynomial<M, T>>,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Option<
        SymmetricalBasisPolynomial<
            {
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            },
            T,
        >,
    > {
        let new_self_x = self
            .x
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_self_y = self
            .y
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_other_x = other
            .x
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_other_y = other
            .y
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;

        let x1x2 = new_self_x.truncating_product(&new_other_x, zero_pred, true)?;
        let y1y2 = new_self_y.truncating_product(&new_other_y, zero_pred, true)?;
        Some(x1x2 + y1y2)
    }

    fn cross_generic<const M: usize>(
        self,
        other: TwoPolynomials<T, SymmetricalBasisPolynomial<M, T>>,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Option<
        SymmetricalBasisPolynomial<
            {
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            },
            T,
        >,
    > {
        let new_self_x = self
            .x
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_self_y = self
            .y
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_other_x = other
            .x
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let new_other_y = other
            .y
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;

        let x1y2 = new_self_x.truncating_product(&new_other_y, zero_pred, true)?;
        let y1x2 = new_self_y.truncating_product(&new_other_x, zero_pred, true)?;
        Some(x1y2 - y1x2)
    }
}

#[cfg(not(feature = "GADT"))]
impl<T, P> TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    /// taking the pointwise norm of `TwoPolynomials` gives a single polynomial
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    fn norm_squared(self, zero_pred: &impl Fn(&T) -> bool, sure_will_cancel: bool) -> Option<P> {
        let x1x2 = self
            .x
            .truncating_product(&self.x, zero_pred, sure_will_cancel)?;
        let y1y2 = self
            .y
            .truncating_product(&self.y, zero_pred, sure_will_cancel)?;
        Some(x1x2 + y1y2)
    }

    /// taking the pointwise dot product of two of `TwoPolynomials` gives a single polynomial
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    /// like the P types in `TwoPolynomials<T,P>` are only allowing cubic polynomials and then when we
    /// are ending up with something that doesn't fit within those constraints because it is degree 6
    #[allow(clippy::needless_pass_by_value)]
    fn dot_generic(
        self,
        other: Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<P> {
        let x1x2 = self
            .x
            .truncating_product(&other.x, zero_pred, sure_will_cancel)?;
        let y1y2 = self
            .y
            .truncating_product(&other.y, zero_pred, sure_will_cancel)?;
        Some(x1x2 + y1y2)
    }

    /// taking the pointwise cross product of two of `TwoPolynomials` gives a single polynomial
    /// implicitly it is proportional to the missing z-axis
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    /// like the P types in `TwoPolynomials<T,P>` are only allowing cubic polynomials and then when we
    /// are ending up with something that doesn't fit within those constraints because it is degree 6
    #[allow(clippy::needless_pass_by_value)]
    fn cross_generic(
        self,
        other: Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<P> {
        let x1y2 = self
            .x
            .truncating_product(&other.y, zero_pred, sure_will_cancel)?;
        let y1x2 = self
            .y
            .truncating_product(&other.x, zero_pred, sure_will_cancel)?;
        Some(x1y2 - y1x2)
    }
}

impl<T, P> AddAssign<(T, T)> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    fn add_assign(&mut self, rhs: (T, T)) {
        self.x += rhs.0;
        self.y += rhs.1;
    }
}

impl<T, P> Add<(T, T)> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    type Output = Self;

    fn add(mut self, rhs: (T, T)) -> Self::Output {
        self += rhs;
        self
    }
}

impl<T, P> Add<Self> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<T, P> AddAssign<Self> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    fn add_assign(&mut self, rhs: Self) {
        self.x += rhs.x;
        self.y += rhs.y;
    }
}

impl<T, P> MulAssign<T> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    fn mul_assign(&mut self, rhs: T) {
        self.x *= rhs.clone();
        self.y *= rhs;
    }
}

impl<T, P> Mul<T> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    type Output = Self;

    fn mul(mut self, rhs: T) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<T, P> Neg for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            x: -self.x,
            y: -self.y,
            dummy_t: PhantomData,
        }
    }
}

impl<T, P> SubAssign<(T, T)> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    fn sub_assign(&mut self, rhs: (T, T)) {
        self.x -= rhs.0;
        self.y -= rhs.1;
    }
}

impl<T, P> Sub<(T, T)> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    type Output = Self;

    fn sub(mut self, rhs: (T, T)) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<T, P> Sub<Self> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<T, P> SubAssign<Self> for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    fn sub_assign(&mut self, rhs: Self) {
        self.x -= rhs.x;
        self.y -= rhs.y;
    }
}

impl<T, P> TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T>,
{
    /// differentiate each component
    /// # Errors
    /// the subspace for the components does not have to be closed under `d/dx` operator
    pub fn differentiate(self) -> Result<Self, DifferentiateError> {
        let x = self.x.differentiate()?;
        let y = self.y.differentiate()?;
        Ok(Self {
            x,
            y,
            dummy_t: PhantomData,
        })
    }

    pub fn evaluate_at(&self, t: T) -> (T, T) {
        (self.x.evaluate_at(t.clone()), self.y.evaluate_at(t))
    }

    pub fn evaluate_at_many<const POINT_COUNT: usize>(
        &self,
        ts: [T; POINT_COUNT],
    ) -> [(T, T); POINT_COUNT] {
        let xs = self.x.evaluate_at_many(ts.clone());
        let mut ys = self.y.evaluate_at_many(ts);
        let mut pairs = xs.map(|z| (z, 0.into()));
        for (idx, (_x, y)) in pairs.iter_mut().enumerate() {
            core::mem::swap(y, &mut ys[idx]);
        }
        pairs
    }

    pub fn evaluate_at_zero(&self) -> (T, T) {
        (self.x.evaluate_at_zero(), self.y.evaluate_at_zero())
    }
    pub fn evaluate_at_one(&self) -> (T, T) {
        (self.x.evaluate_at_one(), self.y.evaluate_at_one())
    }
    pub fn evaluate_at_neg_one(&self) -> (T, T) {
        (self.x.evaluate_at_neg_one(), self.y.evaluate_at_neg_one())
    }

    /// first order approximation around the given point
    /// # Errors
    /// it might fail because the subspace for each component does not have to be closed under `d/dx` operator
    /// another possibility is that the subspace does not include the linear function `x`
    ///     that should be very unusual, because we typically truncate
    ///     by degree and 1 is too low of a degree to fall to the chopping block
    pub fn linear_approx_poly(
        self,
        around_here: PointSpecifier<T>,
    ) -> Result<Self, Result<DifferentiateError, MonomialError>> {
        let x = self.x.linear_approx_poly(around_here.clone())?;
        let y = self.y.linear_approx_poly(around_here)?;
        Ok(Self {
            x,
            y,
            dummy_t: PhantomData,
        })
    }

    #[must_use]
    #[allow(clippy::many_single_char_names)]
    /// A B x
    /// C D y
    pub fn apply_matrix(self, two_d_matrix: [[T; 2]; 2]) -> Self
    where
        P: Clone,
    {
        let [[a, b], [c, d]] = two_d_matrix;
        let x = self.x.clone() * a + self.y.clone() * b;
        let y = self.x * c + self.y * d;
        Self {
            x,
            y,
            dummy_t: PhantomData,
        }
    }

    #[must_use]
    pub fn reflect_y(self) -> Self {
        let x = -self.x;
        Self {
            x,
            y: self.y,
            dummy_t: PhantomData,
        }
    }

    #[must_use]
    pub fn reflect_x(self) -> Self {
        let y = -self.y;
        Self {
            x: self.x,
            y,
            dummy_t: PhantomData,
        }
    }

    #[must_use]
    pub fn swap_axes(self) -> Self {
        Self {
            x: self.y,
            y: self.x,
            dummy_t: PhantomData,
        }
    }
}

impl<T, P> Clone for TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign,
    P: Generic1DPoly<T> + Clone,
{
    fn clone(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            dummy_t: self.dummy_t,
        }
    }
}

pub enum NormalTangentError {
    DifferentiateError(DifferentiateError),
    FindZeroError(FindZeroError),
    ProductNotInSubspace,
}

#[cfg(not(feature = "GADT"))]
impl<T, P> TwoPolynomials<T, P>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign
        + DivAssign<T>,
    P: Generic1DPoly<T> + Clone + FundamentalTheorem<T>,
{
    /// given a parameterized curve in the plane
    /// find the values of the parameter where the
    /// tangent at that point is perpendicular to
    /// the displacement vector pointing between the given point
    /// and the curve
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace
    /// - a polynomial was not exactly solvable
    pub fn normals_to_point(
        self,
        point: (T, T),
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, NormalTangentError> {
        let displacement = self.clone() - point;
        let tangent_vecs = self
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let dot_product = displacement
            .dot_generic(tangent_vecs, zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        dot_product
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// given a parameterized curve in the plane
    /// find the values of the parameter where the
    /// tangent at that point is in the same direction
    /// as the displacement vector pointing between the given point
    /// and the curve
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a cross product was not in the subspace
    /// - a polynomial was not exactly solvable
    pub fn tangents_to_points(
        self,
        point: (T, T),
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, NormalTangentError> {
        let displacement = self.clone() - point;
        let tangent_vecs = self
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let cross_product = displacement
            .cross_generic(tangent_vecs, zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        cross_product
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// given two parameterized curves in the plane
    /// find the values of the parameter where the
    /// distance between the two curves becomes 0
    /// # Errors
    /// - a norm squared was not in the subspace
    /// - a polynomial was not exactly solvable
    pub fn collision_curve(
        self,
        other: Self,
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, NormalTangentError> {
        let displacement = self - other;
        let distance_squared = displacement
            .norm_squared(zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        distance_squared
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// for the curvature `kappa`, take the absolute value of the first output polynomial (in P)
    /// then divide by the speed cubed
    /// the speed squared is the second output
    /// we can't do it purely within this level of generality with P
    /// because you can't take the square root
    /// nor can we divide
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace
    /// - a cross product was not in the subspace
    pub fn signed_curvature_times_speed_cubed_and_speed_squared(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<(P, P), NormalTangentError> {
        let xprime = self
            .x
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let yprime = self
            .y
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let xdoubleprime = xprime
            .clone()
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let ydoubleprime = yprime
            .clone()
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;

        let speed_vec = Self {
            x: xprime,
            y: yprime,
            dummy_t: PhantomData,
        };
        let speed_squared = speed_vec
            .clone()
            .dot_generic(speed_vec.clone(), zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        let double_derivative = Self {
            x: xdoubleprime,
            y: ydoubleprime,
            dummy_t: PhantomData,
        };
        let cross_product = speed_vec
            .cross_generic(double_derivative, zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        Ok((cross_product, speed_squared))
    }

    /// speed squared
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace
    pub fn speed_squared(self, zero_pred: &impl Fn(&T) -> bool) -> Result<P, NormalTangentError> {
        let xprime = self
            .x
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let yprime = self
            .y
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let speed_summand_1 = xprime
            .truncating_product(&xprime, zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        let speed_summand_2 = yprime
            .truncating_product(&xprime, zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        Ok(speed_summand_1 + speed_summand_2)
    }
}

#[cfg(feature = "GADT")]
impl<T, const N: usize> TwoPolynomials<T, SymmetricalBasisPolynomial<N, T>>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign
        + DivAssign<T>
        + PartialEq<T>,
{
    /// given a parameterized curve in the plane
    /// find the values of the parameter where the
    /// tangent at that point is perpendicular to
    /// the displacement vector pointing between the given point
    /// and the curve
    pub fn normals_to_point(
        self,
        point: (T, T),
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, NormalTangentError>
    where
        [(); {
            SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + 2
        }]:,
    {
        let displacement = self.clone() - point;
        let tangent_vecs = self
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let dot_product: SymmetricalBasisPolynomial<
            {
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + 2
            },
            T,
        > = displacement
            .dot_generic::<N>(tangent_vecs, zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        dot_product
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// given a parameterized curve in the plane
    /// find the values of the parameter where the
    /// tangent at that point is in the same direction
    /// as the displacement vector pointing between the given point
    /// and the curve
    pub fn tangents_to_points(
        self,
        point: (T, T),
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, NormalTangentError>
    where
        [(); {
            SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + 2
        }]:,
    {
        let displacement = self.clone() - point;
        let tangent_vecs = self
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let cross_product: SymmetricalBasisPolynomial<
            {
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + 2
            },
            T,
        > = displacement
            .cross_generic(tangent_vecs, zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        cross_product
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// given two parameterized curves in the plane
    /// find the values of the parameter where the
    /// distance between the two curves becomes 0
    pub fn collision_curve<const M: usize>(
        self,
        other: TwoPolynomials<T, SymmetricalBasisPolynomial<M, T>>,
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, NormalTangentError>
    where
        [(); 2 * SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound() + 2]:,
    {
        assert!(M <= N, "The larger degree should be first");
        let other_upgraded_x = other
            .x
            .try_convert_degree::<{ N }>(zero_pred)
            .expect("Lower to higher degree is fine");
        let other_upgraded_y = other
            .y
            .try_convert_degree::<{ N }>(zero_pred)
            .expect("Lower to higher degree is fine");
        let other_upgraded = Self {
            x: other_upgraded_x,
            y: other_upgraded_y,
            dummy_t: PhantomData,
        };
        let displacement = self - other_upgraded;
        let distance_squared = displacement
            .norm_squared(zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        distance_squared
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// for the curvature kappa, take the absolute value of the first output polynomial (in P)
    /// then divide by the speed cubed
    /// the speed squared is the second output
    /// we can't do it purely within this level of generality with P
    /// because you can't take the square root
    /// nor can we divide
    pub fn signed_curvature_times_speed_cubed_and_speed_squared(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<
        (
            SymmetricalBasisPolynomial<
                {
                    SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + 2
                },
                T,
            >,
            SymmetricalBasisPolynomial<
                {
                    SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + 2
                },
                T,
            >,
        ),
        NormalTangentError,
    > {
        let xprime = self
            .x
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let yprime = self
            .y
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let xdoubleprime = xprime
            .clone()
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let ydoubleprime = yprime
            .clone()
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let speed_vec = Self {
            x: xprime,
            y: yprime,
            dummy_t: PhantomData,
        };
        let speed_squared = speed_vec
            .clone()
            .dot_generic(speed_vec.clone(), zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        let double_derivative = Self {
            x: xdoubleprime,
            y: ydoubleprime,
            dummy_t: PhantomData,
        };
        let cross_product = speed_vec
            .cross_generic(double_derivative, zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        Ok((cross_product, speed_squared))
    }

    pub fn speed_squared(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<
        SymmetricalBasisPolynomial<
            {
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + 2
            },
            T,
        >,
        NormalTangentError,
    > {
        let xprime = self
            .x
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let yprime = self
            .y
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let speed_vec = Self {
            x: xprime,
            y: yprime,
            dummy_t: PhantomData,
        };
        speed_vec
            .clone()
            .dot_generic(speed_vec, zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)
    }
}
