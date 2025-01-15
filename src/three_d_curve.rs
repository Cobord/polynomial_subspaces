use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::{marker::PhantomData, ops::DivAssign};

use crate::{
    fundamental_theorem::FundamentalTheorem,
    generic_polynomial::{
        DifferentiateError, Generic1DPoly, MonomialError, PointSpecifier, SmallIntegers,
    },
    two_d_curve::NormalTangentError,
};

#[cfg(feature = "GADT")]
use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;

/// T is the type being used to represent the real numbers
/// have three polynomials which can be used as functions from T to T
/// so used for an R -> R^3 curve
pub struct ThreePolynomials<T, P: Generic1DPoly<T>>
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
    z: P,
    dummy_t: PhantomData<T>,
}

#[cfg(feature = "GADT")]
impl<const N: usize, T> ThreePolynomials<T, SymmetricalBasisPolynomial<N, T>>
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
    /// taking the pointwise norm of `ThreePolynomials` gives a single polynomial
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    /// but we have expanded the space so that should not actually occur
    pub fn norm_squared(
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
        let new_self_z = self
            .z
            .try_convert_degree::<{
                2*SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;

        let x1x2 = new_self_x.truncating_product(&new_self_x, zero_pred, true)?;
        let y1y2 = new_self_y.truncating_product(&new_self_y, zero_pred, true)?;
        let z1z2 = new_self_z.truncating_product(&new_self_z, zero_pred, true)?;
        Some(x1x2 + y1y2 + z1z2)
    }

    /// taking the pointwise dot product of two of `ThreePolynomials` gives a single polynomial
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    /// but we have expanded the space so that should not actually occur
    pub fn dot_generic<const M: usize>(
        self,
        other: ThreePolynomials<T, SymmetricalBasisPolynomial<M, T>>,
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
        let new_self_z = self
            .z
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
        let new_other_z = other
            .z
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;

        let x1x2 = new_self_x.truncating_product(&new_other_x, zero_pred, true)?;
        let y1y2 = new_self_y.truncating_product(&new_other_y, zero_pred, true)?;
        let z1z2 = new_self_z.truncating_product(&new_other_z, zero_pred, true)?;
        Some(x1x2 + y1y2 + z1z2)
    }

    /// taking the pointwise cross product of two of `ThreePolynomials` gives another `ThreePolynomials`
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    /// but we have expanded the space so that should not actually occur
    pub fn cross_generic<const M: usize>(
        self,
        other: ThreePolynomials<T, SymmetricalBasisPolynomial<M, T>>,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Option<
        ThreePolynomials<
            T,
            SymmetricalBasisPolynomial<
                {
                    SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                        + 2
                },
                T,
            >,
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
        let new_self_z = self
            .z
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
        let new_other_z = other
            .z
            .try_convert_degree::<{
                SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                    + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                    + 2
            }>(zero_pred)
            .ok()?;
        let mut x = new_self_y.truncating_product(&new_other_z, zero_pred, true)?;
        x -= new_self_z.truncating_product(&new_other_y, zero_pred, true)?;
        let mut y = new_self_z.truncating_product(&new_other_x, zero_pred, true)?;
        y -= new_self_x.truncating_product(&new_other_z, zero_pred, true)?;
        let mut z = new_self_x.truncating_product(&new_other_y, zero_pred, true)?;
        z -= new_self_y.truncating_product(&new_other_x, zero_pred, true)?;
        Some(ThreePolynomials::<
            T,
            SymmetricalBasisPolynomial<
                {
                    SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound()
                        + 2
                },
                T,
            >,
        > {
            x,
            y,
            z,
            dummy_t: PhantomData,
        })
    }
}

#[cfg(not(feature = "GADT"))]
impl<T, P> ThreePolynomials<T, P>
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
    /// taking the pointwise norm of `ThreePolynomials` gives a single polynomial
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    fn norm_squared(self, zero_pred: &impl Fn(&T) -> bool, sure_will_cancel: bool) -> Option<P> {
        let x1x2 = self
            .x
            .truncating_product(&self.x, zero_pred, sure_will_cancel)?;
        let y1y2 = self
            .y
            .truncating_product(&self.y, zero_pred, sure_will_cancel)?;
        let z1z2 = self
            .z
            .truncating_product(&self.z, zero_pred, sure_will_cancel)?;
        Some(x1x2 + y1y2 + z1z2)
    }

    /// taking the pointwise dot product of two of `ThreePolynomials` gives a single polynomial
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
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
        let z1z2 = self
            .z
            .truncating_product(&other.z, zero_pred, sure_will_cancel)?;
        Some(x1x2 + y1y2 + z1z2)
    }

    /// taking the pointwise cross product of two of `ThreePolynomials` gives another `ThreePolynomials`
    /// the reason this returns an option instead of always succeeding is because in truncating product
    /// we don't know if we have the space for all the coefficients we need
    #[allow(clippy::needless_pass_by_value, clippy::similar_names)]
    fn cross_generic(
        self,
        other: Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<Self> {
        let x1y2 = self
            .x
            .truncating_product(&other.y, zero_pred, sure_will_cancel)?;
        let x1z2 = self
            .x
            .truncating_product(&other.z, zero_pred, sure_will_cancel)?;
        let y1x2 = self
            .y
            .truncating_product(&other.x, zero_pred, sure_will_cancel)?;
        let y1z2 = self
            .y
            .truncating_product(&other.z, zero_pred, sure_will_cancel)?;
        let z1y2 = self
            .z
            .truncating_product(&other.y, zero_pred, sure_will_cancel)?;
        let z1x2 = self
            .z
            .truncating_product(&other.x, zero_pred, sure_will_cancel)?;
        Some(Self {
            x: y1z2 - z1y2,
            y: z1x2 - x1z2,
            z: x1y2 - y1x2,
            dummy_t: PhantomData,
        })
    }
}

impl<T, P> AddAssign<(T, T, T)> for ThreePolynomials<T, P>
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
    fn add_assign(&mut self, rhs: (T, T, T)) {
        self.x += rhs.0;
        self.y += rhs.1;
        self.z += rhs.2;
    }
}

impl<T, P> Add<(T, T, T)> for ThreePolynomials<T, P>
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

    fn add(mut self, rhs: (T, T, T)) -> Self::Output {
        self += rhs;
        self
    }
}

impl<T, P> Add<Self> for ThreePolynomials<T, P>
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

impl<T, P> AddAssign<Self> for ThreePolynomials<T, P>
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
        self.z += rhs.z;
    }
}

impl<T, P> MulAssign<T> for ThreePolynomials<T, P>
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
        self.y *= rhs.clone();
        self.z *= rhs;
    }
}

impl<T, P> Mul<T> for ThreePolynomials<T, P>
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

impl<T, P> Neg for ThreePolynomials<T, P>
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
            z: -self.z,
            dummy_t: PhantomData,
        }
    }
}

impl<T, P> SubAssign<(T, T, T)> for ThreePolynomials<T, P>
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
    fn sub_assign(&mut self, rhs: (T, T, T)) {
        self.x -= rhs.0;
        self.y -= rhs.1;
        self.z -= rhs.2;
    }
}

impl<T, P> Sub<(T, T, T)> for ThreePolynomials<T, P>
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

    fn sub(mut self, rhs: (T, T, T)) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<T, P> Sub<Self> for ThreePolynomials<T, P>
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

impl<T, P> SubAssign<Self> for ThreePolynomials<T, P>
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
        self.z -= rhs.z;
    }
}

impl<T, P> ThreePolynomials<T, P>
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
    /// it might fail because the subspace for the component polynomials
    /// does not have to be closed under `d/dx` operator
    pub fn differentiate(self) -> Result<Self, DifferentiateError> {
        let x = self.x.differentiate()?;
        let y = self.y.differentiate()?;
        let z = self.z.differentiate()?;
        Ok(Self {
            x,
            y,
            z,
            dummy_t: PhantomData,
        })
    }

    pub fn evaluate_at(&self, t: T) -> (T, T, T) {
        (
            self.x.evaluate_at(t.clone()),
            self.y.evaluate_at(t.clone()),
            self.z.evaluate_at(t),
        )
    }

    pub fn evaluate_at_many<const POINT_COUNT: usize>(
        &self,
        ts: [T; POINT_COUNT],
    ) -> [(T, T, T); POINT_COUNT] {
        let xs = self.x.evaluate_at_many(ts.clone());
        let mut ys = self.y.evaluate_at_many(ts.clone());
        let mut zs = self.z.evaluate_at_many(ts);
        let mut triples = xs.map(|z| (z, 0.into(), 0.into()));
        for (idx, (_x, y, z)) in triples.iter_mut().enumerate() {
            core::mem::swap(y, &mut ys[idx]);
            core::mem::swap(z, &mut zs[idx]);
        }
        triples
    }

    pub fn evaluate_at_zero(&self) -> (T, T, T) {
        (
            self.x.evaluate_at_zero(),
            self.y.evaluate_at_zero(),
            self.z.evaluate_at_zero(),
        )
    }

    pub fn evaluate_at_one(&self) -> (T, T, T) {
        (
            self.x.evaluate_at_one(),
            self.y.evaluate_at_one(),
            self.z.evaluate_at_one(),
        )
    }

    pub fn evaluate_at_neg_one(&self) -> (T, T, T) {
        (
            self.x.evaluate_at_neg_one(),
            self.y.evaluate_at_neg_one(),
            self.z.evaluate_at_neg_one(),
        )
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
        let y = self.y.linear_approx_poly(around_here.clone())?;
        let z = self.z.linear_approx_poly(around_here)?;
        Ok(Self {
            x,
            y,
            z,
            dummy_t: PhantomData,
        })
    }

    #[must_use]
    #[allow(clippy::many_single_char_names)]
    /// A B C x
    /// D E F y
    /// G H I z
    pub fn apply_matrix(self, three_d_matrix: [[T; 3]; 3]) -> Self
    where
        P: Clone,
    {
        let [[a, b, c], [d, e, f], [g, h, i]] = three_d_matrix;
        let x = self.x.clone() * a + self.y.clone() * b + self.z.clone() * c;
        let y = self.x.clone() * d + self.y.clone() * e + self.z.clone() * f;
        let z = self.x * g + self.y * h + self.z * i;
        Self {
            x,
            y,
            z,
            dummy_t: PhantomData,
        }
    }
}

impl<T, P> Clone for ThreePolynomials<T, P>
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
            z: self.z.clone(),
            dummy_t: self.dummy_t,
        }
    }
}

#[cfg(not(feature = "GADT"))]
impl<T, P> ThreePolynomials<T, P>
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
    /// given a parameterized curve in 3 space
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
        point: (T, T, T),
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

    /// given a parameterized curve in 3 space
    /// find the values of the parameter where the
    /// tangent at that point is in the same direction
    /// as the displacement vector pointing between the given point
    /// and the curve
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - cross product components were not in the subspace
    /// - a norm squared was not in the subspace
    /// - a polynomial was not exactly solvable
    pub fn tangents_to_points(
        self,
        point: (T, T, T),
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
        let norm_cross = cross_product
            .norm_squared(zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        norm_cross
            .find_zeros(zero_pred, my_sqrt, my_cube_root)
            .map_err(NormalTangentError::FindZeroError)
    }

    /// given two parameterized curves in 3 space
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

    /// for the curvature `kappa`, take the absolute value of the first output (in Self)
    /// then divide by the speed cubed
    /// the speed squared is the second output
    /// we can't do it purely within this level of generality with P
    /// because you can't take the square root
    /// nor can we divide
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace
    /// - cross product components were not in the subspace
    pub fn signed_curvature_times_speed_cubed_and_speed_squared(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<(Self, P), NormalTangentError> {
        let xprime = self
            .x
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let yprime = self
            .y
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let zprime = self
            .z
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
        let zdoubleprime = zprime
            .clone()
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;

        let speed_vec = Self {
            x: xprime,
            y: yprime,
            z: zprime,
            dummy_t: PhantomData,
        };
        let speed_squared = speed_vec
            .clone()
            .dot_generic(speed_vec.clone(), zero_pred, false)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        let double_derivative = Self {
            x: xdoubleprime,
            y: ydoubleprime,
            z: zdoubleprime,
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
impl<T, const N: usize> ThreePolynomials<T, SymmetricalBasisPolynomial<N, T>>
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
    /// given a parameterized curve in 3 space
    /// find the values of the parameter where the
    /// tangent at that point is perpendicular to
    /// the displacement vector pointing between the given point
    /// and the curve
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace (which is avoided by the change const N array sizes using GADT)
    /// - a polynomial was not exactly solvable
    pub fn normals_to_point(
        self,
        point: (T, T, T),
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

    #[allow(clippy::needless_pass_by_value)]
    /// given a parameterized curve in 3 space
    /// find the values of the parameter where the
    /// tangent at that point is in the same direction
    /// as the displacement vector pointing between the given point
    /// and the curve
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - cross product components were not in the subspace (which is avoided by the change const N array sizes using GADT)
    /// - a norm squared was not in the subspace (which is avoided by the change const N array sizes using GADT)
    /// - a polynomial was not exactly solvable
    pub fn tangents_to_points(
        self,
        point: (T, T, T),
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<T>, NormalTangentError>
    where
        [(); {
            SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + 2
        }]:,
    {
        let (look_here, displacement, tangent_vecs) = self.clone().possible_tangents_to_points(
            point.clone(),
            zero_pred,
            my_sqrt,
            my_cube_root,
        )?;
        let mut final_answer = Vec::with_capacity(look_here.len() >> 3);
        for t_value in look_here {
            let (displacement_here_x, displacement_here_y, displacement_here_z) =
                displacement.evaluate_at(t_value.clone());
            let (tangent_here_x, tangent_here_y, tangent_here_z) =
                tangent_vecs.evaluate_at(t_value.clone());
            let cross_here_x = displacement_here_y.clone() * tangent_here_z.clone()
                - displacement_here_z.clone() * tangent_here_y.clone();
            let cross_here_y = displacement_here_z * tangent_here_x.clone()
                - displacement_here_x.clone() * tangent_here_z;
            let cross_here_z =
                displacement_here_x * tangent_here_y - displacement_here_y * tangent_here_x;
            let fully_zero =
                zero_pred(&cross_here_x) && zero_pred(&cross_here_y) && zero_pred(&cross_here_z);
            if fully_zero {
                final_answer.push(t_value);
            }
        }
        Ok(final_answer)
    }

    /// given a parameterized curve in 3 space
    /// helper to find the values of the parameter where the
    /// tangent at that point is in the same direction
    /// as the displacement vector pointing between the given point
    /// and the curve
    /// this just gives points where any one component of the cross product
    /// of displacement and tangent vector are 0
    /// the actual parameter values for the final answer will have all
    /// such components be 0
    fn possible_tangents_to_points(
        self,
        point: (T, T, T),
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<(Vec<T>, Self, Self), NormalTangentError>
    where
        [(); {
            SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                + 2
        }]:,
    {
        let displacement: Self = self.clone() - point;
        let tangent_vecs: Self = self
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let cross_product: ThreePolynomials<
            T,
            SymmetricalBasisPolynomial<
                {
                    SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                        + 2
                },
                T,
            >,
        > = displacement
            .clone()
            .cross_generic(tangent_vecs.clone(), zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        let mut final_answer: Vec<T> = Vec::new();
        if !cross_product.x.is_zero_polynomial(zero_pred) {
            let zeros_found = cross_product
                .x
                .find_zeros(zero_pred, my_sqrt, my_cube_root)
                .map_err(NormalTangentError::FindZeroError)?;
            final_answer.extend(zeros_found.into_iter().map(|(z, _)| z));
        };
        if !cross_product.y.is_zero_polynomial(zero_pred) {
            let zeros_found = cross_product
                .y
                .find_zeros(zero_pred, my_sqrt, my_cube_root)
                .map_err(NormalTangentError::FindZeroError)?;
            final_answer.extend(zeros_found.into_iter().map(|(z, _)| z));
        };
        if !cross_product.z.is_zero_polynomial(zero_pred) {
            let zeros_found = cross_product
                .z
                .find_zeros(zero_pred, my_sqrt, my_cube_root)
                .map_err(NormalTangentError::FindZeroError)?;
            final_answer.extend(zeros_found.into_iter().map(|(z, _)| z));
        };
        Ok((final_answer, displacement, tangent_vecs))
    }

    /// given two parameterized curves in 3 space
    /// find the values of the parameter where the
    /// distance between the two curves becomes 0
    /// # Errors
    /// - a norm squared was not in the subspace (which is avoided by the change const N array sizes using GADT)
    /// - a polynomial was not exactly solvable
    /// # Panics
    /// - conversion to higher degrees are fine, but `try_convert_degree` does not know that
    /// - you have to give the higher degree one first
    pub fn collision_curve<const M: usize>(
        self,
        other: ThreePolynomials<T, SymmetricalBasisPolynomial<M, T>>,
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
        let other_upgraded_z = other
            .z
            .try_convert_degree::<{ N }>(zero_pred)
            .expect("Lower to higher degree is fine");
        let other_upgraded = Self {
            x: other_upgraded_x,
            y: other_upgraded_y,
            z: other_upgraded_z,
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

    #[allow(clippy::type_complexity)]
    /// for the curvature `kappa`, take the absolute value of the first output (in Self)
    /// then divide by the speed cubed
    /// the speed squared is the second output
    /// we can't do it purely within this level of generality with P
    /// because you can't take the square root
    /// nor can we divide
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace (which is avoided by the change const N array sizes using GADT)
    /// - cross product components were not in the subspace (which is avoided by the change const N array sizes using GADT)
    pub fn signed_curvature_times_speed_cubed_and_speed_squared(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<
        (
            ThreePolynomials<
                T,
                SymmetricalBasisPolynomial<
                    {
                        SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                            + SymmetricalBasisPolynomial::<N, T>::polynomial_degree_bound()
                            + 2
                    },
                    T,
                >,
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
        let zprime = self
            .z
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
        let zdoubleprime = zprime
            .clone()
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let speed_vec = Self {
            x: xprime,
            y: yprime,
            z: zprime,
            dummy_t: PhantomData,
        };
        let speed_squared = speed_vec
            .clone()
            .dot_generic(speed_vec.clone(), zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        let double_derivative = Self {
            x: xdoubleprime,
            y: ydoubleprime,
            z: zdoubleprime,
            dummy_t: PhantomData,
        };
        let cross_product = speed_vec
            .cross_generic(double_derivative, zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)?;
        Ok((cross_product, speed_squared))
    }

    /// speed squared
    /// # Errors
    /// - one of the errors associated with `differentiate`
    /// - a dot product was not in the subspace (which is avoided by the change const N array sizes using GADT)
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
        let zprime = self
            .z
            .differentiate()
            .map_err(NormalTangentError::DifferentiateError)?;
        let speed_vec = Self {
            x: xprime,
            y: yprime,
            z: zprime,
            dummy_t: PhantomData,
        };
        speed_vec
            .clone()
            .dot_generic(speed_vec, zero_pred)
            .ok_or(NormalTangentError::ProductNotInSubspace)
    }
}
