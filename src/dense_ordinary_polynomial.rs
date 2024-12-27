use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use fast_polynomial::PolyNum;

use crate::generic_polynomial::{
    cubic_solve, quadratic_solve, quartic_solve, BasisIndexingType, DegreeType, DifferentiateError,
    FindZeroError, FundamentalTheorem, Generic1DPoly, MonomialError, SmallIntegers, SubspaceError,
};

#[repr(transparent)]
pub struct DenseMonomialBasisPolynomial<const N: usize, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + Copy
        + PolyNum,
{
    pub(crate) coeffs: [T; N],
}

impl<const N: usize, T> Generic1DPoly<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + Copy
        + PolyNum,
{
    fn create_zero_poly() -> Self {
        let coeffs: [T; N] = core::array::from_fn(|_| 0.into());
        Self { coeffs }
    }

    fn create_monomial(
        degree: DegreeType,
        _zero_pred: &impl Fn(&T) -> bool,
        _surely_fits: bool,
    ) -> Result<Self, MonomialError> {
        let coeffs: [T; N] = core::array::from_fn(|idx| {
            #[allow(clippy::cast_possible_truncation)]
            if (idx as DegreeType) == degree {
                1.into()
            } else {
                0.into()
            }
        });
        Ok(Self { coeffs })
    }

    fn evaluate_at_many<const POINT_COUNT: usize>(
        &self,
        mut _ts: [T; POINT_COUNT],
    ) -> [T; POINT_COUNT] {
        todo!("Can do better when trying to evaluate the same polynomial at many points");
    }

    fn evaluate_at(&self, t: T) -> T {
        fast_polynomial::poly_array(t, &self.coeffs)
    }

    fn evaluate_at_zero(&self) -> T {
        if N == 0 {
            0.into()
        } else {
            self.coeffs[0]
        }
    }

    fn evaluate_at_one(&self) -> T {
        self.coeffs.iter().fold(0.into(), |acc, x| acc + *x)
    }

    fn evaluate_at_neg_one(&self) -> T {
        self.coeffs
            .iter()
            .enumerate()
            .fold(0.into(), |acc, (degree, coeff)| {
                if degree % 2 == 0 {
                    acc + *coeff
                } else {
                    acc - *coeff
                }
            })
    }

    fn is_zero_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.coeffs.iter().all(zero_pred)
    }

    fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.coeffs[1..].iter().all(zero_pred)
    }

    fn polynomial_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<DegreeType> {
        for degree in (0..N).rev() {
            #[allow(clippy::cast_possible_truncation)]
            if !zero_pred(&self.coeffs[degree]) {
                return Some(degree as DegreeType);
            }
        }
        None
    }

    fn differentiate(mut self) -> Result<Self, DifferentiateError> {
        self.coeffs.rotate_left(1);
        #[allow(clippy::cast_possible_truncation)]
        for idx in 1..(N - 1) {
            self.coeffs[idx] *= ((idx + 1) as SmallIntegers).into();
        }
        self.coeffs[N - 1] = 0.into();
        Ok(self)
    }

    fn truncating_product(
        &self,
        rhs: &Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<Self> {
        let mut coeffs: [T; N] = core::array::from_fn(|_| 0.into());
        for (degree_1, coeff_1) in self.coeffs.iter().enumerate() {
            if zero_pred(coeff_1) {
                continue;
            }
            for (degree_2, coeff_2) in rhs.coeffs.iter().enumerate() {
                if zero_pred(coeff_2) {
                    continue;
                }
                let seek = degree_1 + degree_2;
                if seek < N {
                    coeffs[seek] += *coeff_1 * *coeff_2;
                } else if !sure_will_cancel {
                    return None;
                }
            }
        }
        Some(Self { coeffs })
    }

    fn all_basis_vectors(up_to: BasisIndexingType) -> Result<Vec<Self>, SubspaceError> {
        if (up_to as usize) > N {
            return Err(SubspaceError::NoSuchBasisVector(up_to - 1));
        }
        let mut answer = Vec::with_capacity(up_to as usize);
        for degree in 0..up_to {
            let to_push = Self::create_monomial(degree as DegreeType, &|_| false, true).or(Err(
                SubspaceError::NoSuchBasisVector(degree as BasisIndexingType),
            ))?;
            answer.push(to_push);
        }
        Ok(answer)
    }

    fn set_basis_vector_coeff(
        &mut self,
        which_coeff: BasisIndexingType,
        new_coeff: T,
    ) -> Result<(), SubspaceError> {
        if (which_coeff as usize) >= N {
            return Err(SubspaceError::NoSuchBasisVector(which_coeff));
        }
        self.coeffs[which_coeff as usize] = new_coeff;
        Ok(())
    }
}

impl<const N: usize, T> FundamentalTheorem<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + DivAssign<T>
        + Copy
        + PolyNum,
{
    fn find_zeros(
        &self,
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, crate::generic_polynomial::FindZeroError> {
        let degree = self.polynomial_degree(zero_pred);

        match degree {
            Some(0) => Ok(vec![]),
            Some(1) => {
                let constant_term = self.evaluate_at_zero();
                let linear_term: T = self.coeffs[1];
                let mut only_zero = -constant_term;
                only_zero /= linear_term;
                Ok(vec![(only_zero, 0)])
            }
            Some(2) => {
                let constant_term = self.evaluate_at_zero();
                let linear_coeff: T = self.coeffs[1];
                let quadratic_coeff: T = self.coeffs[2];
                Ok(quadratic_solve(
                    constant_term,
                    linear_coeff,
                    quadratic_coeff,
                    zero_pred,
                    my_sqrt,
                ))
            }
            Some(3) => {
                let constant_term = self.evaluate_at_zero();
                let linear_coeff: T = self.coeffs[1];
                let quadratic_coeff: T = self.coeffs[2];
                let cubic_coeff: T = self.coeffs[3];
                cubic_solve(
                    constant_term,
                    linear_coeff,
                    quadratic_coeff,
                    cubic_coeff,
                    zero_pred,
                    my_sqrt,
                    my_cube_root,
                )
            }
            Some(4) => {
                let constant_term = self.evaluate_at_zero();
                let linear_coeff: T = self.coeffs[1];
                let quadratic_coeff: T = self.coeffs[2];
                let cubic_coeff: T = self.coeffs[3];
                let quartic_coeff: T = self.coeffs[4];
                quartic_solve(
                    constant_term,
                    linear_coeff,
                    quadratic_coeff,
                    cubic_coeff,
                    quartic_coeff,
                    zero_pred,
                    my_sqrt,
                    my_cube_root,
                )
            }
            Some(x) if x > 4 => Err(FindZeroError::AbelRuffiniUnsolvability(x)),
            None => Err(FindZeroError::EverythingIsAZeroForZeroPolynomial),
            _ => {
                unreachable!("x>4 exhausted all the other Some cases")
            }
        }
    }
}

impl<const N: usize, T> Mul<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    type Output = Self;

    fn mul(mut self, rhs: T) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const N: usize, T> MulAssign<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    fn mul_assign(&mut self, rhs: T) {
        self.coeffs.iter_mut().for_each(|z1| *z1 *= rhs);
    }
}

impl<const N: usize, T> Add<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    type Output = Self;

    fn add(mut self, rhs: T) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const N: usize, T> AddAssign<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    fn add_assign(&mut self, rhs: T) {
        assert!(N >= 1, "The zero subspace");
        self.coeffs[0] += rhs;
    }
}

impl<const N: usize, T> Sub<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    type Output = Self;

    fn sub(mut self, rhs: T) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const N: usize, T> SubAssign<T> for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    fn sub_assign(&mut self, rhs: T) {
        assert!(N >= 1, "The zero subspace");
        self.coeffs[0] -= rhs;
    }
}

impl<const N: usize, T> Add for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const N: usize, T> AddAssign for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    fn add_assign(&mut self, rhs: Self) {
        for idx in 0..N {
            self.coeffs[idx] += rhs.coeffs[idx];
        }
    }
}

impl<const N: usize, T> Sub for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const N: usize, T> SubAssign for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    fn sub_assign(&mut self, rhs: Self) {
        for idx in 0..N {
            self.coeffs[idx] -= rhs.coeffs[idx];
        }
    }
}

impl<const N: usize, T> Neg for DenseMonomialBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>
        + PolyNum,
{
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for idx in 0..N {
            self.coeffs[idx] = -self.coeffs[idx];
        }
        self
    }
}
