/// const generics mean we can have the alpha and beta parameters of Jacobi polynomials at compile time
/// but we have to restrict them to some natural number-ness instead of being continuous parameters
/// but we only really ever really ever use them at certain half-integer values
use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::generic_polynomial::{
    BasisIndexingType, DegreeType, DifferentiateError, FindZeroError, FundamentalTheorem,
    Generic1DPoly, MonomialError, SmallIntegers, SubspaceError,
};

#[allow(dead_code)]
const OFFSET: usize = 1;

/// store the coefficients of J^{alpha,beta}_0,J^{alpha,beta}_1 ... in that order
/// up to N of them
/// this provides an alternative basis for the vector space of polynomials
/// alpha is restricted so that TWICE_ALPHA_PLUS_OFFSET is usize and same for beta
#[repr(transparent)]
#[derive(Clone)]
pub struct JacobiBasisPolynomial<
    const N: usize,
    const TWICE_ALPHA_PLUS_OFFSET: usize,
    const TWICE_BETA_PLUS_OFFSET: usize,
    T,
> {
    pub(crate) coeffs: [T; N],
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
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
{
    /// given offset+2(n+alpha) and n
    /// compute binom(n+alpha,n)
    /// reason not just giving n+alpha is because that might be a half integer or negative
    /// but with the offset and multiplication, it is natural number
    fn binomial_helper(&self, _offset_plus_two_times_quantity_n_plus_alpha: usize, _n: usize) -> T {
        todo!();
    }

    #[allow(dead_code)]
    fn base_change<U>(
        self,
    ) -> JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, U>
    where
        U: Clone
            + Neg<Output = U>
            + AddAssign<U>
            + Add<U, Output = U>
            + Mul<U, Output = U>
            + MulAssign<U>
            + From<SmallIntegers>
            + Sub<U, Output = U>
            + SubAssign<U>
            + From<T>,
    {
        JacobiBasisPolynomial::<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, U> {
            coeffs: core::array::from_fn(|idx| self.coeffs[idx].clone().into()),
        }
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Generic1DPoly<T>
    for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    fn create_zero_poly() -> Self {
        Self {
            coeffs: core::array::from_fn(|_| 0.into()),
        }
    }

    fn create_monomial(
        degree: DegreeType,
        _zero_pred: &impl Fn(&T) -> bool,
        _surely_fits: bool,
    ) -> Result<Self, MonomialError> {
        if (degree as usize) >= N {
            return Err(MonomialError::DesiredMonomialNotInSpace(degree));
        }
        todo!();
    }

    fn evaluate_at(&self, _t: T) -> T {
        todo!()
    }

    fn evaluate_at_zero(&self) -> T {
        todo!()
    }

    #[allow(unreachable_code, unused_variables, clippy::diverging_sub_expression)]
    fn evaluate_at_one(&self) -> T {
        // n + alpha choose n for each coefficient
        self.coeffs
            .iter()
            .enumerate()
            .fold(0.into(), |acc, (n, coeff)| {
                let offset_plus_two_times_quantity_n_plus_alpha = 2 * n + TWICE_ALPHA_PLUS_OFFSET;
                let nth_contrib: T =
                    { self.binomial_helper(offset_plus_two_times_quantity_n_plus_alpha, n) };
                acc + (nth_contrib * coeff.clone())
            })
    }

    #[allow(unreachable_code, unused_variables, clippy::diverging_sub_expression)]
    fn evaluate_at_neg_one(&self) -> T {
        // n + beta choose n for each coefficient multiplied by (-1)^n
        self.coeffs
            .iter()
            .enumerate()
            .fold(0.into(), |acc, (n, coeff)| {
                let offset_plus_two_times_quantity_n_plus_beta = 2 * n + TWICE_BETA_PLUS_OFFSET;
                let nth_contrib: T = {
                    let mut to_return =
                        self.binomial_helper(offset_plus_two_times_quantity_n_plus_beta, n);
                    if n % 2 != 0 {
                        to_return = -to_return;
                    }
                    to_return
                };
                if n % 2 == 0 {
                    acc + (nth_contrib * coeff.clone())
                } else {
                    acc - (nth_contrib * coeff.clone())
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
        self.coeffs
            .iter()
            .enumerate()
            .filter_map(|(power, coeff)| {
                if !zero_pred(coeff) {
                    Some(power as DegreeType)
                } else {
                    None
                }
            })
            .max()
    }

    fn differentiate(self) -> Result<Self, DifferentiateError> {
        todo!()
    }

    fn truncating_product(
        &self,
        _rhs: &Self,
        _zero_pred: &impl Fn(&T) -> bool,
        _sure_will_cancel: bool,
    ) -> Option<Self> {
        todo!()
    }

    fn all_basis_vectors(up_to: BasisIndexingType) -> Result<Vec<Self>, SubspaceError> {
        if (up_to as usize) > N {
            return Err(SubspaceError::NoSuchBasisVector(up_to - 1));
        }
        let mut answer = Vec::with_capacity(up_to as usize);
        for degree in 0..up_to {
            let coeffs: [T; N] = core::array::from_fn(|idx| {
                if (idx as DegreeType) == (degree as DegreeType) {
                    1.into()
                } else {
                    0.into()
                }
            });
            answer.push(Self { coeffs });
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

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
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
        + DivAssign<T>,
{
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > FundamentalTheorem<T>
    for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
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
        + DivAssign<T>,
{
    fn find_zeros(
        &self,
        zero_pred: &impl Fn(&T) -> bool,
        _my_sqrt: &impl Fn(&T) -> Option<T>,
        _my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, crate::generic_polynomial::FindZeroError> {
        let degree = self.polynomial_degree(zero_pred);
        match degree {
            Some(0) => Ok(vec![]),
            Some(1) => {
                todo!()
            }
            Some(2) => {
                todo!()
            }
            Some(3) => {
                todo!()
            }
            Some(4) => {
                todo!()
            }
            Some(x) if x > 4 => Err(FindZeroError::AbelRuffiniUnsolvability(x)),
            None => Err(FindZeroError::EverythingIsAZeroForZeroPolynomial),
            _ => {
                unreachable!("x>4 exhausted all the other Some cases")
            }
        }
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Mul<T> for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    type Output = Self;

    fn mul(mut self, rhs: T) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > MulAssign<T> for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    fn mul_assign(&mut self, rhs: T) {
        self.coeffs.iter_mut().for_each(|z1| *z1 *= rhs.clone());
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Add<T> for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    type Output = Self;

    fn add(mut self, rhs: T) -> Self::Output {
        self += rhs;
        self
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > AddAssign<T> for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    fn add_assign(&mut self, rhs: T) {
        if N == 0 {
            panic!("The zero subspace");
        }
        self.coeffs[0] += rhs;
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Sub<T> for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    type Output = Self;

    fn sub(mut self, rhs: T) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > SubAssign<T> for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    fn sub_assign(&mut self, rhs: T) {
        if N == 0 {
            panic!("The zero subspace");
        }
        self.coeffs[0] -= rhs;
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Add for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > AddAssign for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    fn add_assign(&mut self, rhs: Self) {
        for (idx, cur_coeff) in rhs.coeffs.into_iter().enumerate() {
            self.coeffs[idx] += cur_coeff;
        }
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Sub for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > SubAssign for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    fn sub_assign(&mut self, rhs: Self) {
        for (idx, cur_coeff) in rhs.coeffs.into_iter().enumerate() {
            self.coeffs[idx] -= cur_coeff;
        }
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > Neg for JacobiBasisPolynomial<N, TWICE_ALPHA_PLUS_OFFSET, TWICE_BETA_PLUS_OFFSET, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>
        + SubAssign<T>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut answer = Self::create_zero_poly();
        answer -= self;
        answer
    }
}

// alpha = beta = Galpha - 1/2
// twice_alpha_plus_offset = 2*Galpha
#[allow(dead_code)]
pub type GegenbauerBasisPolynomial<const N: usize, const TWICE_GALPHA: usize, T> =
    JacobiBasisPolynomial<N, TWICE_GALPHA, TWICE_GALPHA, T>;

/// normalized in the same way, coefficients of J^{0,0}_n (x) = P_n(x)
#[allow(dead_code)]
pub type LegendreBasisPolynomial<const N: usize, T> = GegenbauerBasisPolynomial<N, 1, T>;

/// not normalized in the same way, coefficients of J^{-1/2,-1/2}_n (x) rather than T_n(x)
/// J^{-1/2,-1/2}_n (x) = Gamma(n+1/2)/(Sqrt[pi]*Gamma(n+1))*T_n(x)
/// so all the coefficients will be changed by these factors
#[allow(dead_code)]
pub type ChebyshevBasisPolynomial<const N: usize, T> = GegenbauerBasisPolynomial<N, 0, T>;
