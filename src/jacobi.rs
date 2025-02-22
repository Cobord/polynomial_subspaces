/// const generics mean we can have the alpha and beta parameters of Jacobi polynomials at compile time
/// but we have to restrict them to some natural number-ness instead of being continuous parameters
/// but we only really ever really ever use them at certain half-integer values
use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{
    fundamental_theorem::{FindZeroError, FundamentalTheorem},
    generic_polynomial::{
        BasisIndexingType, DegreeType, DifferentiateError, Generic1DPoly, MonomialError,
        SmallIntegers, SubspaceError,
    },
    inner_product::InnerProductSubspace,
    special_numbers::SpecialNumbers,
};

/// 2alpha+1 >= 0 so 2alpha>=-1, alpha>=-1/2
/// and it is a half-integer
/// if we want alpha/beta=-1 as well, then we need to change this to 2
const OFFSET: usize = 1;

/// store the coefficients of `J^{alpha,beta}_0,J^{alpha,beta}_1` ... in that order
/// up to N of them
/// this provides an alternative basis for the vector space of polynomials
/// alpha is restricted so that `TWICE_ALPHA_PLUS_OFFSET` is usize and same for beta
#[allow(clippy::module_name_repetitions)]
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
        + AddAssign<T>
        + Add<T, Output = T>
        + Mul<T, Output = T>
        + MulAssign<T>
        + From<SmallIntegers>
        + Sub<T, Output = T>
        + SubAssign<T>
        + DivAssign<T>
        + SpecialNumbers,
{
    /// given offset+2(n+alpha) and n
    /// compute binom(n+alpha,n)
    /// reason not just giving n+alpha is because that might be a half integer or negative
    /// but with the offset and multiplication, it is natural number
    fn binomial_helper(&self, _offset_plus_two_times_top: usize, _bottom: usize) -> T {
        todo!("binom(top,bottom) but top is not given directly");
    }

    /// Gamma(x)
    /// but provide 2x so it is a natural number
    fn gamma(two_x: usize, accumulator: T) -> Option<T> {
        match two_x {
            0 => None,
            1 => Some(T::SQRT_PI * accumulator),
            2 => Some(accumulator),
            n => {
                #[allow(clippy::cast_possible_truncation)]
                let mut z = ((n as SmallIntegers) - 2).into();
                z /= 2.into();
                Self::gamma(n - 2, z)
            }
        }
    }

    /// Gamma(alpha+1), Gamma(beta+1) and Gamma(alpha+beta+1)
    /// the last one can be infinite for alpha=beta=-1/2
    /// the into and loop prevent this from being const
    /// but it should be thought of as such
    fn gamma_alpha_beta_one() -> (T, T, Option<T>) {
        let (mut floor_alpha_plus_beta_plus_1, extra_one_half) =
            Self::useful_alpha_beta_combinations();
        #[allow(clippy::if_not_else)]
        let third_return = if !extra_one_half {
            #[allow(clippy::cast_possible_truncation)]
            if floor_alpha_plus_beta_plus_1 == 0 {
                None
            } else if floor_alpha_plus_beta_plus_1 == 1 {
                Some(1.into())
            } else {
                floor_alpha_plus_beta_plus_1 -= 1;
                let mut answer: T = (floor_alpha_plus_beta_plus_1 as SmallIntegers).into();
                while floor_alpha_plus_beta_plus_1 > 1 {
                    floor_alpha_plus_beta_plus_1 -= 1;
                    answer *= (floor_alpha_plus_beta_plus_1 as SmallIntegers).into();
                }
                Some(answer)
            }
        } else {
            todo!("there is an extra one half so sqrt pi is in there");
        };
        let first_return = Self::gamma(Self::two_alphabeta_plus_2(true), 1.into())
            .expect("alpha+1>0 so never doing Gamma(0) here");
        let second_return = Self::gamma(Self::two_alphabeta_plus_2(false), 1.into())
            .expect("beta+1>0 so never doing Gamma(0) here");
        (first_return, second_return, third_return)
    }

    /// `Gamma(alpha+beta+2)`
    /// the `into` and `gamma` prevent this from being const
    /// but it should be thought of as such
    fn gamma_alpha_beta_two() -> T {
        // 2*alpha + offset + 2*beta + offset = 2*(alpha+beta+offset)
        let mut twice_quantity: usize = TWICE_ALPHA_PLUS_OFFSET + TWICE_BETA_PLUS_OFFSET;
        if twice_quantity + 4 >= 2 * OFFSET {
            twice_quantity += 4;
            twice_quantity -= 2 * OFFSET;
        } else {
            panic!("2*(alpha+beta+2) is not a natural number");
        }
        Self::gamma(twice_quantity, 1.into())
            .expect("because alpha,beta>=-1/2, alpha+beta+2 is greater than zero")
    }

    // either 2*alpha+2 or 2*beta+2
    const fn two_alphabeta_plus_2(do_alpha: bool) -> usize {
        let mut two_gamma_plus_two = if do_alpha {
            TWICE_ALPHA_PLUS_OFFSET
        } else {
            TWICE_BETA_PLUS_OFFSET
        };
        let whichever_doing = if do_alpha {
            TWICE_ALPHA_PLUS_OFFSET
        } else {
            TWICE_BETA_PLUS_OFFSET
        };
        #[allow(clippy::collapsible_else_if)]
        if whichever_doing + 2 >= OFFSET {
            two_gamma_plus_two += 2;
            two_gamma_plus_two -= OFFSET;
        } else {
            if do_alpha {
                panic!("2*alpha+2 is not a natural number");
            } else {
                panic!("2*beta+2 is not a natural number");
            }
        }
        two_gamma_plus_two
    }

    /// alpha + beta + 1 which is a nonnegative half integer
    /// because alpha,beta>=-1/2
    const fn useful_alpha_beta_combinations() -> (usize, bool) {
        let mut floor_alpha_plus_beta_plus_1 = TWICE_ALPHA_PLUS_OFFSET + TWICE_BETA_PLUS_OFFSET;
        // extra_one_half when alpha+beta is a half-integer and not an integer
        // in particular they can't be equal
        let extra_one_half = floor_alpha_plus_beta_plus_1 % 2 == 1;
        floor_alpha_plus_beta_plus_1 /= 2;
        if OFFSET <= 1 {
            floor_alpha_plus_beta_plus_1 += 1 - OFFSET;
        } else if floor_alpha_plus_beta_plus_1 + 1 >= OFFSET {
            floor_alpha_plus_beta_plus_1 += 1;
            floor_alpha_plus_beta_plus_1 -= OFFSET;
        } else {
            panic!("getting negative answer for alpha + beta + 1");
        }
        (floor_alpha_plus_beta_plus_1, extra_one_half)
    }

    /// alpha + 1 , beta + 1 and alpha + beta + 1
    /// the into prevent this from being const
    /// but it should be thought of as such
    fn more_useful_alpha_beta_combinations() -> (T, T, T)
    where
        T: DivAssign<T> + From<SmallIntegers>,
    {
        let alpha_plus_one: T = {
            #[allow(clippy::cast_possible_truncation)]
            let two_alpha: SmallIntegers = if TWICE_ALPHA_PLUS_OFFSET > OFFSET {
                (TWICE_ALPHA_PLUS_OFFSET - OFFSET) as SmallIntegers
            } else {
                -((OFFSET - TWICE_ALPHA_PLUS_OFFSET) as SmallIntegers)
            };
            let mut to_return: T = two_alpha.into();
            to_return /= 2.into();
            to_return += 1.into();
            to_return
        };
        let beta_plus_one: T = {
            #[allow(clippy::cast_possible_truncation)]
            let two_beta: SmallIntegers = if TWICE_BETA_PLUS_OFFSET > OFFSET {
                (TWICE_BETA_PLUS_OFFSET - OFFSET) as SmallIntegers
            } else {
                -((OFFSET - TWICE_BETA_PLUS_OFFSET) as SmallIntegers)
            };
            let mut to_return: T = two_beta.into();
            to_return /= 2.into();
            to_return += 1.into();
            to_return
        };
        let (floor_alpha_plus_beta_plus_1, extra_one_half) = Self::useful_alpha_beta_combinations();
        let alpha_beta_plus_one: T = {
            if extra_one_half {
                #[allow(clippy::cast_possible_truncation)]
                let mut to_return = (floor_alpha_plus_beta_plus_1 as SmallIntegers).into();
                let mut one_half: T = 1.into();
                one_half /= 2.into();
                to_return += one_half;
                to_return
            } else {
                #[allow(clippy::cast_possible_truncation)]
                (floor_alpha_plus_beta_plus_1 as SmallIntegers).into()
            }
        };
        (alpha_plus_one, beta_plus_one, alpha_beta_plus_one)
    }

    pub fn base_change<U>(
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
        + SubAssign<T>
        + DivAssign<T>
        + PartialEq<T>
        + SpecialNumbers,
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
        todo!("create x^{degree}");
    }

    fn evaluate_at_many<const POINT_COUNT: usize>(
        &self,
        mut _ts: [T; POINT_COUNT],
    ) -> [T; POINT_COUNT] {
        todo!("Can do better when trying to evaluate the same polynomial at many points");
    }

    fn evaluate_at(&self, t: T) -> T {
        if N == 0 {
            return 0.into();
        }
        if N == 1 {
            return self.evaluate_at_one();
        }
        // TODO use the recurrence relation instead
        // also below assumes that t is a real number
        let mut answer: T = 0.into();
        let mut half_t_minus_one = t.clone() - 1.into();
        half_t_minus_one /= 2.into();
        let mut half_t_plus_one = t.clone() + 1.into();
        half_t_plus_one /= 2.into();
        let mut two_over_t_plus_one: T = 2.into();
        two_over_t_plus_one /= t + 1.into();
        let mut starting_n_minus_s_power: T = 1.into();
        for (which_pn, cur_coeff) in self.coeffs.iter().enumerate() {
            let mut pn_value: T = 0.into();
            let mut s_power: T = 1.into();
            let mut n_minus_s_power: T = starting_n_minus_s_power.clone();
            starting_n_minus_s_power *= half_t_plus_one.clone();
            if *cur_coeff == 0.into() {
                continue;
            }
            for s in 0..=which_pn {
                let n_minus_s = which_pn - s;
                let offset_plus_twice_quantity_n_plus_alpha =
                    TWICE_ALPHA_PLUS_OFFSET + 2 * which_pn;
                let n_plus_alpha_choose_n_minus_s =
                    self.binomial_helper(offset_plus_twice_quantity_n_plus_alpha, n_minus_s);
                let offset_plus_twice_quantity_n_plus_beta = TWICE_BETA_PLUS_OFFSET + 2 * which_pn;
                let n_plus_beta_choose_s =
                    self.binomial_helper(offset_plus_twice_quantity_n_plus_beta, s);
                let s_contrib = n_plus_alpha_choose_n_minus_s
                    * n_plus_beta_choose_s
                    * s_power.clone()
                    * n_minus_s_power.clone();
                s_power *= half_t_minus_one.clone();
                n_minus_s_power *= two_over_t_plus_one.clone();
                pn_value += s_contrib;
            }
            answer += pn_value * cur_coeff.clone();
        }
        answer
    }

    fn evaluate_at_zero(&self) -> T {
        // TODO is there a better way with a rearrangement of the formula
        self.evaluate_at(0.into())
    }

    fn evaluate_at_one(&self) -> T {
        // n + alpha choose n for each coefficient
        self.coeffs
            .iter()
            .enumerate()
            .fold(0.into(), |acc, (n, coeff)| {
                if *coeff == 0.into() {
                    return acc;
                }
                let offset_plus_two_times_quantity_n_plus_alpha = 2 * n + TWICE_ALPHA_PLUS_OFFSET;
                let nth_contrib: T =
                    { self.binomial_helper(offset_plus_two_times_quantity_n_plus_alpha, n) };
                acc + (nth_contrib * coeff.clone())
            })
    }

    fn evaluate_at_neg_one(&self) -> T {
        // n + beta choose n for each coefficient multiplied by (-1)^n
        self.coeffs
            .iter()
            .enumerate()
            .fold(0.into(), |acc, (n, coeff)| {
                if *coeff == 0.into() {
                    return acc;
                }
                let offset_plus_two_times_quantity_n_plus_beta = 2 * n + TWICE_BETA_PLUS_OFFSET;
                let nth_contrib: T = {
                    let mut to_return =
                        self.binomial_helper(offset_plus_two_times_quantity_n_plus_beta, n);
                    if n % 2 != 0 {
                        to_return = -to_return;
                    }
                    to_return
                };
                acc + (nth_contrib * coeff.clone())
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
                if zero_pred(coeff) {
                    None
                } else {
                    #[allow(clippy::cast_possible_truncation)]
                    Some(power as DegreeType)
                }
            })
            .max()
    }

    /// derivatives are nicely expressed with different alpha and beta
    /// not the same alpha and beta
    fn differentiate(self) -> Result<Self, DifferentiateError> {
        let my_degree = self.polynomial_degree(&|z| *z == 0.into());
        if my_degree.is_none() {
            return Ok(Self::create_zero_poly());
        }
        let my_degree = my_degree.unwrap();
        if my_degree == 0 {
            return Ok(Self::create_zero_poly());
        }
        if my_degree == 2 {
            let mut one_poly = Self::create_monomial(1, &|z| *z == 0.into(), true)
                .expect("creating 1 is no problem");
            #[allow(clippy::cast_possible_truncation)]
            let derivative_constant: T = {
                let twice_alpha_beta_offset = TWICE_ALPHA_PLUS_OFFSET + TWICE_BETA_PLUS_OFFSET;
                let mut alpha_plus_beta_plus_2 = (twice_alpha_beta_offset as SmallIntegers).into();
                alpha_plus_beta_plus_2 /= 2.into();
                alpha_plus_beta_plus_2 += (2 - (OFFSET as SmallIntegers)).into();
                let mut to_return = alpha_plus_beta_plus_2;
                to_return /= 2.into();
                to_return
            };
            one_poly *= derivative_constant;
            one_poly *= self.coeffs[1].clone();
            return Ok(one_poly);
        }
        Err(DifferentiateError::CantComputeDerivative)
    }

    fn truncating_product(
        &self,
        rhs: &Self,
        zero_pred: &impl Fn(&T) -> bool,
        _sure_will_cancel: bool,
    ) -> Option<Self> {
        let my_degree = self.polynomial_degree(zero_pred);
        if my_degree.is_none() {
            return Some(Self::create_zero_poly());
        }
        let rhs_degree = rhs.polynomial_degree(zero_pred);
        #[allow(clippy::match_same_arms)]
        match (my_degree, rhs_degree) {
            (None, None) => Some(Self::create_zero_poly()),
            (None, Some(_)) => Some(Self::create_zero_poly()),
            (Some(_), None) => Some(Self::create_zero_poly()),
            (Some(0), Some(_)) => {
                let mut return_value = rhs.clone();
                return_value *= self.evaluate_at_zero();
                Some(return_value)
            }
            (Some(_), Some(0)) => {
                let mut return_value = self.clone();
                return_value *= rhs.evaluate_at_zero();
                Some(return_value)
            }
            _ => None,
        }
    }

    fn all_basis_vectors(up_to: BasisIndexingType) -> Result<Vec<Self>, SubspaceError> {
        if (up_to as usize) > N {
            return Err(SubspaceError::NoSuchBasisVector(up_to - 1));
        }
        let mut answer = Vec::with_capacity(up_to as usize);
        for degree in 0..up_to {
            let coeffs: [T; N] = core::array::from_fn(|idx| {
                #[allow(clippy::cast_possible_truncation)]
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
        + DivAssign<T>
        + PartialEq<T>
        + SpecialNumbers,
{
    fn find_zeros(
        &self,
        zero_pred: &impl Fn(&T) -> bool,
        _my_sqrt: &impl Fn(&T) -> Option<T>,
        _my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, FindZeroError> {
        let degree = self.polynomial_degree(zero_pred);
        match degree {
            Some(0) => Ok(vec![]),
            Some(1) => {
                todo!("to pull out constant term and linear term so can solve for zeros")
            }
            Some(2) => {
                todo!("to pull out 0,1,2 degree terms so can pass to quadratic_solve")
            }
            Some(3) => {
                todo!("to pull out 0,1,2,3 degree terms so can pass to cubic solve")
            }
            Some(4) => {
                todo!("to pull out 0,1,2,3,4 degree terms so can pass to quartic solve")
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
        assert!(N != 0, "The zero subspace");
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
        assert!(N != 0, "The zero subspace");
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
        + SubAssign<T>
        + DivAssign<T>
        + PartialEq<T>
        + SpecialNumbers,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut answer = Self::create_zero_poly();
        answer -= self;
        answer
    }
}

impl<
        const N: usize,
        const TWICE_ALPHA_PLUS_OFFSET: usize,
        const TWICE_BETA_PLUS_OFFSET: usize,
        T,
    > InnerProductSubspace<T>
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
        + DivAssign<T>
        + PartialEq<T>
        + SpecialNumbers,
{
    fn are_basis_vectors_orthogonal(
        _up_to: BasisIndexingType,
        _zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<bool, SubspaceError> {
        Ok(true)
    }

    #[allow(clippy::too_many_lines)]
    fn inner_product(&self, rhs: &Self) -> T {
        if N == 0 {
            return 0.into();
        }
        let mut answer: T = 0.into();

        let (floor_alpha_plus_beta_plus_1, extra_one_half): (usize, bool) =
            Self::useful_alpha_beta_combinations();
        let (alpha_plus_one, beta_plus_one, alpha_beta_plus_one) =
            Self::more_useful_alpha_beta_combinations();

        let two_to_alpha_beta_one: T = {
            let mut to_return: T = 1.into();
            for _ in 1..floor_alpha_plus_beta_plus_1 {
                to_return *= 2.into();
            }
            if extra_one_half {
                to_return *= T::SQRT_TWO;
                to_return
            } else {
                to_return
            }
        };
        let (gamma_alpha_one, gamma_beta_one, gamma_alpha_beta_one_pre) =
            Self::gamma_alpha_beta_one();
        let alpha_beta_one: T = alpha_beta_plus_one.clone();

        #[allow(clippy::single_match_else)]
        let (
            mut gamma_n_alpha_beta_one,
            mut gamma_n_alpha_one,
            mut gamma_n_beta_one,
            mut gamma_n_one,
            mut two_n_alpha_beta_one,
            do_skip,
        ): (T, T, T, T, T, bool) = match gamma_alpha_beta_one_pre {
            Some(gamma_alpha_beta_one) => (
                gamma_alpha_beta_one,
                gamma_alpha_one,
                gamma_beta_one,
                1.into(),
                alpha_beta_one,
                false,
            ),
            None => {
                // when alpha=beta=-1/2 we must cancel
                // the 0 from 2*n+alpha+beta+1
                // the infinity from Gamma(alpha+beta+1) = Gamma(0)
                // so we take special care of the 0th term then continue the loop after skipping 1
                if self.coeffs[0] != 0.into() && rhs.coeffs[0] != 0.into() {
                    let mut contribution: T = gamma_alpha_one.clone();
                    contribution *= gamma_beta_one.clone();
                    contribution *= self.coeffs[0].clone();
                    contribution *= rhs.coeffs[0].clone();
                    answer += contribution;
                }

                let gamma_1_alpha_one = gamma_alpha_one * alpha_plus_one.clone();
                let gamma_1_beta_one = gamma_beta_one * beta_plus_one.clone();
                let two_1_alpha_beta_one = 2.into();
                let gamma_1_alpha_beta_one = Self::gamma_alpha_beta_two();
                (
                    gamma_1_alpha_beta_one,
                    gamma_1_alpha_one,
                    gamma_1_beta_one,
                    1.into(),
                    two_1_alpha_beta_one,
                    true,
                )
            }
        };

        #[allow(clippy::cast_possible_truncation, clippy::bool_to_int_with_if)]
        for (idx, (self_coeff, rhs_coeff)) in self
            .coeffs
            .iter()
            .zip(rhs.coeffs.iter())
            .enumerate()
            .skip(if do_skip { 1 } else { 0 })
        {
            if *self_coeff == 0.into() || *rhs_coeff == 0.into() {
                // before it was gamma(idx+alpha+1)
                // want it to be gamma(idx+1+alpha+1) after
                gamma_n_alpha_one *= Into::<T>::into(idx as SmallIntegers) + alpha_plus_one.clone();
                gamma_n_beta_one *= Into::<T>::into(idx as SmallIntegers) + beta_plus_one.clone();
                gamma_n_alpha_beta_one *=
                    Into::<T>::into(idx as SmallIntegers) + alpha_beta_plus_one.clone();
                gamma_n_one *= ((idx + 1) as SmallIntegers).into();
                two_n_alpha_beta_one += 2.into();
                continue;
            }
            let mut contribution: T = 1.into();
            contribution *= gamma_n_alpha_one.clone();
            contribution *= gamma_n_beta_one.clone();
            contribution /= gamma_n_alpha_beta_one.clone();
            contribution /= gamma_n_one.clone();
            contribution /= two_n_alpha_beta_one.clone();
            contribution *= self_coeff.clone();
            contribution *= rhs_coeff.clone();
            answer += contribution;

            gamma_n_alpha_one *= Into::<T>::into(idx as SmallIntegers) + alpha_plus_one.clone();
            gamma_n_beta_one *= Into::<T>::into(idx as SmallIntegers) + beta_plus_one.clone();
            gamma_n_alpha_beta_one *=
                Into::<T>::into(idx as SmallIntegers) + alpha_beta_plus_one.clone();
            gamma_n_one *= ((idx + 1) as SmallIntegers).into();
            two_n_alpha_beta_one += 2.into();
        }
        answer *= two_to_alpha_beta_one;
        answer
    }
}

// alpha = beta = Galpha - 1/2
// twice_alpha_plus_offset = 2*Galpha
/// not normalized in the same way, coefficients of `J^{Galpha-1/2,Galpha-1/2}_n (x)` rather than `C_n^{Galpha}(x)`
/// so all the coefficients will be changed by factors relating these two for each n
pub type GegenbauerBasisPolynomial<const N: usize, const TWICE_GALPHA: usize, T> =
    JacobiBasisPolynomial<N, TWICE_GALPHA, TWICE_GALPHA, T>;

/// normalized in the same way, coefficients of `J^{0,0}_n (x) = P_n(x)`
pub type LegendreBasisPolynomial<const N: usize, T> = GegenbauerBasisPolynomial<N, 1, T>;

/// not normalized in the same way, coefficients of `J^{-1/2,-1/2}_n (x)` rather than `T_n(x)`
/// `J^{-1/2,-1/2}_n (x) = Gamma(n+1/2)/(Sqrt[pi]*Gamma(n+1))*T_n(x)`
/// so all the coefficients will be changed by these factors
pub type ChebyshevBasisPolynomial<const N: usize, T> = GegenbauerBasisPolynomial<N, 0, T>;

mod test {
    #[test]
    fn presence() {
        // just that using jacobi feature
    }
}
