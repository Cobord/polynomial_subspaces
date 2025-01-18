use core::ops::{Add, AddAssign, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{
    fundamental_theorem::{
        cubic_solve, quadratic_solve, quartic_solve, FindZeroError, FundamentalTheorem,
    },
    generic_polynomial::{
        BasisIndexingType, DegreeType, DifferentiateError, Generic1DPoly, MonomialError,
        SmallIntegers, SubspaceError,
    },
    ordinary_polynomial::MonomialBasisPolynomial,
};

/// store the coefficients of 1-t, t, (1-t)*s^1, t*s^1, (1-t)*s^2, t*s^2, ... in that order
/// up to N of them
/// s is shorthand for t*(1-t)
/// this provides an alternative basis for the vector space of polynomials
#[repr(transparent)]
#[derive(Clone)]
pub struct SymmetricalBasisPolynomial<const N: usize, T> {
    pub(crate) coeffs: [T; N],
}

impl<const N: usize, T> SymmetricalBasisPolynomial<N, T>
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
    /// with only knowing the const generic N, we can constrain the polynomial degree
    /// as an upper bound, without worrying about if a coefficient was actually 0 or not
    #[must_use]
    pub const fn polynomial_degree_bound() -> usize {
        // 1 -> 1-t -> 1
        // 2 -> t,1-t -> 1
        // 3 -> t,1-t,(1-t)^2*t -> 3
        // 4 -> t,1-t,(1-t)^2*t,(1-t)*t^2 -> 3
        if N % 2 == 0 {
            N - 1
        } else {
            N
        }
    }

    pub fn coeffs_view(&self) -> &[T; N] {
        &self.coeffs
    }

    /// precompose with t <-> 1-t
    /// can fail if N is odd, because
    /// then the last coefficient should swap
    /// with the one after it, but that doesn't exist
    fn reverse(&mut self) {
        #[allow(clippy::manual_assert)]
        if N % 2 == 1 {
            panic!("Only allowed to reverse in place on polynomials with even number of basis coefficients because they come in pairs for reversal");
        }
        for coeff_pair in self.coeffs.chunks_exact_mut(2) {
            coeff_pair.reverse();
        }
    }

    /// precompose with t <-> 1-t
    /// check if it would fail rather than panic
    /// that distinction can be done with compile time information
    pub fn try_reverse(&mut self) -> bool {
        if N % 2 == 0 {
            return false;
        }
        self.reverse();
        true
    }

    fn differentiate_single_hardcoded(n: usize) -> Option<Self> {
        // hard coded for small n, because those are the ones that are used more often
        if n < 2 {
            let coeffs: [T; N] = core::array::from_fn(|idx| {
                if idx > 1 {
                    0.into()
                } else {
                    let ans: T = 1.into();
                    if n == 0 {
                        -ans
                    } else {
                        //
                        ans
                    }
                }
            });
            return Some(Self { coeffs });
        }
        if n == 2 {
            #[allow(clippy::match_same_arms)]
            let coeffs: [T; N] = core::array::from_fn(|idx| match idx {
                0 => 1.into(),
                2 => (-3).into(),
                3 => (-3).into(),
                _ => 0.into(),
            });
            return Some(Self { coeffs });
        }
        if n == 3 {
            #[allow(clippy::match_same_arms)]
            let coeffs: [T; N] = core::array::from_fn(|idx| match idx {
                1 => (-1).into(),
                2 => (3).into(),
                3 => (3).into(),
                _ => 0.into(),
            });
            return Some(Self { coeffs });
        }
        if n == 4 {
            #[allow(clippy::match_same_arms)]
            let coeffs: [T; N] = core::array::from_fn(|idx| match idx {
                2 => (2).into(),
                4 => (-5).into(),
                5 => (-5).into(),
                _ => 0.into(),
            });
            return Some(Self { coeffs });
        }
        if n == 5 {
            #[allow(clippy::match_same_arms)]
            let coeffs: [T; N] = core::array::from_fn(|idx| match idx {
                3 => (-2).into(),
                4 => 5.into(),
                5 => 5.into(),
                _ => 0.into(),
            });
            return Some(Self { coeffs });
        }
        None
    }

    /// helper do differentiate when a single coefficient is 1 and the rest are 0
    fn differentiate_single(n: usize) -> Self {
        let hard_coded = Self::differentiate_single_hardcoded(n);
        if let Some(got_hard_coded) = hard_coded {
            return got_hard_coded;
        }
        // D_t (?*t^s_power*(1-t)^s_power)
        // Term 1 : (D_t ?)*t^s_power*(1-t)^s_power = +-1   t^s_power*(1-t)^s_power
        // Term 2 : ?*s_power*t^(s_power-1)*(1-t)^s_power = ?*s_power*(1-t)*    t^(s_power-1)*(1-t)^(s_power-1)
        // Term 3 : ?*t^s_power*s_power*(-1)*(1-t)^(s_power-1) = -?*s_power*t*   t^(s_power-1)*(1-t)^(s_power-1)
        let s_power = n >> 1;
        #[allow(clippy::cast_possible_truncation)]
        let s_power_t: T = ((n >> 1) as SmallIntegers).into();
        // index of (1-t)*s^s_power
        let where_one_minus_t_s_k = s_power << 1;
        let mut answer = Self::create_zero_poly();
        // Term 1 +-1   t^s_power*(1-t)^s_power
        if n % 2 == 0 {
            answer.coeffs[where_one_minus_t_s_k] -= 1.into();
            answer.coeffs[where_one_minus_t_s_k + 1] -= 1.into();
        } else {
            answer.coeffs[where_one_minus_t_s_k] += 1.into();
            answer.coeffs[where_one_minus_t_s_k + 1] += 1.into();
        }
        // Term 2 ?*s_power*(1-t)*    t^(s_power-1)*(1-t)^(s_power-1)
        let shift_for_s_power_minus_1 = (s_power - 1) << 1;
        let without_s_n_even = n % 2 == 0;
        match Self::product_goes_01(without_s_n_even, true) {
            Ok(x) => {
                let which_coeff_x = x + (shift_for_s_power_minus_1);
                answer.coeffs[which_coeff_x] += s_power_t.clone();
                answer.coeffs[which_coeff_x + 1] += s_power_t.clone();
            }
            Err((x, y)) => {
                let which_coeff_x = x + shift_for_s_power_minus_1;
                answer.coeffs[which_coeff_x] += s_power_t.clone();
                let which_coeff_y = y + shift_for_s_power_minus_1;
                answer.coeffs[which_coeff_y] -= s_power_t.clone();
                answer.coeffs[which_coeff_y + 1] -= s_power_t.clone();
            }
        }
        // Term 3 -?*s_power*t*   t^(s_power-1)*(1-t)^(s_power-1)
        match Self::product_goes_01(without_s_n_even, false) {
            Ok(x) => {
                let which_coeff_x = x + shift_for_s_power_minus_1;
                answer.coeffs[which_coeff_x] -= s_power_t.clone();
                answer.coeffs[which_coeff_x + 1] -= s_power_t;
            }
            Err((x, y)) => {
                let which_coeff_x = x + shift_for_s_power_minus_1;
                answer.coeffs[which_coeff_x] -= s_power_t.clone();
                let which_coeff_y = y + shift_for_s_power_minus_1;
                answer.coeffs[which_coeff_y] += s_power_t.clone();
                answer.coeffs[which_coeff_y + 1] += s_power_t;
            }
        }
        answer
    }

    const fn product_goes_01(
        idx_is_zero: bool,
        jdx_is_zero: bool,
    ) -> Result<usize, (usize, usize)> {
        match (idx_is_zero, jdx_is_zero) {
            (true, true) => {
                // (1-t)^2
                // 1-t,t,(1-t)*t*(1-t),t*t*(1-t)
                // (1-t)^2 = (1-t) - (1-t)*t
                // (1-t)*t*(1-t) + t*t*(1-t) = t*(1-t)
                // (1-t)^2 = -1 * (1-t)*t*(1-t) + -1 * t*t*(1-t) + (1-t)
                Err((0, 2))
            }
            (true, false) => {
                // (1-t)*t
                Ok(2)
            }
            (false, true) => {
                // t*(1-t)
                Ok(2)
            }
            (false, false) => {
                // t^2
                // 1-t,t,(1-t)*t*(1-t),t*t*(1-t)
                // t^2 = -1*(1-t)*t+t
                // (1-t)*t*(1-t) + t*t*(1-t) = t*(1-t)
                // t^2 = -1 * (1-t)*t*(1-t) + -1 * t*t*(1-t) + t
                Err((1, 2))
            }
        }
    }

    /// when multiplying the term associated with `self.coeffs[idx]` and `self.coeffs[jdx]`
    /// the possibilities are either 2 terms in the result or 3 terms
    /// in the Ok case we have two terms both coming with + signs Ok(x) meaning x and x+1
    /// in the Err case we have three terms with the first with a + sign and the other two with - signs
    /// Err((x,y)) meaning x comes with + and y and y+1 come with - sign
    #[allow(clippy::similar_names)]
    const fn product_goes(idx: usize, jdx: usize) -> Result<usize, (usize, usize)> {
        let power_of_s_idx = idx >> 1;
        let power_of_s_jdx = jdx >> 1;
        let answer = Self::product_goes_01(idx % 2 == 0, jdx % 2 == 0);
        let products_power_of_s = power_of_s_idx + power_of_s_jdx;
        if products_power_of_s == 0 {
            return answer;
        }
        match answer {
            Ok(mut idx) => {
                idx += (products_power_of_s) << 1;
                Ok(idx)
            }
            Err((mut x, mut y)) => {
                x += products_power_of_s << 1;
                y += products_power_of_s << 1;
                Err((x, y))
            }
        }
    }

    pub fn multiply_by_t(
        self,
        sure_will_cancel: bool,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Option<Self> {
        let mut answer = Self::create_zero_poly();
        for (which, coeff) in self.coeffs.into_iter().enumerate() {
            if zero_pred(&coeff) {
                continue;
            }
            match Self::product_goes(which, 1) {
                Ok(x) => {
                    if x + 1 < N {
                        answer.coeffs[x] += coeff.clone();
                        answer.coeffs[x + 1] += coeff.clone();
                    } else if sure_will_cancel {
                        if x < N {
                            answer.coeffs[x] += coeff.clone();
                        }
                    } else {
                        return None;
                    }
                }
                Err((y, z)) => {
                    if z + 1 < N {
                        answer.coeffs[y] += coeff.clone();
                        answer.coeffs[z] -= coeff.clone();
                        answer.coeffs[z + 1] -= coeff.clone();
                    } else if sure_will_cancel {
                        if y < N {
                            answer.coeffs[y] += coeff.clone();
                        }
                        if z < N {
                            answer.coeffs[z] -= coeff.clone();
                        }
                    } else {
                        return None;
                    }
                }
            }
        }
        Some(answer)
    }

    /// do the product of two polynomials
    /// one with at most the first N coefficients in this basis
    /// one with at most the first M coefficients in this basis
    /// the product should fit within the first N
    /// this can be done by making sure we pad self with 0's so N is large enough first
    /// knowing when elements are 0 allows us to avoid multiplications by 0 and additions of 0, etc
    /// `sure_will_cancel` means even if it looks like coefficients that are not in the first N,
    ///     will be present in the middle of the computation, they will eventually cancel so no need to worry
    fn try_product<const M: usize>(
        &self,
        rhs: &SymmetricalBasisPolynomial<M, T>,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<Self> {
        let mut answer = Self::create_zero_poly();
        for (idx, factor_1_coeff) in self.coeffs.iter().enumerate() {
            if zero_pred(factor_1_coeff) {
                continue;
            }
            for (jdx, factor_2_coeff) in rhs.coeffs.iter().enumerate() {
                if zero_pred(factor_2_coeff) {
                    continue;
                }
                let product_these_coeffs = factor_1_coeff.clone() * factor_2_coeff.clone();
                match Self::product_goes(idx, jdx) {
                    Ok(a) => {
                        if a + 1 >= N {
                            if sure_will_cancel {
                                if a < N {
                                    answer.coeffs[a] += product_these_coeffs;
                                }
                            } else {
                                return None;
                            }
                        } else {
                            answer.coeffs[a] += product_these_coeffs.clone();
                            answer.coeffs[a + 1] += product_these_coeffs;
                        }
                    }
                    Err((a, b)) => {
                        if b + 1 >= N {
                            if sure_will_cancel {
                                if a < N {
                                    answer.coeffs[a] += product_these_coeffs.clone();
                                }
                                if b < N {
                                    answer.coeffs[b] -= product_these_coeffs;
                                }
                            } else {
                                return None;
                            }
                        } else {
                            answer.coeffs[a] += product_these_coeffs.clone();
                            answer.coeffs[b] -= product_these_coeffs.clone();
                            answer.coeffs[b + 1] -= product_these_coeffs.clone();
                        }
                    }
                }
            }
        }
        Some(answer)
    }

    #[allow(clippy::result_unit_err)]
    /// change the degree by padding with extra 0's for a larger M
    /// or get rid of the 0's on the higher degree basis vectors to truncate to a smaller M
    /// # Errors
    /// if we are trying to shrink the size, but those terms being discarded were not 0
    pub fn try_convert_degree<const M: usize>(
        self,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<SymmetricalBasisPolynomial<M, T>, ()> {
        if M < N {
            match self.polynomial_degree(zero_pred) {
                Some(big_degree)
                    if usize::from(big_degree)
                        > SymmetricalBasisPolynomial::<M, T>::polynomial_degree_bound() =>
                {
                    return Err(());
                }
                Some(_) => {
                    if !self.coeffs[M..].iter().all(zero_pred) {
                        return Err(());
                    }
                }
                None => return Ok(SymmetricalBasisPolynomial::<M, T>::create_zero_poly()),
            }
        }
        let coeffs = core::array::from_fn(|idx| {
            if idx < N {
                self.coeffs[idx].clone()
            } else {
                0.into()
            }
        });
        Ok(SymmetricalBasisPolynomial::<M, T> { coeffs })
    }

    pub fn pretty_format(&self, variable: &str, zero_pred: &impl Fn(&T) -> bool) -> String
    where
        T: std::fmt::Debug,
    {
        let answers: [String; N] = core::array::from_fn(|idx| {
            if zero_pred(&self.coeffs[idx]) {
                "0".to_string()
            } else {
                let zeroth_part = format!("({:?})", self.coeffs[idx]);
                let first_part = if idx % 2 == 0 {
                    format!("(1 - {variable})")
                } else {
                    variable.to_string()
                };
                let s_power = idx >> 1;
                if s_power == 0 {
                    format!("{zeroth_part}*{first_part}")
                } else {
                    let second_part =
                        format!("({variable}**{s_power})*((1 - {variable})**{s_power})");
                    format!("{zeroth_part}*{first_part}*{second_part}")
                }
            }
        });
        answers.join(" + ")
    }
}

impl<const N: usize, T> Generic1DPoly<T> for SymmetricalBasisPolynomial<N, T>
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
    fn create_zero_poly() -> Self {
        let coeffs = core::array::from_fn(|_| 0.into());
        Self { coeffs }
    }

    fn create_monomial(
        n: DegreeType,
        zero_pred: &impl Fn(&T) -> bool,
        surely_fits: bool,
    ) -> Result<Self, MonomialError> {
        if n == 0 {
            if N < 2 {
                return Err(MonomialError::DesiredMonomialNotInSpace(0));
            }
            let coeffs: [T; N] =
                core::array::from_fn(|idx| if idx > 1 { 0.into() } else { 1.into() });
            return Ok(Self { coeffs });
        }
        if n == 1 {
            if N < 2 {
                return Err(MonomialError::DesiredMonomialNotInSpace(1));
            }
            let coeffs: [T; N] =
                core::array::from_fn(|idx| if idx == 1 { 1.into() } else { 0.into() });
            return Ok(Self { coeffs });
        }
        let mut answer = Self::create_monomial(1, zero_pred, true)?;
        for cur_power in 1..n {
            // answer is t^cur_power
            answer = answer
                .multiply_by_t(surely_fits, zero_pred)
                .ok_or(MonomialError::DesiredMonomialNotInSpace(cur_power + 1))?;
            // answer is t^(cur_power+1)
        }
        Ok(answer)
    }

    fn evaluate_at_many<const POINT_COUNT: usize>(&self, ts: [T; POINT_COUNT]) -> [T; POINT_COUNT] {
        let s_values: [T; POINT_COUNT] =
            core::array::from_fn(|idx| ts[idx].clone() * (Into::<T>::into(1) - ts[idx].clone()));
        let mut cur_power_of_s: [T; POINT_COUNT] = core::array::from_fn(|_| 1.into());
        let mut answers: [T; POINT_COUNT] = core::array::from_fn(|_| 0.into());
        for term in self.coeffs.chunks_exact(2) {
            let mut to_add: [T; POINT_COUNT] = core::array::from_fn(|_| term[0].clone());
            // term[0]*(1-t)+term[1]*t = term[0] + (term[1]-term[0])*t
            to_add.iter_mut().zip(&ts).zip(&cur_power_of_s).for_each(
                |((to_add_idx, ts_idx), cur_power_of_s_idx)| {
                    *to_add_idx += (term[1].clone() - term[0].clone()) * ts_idx.clone();
                    *to_add_idx *= cur_power_of_s_idx.clone();
                },
            );
            answers
                .iter_mut()
                .zip(to_add)
                .for_each(|(cur_answer, to_add_idx)| {
                    *cur_answer += to_add_idx;
                });
            cur_power_of_s
                .iter_mut()
                .zip(&s_values)
                .for_each(|(cur_power_of_s_idx, s_idx)| {
                    *cur_power_of_s_idx *= s_idx.clone();
                });
        }
        if N % 2 == 1 {
            let mut to_add: [T; POINT_COUNT] = core::array::from_fn(|_| self.coeffs[N - 1].clone());
            // term[0]*(1-t)+term[1]*t = term[0] + (term[1]-term[0])*t

            to_add.iter_mut().zip(&ts).zip(&cur_power_of_s).for_each(
                |((to_add_idx, ts_idx), cur_power_of_s_idx)| {
                    *to_add_idx -= self.coeffs[N - 1].clone() * ts_idx.clone();
                    *to_add_idx *= cur_power_of_s_idx.clone();
                },
            );
            answers
                .iter_mut()
                .zip(to_add)
                .for_each(|(cur_answer, to_add_idx)| {
                    *cur_answer += to_add_idx;
                });
        }
        answers
    }

    fn evaluate_at(&self, t: T) -> T {
        let one_t: T = 1.into();
        let s = t.clone() * (one_t - t.clone());
        let mut cur_power_of_s: T = 1.into();
        let mut answer: T = 0.into();
        for term in self.coeffs.chunks_exact(2) {
            let mut to_add = term[0].clone();
            // term[0]*(1-t)+term[1]*t = term[0] + (term[1]-term[0])*t
            to_add += (term[1].clone() - term[0].clone()) * t.clone();
            to_add *= cur_power_of_s.clone();
            answer += to_add;
            cur_power_of_s *= s.clone();
        }
        if N % 2 == 1 {
            let mut to_add = self.coeffs[N - 1].clone();
            to_add -= self.coeffs[N - 1].clone() * t.clone();
            to_add *= cur_power_of_s.clone();
            answer += to_add;
        }
        answer
    }

    fn evaluate_at_zero(&self) -> T {
        self.coeffs[0].clone()
    }

    fn evaluate_at_one(&self) -> T {
        self.coeffs[1].clone()
    }

    fn evaluate_at_neg_one(&self) -> T {
        let mut cur_power_of_s: T = 1.into();
        let mut answer: T = 0.into();
        for term in self.coeffs.chunks_exact(2) {
            let mut to_add = term[0].clone() * 2.into();
            // term[0]*(1-(-1))+term[1]*(-1) = term[0]*2 - term[1]
            to_add -= term[1].clone();
            to_add *= cur_power_of_s.clone();
            answer += to_add;
            cur_power_of_s *= 2.into();
            cur_power_of_s = -cur_power_of_s;
        }
        if N % 2 == 1 {
            let mut to_add = self.coeffs[N - 1].clone() * 2.into();
            to_add *= cur_power_of_s.clone();
            answer += to_add;
        }
        answer
    }

    fn is_zero_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.coeffs.iter().all(zero_pred)
    }

    fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        let linear_coeff_truncated = if N == 1 {
            -self.coeffs[0].clone()
        } else {
            self.coeffs[1].clone() - self.coeffs[0].clone()
        };
        zero_pred(&linear_coeff_truncated) && self.coeffs[1..].iter().all(zero_pred)
    }

    fn polynomial_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<DegreeType> {
        let mut upper_bound = Self::polynomial_degree_bound();
        if N % 2 == 1 && !zero_pred(&self.coeffs[N - 1]) {
            #[allow(clippy::cast_possible_truncation)]
            return Some(upper_bound as DegreeType);
        }
        while upper_bound > 1 {
            // a*(1-t)*s^k + b*t*s^k
            // ((b-a)*t + a)*s^k
            let a = &self.coeffs[upper_bound - 1];
            let b = &self.coeffs[upper_bound - 2];
            let a_zero = zero_pred(a);
            let b_zero = zero_pred(b);
            #[allow(clippy::cast_possible_truncation)]
            if a_zero && b_zero {
                upper_bound -= 2;
            } else if a_zero || b_zero {
                return Some(upper_bound as DegreeType);
            } else {
                let b_minus_a = b.clone() - a.clone();
                return if zero_pred(&b_minus_a) {
                    Some((upper_bound - 1) as DegreeType)
                } else {
                    Some(upper_bound as DegreeType)
                };
            }
        }
        None
    }

    fn differentiate(self) -> Result<Self, DifferentiateError> {
        if N % 2 == 1 && self.coeffs[N - 1] != 0.into() {
            // has a term C*(1-t)*s^k with C nonzero
            // so that it gives a 2k+1 degree polynomial
            // but we don't have t*s*k and that is needed
            // for the leading coefficient A of the 2k degree derivative
            // namely we must have A(1-t)*s^k + A*t*s^k as the top two terms
            // but t*s^k is not in this subspace
            return Err(DifferentiateError::NotInTheSpace);
        }
        let mut answer = Self::create_zero_poly();
        for (idx, cur_coeff) in self.coeffs.into_iter().enumerate() {
            let mut new_term = Self::differentiate_single(idx);
            new_term *= cur_coeff;
            answer += new_term;
        }
        Ok(answer)
    }

    fn truncating_product(
        &self,
        rhs: &Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<Self> {
        self.try_product(rhs, zero_pred, sure_will_cancel)
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

impl<const N: usize, T> SymmetricalBasisPolynomial<N, T>
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
    pub fn base_change<U>(self) -> SymmetricalBasisPolynomial<N, U>
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
        SymmetricalBasisPolynomial::<N, U> {
            coeffs: core::array::from_fn(|idx| self.coeffs[idx].clone().into()),
        }
    }
}

impl<const N: usize, T> FundamentalTheorem<T> for SymmetricalBasisPolynomial<N, T>
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
        + DivAssign<T>
        + PartialEq<T>,
{
    /// zeros of the polynomial along with their
    /// multiplicities
    /// the second term is 1 below the multiplicity
    /// so that we can still use 0 as something meaningful -> 0 is a simple root of multiplicity 1
    fn find_zeros(
        &self,
        zero_pred: &impl Fn(&T) -> bool,
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> (Option<T>, Option<T>),
    ) -> Result<Vec<(T, usize)>, FindZeroError> {
        let degree = self.polynomial_degree(zero_pred);
        match degree {
            Some(0) => Ok(vec![]),
            Some(1) => {
                let constant_term = self.evaluate_at_zero();
                let linear_coeff = if N == 1 {
                    -self.coeffs[0].clone()
                } else {
                    self.coeffs[1].clone() - self.coeffs[0].clone()
                };
                // linear_coeff*t+constant_term = 0
                let mut only_zero = -constant_term;
                only_zero /= linear_coeff;
                Ok(vec![(only_zero, 0)])
            }
            Some(2) => {
                // in order to be quadratic both coeffs[2] and coeffs[3] must be present
                // without coeffs[3] but with nonzero coeffs[2] it would be cubic
                // and if coeffs[2] was 0 it would be linear, constant or 0
                let constant_term = self.evaluate_at_zero();
                //self.coeffs[0]*(1-t) + self.coeffs[1]*t + self.coeffs[2]*(1-t)*t*(1-t) + self.coeffs[3]*t*(1-t)*t
                let two_t: T = 2.into();
                let linear_coeff =
                    self.coeffs[1].clone() - self.coeffs[0].clone() + self.coeffs[2].clone();
                let quadratic_coeff =
                    -two_t.clone() * self.coeffs[2].clone() + self.coeffs[3].clone();
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
                //self.coeffs[0]*(1-t) + self.coeffs[1]*t + self.coeffs[2]*(1-t)*t*(1-t) + self.coeffs[3]*t*(1-t)*t
                let two_t: T = 2.into();
                let linear_coeff =
                    self.coeffs[1].clone() - self.coeffs[0].clone() + self.coeffs[2].clone();
                let (quadratic_coeff, cubic_coeff) = if N < 4 {
                    let quadratic_coeff = -two_t.clone() * self.coeffs[2].clone();
                    let cubic_coeff = -self.coeffs[2].clone();
                    (quadratic_coeff, cubic_coeff)
                } else {
                    let quadratic_coeff =
                        -two_t.clone() * self.coeffs[2].clone() + self.coeffs[3].clone();
                    let cubic_coeff = -(self.coeffs[2].clone() + self.coeffs[3].clone());
                    (quadratic_coeff, cubic_coeff)
                };
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
                // the terms from before and
                // self.coeffs[4]*(1-t)*(1-t)^2*t^2 + self.coeffs[5]*t*(1-t)^2*t^2
                // with -self.coeffs[4]+self.coeffs[5] = 0 to cancel out the t^5 term
                let two_t: T = 2.into();
                let linear_coeff =
                    self.coeffs[1].clone() - self.coeffs[0].clone() + self.coeffs[2].clone();
                let (mut quadratic_coeff, mut cubic_coeff) = if N < 4 {
                    let quadratic_coeff = -two_t.clone() * self.coeffs[2].clone();
                    let cubic_coeff = -self.coeffs[2].clone();
                    (quadratic_coeff, cubic_coeff)
                } else {
                    let quadratic_coeff =
                        -two_t.clone() * self.coeffs[2].clone() + self.coeffs[3].clone();
                    let cubic_coeff = -(self.coeffs[2].clone() + self.coeffs[3].clone());
                    (quadratic_coeff, cubic_coeff)
                };
                quadratic_coeff += self.coeffs[4].clone();
                let three_t: T = 3.into();
                let three_coeff_4 = three_t * self.coeffs[4].clone();
                cubic_coeff += self.coeffs[5].clone() - three_coeff_4.clone();
                let quartic_coeff = -(three_coeff_4 + two_t * self.coeffs[5].clone());
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

impl<const N: usize, T> SubAssign<T> for SymmetricalBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + SubAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>,
{
    fn sub_assign(&mut self, rhs: T) {
        assert!(N >= 1, "The zero subspace");
        assert!(N >= 2, "The subspace spanned by only (1-t)");
        self.coeffs[0] -= rhs.clone();
        self.coeffs[1] -= rhs.clone();
    }
}

impl<const N: usize, T> AddAssign<T> for SymmetricalBasisPolynomial<N, T>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign
        + SubAssign
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + From<SmallIntegers>
        + Sub<Output = T>,
{
    fn add_assign(&mut self, rhs: T) {
        assert!(N >= 1, "The zero subspace");
        assert!(N >= 2, "The subspace spanned by only (1-t)");
        self.coeffs[0] += rhs.clone();
        self.coeffs[1] += rhs.clone();
    }
}

impl<const N: usize, T> MulAssign<T> for SymmetricalBasisPolynomial<N, T>
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
    fn mul_assign(&mut self, rhs: T) {
        for cur_coeff in &mut self.coeffs {
            *cur_coeff *= rhs.clone();
        }
    }
}

impl<const N: usize, T> Mul<T> for SymmetricalBasisPolynomial<N, T>
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
    type Output = Self;
    fn mul(mut self, rhs: T) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const N: usize, T> Sub<T> for SymmetricalBasisPolynomial<N, T>
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
    type Output = Self;
    fn sub(mut self, rhs: T) -> Self::Output {
        assert!(N >= 1, "The zero subspace");
        assert!(N >= 2, "The subspace spanned by only (1-t)");
        self.coeffs[0] = self.coeffs[0].clone() - rhs.clone();
        self.coeffs[1] = self.coeffs[1].clone() - rhs.clone();
        self
    }
}

impl<const N: usize, T> Add<T> for SymmetricalBasisPolynomial<N, T>
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
    type Output = Self;
    fn add(mut self, rhs: T) -> Self::Output {
        assert!(N >= 1, "The zero subspace");
        assert!(N >= 2, "The subspace spanned by only (1-t)");
        self.coeffs[0] += rhs.clone();
        self.coeffs[1] += rhs;
        self
    }
}

impl<const N: usize, T> Add<Self> for SymmetricalBasisPolynomial<N, T>
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
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const N: usize, T> AddAssign for SymmetricalBasisPolynomial<N, T>
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
    fn add_assign(&mut self, rhs: Self) {
        for (idx, cur_coeff) in rhs.coeffs.into_iter().enumerate() {
            self.coeffs[idx] += cur_coeff;
        }
    }
}

impl<const N: usize, T> Sub<Self> for SymmetricalBasisPolynomial<N, T>
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
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const N: usize, T> SubAssign for SymmetricalBasisPolynomial<N, T>
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
    fn sub_assign(&mut self, rhs: Self) {
        for (idx, cur_coeff) in rhs.coeffs.into_iter().enumerate() {
            self.coeffs[idx] -= cur_coeff;
        }
    }
}

impl<const N: usize, T> Neg for SymmetricalBasisPolynomial<N, T>
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
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut answer = Self::create_zero_poly();
        answer -= self;
        answer
    }
}

impl<const N: usize, T> TryFrom<MonomialBasisPolynomial<T>> for SymmetricalBasisPolynomial<N, T>
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
    type Error = MonomialError;

    fn try_from(value: MonomialBasisPolynomial<T>) -> Result<Self, Self::Error> {
        let mut answer = Self::create_zero_poly();
        for term in value.coeffs {
            match Self::create_monomial(term.0, &|_| false, false) {
                Ok(monomial_symmetrized) => {
                    answer += monomial_symmetrized * term.1;
                }
                Err(e) => {
                    return Err(e);
                }
            }
        }
        Ok(answer)
    }
}

mod test {

    #[allow(clippy::float_cmp)]
    #[test]
    fn test_product_goes_small() {
        use super::SymmetricalBasisPolynomial;
        use crate::generic_polynomial::{Generic1DPoly, SmallIntegers};
        let t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -1., 0., 0.],
        };
        let s = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 0., 1., 1., 0., 0.],
        };
        let one_minus_t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [1., 0., -1., -1., 0., 0.],
        };
        let expected_results = [[one_minus_t_squared, s.clone()], [s, t_squared]];
        let into_poly = |current: Result<usize, (usize, usize)>| match current {
            Ok(x) => {
                let mut answer = SymmetricalBasisPolynomial::<6, f64>::create_zero_poly();
                answer.coeffs[x] += Into::<f64>::into(1 as SmallIntegers);
                answer.coeffs[x + 1] += Into::<f64>::into(1 as SmallIntegers);
                answer
            }
            Err((x, y)) => {
                let mut answer = SymmetricalBasisPolynomial::<6, f64>::create_zero_poly();
                answer.coeffs[x] += Into::<f64>::into(1 as SmallIntegers);
                answer.coeffs[y] -= Into::<f64>::into(1 as SmallIntegers);
                answer.coeffs[y + 1] -= Into::<f64>::into(1 as SmallIntegers);
                answer
            }
        };
        for idx in [0, 1] {
            for jdx in [0, 1] {
                let current = SymmetricalBasisPolynomial::<6, f64>::product_goes(idx, jdx);
                assert_eq!(
                    into_poly(current).coeffs,
                    expected_results[idx][jdx].coeffs,
                    "{idx} {jdx}"
                );
            }
        }
    }

    #[test]
    #[allow(clippy::float_cmp, clippy::too_many_lines)]
    fn test_differentiate_single_small() {
        use super::SymmetricalBasisPolynomial;
        use crate::generic_polynomial::Generic1DPoly;
        let one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [1., 1., 0., 0., 0., 0.],
        };
        let t_to_one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., 0., 0., 0., 0.],
        };
        let t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -1., 0., 0.],
        };
        assert_eq!(
            t_to_one
                .differentiate()
                .expect("this can be differentiated without issue")
                .coeffs,
            one.coeffs
        );
        let neg_one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [-1., -1., 0., 0., 0., 0.],
        };
        let diff_0 = SymmetricalBasisPolynomial::<6, f64>::differentiate_single(0);
        assert_eq!(diff_0.coeffs, neg_one.coeffs);
        assert_eq!(
            SymmetricalBasisPolynomial::<6, f64>::differentiate_single(1).coeffs,
            one.coeffs
        );
        // derivative of (1-t)*s=t-2t^2+t^3
        // is 1 - 4t + 3t^2
        let single_term_2 = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 0., 1., 0., 0., 0.],
        };
        let t_cubed = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -2., 0., 0.],
        };
        let t_to_one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., 0., 0., 0., 0.],
        };
        let expected = t_to_one - t_squared * 2. + t_cubed;
        assert_eq!(single_term_2.coeffs, expected.coeffs);
        let t_to_one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., 0., 0., 0., 0.],
        };
        let t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -1., 0., 0.],
        };
        let expected: SymmetricalBasisPolynomial<6, f64> = one + t_to_one * (-4.) + t_squared * 3.;
        let diff_2 = SymmetricalBasisPolynomial::<6, f64>::differentiate_single(2);
        let pretty_diff_2 = diff_2.pretty_format("t", &|z: &f64| z.abs() < f64::EPSILON);
        let pretty_expected = expected.pretty_format("t", &|z: &f64| z.abs() < f64::EPSILON);
        assert_eq!(pretty_expected, pretty_diff_2);
        assert_eq!(diff_2.coeffs, expected.coeffs);
        // derivative of t*s=t^2-t^3
        // is 2t-3t^2
        let t_to_one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., 0., 0., 0., 0.],
        };
        let t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -1., 0., 0.],
        };
        let expected: SymmetricalBasisPolynomial<6, f64> = t_to_one * 2. - t_squared * 3.;
        assert_eq!(
            SymmetricalBasisPolynomial::<6, f64>::differentiate_single(3).coeffs,
            expected.coeffs
        );
        // derivative of (1-t)*s*2=t^2-3t^3+3t^4-t^5
        // is 2t - 9t^2+12t^3-5t^4
        let t_to_one = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., 0., 0., 0., 0.],
        };
        let t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -1., 0., 0.],
        };
        let t_cubed = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -2., 0., 0.],
        };
        let t_fourth = t_cubed
            .multiply_by_t(true, &|z| z.abs() < 0.000_001)
            .unwrap();
        let t_cubed = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -2., 0., 0.],
        };
        let expected: SymmetricalBasisPolynomial<6, f64> =
            t_to_one * 2. - t_squared * 9. + t_cubed * 12. - t_fourth * 5.;
        assert_eq!(
            SymmetricalBasisPolynomial::<6, f64>::differentiate_single(4).coeffs,
            expected.coeffs
        );
        // derivative of t*s*2=t^3*(1-2t+t^2)=t^3-2*t^4+t^5
        // 3t^2 -8t^3 + 5t^4
        let t_squared = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -1., 0., 0.],
        };
        let t_cubed = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -2., 0., 0.],
        };
        let t_fourth = t_cubed
            .multiply_by_t(true, &|z| z.abs() < 0.000_001)
            .unwrap();
        assert_eq!(t_fourth.coeffs, [0., 1., -1., -3., 1., 1.]);
        let t_cubed = SymmetricalBasisPolynomial::<6, f64> {
            coeffs: [0., 1., -1., -2., 0., 0.],
        };
        let expected: SymmetricalBasisPolynomial<6, f64> =
            t_fourth * 5. - t_cubed * 8. + t_squared * 3.;
        assert_eq!(
            SymmetricalBasisPolynomial::<6, f64>::differentiate_single(5).coeffs,
            expected.coeffs
        );
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_differentiate_single_nonhardcoded() {
        use super::SymmetricalBasisPolynomial;
        //use crate::generic_polynomial::Generic1DPoly;
        let diff_6 = SymmetricalBasisPolynomial::<10, f64>::differentiate_single_hardcoded(6);
        assert!(diff_6.is_none());
        let diff_6 = SymmetricalBasisPolynomial::<10, f64>::differentiate_single(6);
        let expected_diff_6 = SymmetricalBasisPolynomial::<10, f64> {
            coeffs: [0., 0., 0., 0., 3., 0., -7., -7., 0., 0.],
        };
        assert_eq!(diff_6.coeffs, expected_diff_6.coeffs);
    }

    // different order of computation so the errors for accurately running tests
    // could be larger than machine epsilon for f64
    // things like non-associativity building up over many steps
    #[allow(dead_code)]
    const TEST_EPSILON: f64 = f64::EPSILON;

    #[test]
    fn monomial_multiply_by_t() {
        use crate::generic_polynomial::{DegreeType, Generic1DPoly};
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        const HOW_MANY_SYM_BASIS: usize = 10;
        const DEGREE_HANDLEABLE: DegreeType = 9;
        const EXPECT_MESSAGE: &str = "For degrees <= 9, 10 symmetric basis coefficients are enough";
        const EXPECT_MESSAGE_2 : &str = "If degree+1 <= 9, then there should be no problem multiplying t^degree by t to get t^(degree+1)";
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..DEGREE_HANDLEABLE + 5 {
            let in_sym_basis =
                SymmetricalBasisPolynomial::<HOW_MANY_SYM_BASIS, f64>::create_monomial(
                    degree,
                    &zero_float,
                    degree <= DEGREE_HANDLEABLE,
                );
            if degree > DEGREE_HANDLEABLE {
                assert!(in_sym_basis.is_err());
            } else {
                let real_in_sym_basis = in_sym_basis.expect(EXPECT_MESSAGE);
                #[allow(clippy::int_plus_one)]
                let after_mul_t = real_in_sym_basis
                    .clone()
                    .multiply_by_t(degree + 1 <= DEGREE_HANDLEABLE, &zero_float);
                #[allow(clippy::collapsible_if)]
                if after_mul_t.is_none() {
                    if degree + 1 > DEGREE_HANDLEABLE {
                        break;
                    }
                }
                let after_mul_t = after_mul_t.expect(EXPECT_MESSAGE_2);
                for t_point in [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.] {
                    let without_t_factor = real_in_sym_basis.evaluate_at(t_point);
                    let with_t_factor = after_mul_t.evaluate_at(t_point);
                    let diff = without_t_factor * t_point - with_t_factor;
                    assert!(
                        diff.abs() < TEST_EPSILON,
                        "{without_t_factor} {with_t_factor} {degree} {t_point}"
                    );
                }
            }
        }
    }
}

mod test_more {

    // different order of computation so the errors for accurately running tests
    // could be larger than machine epsilon for f64
    // things like non-associativity building up over many steps
    #[allow(dead_code)]
    const TEST_EPSILON: f64 = 1e-9;

    #[test]
    fn monomials_match() {
        use crate::generic_polynomial::test_same_polynomial;
        use crate::generic_polynomial::{DegreeType, Generic1DPoly};
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        const HOW_MANY_SYM_BASIS: usize = 9;
        const DEGREE_HANDLEABLE: DegreeType = 7;
        const EXPECT_MESSAGE: &str = "For degrees <= 7, 9 symmetric basis coefficients are enough, can't do 8 without the 10th, once have 10th then can do 8 and 9";
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..DEGREE_HANDLEABLE + 5 {
            let in_ordinary =
                MonomialBasisPolynomial::<f64>::create_monomial(degree, &zero_float, true)
                    .expect("No out of const size for these");
            let in_sym_basis =
                SymmetricalBasisPolynomial::<HOW_MANY_SYM_BASIS, f64>::create_monomial(
                    degree,
                    &zero_float,
                    degree <= DEGREE_HANDLEABLE,
                );
            if degree > DEGREE_HANDLEABLE {
                assert!(in_sym_basis.is_err());
            } else {
                let real_in_sym_basis = in_sym_basis.expect(EXPECT_MESSAGE);
                test_same_polynomial(
                    &in_ordinary,
                    &real_in_sym_basis,
                    degree,
                    [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.],
                    &|&diff| (diff.abs() < TEST_EPSILON),
                );
            }
        }
    }

    #[test]
    fn monomial_derivatives_match() {
        use crate::generic_polynomial::test_same_polynomial;
        use crate::generic_polynomial::{DegreeType, Generic1DPoly};
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        const HOW_MANY_SYM_BASIS: usize = 10;
        const DEGREE_HANDLEABLE: DegreeType = 9;
        const EXPECT_MESSAGE: &str = "For degrees <= 9, 10 symmetric basis coefficients are enough";
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..DEGREE_HANDLEABLE + 5 {
            let in_ordinary =
                MonomialBasisPolynomial::<f64>::create_monomial(degree, &zero_float, true)
                    .expect("No out of const size for these");
            let in_ordinary = in_ordinary
                .differentiate()
                .expect("this can be differentiated without issue");
            let in_sym_basis =
                SymmetricalBasisPolynomial::<HOW_MANY_SYM_BASIS, f64>::create_monomial(
                    degree,
                    &zero_float,
                    degree <= DEGREE_HANDLEABLE,
                );
            if degree > DEGREE_HANDLEABLE {
                assert!(in_sym_basis.is_err());
            } else {
                let real_in_sym_basis = in_sym_basis.expect(EXPECT_MESSAGE);
                let real_in_sym_basis = real_in_sym_basis
                    .differentiate()
                    .expect("this can be differentiated without issue");
                test_same_polynomial(
                    &in_ordinary,
                    &real_in_sym_basis,
                    degree,
                    [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.],
                    &|&diff| (diff.abs() < TEST_EPSILON),
                );
            }
        }
    }

    #[test]
    fn evaluate_one_vs_more() {
        use crate::generic_polynomial::{DegreeType, Generic1DPoly};
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        const HOW_MANY_SYM_BASIS: usize = 9;
        const DEGREE_HANDLEABLE: DegreeType = 7;
        const EXPECT_MESSAGE: &str = "For degrees <= 7, 9 symmetric basis coefficients are enough, can't do 8 without the 10th, once have 10th then can do 8 and 9";
        const NUM_T_POINTS: usize = 7;
        const T_POINTS: [f64; NUM_T_POINTS] = [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.];
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..DEGREE_HANDLEABLE + 5 {
            let in_sym_basis =
                SymmetricalBasisPolynomial::<HOW_MANY_SYM_BASIS, f64>::create_monomial(
                    degree,
                    &zero_float,
                    degree <= DEGREE_HANDLEABLE,
                );
            if degree > DEGREE_HANDLEABLE {
                assert!(in_sym_basis.is_err());
            } else {
                let real_in_sym_basis = in_sym_basis.expect(EXPECT_MESSAGE);
                let from_point_by_point: [f64; NUM_T_POINTS] =
                    core::array::from_fn(|idx| real_in_sym_basis.evaluate_at(T_POINTS[idx]));
                let from_many = real_in_sym_basis.evaluate_at_many(T_POINTS);
                for (a, b) in from_point_by_point.into_iter().zip(from_many) {
                    let diff = a - b;
                    assert!(zero_float(&diff));
                }
            }
        }
    }
}
