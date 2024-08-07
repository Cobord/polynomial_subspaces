/// TODO
/// not packed tightly or guaranteeing sorting by degree
/// only using for testing
/// can get rid of it after have tests that don't need it anymore
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::ops::DivAssign;

use crate::generic_polynomial::{
    cubic_solve, quadratic_solve, quartic_solve, DegreeType, FindZeroError, FundamentalTheorem,
    Generic1DPoly, PointSpecifier, SmallIntegers,
};
pub struct MonomialBasisPolynomial<T>
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
    pub(crate) coeffs: Vec<(DegreeType, T)>,
}

impl<T> MonomialBasisPolynomial<T>
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
    fn extract_coeff(&self, which: DegreeType) -> T {
        self.coeffs
            .iter()
            .filter_map(|(power, coeff)| {
                if *power == which {
                    Some(coeff.clone())
                } else {
                    None
                }
            })
            .fold(Into::<T>::into(0), |acc, next| acc + next)
    }
}

impl<T> Generic1DPoly<T> for MonomialBasisPolynomial<T>
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
        Self { coeffs: Vec::new() }
    }

    fn create_monomial(
        degree: DegreeType,
        _zero_pred: &impl Fn(&T) -> bool,
        _surely_fits: bool,
    ) -> Option<Self> {
        Some(Self {
            coeffs: vec![(degree, 1.into())],
        })
    }

    fn evaluate_at(&self, t: T) -> T {
        let mut answer = 0.into();
        let mut last_power: (DegreeType, T) = (0, 1.into());
        for term in self.coeffs.iter() {
            if 2 * last_power.0 == term.0 {
                last_power.0 = term.0;
                last_power.1 *= last_power.1.clone();
            } else if last_power.0 <= term.0 {
                for _ in last_power.0..term.0 {
                    last_power.1 *= t.clone();
                }
                last_power.0 = term.0;
            } else {
                last_power.1 = 1.into();
                for _ in 0..term.0 {
                    last_power.1 *= t.clone();
                }
                last_power.0 = term.0;
            }
            answer += term.1.clone() * last_power.1.clone();
        }
        answer
    }

    fn evaluate_at_zero(&self) -> T {
        self.coeffs
            .iter()
            .filter_map(|(power, coeff)| {
                if *power == 0 {
                    Some(coeff.clone())
                } else {
                    None
                }
            })
            .fold(0.into(), |acc, next| acc + next)
    }

    fn evaluate_at_one(&self) -> T {
        self.coeffs
            .iter()
            .fold(0.into(), |acc, next| acc + next.1.clone())
    }

    fn evaluate_at_neg_one(&self) -> T {
        self.coeffs.iter().fold(0.into(), |acc, next| {
            if next.0 % 2 == 0 {
                acc + next.1.clone()
            } else {
                acc - next.1.clone()
            }
        })
    }

    fn is_zero_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.coeffs.iter().all(|(_degree, coeff)| zero_pred(coeff))
    }

    fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool {
        self.coeffs
            .iter()
            .all(|(degree, coeff)| zero_pred(coeff) || *degree == 0)
    }

    fn polynomial_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<DegreeType> {
        self.coeffs
            .iter()
            .filter_map(|(power, coeff)| {
                if !zero_pred(coeff) {
                    Some(*power)
                } else {
                    None
                }
            })
            .max()
    }

    fn differentiate(mut self) -> Self {
        let mut drop_idcs = vec![];
        self.coeffs
            .iter_mut()
            .enumerate()
            .for_each(|(idx, (degree, coeff))| {
                if *degree > 0 {
                    *coeff *= (*degree as SmallIntegers).into();
                    *degree -= 1;
                } else {
                    *coeff = (0 as SmallIntegers).into();
                    drop_idcs.push(idx);
                }
            });
        drop_idcs.sort_unstable();
        drop_idcs.reverse();
        for to_drop in drop_idcs {
            self.coeffs.remove(to_drop);
        }
        self
    }

    fn truncating_product(
        &self,
        rhs: &Self,
        zero_pred: &impl Fn(&T) -> bool,
        _sure_will_cancel: bool,
    ) -> Option<Self> {
        let mut answer: Vec<(DegreeType, T)> =
            Vec::with_capacity(self.coeffs.len() * rhs.coeffs.len());
        for (degree_1, coeff_1) in self.coeffs.iter() {
            if zero_pred(coeff_1) {
                continue;
            }
            for (degree_2, coeff_2) in rhs.coeffs.iter() {
                if zero_pred(coeff_2) {
                    continue;
                }
                let seek = degree_1 + degree_2;
                match answer.binary_search_by(|(z0, _z1)| z0.cmp(&seek)) {
                    Ok(found_point) => {
                        answer[found_point].1 += coeff_1.clone() * coeff_2.clone();
                    }
                    Err(insertion_point) => {
                        answer.insert(insertion_point, (seek, coeff_1.clone() * coeff_2.clone()));
                    }
                }
            }
        }
        Some(Self { coeffs: answer })
    }

    fn linear_approx(self, around_here: PointSpecifier<T>) -> (T, T) {
        let constant_term = match &around_here {
            PointSpecifier::NegOne => self.evaluate_at_neg_one(),
            PointSpecifier::Zero => self.evaluate_at_zero(),
            PointSpecifier::One => self.evaluate_at_one(),
            PointSpecifier::General(t) => self.evaluate_at(t.clone()),
        };
        let linear_term = match around_here {
            PointSpecifier::NegOne => {
                let derivative = self.differentiate();
                derivative.evaluate_at_neg_one()
            }
            PointSpecifier::Zero => {
                // overrides the default implementation because this way when asking
                // for linear approximation at 0, don't have to differentiate
                self.extract_coeff(1)
            }
            PointSpecifier::One => {
                let derivative = self.differentiate();
                derivative.evaluate_at_one()
            }
            PointSpecifier::General(t) => {
                let derivative = self.differentiate();
                derivative.evaluate_at(t)
            }
        };
        (constant_term, linear_term)
    }
}

impl<T> FundamentalTheorem<T> for MonomialBasisPolynomial<T>
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
        my_sqrt: &impl Fn(&T) -> Option<T>,
        my_cube_root: &impl Fn(&T) -> T,
    ) -> Result<Vec<(T, usize)>, crate::generic_polynomial::FindZeroError> {
        let degree = self.polynomial_degree(zero_pred);

        match degree {
            Some(0) => Ok(vec![]),
            Some(1) => {
                let constant_term = self.evaluate_at_zero();
                let linear_term: T = self.extract_coeff(1);
                let mut only_zero = -constant_term;
                only_zero /= linear_term;
                Ok(vec![(only_zero, 0)])
            }
            Some(2) => {
                let constant_term = self.evaluate_at_zero();
                let linear_coeff: T = self.extract_coeff(1);
                let quadratic_coeff: T = self.extract_coeff(2);
                quadratic_solve(
                    constant_term,
                    linear_coeff,
                    quadratic_coeff,
                    zero_pred,
                    my_sqrt,
                )
            }
            Some(3) => {
                let constant_term = self.evaluate_at_zero();
                let linear_coeff: T = self.extract_coeff(1);
                let quadratic_coeff: T = self.extract_coeff(2);
                let cubic_coeff: T = self.extract_coeff(3);
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
                let linear_coeff: T = self.extract_coeff(1);
                let quadratic_coeff: T = self.extract_coeff(2);
                let cubic_coeff: T = self.extract_coeff(3);
                let quartic_coeff: T = self.extract_coeff(4);
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
            Some(x) if x > 4 => Err(FindZeroError::AbelRuffiniUnsolvability),
            None => Err(FindZeroError::EverythingIsAZeroForZeroPolynomial),
            _ => {
                unreachable!("x>4 exhausted all the other Some cases")
            }
        }
    }
}

impl<T> Mul<T> for MonomialBasisPolynomial<T>
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

impl<T> MulAssign<T> for MonomialBasisPolynomial<T>
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
        self.coeffs
            .iter_mut()
            .for_each(|(_z0, z1)| *z1 *= rhs.clone());
    }
}

impl<T> Add<T> for MonomialBasisPolynomial<T>
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

impl<T> AddAssign<T> for MonomialBasisPolynomial<T>
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
        let const_term = self
            .coeffs
            .iter()
            .enumerate()
            .find(|(_idx, (z0, _z1))| *z0 == 0)
            .map(|z| z.0);
        if let Some(found_constant_term) = const_term {
            self.coeffs[found_constant_term].1 += rhs;
        } else {
            self.coeffs.insert(0, (0, rhs));
        }
    }
}

impl<T> Sub<T> for MonomialBasisPolynomial<T>
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

impl<T> SubAssign<T> for MonomialBasisPolynomial<T>
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
        let const_term = self
            .coeffs
            .iter()
            .enumerate()
            .find(|(_idx, (z0, _z1))| *z0 == 0)
            .map(|z| z.0);
        if let Some(found_constant_term) = const_term {
            self.coeffs[found_constant_term].1 -= rhs;
        } else {
            self.coeffs.insert(0, (0, -rhs));
        }
    }
}

impl<T> Add for MonomialBasisPolynomial<T>
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

impl<T> AddAssign for MonomialBasisPolynomial<T>
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
        self.coeffs.extend(rhs.coeffs);
        self.coeffs.sort_by(|z0, z1| z0.0.cmp(&z1.0));
    }
}

impl<T> Sub for MonomialBasisPolynomial<T>
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

impl<T> SubAssign for MonomialBasisPolynomial<T>
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
        self.coeffs.extend(
            rhs.coeffs
                .into_iter()
                .map(|(degree, coeff)| (degree, -coeff)),
        );
        self.coeffs.sort_by(|z0, z1| z0.0.cmp(&z1.0));
    }
}

impl<T> Neg for MonomialBasisPolynomial<T>
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
