use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub type DegreeType = u8;
pub type BasisIndexingType = u8;
pub type SmallIntegers = i8;

#[derive(Debug)]
pub enum DifferentiateError {
    NotInTheSpace,
    CantComputeDerivative,
}

#[derive(Debug)]
pub enum MonomialError {
    DesiredMonomialNotInSpace(DegreeType),
}

#[derive(Debug)]
pub enum SubspaceError {
    NotStoredAsCoefficients,
    NoSuchBasisVector(BasisIndexingType),
}

// TODO
// may make T Copy, but I like not having that at first
// so I can make the arithmetic I am doing with it
// not have to use those copies, having to put clone
// provides the painfulness to make aware of that happening

#[derive(Clone)]
pub enum PointSpecifier<T> {
    NegOne,
    Zero,
    One,
    General(T),
}

/// a subspace of the vector space T[x] where T is some ring
/// the subspace does not have to be closed under derivative
/// the common way this subspace is chosen is if we have some
/// natural number indexed basis and we demand to only take the
/// first N of these basis vectors
/// that is the case with `SymmetricalBasisPolynomial<N>`
/// where the basis is (1-x),x,(1-x)*x,x*s,... with s=x*(1-x)
/// that is also the case with `JacobiBasisPolynomial<N,TWICE_ALPHA_PLUS_OFFSET,TWICE_BETA_PLUS_OFFSET>`
/// where the basis is P^{alpha,beta}_n
/// similarly for the specializations of alpha and beta to get the other special polynomials
pub trait Generic1DPoly<T>:
    Sized
    + AddAssign<T>
    + Add<T, Output = Self>
    + Add<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<T>
    + Sub<T, Output = Self>
    + Sub<Self, Output = Self>
    + SubAssign<Self>
    + MulAssign<T>
    + Mul<T, Output = Self>
    + Neg<Output = Self>
where
    T: Clone
        + Neg<Output = T>
        + AddAssign<T>
        + Add<T, Output = T>
        + Mul<T, Output = T>
        + MulAssign<T>
        + From<SmallIntegers>
        + Sub<T, Output = T>,
{
    /// the zero polynomial as an element of the subspace
    fn create_zero_poly() -> Self;

    /// create `x^n` as an element of `V \subseteq R[x]`
    /// # Errors
    /// the monomial we are trying to create might not be in the subspace of R[X] specified
    fn create_monomial(
        degree: DegreeType,
        zero_pred: &impl Fn(&T) -> bool,
        surely_fits: bool,
    ) -> Result<Self, MonomialError>;

    fn evaluate_at(&self, t: T) -> T;

    /// evaluate the `self \in V \subseteq R[x]` at many values of x
    /// override this if there is repeated computation that is common to evaluate
    /// the polynomial at multiple points
    /// the default implementation does them individually without reusing any work
    fn evaluate_at_many<const POINT_COUNT: usize>(
        &self,
        mut ts: [T; POINT_COUNT],
    ) -> [T; POINT_COUNT] {
        #[allow(clippy::needless_range_loop)]
        for idx in 0..ts.len() {
            let mut cur_evaluate_point = 0.into();
            core::mem::swap(&mut cur_evaluate_point, &mut ts[idx]);
            ts[idx] = self.evaluate_at(cur_evaluate_point);
        }
        ts
    }

    // evaluate `self \in V \subseteq R[x]` at x=0
    /// override these because there is likely a better evaluation method for these special points
    fn evaluate_at_zero(&self) -> T {
        self.evaluate_at(0.into())
    }
    // evaluate `self \in V \subseteq R[x]` at x=1
    /// override these because there is likely a better evaluation method for these special points
    fn evaluate_at_one(&self) -> T {
        self.evaluate_at(1.into())
    }
    // evaluate `self \in V \subseteq R[x]` at x=-1
    /// override these because there is likely a better evaluation method for these special points
    fn evaluate_at_neg_one(&self) -> T {
        self.evaluate_at((-1).into())
    }

    /// is this equal to the 0 polynomial
    fn is_zero_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool;

    /// is it degree 0
    fn is_constant_polynomial(&self, zero_pred: &impl Fn(&T) -> bool) -> bool;

    /// what is the degree
    /// None for the 0 polynomial to signify `- \infty`
    fn polynomial_degree(&self, zero_pred: &impl Fn(&T) -> bool) -> Option<DegreeType>;

    /// attempt to differentiate this polynomial
    /// # Errors
    /// it might fail because the subspace does not have to be closed under `d/dx` operator
    fn differentiate(self) -> Result<Self, DifferentiateError>;

    /// take the product of these two polynomials
    /// the type of `Self` constrains the allowed terms
    /// if `sure_will_cancel` then even if we seem to be breaking those constraints
    /// then ignore that problem because we are told it will cancel out and that term
    /// will be 0 anyway
    fn truncating_product(
        &self,
        rhs: &Self,
        zero_pred: &impl Fn(&T) -> bool,
        sure_will_cancel: bool,
    ) -> Option<Self>;

    fn evaluate_at_specifier(&self, around_here: PointSpecifier<T>) -> T {
        match around_here {
            PointSpecifier::NegOne => self.evaluate_at_neg_one(),
            PointSpecifier::Zero => self.evaluate_at_zero(),
            PointSpecifier::One => self.evaluate_at_one(),
            PointSpecifier::General(t) => self.evaluate_at(t),
        }
    }

    /// first order approximation around the given point
    /// see override in `ordinary_polynomial` for a case
    /// when can avoid the differentiation
    /// both avoiding that extra work and the potential source of error
    /// # Errors
    /// it might fail because the subspace does not have to be closed under `d/dx` operator
    fn linear_approx(self, around_here: PointSpecifier<T>) -> Result<(T, T), DifferentiateError> {
        let constant_term = match &around_here {
            PointSpecifier::NegOne => self.evaluate_at_neg_one(),
            PointSpecifier::Zero => self.evaluate_at_zero(),
            PointSpecifier::One => self.evaluate_at_one(),
            PointSpecifier::General(t) => self.evaluate_at(t.clone()),
        };
        let derivative = self.differentiate()?;
        let linear_term = derivative.evaluate_at_specifier(around_here);
        Ok((constant_term, linear_term))
    }

    /// first order approximation around the given point
    /// # Errors
    /// it might fail because the subspace does not have to be closed under `d/dx` operator
    /// another possibility is that the subspace does not include the linear function `x`
    ///     that should be very unusual, because we typically truncate
    ///     by degree and 1 is too low of a degree to fall to the chopping block
    fn linear_approx_poly(
        self,
        around_here: PointSpecifier<T>,
    ) -> Result<Self, Result<DifferentiateError, MonomialError>> {
        let (constant_term, linear_term) = self.linear_approx(around_here).map_err(Ok)?;
        let mut answer = Self::create_zero_poly();
        answer += constant_term;
        // the subspace doesn't include the linear function x is the error below
        let mut linear_poly = Self::create_monomial(1, &|_| false, false).map_err(Err)?;
        linear_poly *= linear_term;
        Ok(answer + linear_poly)
    }

    /// assuming there is some natural number indexed basis at work behind the scenes
    /// give the first `up_to` of them as long as they are all within this subspace
    /// # Errors
    /// this can fail when this implicit assumption does not hold in which case `NotStoredAsCoefficients`
    /// or the `up_to` being too large causing us to leave the subspace, `NoSuchBasisVector`
    fn all_basis_vectors(up_to: BasisIndexingType) -> Result<Vec<Self>, SubspaceError>;

    /// assuming there is some natural number indexed basis at work behind the scenes
    /// set the coefficient of a particular basis polynomial
    /// # Errors
    /// this can fail when this implicit assumption does not hold in which case `NotStoredAsCoefficients`
    /// or the `which_coeff` being too large causing us to leave the subspace, `NoSuchBasisVector`
    fn set_basis_vector_coeff(
        &mut self,
        which_coeff: BasisIndexingType,
        new_coeff: T,
    ) -> Result<(), SubspaceError>;
}

/// # Panics
/// if these two are not the same polynomial
/// as measured by evaluating them both at several points
/// and making sure they are within some `small_enough` tolerance
pub fn test_same_polynomial<const N: usize, T, P, Q>(
    p: &P,
    q: &Q,
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
