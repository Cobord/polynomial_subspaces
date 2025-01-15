use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub};

use crate::generic_polynomial::{
    BasisIndexingType, Generic1DPoly, MonomialError, SmallIntegers, SubspaceError,
};

#[allow(clippy::module_name_repetitions)]
pub trait InnerProductSubspace<T>: Generic1DPoly<T>
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
    /// the subspace `V \subseteq R[x]` is closed under this provided `inner_product`
    fn inner_product(&self, rhs: &Self) -> T;

    /// take the `inner_product` with `1*x^0`
    /// # Errors
    /// the subspace does not include the constant function `1*x^0`
    ///     that should be very unusual, because we typically truncate
    ///     by degree and 0 is too low of a degree to fall to the chopping block
    fn against_one(&self) -> Result<T, MonomialError> {
        let one_poly = Self::create_monomial(0, &|_| false, false)?;
        Ok(self.inner_product(&one_poly))
    }

    /// if already know this, don't have to do this double checking
    /// and can just return Ok(true) immediately when overriding this
    /// for this default implementation, assuming there is some natural number indexed
    ///     basis at work behind the scenes so we can use `all_basis_vectors`
    /// # Errors
    /// this can fail when the implicit assumption does not hold in which case `NotStoredAsCoefficients`
    /// or the `up_to` being too large causing us to leave the subspace, `NoSuchBasisVector`
    fn are_basis_vectors_orthogonal(
        up_to: BasisIndexingType,
        zero_pred: &impl Fn(&T) -> bool,
    ) -> Result<bool, SubspaceError> {
        let basis_vectors = Self::all_basis_vectors(up_to)?;
        for (idx, basis_vector_idx) in basis_vectors.iter().enumerate() {
            for basis_vector_jdx in basis_vectors.iter().skip(idx + 1) {
                if !zero_pred(&basis_vector_idx.inner_product(basis_vector_jdx)) {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}
