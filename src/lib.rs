#![cfg_attr(feature = "GADT", feature(generic_const_exprs))]

pub mod dense_ordinary_polynomial;
pub mod fundamental_theorem;
pub mod generic_polynomial;

#[cfg(feature = "orthogonal")]
pub mod inner_product;

#[cfg(feature = "jacobi")]
pub mod jacobi;
pub mod special_numbers;

pub mod my_symmetrical_basis_pair;
pub mod ordinary_polynomial;
pub mod three_d_curve;
pub mod two_d_curve;

#[cfg(feature = "pade")]
pub mod pade;

pub use dense_ordinary_polynomial::DenseMonomialBasisPolynomial;
pub use fundamental_theorem::{FindZeroError, FundamentalTheorem};
pub use generic_polynomial::{
    BasisIndexingType, DegreeType, DifferentiateError, Generic1DPoly, MonomialError,
    PointSpecifier, SmallIntegers, SubspaceError,
};
#[cfg(feature = "orthogonal")]
pub use inner_product::InnerProductSubspace;

#[cfg(feature = "jacobi")]
pub use jacobi::{
    ChebyshevBasisPolynomial, GegenbauerBasisPolynomial, JacobiBasisPolynomial,
    LegendreBasisPolynomial,
};
pub use special_numbers::SpecialNumbers;

pub use my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
pub use ordinary_polynomial::MonomialBasisPolynomial;

pub use three_d_curve::ThreePolynomials;
pub use two_d_curve::{NormalTangentError, TwoPolynomials};

#[cfg(feature = "pade")]
pub use pade::PadeApproximant;
