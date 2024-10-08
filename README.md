# Introduction

Overall this is in regards to generally useful ways to deal with subspaces of the polynomial rings R[X]. There are multiple feature flags so you can concentrate on only the parts you need.

The ring R is a generic for the overall trait Generic1DPoly<R> that the main objects of concern all implement.

It must be a ring. That is enforced through it's implementation of certain core ops.
 - Clone
 - Negate<Output=R>
 - AddAssign<R>
 - Add<R, Output=R>
 - Mul<R, Output=R>
 - MulAssign<R>
 - From<SmallIntegers> (an alias for i8, the conversion being the initial arrow Z -> R restricted to those small integers)
 - Sub<R, Output=R>

One can do the following with a polynomial subspace
 - create the zero polynomial as an element of that subspace
 - attempt to create a monomial X^n though that may fail with an Err if the subspace does not include that particular polynomial
 - Query if the polynomial in question is zero or a constant
 - Evaluate at certain points with special versions for -1,0,1 where the evaluation might be done in a faster manner
 - Attempt to take a product of two polynomials though that might fail if the product would go outside the subspace
 - Differentiate though that might fail if the subspace is not closed under d/dX or if the way the polynomials are stored is not conducive to differentiation
 - Linearly approximate the given polynomial though that might fail because taking derivatives failed or constructing X^1 failed
 - If the subspace is explicitly the coefficients of a certain polynomial basis, then we can also list out that basis and reset individual coefficients. If it is not stored in that way, then that is an Err
 - AddAssign<R>, Add<R, Output = Self>, SubAssign<R>, Sub<R, Output = Self> for addition/subtraction of constant polynomials
 - Add<Self, Output = Self>, AddAssign<Self>,Sub<Self, Output = Self>, SubAssign<Self> for subspace being closed under addition and subtraction
 - MulAssign<R>, Mul<T, Output = Self>, Neg<Output = Self> for multiplication by scalars from the base ring

# Zeros

On such a subspace, we may also implement FundamentalTheorem<R> in reference to the fundamental theorem of algebra. For a subspace which implements this trait we have a find zeros method which either gives the zeros with multiplicities (only the ones within T itself without going to an extension) or a FindZeroError for the cases when the polynomial in question was the zero polynomial or the zeros could not be determined. This would be the case when the Abel-Ruffini unsolvability comes up. In this method, me must provide the square and cube root functions that are needed in the relavant quadratic or Cardano's formulae. They both return options to account for the possibilities that the generic ring R is not algebraically closed/doesn't have cube roots of unity, etc. We don't demnad such a restriction on R in the constraints on the type R when implementing Generic1DPoly<R>. The complicated square root and cube root functions are only as inputs and only relevant if we implement FundamentalTheorem<R>.

# Monomial Basis

## Dense

DenseMonomialBasisPolynomial<const N: usize, R> provides the most obvious such subspace where we are storing the coefficients of X^0 through X^{N-1}. The const generic means we are always assured to remain within this bounded degree subspace.
The implementations are the obvious ones and use the fast_polynomial package.

# Symmetrical Basis

The symmetrical basis is useful in the context of Bezier curves. This is because we want an easy way to privelege 0 and 1 as special points for being the endpoints of the interval that is parameterizing the curve. This basis is (1-t),t,(1-t)*s,t*s,(1-t)*s^2,t*s^2 and so on.
Here s is the quantity t*(1-t).

Again there is a const generic which describes how many of these basis vectors we are including in the subspace. In the Bezier context, this is usually bounded by 7, so N=8 to give a type level constraint that we are only ever working with such low degree polynomials.

# 2D Curves

We can consider such a curve with TwoPolynomials<R, P> so we get two polynomials representing the x and y components with both polynomials being in the subspace described by P. We can do the corresponding operations as on single polynomials that come from operating on each coordinate.

Because these are vector valued, we can consider their dot products and cross products to get back to single polynomials in the appropriate subspaces.

If we use the GADT flag, then the implementation of the product uses the sum operations on the const generic N which is describing the maximal degree in the subspace. The product then uses compile time operations on these bounds to get the appropriate larger degree. The GADT flag requires the unstable generic_const_exprs so +nightly if doing that.

If we don't use the GADT flag, then the multiplications of polynomials that happen when doing the cross and dot products are just the truncating product where we just attempt to multiply two elements of the subspace but have an Err return if we are no longer within the subspace.

We can ask for the parameter values when the curve is tangent and/or normal to the displacement from a point. In addition we can find those parameter values where one collides with another such curve (not the images of the curves intersecting which would be two independent parameters for each curve). There is also information about the curvature and speed (the name being from the case of R being reals but in general the functions still work though without such interpretability). Whenever dot or cross products are used the relevant caveat about the GADT flag holds.

## Bezier

This is behind the feature flag of bezier. Not particularly because of the functionality here but more so because of the dependence on bezier-rs and glam.

If we want this then we can describe a 2d up to cubic Bezier curves with the pairs of polynomials above particularly using the Symmetrical Basis. This provides the conversion from the Bezier of the bezier-rs package which uses the control points rather than the component polynomials. After such a conversion, we can do all the manipulations on TwoPolynomials<R,P> as above.

## 3D Curves

Similarly with curves as interpreted as polynomial maps R -> R^3 (R again not necessarily being the real numbers but the names of some of the functions are in that context). The only difference being the cross product is not a single polynomial implicitly multiplied by a unit z vector. Instead it is a member of the same ThreePolynomials<R,P>. Otherwise the corresponding description of 2D curves carries over mutatis munandi.

# Jacobi

This is not useful for general purpose so is behind the jacobi feature flag.

Jacobi polynomials are a generally useful orthogonal basis for the space of polynomials. Here T is more specialized. It must now be a field so it implements the Div core operations and it must have special constants like the square root of pi.
This does not mean we are restricted to only types like floats and complex. We still profit over remaining generic because we can enable symbolic expressions to use the same implementation with no change.

The parameters for Jacobi Polynomials are alpha and beta. But they are most often half-integral values and at least -1/2. This allows us to still use usize const generics to fix these values in the type though with a bit of shifting and scaling.

This subspace is again restricting the degree of the Jacobi Polynomials we are including in the subspace to be P_0^{alpha,beta} through P_{N-1}^{alpha,beta}.

## Gegenbauer

This provides a type alias with alpha and beta set equal to each other.

## Legendre

This provides a type alias with alpha and beta both set to 0.

## Chebyshev

This provides a type alias with alpha and beta both set to -1/2. CAUTION: this is not the same normalization as usual because it is just a type alias and they are really treated as coefficients of the corresponding Jacobi polynomials.

# Pade

This is behind a feature flag of pade. This is the struct of PadeApproximant<R, P, Q>. This covers the case of R(X) where we have described the numerator as something of type P and the denominator as of type Q. P and Q being types that implement the Generic1DPoly<R>.
This means we can do all the usual evaluations, querying if the rational function was 0 or constant and attempt to linearly approximate it (again possibly failing if the subspaces described by P and Q could not be differenetiated for any reason).

# Inner Product

We can demand the subspace in question is closed under some inner product. This is particularly in the context of orthogonal polynomials when the base R is the real numbers and there is some weighting and integration pairing.

This is unnecessary in many applications, so this is behind the orthogonal feature. If you enable jacobi, this is also enabled because Jacobi polynomials are explicitly such an orthogonal polynomial system.

