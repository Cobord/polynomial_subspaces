#![cfg_attr(feature = "GADT", feature(generic_const_exprs))]

#[cfg(feature = "bezier")]
use bezier_rs::Bezier;

mod dense_ordinary_polynomial;
mod generic_polynomial;
mod jacobi;
mod my_symmetrical_basis_pair;
mod ordinary_polynomial;

#[cfg(feature = "pade")]
mod pade;

fn main() {
    #[cfg(feature = "bezier")]
    {
        let b = Bezier::from_linear_coordinates(0.0, -1.0, 5.0, 5.0);
        let z = b.roots();
        println!("{:?}", z[0]);
        println!("{:?}", z[1]);
        let b = Bezier::from_cubic_coordinates(0.0, -1.0, 5.0, 5.0, 3.0, 4.0, -7.0, -4.0);
        let z = b.roots();
        println!("{:?}", z[0]);
        println!("{:?}", z[1]);
    }
    {
        const TEST_EPSILON: f64 = 1e-15;
        use crate::generic_polynomial::test_same_polynomial;
        use crate::generic_polynomial::Generic1DPoly;
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..10 {
            let in_ordinary =
                MonomialBasisPolynomial::<f64>::create_monomial(degree, &zero_float, true)
                    .expect("No out of const size for these");
            println!("{:?}", in_ordinary.coeffs);
            let in_ordinary = in_ordinary
                .differentiate()
                .expect("this can be differentiated without issue");
            println!("{:?}", in_ordinary.coeffs);
            let in_sym_basis = SymmetricalBasisPolynomial::<6, f64>::create_monomial(
                degree,
                &zero_float,
                degree < 6,
            );
            if degree >= 6 {
                assert!(in_sym_basis.is_err());
            } else {
                let real_in_sym_basis = in_sym_basis
                    .expect("For degrees <= 5, 6 symmetric basis coefficients are enough");
                println!("function using sym {:?}", real_in_sym_basis.coeffs);
                let real_in_sym_basis = real_in_sym_basis
                    .differentiate()
                    .expect("this can be differentiated without issue");
                println!("derivative using ordinary {:?}", in_ordinary.coeffs);
                println!("derivative using sym {:?}", real_in_sym_basis.coeffs);
                test_same_polynomial(
                    in_ordinary,
                    real_in_sym_basis,
                    degree,
                    [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.],
                    &|&diff| (diff.abs() < TEST_EPSILON),
                );
            }
        }
    }
}

mod test {

    // different order of computation so the errors for accurately running tests
    // could be larger than machine epsilon for f64
    // things like non-associativity building up over many steps
    #[allow(dead_code)]
    const TEST_EPSILON: f64 = 1e-15;

    #[test]
    #[allow(dead_code)]
    fn monomials_match() {
        use crate::generic_polynomial::test_same_polynomial;
        use crate::generic_polynomial::{DegreeType, Generic1DPoly};
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        const HOW_MANY_SYM_BASIS: usize = 9;
        const DEGREE_HANDLEABLE: DegreeType = 7;
        const EXPECT_MESSAGE: &str = "For degrees <= 7, 9 symmetric basis coefficients are enough, can't do 8 without the 10th, once have 10th then can do 8 and 9";
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
                    in_ordinary,
                    real_in_sym_basis,
                    degree,
                    [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.],
                    &|&diff| (diff.abs() < TEST_EPSILON),
                );
            }
        }
    }

    #[test]
    #[allow(dead_code)]
    fn monomial_derivatives_match() {
        use crate::generic_polynomial::test_same_polynomial;
        use crate::generic_polynomial::{DegreeType, Generic1DPoly};
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        const HOW_MANY_SYM_BASIS: usize = 6;
        const DEGREE_HANDLEABLE: DegreeType = 5;
        const EXPECT_MESSAGE: &str = "For degrees <= 5, 6 symmetric basis coefficients are enough";
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
                    in_ordinary,
                    real_in_sym_basis,
                    degree,
                    [0., 0.2, 0.3564, 0.5335, 0.789, 0.999, 1.],
                    &|&diff| (diff.abs() < TEST_EPSILON),
                );
            }
        }
    }
}
