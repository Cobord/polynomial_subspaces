use bezier_rs::Bezier;
mod generic_polynomial;
mod jacobi;
mod my_symmetrical_basis_pair;
mod ordinary_polynomial;

fn main() {
    let b = Bezier::from_linear_coordinates(0.0, -1.0, 5.0, 5.0);
    let z = b.roots();
    println!("{:?}", z[0]);
    println!("{:?}", z[1]);
    let b = Bezier::from_cubic_coordinates(0.0, -1.0, 5.0, 5.0, 3.0, 4.0, -7.0, -4.0);
    let z = b.roots();
    println!("{:?}", z[0]);
    println!("{:?}", z[1]);
    println!("Hello, world!");
}

mod test {

    // different order of computation so the errors for accurately running tests
    // could be larger than machine epsilon for f64
    // things like non-associativity building up over many steps
    #[allow(dead_code)]
    const TEST_EPSILON: f64 = f64::EPSILON;

    #[test]
    #[allow(dead_code)]
    fn multiply_by_t() {
        use crate::generic_polynomial::Generic1DPoly;
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..10 {
            let in_sym_basis = SymmetricalBasisPolynomial::<6, f64>::create_monomial(
                degree,
                &zero_float,
                degree < 6,
            );
            if degree >= 6 {
                assert!(in_sym_basis.is_none());
            } else {
                let real_in_sym_basis = in_sym_basis
                    .expect("For degrees <= 5, 6 symmetric basis coefficients are enough");
                let after_mul_t = real_in_sym_basis.clone().multiply_by_t(false, &zero_float);
                if after_mul_t.is_none() {
                    if degree > 3 {
                        break;
                    }
                }
                let after_mul_t = after_mul_t.unwrap();
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

    #[test]
    #[allow(dead_code)]
    fn monomials_match() {
        use crate::generic_polynomial::test_same_polynomial;
        use crate::generic_polynomial::Generic1DPoly;
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..10 {
            let in_ordinary =
                MonomialBasisPolynomial::<f64>::create_monomial(degree, &zero_float, true)
                    .expect("No out of const size for these");
            let in_sym_basis = SymmetricalBasisPolynomial::<6, f64>::create_monomial(
                degree,
                &zero_float,
                degree < 6,
            );
            if degree >= 6 {
                assert!(in_sym_basis.is_none());
            } else {
                let real_in_sym_basis = in_sym_basis
                    .expect("For degrees <= 5, 6 symmetric basis coefficients are enough");
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
        use crate::generic_polynomial::Generic1DPoly;
        use crate::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
        use crate::ordinary_polynomial::MonomialBasisPolynomial;
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..10 {
            let in_ordinary =
                MonomialBasisPolynomial::<f64>::create_monomial(degree, &zero_float, true)
                    .expect("No out of const size for these");
            println!("{:?}", in_ordinary.coeffs);
            let in_ordinary = in_ordinary.differentiate();
            println!("{:?}", in_ordinary.coeffs);
            let in_sym_basis = SymmetricalBasisPolynomial::<6, f64>::create_monomial(
                degree,
                &zero_float,
                degree < 6,
            );
            if degree >= 6 {
                assert!(in_sym_basis.is_none());
            } else {
                let real_in_sym_basis = in_sym_basis
                    .expect("For degrees <= 5, 6 symmetric basis coefficients are enough");
                println!("function using sym {:?}", real_in_sym_basis.coeffs);
                let real_in_sym_basis = real_in_sym_basis.differentiate();
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
