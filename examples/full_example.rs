use polynomial_subspaces::generic_polynomial::test_same_polynomial;
use polynomial_subspaces::generic_polynomial::Generic1DPoly;
use polynomial_subspaces::my_symmetrical_basis_pair::SymmetricalBasisPolynomial;
use polynomial_subspaces::ordinary_polynomial::MonomialBasisPolynomial;

#[cfg(feature = "bezier")]
use bezier_rs::Bezier;
#[cfg(feature = "bezier")]
use polynomial_subspaces::TwoPolynomials;

const TEST_EPSILON: f64 = 1e-15;

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
        let two_polys: TwoPolynomials<f64, SymmetricalBasisPolynomial<4, f64>> = b.into();
        println!(
            "{}",
            two_polys.pretty_format("x", &|z: &f64| z.abs() < f64::EPSILON)
        );
    }
    {
        let zero_float = |z: &f64| z.abs() < TEST_EPSILON;
        for degree in 0..10 {
            let in_ordinary =
                MonomialBasisPolynomial::<f64>::create_monomial(degree, &zero_float, true)
                    .expect("No out of const size for these");
            println!("{:?}", in_ordinary.coeffs_view());
            let in_ordinary = in_ordinary
                .differentiate()
                .expect("this can be differentiated without issue");
            println!("{:?}", in_ordinary.coeffs_view());
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
                println!("function using sym {:?}", real_in_sym_basis.coeffs_view());
                let real_in_sym_basis = real_in_sym_basis
                    .differentiate()
                    .expect("this can be differentiated without issue");
                println!("derivative using ordinary {:?}", in_ordinary.coeffs_view());
                println!("derivative using sym {:?}", real_in_sym_basis.coeffs_view());
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
}
