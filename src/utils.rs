use std::rc::Rc;

use p3_field::{ExtensionField, Field};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, vpoly::VPoly};
use sum_check::primitives::SumCheckProof;

pub fn generate_eq<F: Field, E: ExtensionField<F>>(points: &[E]) -> Vec<E> {
    let mut res = vec![E::one()];

    for point in points {
        let mut v = vec![];
        for val in &res {
            v.push(*val * (E::one() - *point));
            v.push(*val * *point);
        }
        res = v;
    }

    res
}

// Algorithm 4
pub fn initialize_phase_one<F: Field, E: ExtensionField<F>>(
    igz: &[E],
    f1: &[(usize, usize, usize)],
    f3: &[F],
) -> Vec<E> {
    let mut res = vec![E::zero(); f3.len()];

    for (z, x, y) in f1 {
        // It is assumed the operation poly outputs 1 where there is a valid gate
        res[*x] += igz[*z] * f3[*y];
    }

    res
}

// Algorithm 5
pub fn initialize_phase_two<F: Field, E: ExtensionField<F>>(
    igz: &Vec<E>,
    iux: &Vec<E>,
    f1: &Vec<(usize, usize, usize)>,
) -> Vec<E> {
    let mut res = vec![E::zero(); iux.len()];

    for (z, x, y) in f1 {
        // It is assumed the operation poly outputs 1 where there is a valid gate
        res[*y] += igz[*z] * iux[*x];
    }

    res
}

// Combines a vector of sumcheck proofs into one sumcheck proof
pub fn combine_sumcheck_proofs<F: Field, E: ExtensionField<F>>(
    sumcheck_proofs: Vec<SumCheckProof<F, E>>,
) -> SumCheckProof<F, E> {
    sumcheck_proofs
        .into_iter()
        .reduce(|mut acc, val| {
            acc.round_polynomials
                .extend_from_slice(&val.round_polynomials);
            acc
        })
        .unwrap()
}

pub fn prepare_phase_one_params<F: Field, E: ExtensionField<F>>(
    g: &Vec<E>,
    add_i: &Vec<(usize, usize, usize)>,
    mul_i: &Vec<(usize, usize, usize)>,
    w_i_plus_one: &Vec<F>,
) -> (Vec<E>, Vec<E>, Vec<E>, Vec<E>) {
    let igz = generate_eq(&g);

    let ident = vec![F::one(); w_i_plus_one.len()];

    // Build Ahg for mul, add_b and add_c
    let mul_ahg = initialize_phase_one(&igz, &mul_i, &w_i_plus_one);

    // Can this be removed in the first phase?
    let add_b_ahg = initialize_phase_one(&igz, &add_i, &ident);

    let add_c_ahg = initialize_phase_one(&igz, &add_i, &w_i_plus_one);

    (igz, mul_ahg, add_b_ahg, add_c_ahg)
}

// hg(x)
pub fn build_phase_one_libra_sumcheck_poly<F: Field, E: ExtensionField<F>>(
    mul_ahg: &Vec<E>,
    add_b_ahg: &Vec<E>,
    add_c_ahg: &Vec<E>,
    w_i_plus_one_poly: &MultilinearPoly<F, E>,
) -> VPoly<F, E> {
    let n_vars = w_i_plus_one_poly.num_vars();

    VPoly::new(
        vec![
            MultilinearPoly::new_from_vec(
                n_vars,
                mul_ahg
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_b_ahg
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_c_ahg
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            w_i_plus_one_poly.clone(),
        ],
        2,
        n_vars,
        Rc::new(|data: &[Fields<F, E>]| (data[3] * (data[0] + data[1])) + data[2]),
    )
}

pub fn prepare_phase_one_params_with_alpha_beta_rb_rc<F: Field, E: ExtensionField<F>>(
    rb: &Vec<E>,
    rc: &Vec<E>,
    alpha_n_beta: &[E],
    add_i: &Vec<(usize, usize, usize)>,
    mul_i: &Vec<(usize, usize, usize)>,
    w_i_plus_one: &Vec<F>,
) -> (Vec<E>, Vec<E>, Vec<E>, Vec<E>) {
    let ident = vec![F::one(); w_i_plus_one.len()];

    // get Igz for rb and rc
    let alpha_rb_igz: Vec<E> = generate_eq(&rb)
        .iter()
        .map(|val| *val * alpha_n_beta[0])
        .collect::<Vec<E>>();
    let beta_rc_igz: Vec<E> = generate_eq(&rc)
        .iter()
        .map(|val| *val * alpha_n_beta[1])
        .collect::<Vec<E>>();
    let new_igz = alpha_rb_igz
        .iter()
        .zip(&beta_rc_igz)
        .map(|(rhs, lhs)| *rhs + *lhs)
        .collect::<Vec<E>>();

    // Get new_addi_b for rb and rc
    let new_addi_b_ahg: Vec<E> = initialize_phase_one(&new_igz, add_i, &ident);
    // let rc_addi_b_ahg: Vec<E> = initialize_phase_one(&beta_igz_rc, add_i, &ident);
    // let new_addi_b_ahg = rb_addi_b_ahg
    //     .iter()
    //     .zip(rc_addi_b_ahg)
    //     .map(|(rhs, lhs)| *rhs + lhs)
    //     .collect::<Vec<E>>();

    // Get new_addi_c for rb and rc
    let new_addi_c_ahg = initialize_phase_one(&new_igz, add_i, w_i_plus_one);
    // let rc_addi_c_ahg = initialize_phase_one(&beta_igz_rc, add_i, w_i_plus_one);

    // let new_addi_c_ahg = rb_addi_c_ahg
    //     .iter()
    //     .zip(rc_addi_c_ahg)
    //     .map(|(rhs, lhs)| *rhs + lhs)
    //     .collect::<Vec<E>>();

    // Get new_muli for rb and rc
    let new_mul_ahg = initialize_phase_one(&new_igz, mul_i, w_i_plus_one);
    // let rc_mul_ahg = initialize_phase_one(&beta_igz_rc, mul_i, w_i_plus_one);
    // let new_mul_ahg = rb_mul_ahg
    //     .iter()
    //     .zip(rc_mul_ahg)
    //     .map(|(rhs, lhs)| *rhs + lhs)
    //     .collect::<Vec<E>>();

    // put correct new igz
    (new_igz, new_mul_ahg, new_addi_b_ahg, new_addi_c_ahg)
}

pub fn prepare_phase_two_params<F: Field, E: ExtensionField<F>>(
    igz: &Vec<E>,
    u: &Vec<E>,
    add_i: &Vec<(usize, usize, usize)>,
    mul_i: &Vec<(usize, usize, usize)>,
) -> (Vec<E>, Vec<E>) {
    let iux = generate_eq(u);

    // Build Af1 for mul and add
    let mul_af1 = initialize_phase_two(&igz, &iux, &mul_i);

    let add_af1 = initialize_phase_two(&igz, &iux, &add_i);

    (mul_af1, add_af1)
}

pub fn build_phase_two_libra_sumcheck_poly<F: Field, E: ExtensionField<F>>(
    mul_af1: &Vec<E>,
    add_af1: &Vec<E>,
    wb: &E,
    w_i_plus_one_poly: &MultilinearPoly<F, E>,
) -> VPoly<F, E> {
    let n_vars = w_i_plus_one_poly.num_vars();

    VPoly::new(
        vec![
            MultilinearPoly::new_from_vec(
                n_vars,
                mul_af1
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_af1
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                vec![wb; w_i_plus_one_poly.evaluations.len()]
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(**val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            w_i_plus_one_poly.clone(),
        ],
        2,
        n_vars,
        Rc::new(|data: &[Fields<F, E>]| {
            (data[0] * data[2] * data[3]) + (data[1] * (data[2] + data[3]))
        }),
    )
}

#[cfg(test)]
mod tests {
    use p3_field::{AbstractExtensionField, AbstractField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;

    use crate::utils::{generate_eq, initialize_phase_one, initialize_phase_two};

    #[test]
    fn test_precompute() {
        let challenges: Vec<BinomialExtensionField<Mersenne31, 3>> = [1, 3, 5]
            .into_iter()
            .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(Mersenne31::new(val)))
            .collect();

        let precomputed =
            generate_eq::<Mersenne31, BinomialExtensionField<Mersenne31, 3>>(&challenges);

        let expected: Vec<BinomialExtensionField<Mersenne31, 3>> = [
            Mersenne31::zero(),
            Mersenne31::zero(),
            Mersenne31::zero(),
            Mersenne31::zero(),
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        assert_eq!(precomputed, expected);
    }

    #[test]
    fn test_build_ahg() {
        //
        //       12      30      56      90
        //       *       *       *       *
        //     /   \   /   \   /   \   /   \
        //     3   4   5   6   7   8   9   10
        //

        // values (3,5) were used to generate the Igz table
        // (1-a)(1-b) = (1-3)(1-5) = 8
        // (1-a)b = (1-3) 5 = -10
        // a(1-b) = 3 (1-5) = -12
        // ab = 3*5 = 15

        let igz: Vec<_> = [
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        // f(out, left, right) in the sparse form
        let f1 = vec![(0, 0, 1), (1, 2, 3), (2, 4, 5), (3, 6, 7)];

        let f3 = vec![
            Mersenne31::from_canonical_usize(3),
            Mersenne31::from_canonical_usize(4),
            Mersenne31::from_canonical_usize(5),
            Mersenne31::from_canonical_usize(6),
            Mersenne31::from_canonical_usize(7),
            Mersenne31::from_canonical_usize(8),
            Mersenne31::from_canonical_usize(9),
            Mersenne31::from_canonical_usize(10),
        ];

        let ahg = initialize_phase_one(&igz, &f1, &f3);

        let expected: Vec<_> = [
            Mersenne31::from_canonical_usize(32),
            Mersenne31::zero(),
            -Mersenne31::from_canonical_usize(60),
            Mersenne31::zero(),
            -Mersenne31::from_canonical_usize(96),
            Mersenne31::zero(),
            Mersenne31::from_canonical_usize(150),
            Mersenne31::zero(),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        assert_eq!(ahg, expected);
    }

    #[test]
    fn test_build_af1() {
        //
        //       12      30      56      90
        //       *       *       *       *
        //     /   \   /   \   /   \   /   \
        //     3   4   5   6   7   8   9   10
        //

        // values (3,5) were used to generate the Igz table
        // (1-a)(1-b) = (1-3)(1-5) = 8
        // (1-a)b = (1-3) 5 = -10
        // a(1-b) = 3 (1-5) = -12
        // ab = 3*5 = 15

        let igz = [
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        // values (4,7,3) were used to generate the Iux table
        // (1-a)(1-b)(1-c) = (1-4)(1-7)(1-3) = -36
        // (1-a)(1-b)c = (1-4)(1-7)3 = 54
        // (1-a)b(1-c) = (1-4)7(1-3) = 42
        // (1-a)b*c = (1-4)*7*3 = -63
        // a(1-b)(1-c) = 4*(1-7)*(1-3) = 48
        // a(1-b)c = 4*(1-7)*3 = -72
        // a*b(1-c) = 4*7*(1-3) = -56
        // a*b*c = 4*7*3 = 84

        let iux = [
            -Mersenne31::from_canonical_usize(36),
            Mersenne31::from_canonical_usize(54),
            Mersenne31::from_canonical_usize(42),
            -Mersenne31::from_canonical_usize(63),
            Mersenne31::from_canonical_usize(48),
            -Mersenne31::from_canonical_usize(72),
            -Mersenne31::from_canonical_usize(56),
            Mersenne31::from_canonical_usize(84),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        // f(out, left, right) in the sparse form
        let f1 = vec![(0, 0, 1), (1, 2, 3), (2, 4, 5), (3, 6, 7)];

        let af1 = initialize_phase_two::<Mersenne31, BinomialExtensionField<Mersenne31, 3>>(
            &igz, &iux, &f1,
        );

        let expected: Vec<_> = [
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(288),
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(420),
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(576),
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(840),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        assert_eq!(af1, expected);
    }
}
