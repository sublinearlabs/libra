use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly};
use sum_check::{SumCheck, interface::SumCheckInterface, primitives::SumCheckProof};
use transcript::Transcript;

use crate::utils::{
    build_phase_one_libra_sumcheck_poly, build_phase_two_libra_sumcheck_poly,
    prepare_phase_two_params,
};

pub fn prove_libra_sumcheck<F: Field + PrimeField32, E: ExtensionField<F>>(
    igz: &Vec<E>,
    mul_ahg: &Vec<E>,
    add_b_ahg: &Vec<E>,
    add_c_ahg: &Vec<E>,
    add_i: &Vec<(usize, usize, usize)>,
    mul_i: &Vec<(usize, usize, usize)>,
    w_i_plus_one_poly: &MultilinearPoly<F, E>,
    transcript: &mut Transcript<F, E>,
) -> (SumCheckProof<F, E>, Vec<E>, Vec<E>, E, E) {
    let phase_one_poly =
        build_phase_one_libra_sumcheck_poly(mul_ahg, add_b_ahg, add_c_ahg, w_i_plus_one_poly);

    let claimed_sum = phase_one_poly.sum_over_hypercube();

    let (mut round_polys, u) = SumCheck::prove_partial(&phase_one_poly, transcript).unwrap();

    let wb: E = w_i_plus_one_poly
        .evaluate(
            &u.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        )
        .to_extension_field();

    // Prepare parameters for phase two
    let (mul_af1, add_af1) = prepare_phase_two_params(igz, &u, add_i, mul_i);

    let phase_two_poly =
        build_phase_two_libra_sumcheck_poly(&mul_af1, &add_af1, &wb, w_i_plus_one_poly);

    let (phase_two_round_polys, v) = SumCheck::prove_partial(&phase_two_poly, transcript).unwrap();

    round_polys.extend(phase_two_round_polys);

    let wc = w_i_plus_one_poly
        .evaluate(
            &v.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        )
        .to_extension_field();

    let sumcheck_proof = SumCheckProof::new(claimed_sum, round_polys);

    (sumcheck_proof, u, v, wb, wc)
}

#[cfg(test)]
mod tests {
    use p3_field::{AbstractExtensionField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;
    use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, vpoly::VPoly};
    use std::rc::Rc;
    use sum_check::{SumCheck, interface::SumCheckInterface};
    use transcript::Transcript;

    use super::prove_libra_sumcheck;

    use crate::utils::{prepare_phase_one_params, prepare_phase_one_params_with_alpha_beta_rb_rc};

    type F = Mersenne31;

    type E = BinomialExtensionField<Mersenne31, 3>;

    type MLE = VPoly<F, E>;

    #[test]
    fn test_prove_libra_sumcheck() {
        let g = vec![E::from_base(F::new(3))];

        let add_i = vec![(0, 0, 1)];

        let mul_i = vec![(1, 2, 3)];

        let w_i_plus_one_poly = MultilinearPoly::new_from_vec(
            2,
            vec![6, 6, 6, 16]
                .into_iter()
                .map(|val| Fields::Base(F::new(val)))
                .collect(),
        );

        // Traditional poly
        let mut add_i_eval = vec![0; 32];
        add_i_eval[1] = 1;
        let add_i_bln = MultilinearPoly::new_from_vec(
            5,
            add_i_eval
                .into_iter()
                .map(|val| Fields::<F, E>::Base(F::new(val)))
                .collect(),
        )
        .partial_evaluate(&[Fields::Base(F::new(3))]);

        let mut expected_add_i = vec![Fields::Extension(E::from_base(F::new(0))); 16];
        expected_add_i[1] = Fields::<F, E>::Extension(E::from_base(-F::new(2)));

        assert_eq!(add_i_bln.evaluations, expected_add_i);

        let mut mul_i_eval = vec![0; 32];
        mul_i_eval[27] = 1;
        let mul_i_bln = MultilinearPoly::new_from_vec(
            5,
            mul_i_eval
                .into_iter()
                .map(|val| Fields::Base(F::new(val)))
                .collect(),
        )
        .partial_evaluate(&[Fields::Base(F::new(3))]);

        let mut expected_mul_i = vec![Fields::Extension(E::from_base(F::new(0))); 16];
        expected_mul_i[11] = Fields::<F, E>::Extension(E::from_base(F::new(3)));

        assert_eq!(mul_i_bln.evaluations, expected_mul_i);

        let wb_bln = MultilinearPoly::new_from_vec(
            4,
            vec![6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 16, 16, 16, 16]
                .into_iter()
                .map(|val| Fields::<F, E>::Base(F::new(val)))
                .collect(),
        );

        let wc_bln = MultilinearPoly::new_from_vec(
            4,
            vec![6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16]
                .into_iter()
                .map(|val| Fields::Base(F::new(val)))
                .collect(),
        );

        assert_eq!(
            wc_bln.evaluate(&[
                Fields::Base(F::new(0)),
                Fields::Base(F::new(0)),
                Fields::Base(F::new(0)),
                Fields::Base(F::new(0))
            ]),
            Fields::Extension(E::from_base(Mersenne31::new(6)))
        );
        assert_eq!(
            wc_bln.evaluate(&[
                Fields::Base(F::new(0)),
                Fields::Base(F::new(1)),
                Fields::Base(F::new(0)),
                Fields::Base(F::new(1))
            ]),
            Fields::Extension(E::from_base(Mersenne31::new(6)))
        );
        assert_eq!(
            wc_bln.evaluate(&[
                Fields::Base(F::new(1)),
                Fields::Base(F::new(0)),
                Fields::Base(F::new(1)),
                Fields::Base(F::new(0))
            ]),
            Fields::Extension(E::from_base(F::new(6)))
        );
        assert_eq!(
            wc_bln.evaluate(&[
                Fields::Base(F::new(1)),
                Fields::Base(F::new(1)),
                Fields::Base(F::new(1)),
                Fields::Base(F::new(1))
            ]),
            Fields::Extension(E::from_base(F::new(16)))
        );

        let mut transcript = Transcript::<F, E>::init();

        let (igz, mul_ahg, add_b_ahg, add_c_ahg) = prepare_phase_one_params(
            &g,
            &add_i,
            &mul_i,
            &w_i_plus_one_poly
                .evaluations
                .iter()
                .map(|val| val.to_base_field().unwrap())
                .collect::<Vec<F>>(),
        );

        let (proof, rb, rc, wb, wc) = prove_libra_sumcheck(
            &igz,
            &mul_ahg,
            &add_b_ahg,
            &add_c_ahg,
            &add_i,
            &mul_i,
            &w_i_plus_one_poly,
            &mut transcript,
        );

        let mut transcript = Transcript::<F, E>::init();

        let (claimed_sum, challenges) =
            SumCheck::<F, E, MLE>::verify_partial(&proof, &mut transcript);
    }

    #[test]
    fn test_prove_alpha_beta_folding() {
        let rb = vec![E::from_base(F::new(2))];
        let rc = vec![E::from_base(F::new(4))];
        let alpha_n_beta = vec![E::from_base(F::new(3)), E::from_base(F::new(5))];

        let add_i = vec![(0, 0, 1)];

        let mul_i = vec![(1, 2, 3)];

        let w_i_plus_one_poly = MultilinearPoly::new_from_vec(
            2,
            vec![6, 6, 6, 16]
                .into_iter()
                .map(|val| Fields::Base(F::new(val)))
                .collect(),
        );

        // Traditional poly
        let mut add_i_eval = vec![0; 32];
        add_i_eval[1] = 1;

        let add_i_poly = MultilinearPoly::new_from_vec(
            5,
            add_i_eval
                .into_iter()
                .map(|val| Fields::<F, E>::Base(F::new(val)))
                .collect(),
        );

        let add_rb_alpha = add_i_poly
            .partial_evaluate(
                &rb.iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            )
            .evaluations
            .iter()
            .map(|val| val.to_extension_field() * alpha_n_beta[0])
            .collect::<Vec<E>>();
        let add_rc_beta = add_i_poly
            .partial_evaluate(
                &rc.iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            )
            .evaluations
            .iter()
            .map(|val| val.to_extension_field() * alpha_n_beta[1])
            .collect::<Vec<E>>();
        let comb_add = add_rb_alpha
            .iter()
            .zip(add_rc_beta)
            .map(|(lhs, rhs)| *lhs + rhs)
            .collect::<Vec<E>>();

        let mut mul_i_eval = vec![0; 32];
        mul_i_eval[27] = 1;

        let mul_i_poly = MultilinearPoly::new_from_vec(
            5,
            mul_i_eval
                .into_iter()
                .map(|val| Fields::Base(F::new(val)))
                .collect(),
        );

        let mul_rb_alpha = mul_i_poly
            .partial_evaluate(
                &rb.iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            )
            .evaluations
            .iter()
            .map(|val| val.to_extension_field() * alpha_n_beta[0])
            .collect::<Vec<E>>();
        let mul_rc_beta = mul_i_poly
            .partial_evaluate(
                &rc.iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            )
            .evaluations
            .iter()
            .map(|val| val.to_extension_field() * alpha_n_beta[1])
            .collect::<Vec<E>>();
        let comb_mul = mul_rb_alpha
            .iter()
            .zip(mul_rc_beta)
            .map(|(lhs, rhs)| *lhs + rhs)
            .collect::<Vec<E>>();

        let wb_bln = MultilinearPoly::new_from_vec(
            4,
            vec![6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 16, 16, 16, 16]
                .into_iter()
                .map(|val| Fields::<F, E>::Base(F::new(val)))
                .collect(),
        );

        let wc_bln = MultilinearPoly::new_from_vec(
            4,
            vec![6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16]
                .into_iter()
                .map(|val| Fields::<F, E>::Base(F::new(val)))
                .collect(),
        );

        let new_addi_bln = MultilinearPoly::new_from_vec(
            4,
            comb_add
                .into_iter()
                .map(|val| Fields::<F, E>::Extension(val))
                .collect(),
        );

        let new_muli_bln = MultilinearPoly::new_from_vec(
            4,
            comb_mul
                .into_iter()
                .map(|val| Fields::<F, E>::Extension(val))
                .collect(),
        );

        let mut transcript = Transcript::<F, E>::init();

        let (igz, mul_ahg, add_b_ahg, add_c_ahg) = prepare_phase_one_params_with_alpha_beta_rb_rc(
            &rb,
            &rc,
            &alpha_n_beta,
            &add_i,
            &mul_i,
            &w_i_plus_one_poly
                .evaluations
                .iter()
                .map(|val| val.to_base_field().unwrap())
                .collect::<Vec<F>>(),
        );

        let (proof, rb, rc, wb, wc) = prove_libra_sumcheck(
            &igz,
            &mul_ahg,
            &add_b_ahg,
            &add_c_ahg,
            &add_i,
            &mul_i,
            &w_i_plus_one_poly,
            &mut transcript,
        );

        let mut transcript = Transcript::<F, E>::init();

        let (claimed_sum, challenges) =
            SumCheck::<F, E, MLE>::verify_partial(&proof, &mut transcript);
    }
}
