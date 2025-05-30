use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension};
use sum_check::{SumCheck, interface::SumCheckInterface, primitives::SumCheckProof};
use transcript::Transcript;

use crate::utils::{
    ProveLibraInput, build_phase_one_libra_sumcheck_poly, build_phase_two_libra_sumcheck_poly,
    prepare_phase_two_params,
};

pub fn prove_libra_sumcheck<F: Field + PrimeField32, E: ExtensionField<F>>(
    input: ProveLibraInput<'_, F, E>,
    transcript: &mut Transcript<F, E>,
) -> (SumCheckProof<F, E>, Vec<E>, Vec<E>, E, E) {
    let phase_one_poly = build_phase_one_libra_sumcheck_poly(
        input.mul_ahg,
        input.add_b_ahg,
        input.add_c_ahg,
        input.w_i_plus_one_poly,
    );

    let (mut round_polys, u) = SumCheck::prove_partial(&phase_one_poly, transcript).unwrap();

    let wb: E = input
        .w_i_plus_one_poly
        .evaluate(
            &u.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        )
        .to_extension_field();

    // Prepare parameters for phase two
    let (mul_af1, add_af1) = prepare_phase_two_params(input.igz, &u, input.add_i, input.mul_i);

    let phase_two_poly =
        build_phase_two_libra_sumcheck_poly(&mul_af1, &add_af1, &wb, input.w_i_plus_one_poly);

    let (phase_two_round_polys, v) = SumCheck::prove_partial(&phase_two_poly, transcript).unwrap();

    round_polys.extend(phase_two_round_polys);

    let wc = input
        .w_i_plus_one_poly
        .evaluate(
            &v.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        )
        .to_extension_field();

    let sumcheck_proof = SumCheckProof::new(*input.claimed_sum, round_polys);

    (sumcheck_proof, u, v, wb, wc)
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use p3_field::{AbstractExtensionField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;
    use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, vpoly::VPoly};
    use sum_check::{SumCheck, interface::SumCheckInterface};
    use transcript::Transcript;

    use super::prove_libra_sumcheck;

    use crate::utils::{
        ProveLibraInput, prepare_phase_one_params, prepare_phase_one_params_with_alpha_beta_rb_rc,
    };

    type F = Mersenne31;

    type E = BinomialExtensionField<Mersenne31, 3>;

    type Mle = VPoly<F, E>;

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

        let claimed_sum = VPoly::new(
            vec![add_i_bln.clone(), mul_i_bln.clone(), wb_bln, wc_bln],
            2,
            4,
            Rc::new(|data: &[Fields<F, E>]| {
                (data[0] * (data[2] + data[3])) + (data[1] * data[2] * data[3])
            }),
        )
        .sum_over_hypercube();

        let (proof, rb, rc, wb, wc) = prove_libra_sumcheck(
            ProveLibraInput {
                claimed_sum: &claimed_sum,
                igz: &igz,
                mul_ahg: &mul_ahg,
                add_b_ahg: &add_b_ahg,
                add_c_ahg: &add_c_ahg,
                add_i: &add_i,
                mul_i: &mul_i,
                w_i_plus_one_poly: &w_i_plus_one_poly,
            },
            &mut transcript,
        );

        let mut transcript = Transcript::<F, E>::init();

        let (claimed_sum, challenges) =
            SumCheck::<F, E, Mle>::verify_partial(&proof, &mut transcript);

        let verifier_wb = &challenges[0..challenges.len() / 2];
        let verifier_wc = &challenges[&challenges.len() / 2..];

        assert_eq!(
            rb,
            verifier_wb
                .iter()
                .map(|val| val.to_extension_field())
                .collect::<Vec<E>>()
        );
        assert_eq!(
            rc,
            verifier_wc
                .iter()
                .map(|val| val.to_extension_field())
                .collect::<Vec<E>>()
        );

        let evaluated_wb = w_i_plus_one_poly.evaluate(verifier_wb);
        let evaluated_wc = w_i_plus_one_poly.evaluate(verifier_wc);

        assert_eq!(wb, evaluated_wb.to_extension_field());
        assert_eq!(wc, evaluated_wc.to_extension_field());

        let evaluated_add_i = add_i_bln.evaluate(&challenges);
        let evaluated_muli = mul_i_bln.evaluate(&challenges);

        let expected_claimed_sum = (evaluated_add_i * (evaluated_wb + evaluated_wc))
            + (evaluated_muli * (evaluated_wb * evaluated_wc));

        assert_eq!(claimed_sum, expected_claimed_sum.to_extension_field());
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

        let new_addi_bln = MultilinearPoly::new_from_vec(
            4,
            comb_add
                .into_iter()
                .map(Fields::<F, E>::Extension)
                .collect(),
        );

        let new_muli_bln = MultilinearPoly::new_from_vec(
            4,
            comb_mul
                .into_iter()
                .map(Fields::<F, E>::Extension)
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

        let claimed_sum = VPoly::new(
            vec![new_addi_bln.clone(), new_muli_bln.clone(), wb_bln, wc_bln],
            2,
            4,
            Rc::new(|data: &[Fields<F, E>]| {
                (data[0] * (data[2] + data[3])) + (data[1] * data[2] * data[3])
            }),
        )
        .sum_over_hypercube();

        let (proof, rb, rc, wb, wc) = prove_libra_sumcheck(
            ProveLibraInput {
                claimed_sum: &claimed_sum,
                igz: &igz,
                mul_ahg: &mul_ahg,
                add_b_ahg: &add_b_ahg,
                add_c_ahg: &add_c_ahg,
                add_i: &add_i,
                mul_i: &mul_i,
                w_i_plus_one_poly: &w_i_plus_one_poly,
            },
            &mut transcript,
        );

        let mut transcript = Transcript::<F, E>::init();

        let (claimed_sum, challenges) =
            SumCheck::<F, E, Mle>::verify_partial(&proof, &mut transcript);

        let verifier_wb = &challenges[0..challenges.len() / 2];
        let verifier_wc = &challenges[&challenges.len() / 2..];

        assert_eq!(
            rb,
            verifier_wb
                .iter()
                .map(|val| val.to_extension_field())
                .collect::<Vec<E>>()
        );
        assert_eq!(
            rc,
            verifier_wc
                .iter()
                .map(|val| val.to_extension_field())
                .collect::<Vec<E>>()
        );

        let evaluated_wb = w_i_plus_one_poly.evaluate(verifier_wb);
        let evaluated_wc = w_i_plus_one_poly.evaluate(verifier_wc);

        assert_eq!(wb, evaluated_wb.to_extension_field());
        assert_eq!(wc, evaluated_wc.to_extension_field());

        let evaluated_add_i = new_addi_bln.evaluate(&challenges);
        let evaluated_muli = new_muli_bln.evaluate(&challenges);

        let expected_claimed_sum = (evaluated_add_i * (evaluated_wb + evaluated_wc))
            + (evaluated_muli * (evaluated_wb * evaluated_wc));

        assert_eq!(claimed_sum, expected_claimed_sum.to_extension_field());
    }
}
