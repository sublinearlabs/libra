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
) -> (SumCheckProof<F, E>, Fields<F, E>, Fields<F, E>) {
    let mut phase_one_poly = build_phase_one_libra_sumcheck_poly(
        input.mul_ahg,
        input.add_b_ahg,
        input.add_c_ahg,
        input.w_i_plus_one_poly,
    );

    let mut phase_1_proof =
        SumCheck::prove_partial(*input.claimed_sum, &mut phase_one_poly, transcript).unwrap();

    let wb: Fields<F, E> = input.w_i_plus_one_poly.evaluate(&phase_1_proof.challenges);

    // Prepare parameters for phase two
    let (mul_af1, add_af1) = prepare_phase_two_params(
        input.igz,
        &phase_1_proof.challenges,
        input.add_i,
        input.mul_i,
    );

    let mut phase_two_poly =
        build_phase_two_libra_sumcheck_poly(&mul_af1, &add_af1, &wb, input.w_i_plus_one_poly);

    let phase_2_proof =
        SumCheck::prove_partial(*input.claimed_sum, &mut phase_two_poly, transcript).unwrap();

    let wc = input.w_i_plus_one_poly.evaluate(&phase_2_proof.challenges);

    phase_1_proof
        .round_polynomials
        .extend(phase_2_proof.round_polynomials);
    phase_1_proof.challenges.extend(phase_2_proof.challenges);

    (phase_1_proof, wb, wc)
}
