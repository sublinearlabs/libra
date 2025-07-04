use circuits::{
    interface::LibraGKRLayeredCircuitTr,
    layered_circuit::{LayeredCircuit, primitives::Evaluation},
};
use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, utils::generate_eq};
use transcript::Transcript;

use crate::{
    libra_sumcheck::prove_libra_sumcheck,
    proof::LibraProof,
    utils::{ProveLibraInput, igz_n_to_1_fold, prepare_phase_one_params},
};

pub fn prove<F: Field + PrimeField32, E: ExtensionField<F>>(
    circuit: &LayeredCircuit,
    output: Evaluation<F>,
) -> LibraProof<F, E> {
    // Initialize prover transcript
    let mut transcript = Transcript::<F, E>::init();

    let mut sumcheck_proofs = vec![];

    let mut wbs = vec![];

    let mut wcs = vec![];

    // Get the output vector
    let output_evals: Vec<Fields<F, E>> = output.layers[circuit.layers.len()]
        .iter()
        .map(|val| Fields::<F, E>::Base(*val))
        .collect();

    // Build the output polynomial
    let output_mle =
        MultilinearPoly::new_extend_to_power_of_two(output_evals, Fields::Base(F::zero()));

    // Adds the output to the transcript
    transcript.observe_base_element(&output.layers[circuit.layers.len()]);

    // Sample random challenge for the first round
    let g = transcript
        .sample_n_challenges(output_mle.num_vars())
        .into_iter()
        .map(Fields::Extension)
        .collect::<Vec<Fields<F, E>>>();

    let mut challenges = vec![];
    let mut wb = Fields::Extension(E::zero());
    let mut wc = Fields::Extension(E::zero());
    let mut alpha_n_beta = vec![];

    for i in (1..=circuit.layers.len()).rev() {
        let claimed_sum = if i == circuit.layers.len() {
            output_mle.evaluate(&g)
        } else {
            // Sample alpha and beta
            alpha_n_beta = transcript
                .sample_n_challenges(2)
                .into_iter()
                .map(Fields::Extension)
                .collect::<Vec<Fields<F, E>>>();
            (alpha_n_beta[0] * wb) + (alpha_n_beta[1] * wc)
        };

        // Get addi and muli
        let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

        let w_i_plus_one_eval = output.layers[i - 1]
            .iter()
            .map(|val| Fields::<F, E>::Base(*val))
            .collect();

        // Gets w_i+1
        let w_i_plus_one_poly =
            MultilinearPoly::new_extend_to_power_of_two(w_i_plus_one_eval, Fields::Base(F::zero()));

        // Fold Igz for rb and rc using alpha and beta
        let igz = if i == circuit.layers.len() {
            generate_eq(&g)
        } else {
            let (rb, rc) = (
                challenges[..challenges.len() / 2].to_vec(),
                challenges[challenges.len() / 2..].to_vec(),
            );
            igz_n_to_1_fold(&[&rb, &rc], &alpha_n_beta)
        };

        // Gets new addi and muli based on rb, rc, alpha and beta
        let (mul_ahg, add_b_ahg, add_c_ahg) =
            prepare_phase_one_params(&igz, &add_i, &mul_i, &w_i_plus_one_poly.evaluations);

        // Proves sumcheck relation using Libra algorithms
        let (sumcheck_proof, wb_eval, wc_eval) = prove_libra_sumcheck(
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

        wb = wb_eval;
        wc = wc_eval;
        challenges = sumcheck_proof.challenges.to_vec();

        // Adds the messages to the transcript
        transcript.observe(&[wb]);
        transcript.observe(&[wc]);
        transcript.observe(&[sumcheck_proof.claimed_sum]);
        transcript.observe(&sumcheck_proof.round_polynomials.iter().fold(
            vec![],
            |mut acc, val| {
                acc.extend(val);
                acc
            },
        ));

        // Adds the messages to the proof
        sumcheck_proofs.push(sumcheck_proof);
        wbs.push(wb);
        wcs.push(wc);
    }

    LibraProof::new(
        output.layers[output.layers.len() - 1]
            .iter()
            .map(|val| Fields::Base(*val))
            .collect::<Vec<Fields<F, E>>>(),
        sumcheck_proofs,
        wbs,
        wcs,
    )
}
