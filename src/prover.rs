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

    // Gets the addi and muli for the output layer
    let (add_i, mul_i) =
        LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, circuit.layers.len() - 1);

    let w_i_plus_one_eval = output.layers[circuit.layers.len() - 1]
        .iter()
        .map(|val| Fields::Base(*val))
        .collect::<Vec<Fields<F, E>>>();

    // Gets w_i+1
    let mut w_i_plus_one_poly =
        MultilinearPoly::new_extend_to_power_of_two(w_i_plus_one_eval, Fields::Base(F::zero()));

    // Sample random challenge for the first round
    let g = transcript
        .sample_n_challenges(output_mle.num_vars())
        .into_iter()
        .map(Fields::Extension)
        .collect::<Vec<Fields<F, E>>>();

    let mut igz = generate_eq(&g);

    // Prepares parameters for phase one of Libra
    let (mut mul_ahg, mut add_b_ahg, mut add_c_ahg) =
        prepare_phase_one_params(&igz, &add_i, &mul_i, &w_i_plus_one_poly.evaluations);

    let mut claimed_sum = output_mle.evaluate(&g);

    // Proves the sumcheck relation using Libra algorithms
    let (mut sumcheck_proof, mut wb, mut wc) = prove_libra_sumcheck(
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

    let (mut rb, mut rc) = (
        sumcheck_proof.challenges[..sumcheck_proof.challenges.len() / 2].to_vec(),
        sumcheck_proof.challenges[sumcheck_proof.challenges.len() / 2..].to_vec(),
    );

    // Add messages to the transcript
    transcript.observe(&[wb]);
    transcript.observe(&[wc]);
    transcript.observe(&[sumcheck_proof.claimed_sum]);
    transcript.observe(
        &sumcheck_proof
            .round_polynomials
            .iter()
            .fold(vec![], |mut acc, val| {
                acc.extend(val);
                acc
            }),
    );

    // Adds messages to the proof
    sumcheck_proofs.push(sumcheck_proof);
    wbs.push(wb);
    wcs.push(wc);

    // Samples alpha and beta for folding
    let mut alpha_n_beta = transcript
        .sample_n_challenges(2)
        .into_iter()
        .map(Fields::Extension)
        .collect::<Vec<Fields<F, E>>>();

    for i in (1..circuit.layers.len()).rev() {
        // Get addi and muli
        let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

        claimed_sum = alpha_n_beta[0] * w_i_plus_one_poly.evaluate(&rb)
            + alpha_n_beta[1] * w_i_plus_one_poly.evaluate(&rc);

        let w_i_plus_one_eval = output.layers[i - 1]
            .iter()
            .map(|val| Fields::<F, E>::Base(*val))
            .collect();

        // Gets w_i+1
        w_i_plus_one_poly =
            MultilinearPoly::new_extend_to_power_of_two(w_i_plus_one_eval, Fields::Base(F::zero()));

        // Fold Igz for rb and rc using alpha and beta
        igz = igz_n_to_1_fold(&[&rb, &rc], &alpha_n_beta);

        // Gets new addi and muli based on rb, rc, alpha and beta
        (mul_ahg, add_b_ahg, add_c_ahg) =
            prepare_phase_one_params(&igz, &add_i, &mul_i, &w_i_plus_one_poly.evaluations);

        // Proves sumcheck relation using Libra algorithms
        (sumcheck_proof, wb, wc) = prove_libra_sumcheck(
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

        (rb, rc) = (
            sumcheck_proof.challenges[..sumcheck_proof.challenges.len() / 2].to_vec(),
            sumcheck_proof.challenges[sumcheck_proof.challenges.len() / 2..].to_vec(),
        );

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

        // Sample alpha and beta
        alpha_n_beta = transcript
            .sample_n_challenges(2)
            .into_iter()
            .map(Fields::Extension)
            .collect::<Vec<Fields<F, E>>>();
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
