use std::error::Error;

use circuits::{
    interface::LibraGKRLayeredCircuitTr,
    layered_circuit::{LayeredCircuit, utils::compute_num_vars},
};
use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly};
use sum_check::{SumCheck, interface::SumCheckInterface};
use transcript::Transcript;

use crate::{
    proof::LibraProof,
    utils::{
        EvalNewAddNMulInput, eval_layer_mle_given_wb_n_wc, eval_new_addi_n_muli_at_rb_bc_n_rc_bc,
    },
};

// Verify the GKR Proof
pub fn verify<F: Field + PrimeField32, E: ExtensionField<F>>(
    circuit: &LayeredCircuit,
    proofs: LibraProof<F, E>,
    input: Vec<F>,
) -> Result<bool, Box<dyn Error>> {
    // Instantiate verifier transcript
    let mut transcript = Transcript::<F, E>::init();

    // Adds output to the transcript
    transcript.observe(&proofs.circuit_output);

    // Gets output vector
    let mut output: Vec<Fields<F, E>> = proofs.circuit_output;

    if output.len() == 1 {
        output.push(Fields::Base(F::zero()));
    }

    // Build output polynomial
    let output_mle = MultilinearPoly::new_from_vec((output.len() as f64).log2() as usize, output);

    // Samples challenge for round one
    let g = transcript
        .sample_n_challenges(output_mle.num_vars())
        .into_iter()
        .map(Fields::Extension)
        .collect::<Vec<Fields<F, E>>>();

    // Gets claimed sum by evaluating output polynomial at random challenge
    let mut claimed_sum = output_mle.evaluate(&g);

    // Asserts claimed sum is equal to the proof claimed sum
    assert_eq!(claimed_sum, proofs.sumcheck_proofs[0].claimed_sum);

    // Verify prover sumcheck
    let (sumcheck_claimed_sum, rb_n_rc) = SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
        &proofs.sumcheck_proofs[0],
        &mut transcript,
    );

    // Get the correct number of vars
    let n_vars = compute_num_vars(circuit.layers.len() - 1, circuit.layers.len() - 1);

    // Gets addi and muli
    let (add_i, mul_i) =
        LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, circuit.layers.len() - 1);

    // Gets challenges for use in oracle check
    let g_bc = [g.clone(), rb_n_rc.clone()].concat();

    let mut rb = rb_n_rc[..rb_n_rc.len() / 2].to_vec();

    let mut rc = rb_n_rc[(rb_n_rc.len() / 2)..].to_vec();

    // Add messages to the transcript
    transcript.observe(&[proofs.wbs[0]]);
    transcript.observe(&[proofs.wcs[0]]);
    transcript.observe(&[proofs.sumcheck_proofs[0].claimed_sum]);
    transcript.observe(&proofs.sumcheck_proofs[0].round_polynomials.iter().fold(
        vec![],
        |mut acc, val| {
            acc.extend(val);
            acc
        },
    ));

    // Calculate the expected claimed sum given wb and wc and challenges
    let expected_sum = eval_layer_mle_given_wb_n_wc(
        &add_i,
        &mul_i,
        &g_bc,
        &proofs.wbs[0],
        &proofs.wcs[0],
        circuit.layers.len() - 1,
        n_vars,
    );

    // Performs oracle check on the first round
    assert_eq!(sumcheck_claimed_sum, expected_sum.to_extension_field());

    // Get alpha and beta
    let mut alpha_n_beta = transcript
        .sample_n_challenges(2)
        .into_iter()
        .map(Fields::Extension)
        .collect::<Vec<Fields<F, E>>>();

    // Get claimed sum for the next round by calculating: (alpha * wb) + (beta * wc)
    claimed_sum = (alpha_n_beta[0] * proofs.wbs[0]) + (alpha_n_beta[1] * proofs.wcs[0]);

    for i in 1..(proofs.sumcheck_proofs.len() - 1) {
        // Assert claimed sum equals prover claimed sum
        assert_eq!(claimed_sum, proofs.sumcheck_proofs[i].claimed_sum);

        // Verify sumcheck proof
        let (sumcheck_claimed_sum, rb_n_rc) =
            SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[i],
                &mut transcript,
            );

        // Get the correct number of vars
        let n_vars = compute_num_vars(
            proofs.sumcheck_proofs.len() - i - 1,
            circuit.layers.len() - 1,
        );

        // Gets addi and muli
        let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(
            circuit,
            proofs.sumcheck_proofs.len() - i - 1,
        );

        // Calculates expected claimed sum given wb and wc values
        let expected_claimed_sum = eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
            EvalNewAddNMulInput {
                add_i: &add_i,
                mul_i: &mul_i,
                alpha_n_beta: &alpha_n_beta,
                rb: &rb,
                rc: &rc,
                bc: &rb_n_rc,
                wb: &proofs.wbs[i],
                wc: &proofs.wcs[i],
            },
            proofs.sumcheck_proofs.len() - i - 1,
            n_vars,
        );

        // Do oracle check
        assert_eq!(
            sumcheck_claimed_sum,
            expected_claimed_sum.to_extension_field()
        );

        // Add messages to the transcript
        transcript.observe(&[proofs.wbs[i]]);
        transcript.observe(&[proofs.wcs[i]]);
        transcript.observe(&[proofs.sumcheck_proofs[i].claimed_sum]);
        transcript.observe(&proofs.sumcheck_proofs[i].round_polynomials.iter().fold(
            vec![],
            |mut acc, val| {
                acc.extend(val);
                acc
            },
        ));

        // Sample alpha and beta
        alpha_n_beta = transcript
            .sample_n_challenges(2)
            .into_iter()
            .map(Fields::Extension)
            .collect::<Vec<Fields<F, E>>>();

        // Get claimed sum for the next round
        claimed_sum = (alpha_n_beta[0] * proofs.wbs[i]) + (alpha_n_beta[1] * proofs.wcs[i]);

        rb = rb_n_rc[..rb_n_rc.len() / 2].to_vec();

        rc = rb_n_rc[(rb_n_rc.len() / 2)..].to_vec();
    }

    // Verify sumcheck proof for the final round
    let (sumcheck_claimed_sum, rb_n_rc) = SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
        &proofs.sumcheck_proofs[proofs.sumcheck_proofs.len() - 1],
        &mut transcript,
    );

    // Get addi and muli
    let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, 0);

    // Get the number of vars
    let n_vars = compute_num_vars(0, circuit.layers.len() - 1);

    // Calculate expected claimed sum given wb and wc
    let expected_claimed_sum = eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
        EvalNewAddNMulInput {
            add_i: &add_i,
            mul_i: &mul_i,
            alpha_n_beta: &alpha_n_beta,
            rb: &rb,
            rc: &rc,
            bc: &rb_n_rc,
            wb: &proofs.wbs[proofs.sumcheck_proofs.len() - 1],
            wc: &proofs.wcs[proofs.sumcheck_proofs.len() - 1],
        },
        proofs.sumcheck_proofs.len() - 1,
        n_vars,
    );

    // Do oracle check
    assert_eq!(
        sumcheck_claimed_sum,
        expected_claimed_sum.to_extension_field()
    );

    // Get the input polynomial
    let input_poly: MultilinearPoly<F, E> = MultilinearPoly::new_from_vec(
        (input.len() as f64).log2() as usize,
        input.iter().map(|val| Fields::Base(*val)).collect(),
    );

    // Calculate wb and wc on the input polynomial
    let wb = input_poly.evaluate(&rb_n_rc[..rb_n_rc.len() / 2]);

    let wc = input_poly.evaluate(&rb_n_rc[(rb_n_rc.len() / 2)..]);

    // Get the expected claimed sum
    let oracle_query = eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
        EvalNewAddNMulInput {
            add_i: &add_i,
            mul_i: &mul_i,
            alpha_n_beta: &alpha_n_beta,
            rb: &rb,
            rc: &rc,
            bc: &rb_n_rc,
            wb: &wb,
            wc: &wc,
        },
        proofs.sumcheck_proofs.len() - 1,
        n_vars,
    );

    // Do the oracle check
    assert_eq!(expected_claimed_sum, oracle_query);

    Ok(true)
}
