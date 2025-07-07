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
    let output: Vec<Fields<F, E>> = proofs.circuit_output;

    // Build output polynomial
    let output_mle = MultilinearPoly::new_extend_to_power_of_two(output, Fields::Base(F::zero()));

    // Samples challenge for round one
    let g = transcript
        .sample_n_challenges(output_mle.num_vars())
        .into_iter()
        .map(Fields::Extension)
        .collect::<Vec<Fields<F, E>>>();

    // Gets claimed sum by evaluating output polynomial at random challenge
    let mut claimed_sum = output_mle.evaluate(&g);

    let mut challenges = vec![];

    let mut alpha_n_beta = vec![];

    let mut rb = vec![];

    let mut rc = vec![];

    for i in 0..proofs.sumcheck_proofs.len() - 1 {
        // Assert claimed sum equals prover claimed sum
        assert_eq!(claimed_sum, proofs.sumcheck_proofs[i].claimed_sum);

        // Verify sumcheck proof
        let (sumcheck_claimed_sum, rb_n_rc) =
            SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[i],
                &mut transcript,
            );

        challenges = rb_n_rc;

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
        let expected_claimed_sum = if i == 0 {
            let g_bc = [g.clone(), challenges.clone()].concat();

            eval_layer_mle_given_wb_n_wc(
                &add_i,
                &mul_i,
                &g_bc,
                &proofs.wbs[0],
                &proofs.wcs[0],
                circuit.layers.len() - 1,
                n_vars,
            )
        } else {
            eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
                EvalNewAddNMulInput {
                    add_i: &add_i,
                    mul_i: &mul_i,
                    alpha_n_beta: &alpha_n_beta,
                    rb: &rb,
                    rc: &rc,
                    bc: &challenges,
                    wb: &proofs.wbs[i],
                    wc: &proofs.wcs[i],
                },
                proofs.sumcheck_proofs.len() - i - 1,
                n_vars,
            )
        };

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

        let (wb, wc) = 
        // if i == proofs.sumcheck_proofs.len() {
        //     let input_poly: MultilinearPoly<F, E> = MultilinearPoly::new_from_vec(
        //         (input.len() as f64).log2() as usize,
        //         input.iter().map(|val| Fields::Base(*val)).collect(),
        //     );

        //     // Calculate wb and wc on the input polynomial
        //     let wb = input_poly.evaluate(&challenges[..challenges.len() / 2]);

        //     let wc = input_poly.evaluate(&challenges[(challenges.len() / 2)..]);

        //     (wb, wc)
        // } else {
        // };
        (proofs.wbs[i], proofs.wcs[i]);

        // Get claimed sum for the next round
        claimed_sum = (alpha_n_beta[0] * wb) + (alpha_n_beta[1] * wc);

        rb = challenges[..challenges.len() / 2].to_vec();

        rc = challenges[(challenges.len() / 2)..].to_vec();
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

    // Get the input polynomial
    let input_poly: MultilinearPoly<F, E> = MultilinearPoly::new_extend_to_power_of_two(
        input.iter().map(|val| Fields::Base(*val)).collect(),
        Fields::Base(F::zero()),
    );

    // // Calculate wb and wc on the input polynomial
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
    assert_eq!(sumcheck_claimed_sum, oracle_query.to_extension_field());

    Ok(true)
}
