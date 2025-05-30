use std::{error::Error, marker::PhantomData};

use circuits::{
    interface::LibraGKRLayeredCircuitTr,
    layered_circuit::{LayeredCircuit, primitives::Evaluation, utils::compute_num_vars},
};
use libra_sumcheck::prove_libra_sumcheck;
use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly};
use sum_check::{SumCheck, interface::SumCheckInterface, primitives::SumCheckProof};
use transcript::Transcript;
use utils::{
    EvalNewAddNMulInput, ProveLibraInput, eval_layer_mle_given_wb_n_wc,
    eval_new_addi_n_muli_at_rb_bc_n_rc_bc, fold_igz, generate_eq, prepare_phase_one_params,
};

pub mod libra_sumcheck;
pub mod utils;

pub struct Libra<F: Field, E: ExtensionField<F>> {
    _marker: PhantomData<(F, E)>,
}

pub struct LibraProof<F: Field, E: ExtensionField<F>> {
    pub circuit_output: Vec<F>,
    pub sumcheck_proofs: Vec<SumCheckProof<F, E>>,
    pub wbs: Vec<E>,
    pub wcs: Vec<E>,
}

impl<F: Field, E: ExtensionField<F>> LibraProof<F, E> {
    pub fn new(
        output: Vec<F>,
        sumcheck_proofs: Vec<SumCheckProof<F, E>>,
        wbs: Vec<E>,
        wcs: Vec<E>,
    ) -> LibraProof<F, E> {
        LibraProof {
            circuit_output: output,
            sumcheck_proofs,
            wbs,
            wcs,
        }
    }
}

impl<F: Field + PrimeField32, E: ExtensionField<F>> Libra<F, E> {
    pub fn prove(circuit: &LayeredCircuit, output: Evaluation<F>) -> LibraProof<F, E> {
        // Initialize prover transcript
        let mut transcript = Transcript::init();

        let mut sumcheck_proofs = vec![];

        let mut wbs = vec![];

        let mut wcs = vec![];

        // Get the output vector
        let mut output_evals: Vec<Fields<F, E>> = output.layers[circuit.layers.len()]
            .iter()
            .map(|val| Fields::<F, E>::Base(*val))
            .collect();

        if output_evals.len() == 1 {
            output_evals.push(Fields::Base(F::zero()));
        }

        // Build the output polynomial
        let output_mle = MultilinearPoly::new_from_vec(
            (output_evals.len() as f64).log2() as usize,
            output_evals,
        );

        // Adds the output to the transcript
        transcript.observe_base_element(&output.layers[circuit.layers.len()]);

        // Gets the addi and muli for the output layer
        let (add_i, mul_i) =
            LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, circuit.layers.len() - 1);

        // Gets w_i+1
        let mut w_i_plus_one_poly = MultilinearPoly::new_from_vec(
            (output.layers[circuit.layers.len() - 1].len() as f64).log2() as usize,
            output.layers[circuit.layers.len() - 1]
                .iter()
                .map(|val| Fields::Base(*val))
                .collect::<Vec<Fields<F, E>>>(),
        );

        // Sample random challenge for the first round
        let g = transcript.sample_n_challenges(output_mle.num_vars());

        let mut igz = generate_eq(&g);

        // Prepares parameters for phase one of Libra
        let (mut mul_ahg, mut add_b_ahg, mut add_c_ahg) = prepare_phase_one_params(
            &igz,
            &add_i,
            &mul_i,
            &w_i_plus_one_poly
                .evaluations
                .iter()
                .map(|val| val.to_base_field().unwrap())
                .collect::<Vec<F>>(),
        );

        let mut claimed_sum = output_mle.evaluate(
            &g.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        );

        // Proves the sumcheck relation using Libra algorithms
        let (mut sumcheck_proof, mut rb, mut rc, mut wb, mut wc) = prove_libra_sumcheck(
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

        // Add messages to the transcript
        transcript.observe_ext_element(&[wb]);
        transcript.observe_ext_element(&[wc]);
        transcript.observe_ext_element(&[sumcheck_proof.claimed_sum.to_extension_field()]);
        transcript.observe_ext_element(&sumcheck_proof.round_polynomials.iter().fold(
            vec![],
            |mut acc, val| {
                acc.extend(
                    val.iter()
                        .map(|val| val.to_extension_field())
                        .collect::<Vec<E>>(),
                );
                acc
            },
        ));

        // Adds messages to the proof
        sumcheck_proofs.push(sumcheck_proof);
        wbs.push(wb);
        wcs.push(wc);

        // Samples alpha and beta for folding
        let mut alpha_n_beta = transcript.sample_n_challenges(2);

        for i in (1..circuit.layers.len()).rev() {
            // Get addi and muli
            let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

            claimed_sum = (Fields::Extension(alpha_n_beta[0])
                * w_i_plus_one_poly.evaluate(
                    &rb.iter()
                        .map(|val| Fields::Extension(*val))
                        .collect::<Vec<Fields<F, E>>>(),
                ))
                + (Fields::Extension(alpha_n_beta[1])
                    * w_i_plus_one_poly.evaluate(
                        &rc.iter()
                            .map(|val| Fields::Extension(*val))
                            .collect::<Vec<Fields<F, E>>>(),
                    ));

            // Gets w_i+1
            w_i_plus_one_poly = MultilinearPoly::new_from_vec(
                (output.layers[i - 1].len() as f64).log2() as usize,
                output.layers[i - 1]
                    .iter()
                    .map(|val| Fields::<F, E>::Base(*val))
                    .collect(),
            );

            // Fold Igz for rb and rc using alpha and beta
            igz = fold_igz(&rb, &rc, &alpha_n_beta);

            // Gets new addi and muli based on rb, rc, alpha and beta
            (mul_ahg, add_b_ahg, add_c_ahg) = prepare_phase_one_params(
                &igz,
                &add_i,
                &mul_i,
                &w_i_plus_one_poly
                    .evaluations
                    .iter()
                    .map(|val| val.to_base_field().unwrap())
                    .collect::<Vec<F>>(),
            );

            // Proves sumcheck relation using Libra algorithms
            (sumcheck_proof, rb, rc, wb, wc) = prove_libra_sumcheck(
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

            // Adds the messages to the transcript
            transcript.observe_ext_element(&[wb]);
            transcript.observe_ext_element(&[wc]);
            transcript.observe_ext_element(&[sumcheck_proof.claimed_sum.to_extension_field()]);
            transcript.observe_ext_element(&sumcheck_proof.round_polynomials.iter().fold(
                vec![],
                |mut acc, val| {
                    acc.extend(
                        val.iter()
                            .map(|val| val.to_extension_field())
                            .collect::<Vec<E>>(),
                    );
                    acc
                },
            ));

            // Adds the messages to the proof
            sumcheck_proofs.push(sumcheck_proof);
            wbs.push(wb);
            wcs.push(wc);

            // Sample alpha and beta
            alpha_n_beta = transcript.sample_n_challenges(2);
        }

        LibraProof::new(
            output.layers[output.layers.len() - 1].clone(),
            sumcheck_proofs,
            wbs,
            wcs,
        )
    }

    // Verify the GKR Proof
    pub fn verify(
        circuit: &LayeredCircuit,
        proofs: LibraProof<F, E>,
        input: Vec<F>,
    ) -> Result<bool, Box<dyn Error>> {
        // Instantiate verifier transcript
        let mut transcript = Transcript::<F, E>::init();

        // Adds output to the transcript
        transcript.observe_base_element(&proofs.circuit_output);

        // Gets output vector
        let mut output: Vec<Fields<F, E>> = proofs
            .circuit_output
            .iter()
            .map(|val| Fields::<F, E>::Base(*val))
            .collect();

        if output.len() == 1 {
            output.push(Fields::Base(F::zero()));
        }

        // Build output polynomial
        let output_mle =
            MultilinearPoly::new_from_vec((output.len() as f64).log2() as usize, output);

        // Samples challenge for round one
        let g = transcript
            .sample_n_challenges(output_mle.num_vars())
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        // Gets claimed sum by evaluating output polynomial at random challenge
        let mut claimed_sum = output_mle.evaluate(&g);

        // Asserts claimed sum is equal to the proof claimed sum
        assert_eq!(claimed_sum, proofs.sumcheck_proofs[0].claimed_sum);

        // Verify prover sumcheck
        let (sumcheck_claimed_sum, rb_n_rc) =
            SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
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
        transcript.observe_ext_element(&[proofs.wbs[0]]);
        transcript.observe_ext_element(&[proofs.wcs[0]]);
        transcript
            .observe_ext_element(&[proofs.sumcheck_proofs[0].claimed_sum.to_extension_field()]);
        transcript.observe_ext_element(&proofs.sumcheck_proofs[0].round_polynomials.iter().fold(
            vec![],
            |mut acc, val| {
                acc.extend(
                    val.iter()
                        .map(|val| val.to_extension_field())
                        .collect::<Vec<E>>(),
                );
                acc
            },
        ));

        // Calculate the expected claimed sum given wb and wc and challenges
        let expected_sum = eval_layer_mle_given_wb_n_wc(
            &add_i,
            &mul_i,
            &g_bc,
            &Fields::Extension(proofs.wbs[0]),
            &Fields::Extension(proofs.wcs[0]),
            circuit.layers.len() - 1,
            n_vars,
        );

        // Performs oracle check on the first round
        assert_eq!(sumcheck_claimed_sum, expected_sum.to_extension_field());

        // Get alpha and beta
        let mut alpha_n_beta = transcript
            .sample_n_challenges(2)
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        // Get claimed sum for the next round by calculating: (alpha * wb) + (beta * wc)
        claimed_sum = (alpha_n_beta[0] * Fields::Extension(proofs.wbs[0]))
            + (alpha_n_beta[1] * Fields::Extension(proofs.wcs[0]));

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
                    wb: &Fields::Extension(proofs.wbs[i]),
                    wc: &Fields::Extension(proofs.wcs[i]),
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
            transcript.observe_ext_element(&[proofs.wbs[i]]);
            transcript.observe_ext_element(&[proofs.wcs[i]]);
            transcript
                .observe_ext_element(&[proofs.sumcheck_proofs[i].claimed_sum.to_extension_field()]);
            transcript.observe_ext_element(
                &proofs.sumcheck_proofs[i]
                    .round_polynomials
                    .iter()
                    .fold(vec![], |mut acc, val| {
                        acc.extend(
                            val.iter()
                                .map(|val| val.to_extension_field())
                                .collect::<Vec<E>>(),
                        );
                        acc
                    }),
            );

            // Sample alpha and beta
            alpha_n_beta = transcript
                .sample_n_challenges(2)
                .iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>();

            // Get claimed sum for the next round
            claimed_sum = (alpha_n_beta[0] * Fields::Extension(proofs.wbs[i]))
                + (alpha_n_beta[1] * Fields::Extension(proofs.wcs[i]));

            rb = rb_n_rc[..rb_n_rc.len() / 2].to_vec();

            rc = rb_n_rc[(rb_n_rc.len() / 2)..].to_vec();
        }

        // Verify sumcheck proof for the final round
        let (sumcheck_claimed_sum, rb_n_rc) =
            SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
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
                wb: &Fields::Extension(proofs.wbs[proofs.sumcheck_proofs.len() - 1]),
                wc: &Fields::Extension(proofs.wcs[proofs.sumcheck_proofs.len() - 1]),
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
}

#[cfg(test)]
mod tests {
    use circuits::{
        interface::CircuitTr,
        layered_circuit::{
            LayeredCircuit,
            primitives::{Gate, GateOp, Layer},
        },
    };
    use p3_field::{AbstractField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;

    use crate::{Libra, LibraProof};

    #[test]
    fn test_libra_protocol() {
        let circuit = LayeredCircuit::new(vec![
            Layer::new(vec![
                Gate::new(GateOp::Mul, [0, 1]),
                Gate::new(GateOp::Add, [2, 3]),
                Gate::new(GateOp::Add, [4, 5]),
                Gate::new(GateOp::Mul, [6, 7]),
            ]),
            Layer::new(vec![
                Gate::new(GateOp::Mul, [0, 1]),
                Gate::new(GateOp::Add, [2, 3]),
            ]),
            Layer::new(vec![Gate::new(GateOp::Mul, [0, 1])]),
        ]);

        let input = [1, 2, 3, 2, 1, 2, 4, 1]
            .into_iter()
            .map(Mersenne31::from_canonical_usize)
            .collect::<Vec<Mersenne31>>();

        let output = circuit.excecute(&input);

        let proof: LibraProof<Mersenne31, BinomialExtensionField<Mersenne31, 3>> =
            Libra::prove(&circuit, output);

        let verify = Libra::verify(&circuit, proof, input);

        assert!(verify.unwrap());
    }
}
