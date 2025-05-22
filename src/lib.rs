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
    eval_layer_mle_given_wb_n_wc, eval_new_addi_n_muli_at_rb_bc_n_rc_bc, prepare_phase_one_params,
    prepare_phase_one_params_with_alpha_beta_rb_rc,
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
        let mut transcript = Transcript::init();

        let mut sumcheck_proofs = vec![];

        let mut wbs = vec![];

        let mut wcs = vec![];

        let mut rb = vec![];

        let mut rc = vec![];

        let mut alpha_n_beta = vec![];

        let mut wb = E::one();

        let mut wc = E::one();

        let mut sumcheck_proof = SumCheckProof::new(Fields::Base(F::one()), vec![]);

        for i in (1..=circuit.layers.len()).rev() {
            if i == circuit.layers.len() {
                let output_evals: Vec<Fields<F, E>> = if output.layers[i].len() <= 1 {
                    [output.layers[i].clone(), vec![F::zero()]]
                        .concat()
                        .iter()
                        .map(|val| Fields::<F, E>::Base(*val))
                        .collect()
                } else {
                    output.layers[i]
                        .iter()
                        .map(|val| Fields::<F, E>::Base(*val))
                        .collect()
                };

                let output_mle = MultilinearPoly::new_from_vec(
                    (output_evals.len() as f64).log2() as usize,
                    output_evals,
                );

                transcript.observe_base_element(&output.layers[i]);

                let (add_i, mul_i) =
                    LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

                let w_i_plus_one_poly = MultilinearPoly::new_from_vec(
                    (output.layers[i - 1].len() as f64).log2() as usize,
                    output.layers[i - 1]
                        .iter()
                        .map(|val| Fields::Base(*val))
                        .collect::<Vec<Fields<F, E>>>(),
                );

                let g = transcript.sample_n_challenges(output_mle.num_vars());

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
                (sumcheck_proof, rb, rc, wb, wc) = prove_libra_sumcheck(
                    &igz,
                    &mul_ahg,
                    &add_b_ahg,
                    &add_c_ahg,
                    &add_i,
                    &mul_i,
                    &w_i_plus_one_poly,
                    &mut transcript,
                );

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

                sumcheck_proofs.push(sumcheck_proof);
                wbs.push(wb);
                wcs.push(wc);
            } else {
                alpha_n_beta = transcript.sample_n_challenges(2);

                // Get addi and muli
                let (add_i, mul_i) =
                    LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

                let w_i_plus_one_poly = MultilinearPoly::new_from_vec(
                    (output.layers[i - 1].len() as f64).log2() as usize,
                    output.layers[i - 1]
                        .iter()
                        .map(|val| Fields::<F, E>::Base(*val))
                        .collect(),
                );
                // Gets new addi and muli based on rb, rc, alpha and beta
                let (igz, mul_ahg, add_b_ahg, add_c_ahg) =
                    prepare_phase_one_params_with_alpha_beta_rb_rc(
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

                (sumcheck_proof, rb, rc, wb, wc) = prove_libra_sumcheck(
                    &igz,
                    &mul_ahg,
                    &add_b_ahg,
                    &add_c_ahg,
                    &add_i,
                    &mul_i,
                    &w_i_plus_one_poly,
                    &mut transcript,
                );

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

                sumcheck_proofs.push(sumcheck_proof);
                wbs.push(wb);
                wcs.push(wc);
            }
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
        let mut transcript = Transcript::<F, E>::init();

        transcript.observe_base_element(&proofs.circuit_output);

        let output: Vec<Fields<F, E>> = if proofs.circuit_output.len() <= 1 {
            [proofs.circuit_output, vec![F::zero()]]
                .concat()
                .iter()
                .map(|val| Fields::<F, E>::Base(*val))
                .collect()
        } else {
            proofs
                .circuit_output
                .iter()
                .map(|val| Fields::<F, E>::Base(*val))
                .collect()
        };

        let output_mle =
            MultilinearPoly::new_from_vec((output.len() as f64).log2() as usize, output);

        let g = transcript
            .sample_n_challenges(output_mle.num_vars())
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        let mut claimed_sum = output_mle.evaluate(&g);

        assert_eq!(claimed_sum, proofs.sumcheck_proofs[0].claimed_sum);

        let (sumcheck_claimed_sum, rb_n_rc) =
            SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[0],
                &mut transcript,
            );

        // Get the correct number of vars
        let n_vars = compute_num_vars(circuit.layers.len() - 1, circuit.layers.len() - 1);

        let (add_i, mul_i) =
            LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, circuit.layers.len() - 1);

        let g_bc = [g.clone(), rb_n_rc.clone()].concat();

        let mut rb = rb_n_rc[..rb_n_rc.len() / 2].to_vec();

        let mut rc = rb_n_rc[(rb_n_rc.len() / 2)..].to_vec();

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

        let expected_sum = eval_layer_mle_given_wb_n_wc(
            &add_i,
            &mul_i,
            &g_bc,
            &Fields::Extension(proofs.wbs[0]),
            &Fields::Extension(proofs.wcs[0]),
            circuit.layers.len() - 1,
            n_vars,
        );

        assert_eq!(sumcheck_claimed_sum, expected_sum.to_extension_field());

        // Get alpha and beta
        let mut alpha_n_beta = transcript
            .sample_n_challenges(2)
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        // Get claimed sum for the next round
        claimed_sum = (alpha_n_beta[0] * Fields::Extension(proofs.wbs[0]))
            + (alpha_n_beta[1] * Fields::Extension(proofs.wcs[0]));

        for i in 1..(proofs.sumcheck_proofs.len() - 1) {
            assert_eq!(claimed_sum, proofs.sumcheck_proofs[i].claimed_sum);

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

            let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(
                circuit,
                proofs.sumcheck_proofs.len() - i - 1,
            );

            // Do final oracle check
            let expected_claimed_sum = eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
                &add_i,
                &mul_i,
                &alpha_n_beta,
                &rb,
                &rc,
                &rb_n_rc,
                &Fields::Extension(proofs.wbs[i]),
                &Fields::Extension(proofs.wcs[i]),
                proofs.sumcheck_proofs.len() - i - 1,
                n_vars,
            );

            assert_eq!(
                sumcheck_claimed_sum,
                expected_claimed_sum.to_extension_field()
            );

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

        let (sumcheck_claimed_sum, rb_n_rc) =
            SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[proofs.sumcheck_proofs.len() - 1],
                &mut transcript,
            );

        let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, 0);

        // Get the number of vars
        let n_vars = compute_num_vars(0, circuit.layers.len() - 1);

        let expected_claimed_sum = eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
            &add_i,
            &mul_i,
            &alpha_n_beta,
            &rb,
            &rc,
            &rb_n_rc,
            &Fields::Extension(proofs.wbs[proofs.sumcheck_proofs.len() - 1]),
            &Fields::Extension(proofs.wcs[proofs.sumcheck_proofs.len() - 1]),
            proofs.sumcheck_proofs.len() - 1,
            n_vars,
        );

        assert_eq!(
            sumcheck_claimed_sum,
            expected_claimed_sum.to_extension_field()
        );

        // Final oracle check on the input
        let input_poly: MultilinearPoly<F, E> = MultilinearPoly::new_from_vec(
            (input.len() as f64).log2() as usize,
            input.iter().map(|val| Fields::Base(*val)).collect(),
        );

        let wb = input_poly.evaluate(&rb_n_rc[..rb_n_rc.len() / 2]);

        let wc = input_poly.evaluate(&rb_n_rc[(rb_n_rc.len() / 2)..]);

        // Get verifier oracle check
        let oracle_query = eval_new_addi_n_muli_at_rb_bc_n_rc_bc(
            &add_i,
            &mul_i,
            &alpha_n_beta,
            &rb,
            &rc,
            &rb_n_rc,
            &wb,
            &wc,
            proofs.sumcheck_proofs.len() - 1,
            n_vars,
        );

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
