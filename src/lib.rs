use std::{error::Error, marker::PhantomData};

use circuits::{
    interface::{GKRLayeredCircuitTr, LibraGKRLayeredCircuitTr},
    layered_circuit::{
        LayeredCircuit,
        primitives::Evaluation,
        utils::{compute_num_vars, get_gate_properties, mle_vec_to_poly},
    },
};
use libra_sumcheck::prove_libra_sumcheck;
use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly};
use sum_check::{SumCheck, interface::SumCheckInterface, primitives::SumCheckProof};
use transcript::Transcript;
use utils::{
    generate_eq, initialize_phase_one, prepare_phase_one_params,
    prepare_phase_one_params_with_alpha_beta_rb_rc,
};

pub mod libra_sumcheck;
pub mod utils;

struct Libra<F: Field, E: ExtensionField<F>> {
    _marker: PhantomData<(F, E)>,
}

struct LibraProof<F: Field, E: ExtensionField<F>> {
    circuit_output: Vec<F>,
    sumcheck_proofs: Vec<SumCheckProof<F, E>>,
    wbs: Vec<E>,
    wcs: Vec<E>,
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
    fn prove(circuit: &LayeredCircuit, output: Evaluation<F>) -> LibraProof<F, E> {
        let mut transcript = Transcript::init();

        let mut sumcheck_proofs = vec![];

        let mut wbs = vec![];

        let mut wcs = vec![];

        let mut output_evals: Vec<Fields<F, E>> =
            if output.layers[output.layers.len() - 1].len() <= 1 {
                [
                    output.layers[output.layers.len() - 1].clone(),
                    vec![F::zero()],
                ]
                .concat()
                .iter()
                .map(|val| Fields::<F, E>::Base(*val))
                .collect()
            } else {
                output.layers[output.layers.len() - 1]
                    .iter()
                    .map(|val| Fields::<F, E>::Base(*val))
                    .collect()
            };

        let mut output_mle = MultilinearPoly::new_from_vec(
            (output_evals.len() as f64).log2() as usize,
            output_evals,
        );

        transcript.observe_base_element(&output.layers[output.layers.len() - 1]);

        let mut g = transcript.sample_n_challenges(output_mle.num_vars());

        let mut claimed_sum = output_mle.evaluate(
            &g.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        );

        let (mut add_i, mut mul_i) =
            LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, circuit.layers.len() - 1);

        let mut w_i_plus_one_poly = MultilinearPoly::new_from_vec(
            (output.layers[output.layers.len() - 2].len() as f64).log2() as usize,
            output.layers[output.layers.len() - 2]
                .iter()
                .map(|val| Fields::Base(*val))
                .collect::<Vec<Fields<F, E>>>(),
        );

        let (mut igz, mut mul_ahg, mut add_b_ahg, mut add_c_ahg) = prepare_phase_one_params(
            &g,
            &add_i,
            &mul_i,
            &w_i_plus_one_poly
                .evaluations
                .iter()
                .map(|val| val.to_base_field().unwrap())
                .collect::<Vec<F>>(),
        );

        for i in (1..output.layers.len()).rev() {
            let (sumcheck_proof, rb, rc, wb, wc) = prove_libra_sumcheck(
                &igz,
                &mul_ahg,
                &add_b_ahg,
                &add_c_ahg,
                &add_i,
                &mul_i,
                &w_i_plus_one_poly,
                &claimed_sum,
                &mut transcript,
            );

            sumcheck_proofs.push(sumcheck_proof);
            wbs.push(wb);
            wcs.push(wc);

            let alpha_n_beta = transcript.sample_n_challenges(2);

            claimed_sum = Fields::Extension((alpha_n_beta[0] * wb) + (alpha_n_beta[1] * wc));

            // Get addi and muli
            (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

            w_i_plus_one_poly = MultilinearPoly::new_from_vec(
                (output.layers[i - 1].len() as f64).log2() as usize,
                output.layers[i - 1]
                    .iter()
                    .map(|val| Fields::<F, E>::Base(*val))
                    .collect(),
            );

            // Gets new addi and muli based on rb, rc, alpha and beta
            (igz, mul_ahg, add_b_ahg, add_c_ahg) = prepare_phase_one_params_with_alpha_beta_rb_rc(
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
        }

        LibraProof::new(
            output.layers[output.layers.len() - 1].clone(),
            sumcheck_proofs,
            wbs,
            wcs,
        )
    }

    // Verify the GKR Proof
    fn verify(
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

        let mut g = transcript
            .sample_n_challenges(output_mle.num_vars())
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        let mut claimed_sum = output_mle.evaluate(&g);

        let mut rb = vec![];

        let mut rc = vec![];

        for i in 0..proofs.sumcheck_proofs.len() {
            let (_claimed_sum, rb_n_rc) = SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[i],
                &mut transcript,
            );

            rb = rb_n_rc[..rb_n_rc.len() / 2].to_vec();

            rc = rb_n_rc[(rb_n_rc.len() / 2)..].to_vec();

            let alpha_n_beta = transcript.sample_n_challenges(2);

            claimed_sum = Fields::Extension(
                (alpha_n_beta[0] * proofs.wbs[i]) + (alpha_n_beta[1] * proofs.wcs[i]),
            );
        }

        // Final oracle check on the input
        let input_poly = MultilinearPoly::new_from_vec(
            (input.len() as f64).log2() as usize,
            input.iter().map(|val| Fields::Base(*val)).collect(),
        );

        let res = input_poly.evaluate(&[rb, rc].concat());

        assert_eq!(claimed_sum, res);

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
    fn test_libra() {
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

        dbg!("Verification starting...");
        let verify = Libra::verify(&circuit, proof, input);
        dbg!("Verification finished...");

        assert!(verify.unwrap());
    }
}
