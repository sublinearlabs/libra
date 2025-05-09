use std::{error::Error, marker::PhantomData};

use circuits::{
    interface::LibraGKRLayeredCircuitTr,
    layered_circuit::{LayeredCircuit, primitives::Evaluation},
};
use libra_sumcheck::prove_libra_sumcheck;
use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly};
use sum_check::{SumCheck, SumCheckInterface, SumCheckProof};
use transcript::Transcript;

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

        for i in (0..circuit.layers.len()).rev() {
            let layer_evaluations: Vec<Fields<F, E>> = if output.layers[i + 1].len() <= 1 {
                [output.layers[i + 1].clone(), vec![F::zero()]]
                    .concat()
                    .iter()
                    .map(|val| Fields::<F, E>::Base(*val))
                    .collect()
            } else {
                output.layers[i + 1]
                    .iter()
                    .map(|val| Fields::<F, E>::Base(*val))
                    .collect()
            };

            let layer_mle = MultilinearPoly::new_from_vec(
                (layer_evaluations.len() as f64).log2() as usize,
                layer_evaluations,
            );

            dbg!(&layer_mle);

            transcript.observe_base_element(&output.layers[i + 1]);

            let g = transcript.sample_n_challenges(layer_mle.num_vars());

            dbg!("Layer: ", i);
            dbg!(&g);

            let claimed_sum = layer_mle.evaluate(
                &g.iter()
                    .map(|val| Fields::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            );

            dbg!(&claimed_sum);

            let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i);

            let w_i_plus_one = &output.layers[i];

            dbg!(&w_i_plus_one);

            let (sumcheck_proof, wb, wc) = prove_libra_sumcheck::<F, E>(
                i,
                g,
                add_i,
                mul_i,
                w_i_plus_one,
                claimed_sum.to_extension_field(),
                &mut transcript,
            );

            sumcheck_proofs.push(sumcheck_proof);
            wbs.push(wb);
            wcs.push(wc);
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

        dbg!(&output);

        let output_mle =
            MultilinearPoly::new_from_vec((output.len() as f64).log2() as usize, output);

        let mut challenges = transcript
            .sample_n_challenges(output_mle.num_vars())
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        dbg!(&challenges);

        let mut claimed_sum = output_mle.evaluate(&challenges);

        dbg!("Verifier claimed sum: ", claimed_sum);

        for i in 0..proofs.sumcheck_proofs.len() {
            dbg!("Verification round:", i);
            dbg!("{:#?}", &proofs.sumcheck_proofs[i].claimed_sum);

            let resp = SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[i],
                &mut transcript,
            );

            challenges = resp.1;

            claimed_sum = Fields::Extension(resp.0);

            let alpha_n_beta = transcript.sample_n_challenges(2);

            let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i);

            // TODO: Get new add and mul_i
            let (new_addi, new_muli) = (E::one(), E::one());

            claimed_sum = Fields::Extension(
                (new_addi * (proofs.wbs[i] + proofs.wcs[i]))
                    + (new_muli * proofs.wbs[i] * proofs.wcs[i]),
            );
        }

        // Final oracle check on the input
        let input_poly = MultilinearPoly::new_from_vec(
            (input.len() as f64).log2() as usize,
            input.iter().map(|val| Fields::Base(*val)).collect(),
        );

        let res = input_poly.evaluate(&challenges);

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

        dbg!("Proving starting...");
        let proof: LibraProof<Mersenne31, BinomialExtensionField<Mersenne31, 3>> =
            Libra::prove(&circuit, output);
        dbg!("Proving finished...");

        dbg!("Verification starting...");
        let verify = Libra::verify(&circuit, proof, input);
        dbg!("Verification finished...");

        assert!(verify.unwrap());
    }
}
