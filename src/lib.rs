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

        let mut layer_evaluations: Vec<Fields<F, E>> =
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

        let mut layer_mle = MultilinearPoly::new_from_vec(
            (layer_evaluations.len() as f64).log2() as usize,
            layer_evaluations,
        );

        dbg!(&layer_mle);

        transcript.observe_base_element(&output.layers[output.layers.len() - 1]);

        let mut g = transcript.sample_n_challenges(layer_mle.num_vars());

        let mut claimed_sum = layer_mle.evaluate(
            &g.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        );

        dbg!(&g);
        dbg!(&claimed_sum);
        dbg!(&circuit.layers.len());

        let (mut add_i, mut mul_i) =
            LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, circuit.layers.len() - 1);

        let mut w_i_plus_one_poly = MultilinearPoly::new_from_vec(
            (output.layers[output.layers.len() - 2].len() as f64).log2() as usize,
            output.layers[output.layers.len() - 2]
                .iter()
                .map(|val| Fields::Base(*val))
                .collect::<Vec<Fields<F, E>>>(),
        );

        let mut alpha_n_beta = Vec::with_capacity(2);

        for i in (1..output.layers.len() - 1).rev() {
            let (sumcheck_proof, rb, rc, wb, wc) = prove_libra_sumcheck::<F, E>(
                &g,
                &add_i,
                &mul_i,
                &w_i_plus_one_poly,
                &claimed_sum,
                &mut transcript,
            );

            sumcheck_proofs.push(sumcheck_proof);
            wbs.push(wb);
            wcs.push(wc);

            alpha_n_beta = transcript.sample_n_challenges(2);

            dbg!(&alpha_n_beta);

            claimed_sum = Fields::Extension((alpha_n_beta[0] * wb) + (alpha_n_beta[1] * wc));

            dbg!(claimed_sum);

            layer_evaluations = output.layers[i]
                .iter()
                .map(|val| Fields::<F, E>::Base(*val))
                .collect();

            layer_mle = MultilinearPoly::new_from_vec(
                (layer_evaluations.len() as f64).log2() as usize,
                layer_evaluations,
            );

            dbg!(&layer_mle);

            transcript.observe_base_element(&output.layers[i]);

            dbg!("Layer: ", i);

            // TODO: get new addi and muli based on rb and rc
            (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(circuit, i - 1);

            dbg!(&add_i);
            dbg!(&mul_i);

            w_i_plus_one_poly = MultilinearPoly::new_from_vec(
                (output.layers[i - 1].len() as f64).log2() as usize,
                output.layers[i - 1]
                    .iter()
                    .map(|val| Fields::Base(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            );

            dbg!(&w_i_plus_one_poly);
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

        let mut challenge = transcript
            .sample_n_challenges(output_mle.num_vars())
            .iter()
            .map(|val| Fields::Extension(*val))
            .collect::<Vec<Fields<F, E>>>();

        dbg!(&challenge);

        let mut claimed_sum = output_mle.evaluate(&challenge);

        dbg!("Verifier claimed sum: ", claimed_sum);

        let mut rb = vec![];

        let mut rc = vec![];

        for i in 0..proofs.sumcheck_proofs.len() {
            dbg!("Verification round:", i);
            dbg!("{:#?}", &proofs.sumcheck_proofs[i].claimed_sum);
            dbg!("{:#?}", &proofs.sumcheck_proofs[i].round_polynomials);

            let (_claimed_sum, rb_n_rc) = SumCheck::<F, E, MultilinearPoly<F, E>>::verify_partial(
                &proofs.sumcheck_proofs[i],
                &mut transcript,
            );

            let mut rb_b_c = rb.clone();

            rb_b_c.extend(&rb_n_rc);

            let mut rc_b_c = rc.clone();

            rc_b_c.extend(&rb_n_rc);

            dbg!(&challenge);
            dbg!(&rb);
            dbg!(&rc);
            dbg!(&rb_n_rc);
            dbg!(&rb_b_c);
            dbg!(&rc_b_c);

            (rb, rc) = (
                rb_n_rc[..rb_n_rc.len() / 2].to_vec(),
                rb_n_rc[(rb_n_rc.len() / 2)..].to_vec(),
            );

            dbg!(&circuit.layers[circuit.layers.len() - i - 1]);

            let (add_i, mul_i) = LibraGKRLayeredCircuitTr::<F, E>::add_and_mul_mle(
                circuit,
                circuit.layers.len() - i - 1,
            );

            dbg!(&add_i);

            let alpha_n_beta = transcript.sample_n_challenges(2);

            dbg!(&alpha_n_beta);

            // Convert addi and muli to sparse rep and evaluate it
            let nvars = compute_num_vars(i, circuit.layers.len());

            dbg!(nvars);

            dbg!(2_usize.pow(nvars as u32));

            dbg!(i);

            let add_i_mle_vec = add_i.iter().fold(vec![], |mut acc, (a, b, c)| {
                dbg!(i);
                // verify the layer index
                let res = get_gate_properties(*a, *b, *c, i);
                acc.push(res);
                acc
            });

            let mul_i_mle_vec = mul_i.iter().fold(vec![], |mut acc, (a, b, c)| {
                dbg!(i);
                // verify the layer index
                let res = get_gate_properties(*a, *b, *c, i);
                acc.push(res);
                acc
            });

            let add_i_poly: MultilinearPoly<F, E> = mle_vec_to_poly(&add_i_mle_vec, nvars);
            let mul_i_poly: MultilinearPoly<F, E> = mle_vec_to_poly(&mul_i_mle_vec, nvars);

            dbg!(&mul_i_poly.evaluations.len());
            dbg!(&mul_i_poly.sum_over_hypercube());

            let new_addi = (alpha_n_beta[0] * add_i_poly.evaluate(&rb_b_c).to_extension_field())
                + (alpha_n_beta[1] * add_i_poly.evaluate(&rc_b_c).to_extension_field());

            let new_muli = (alpha_n_beta[0] * mul_i_poly.evaluate(&rb_b_c).to_extension_field())
                + (alpha_n_beta[1] * mul_i_poly.evaluate(&rc_b_c).to_extension_field());

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
