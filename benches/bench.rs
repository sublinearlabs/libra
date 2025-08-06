use circuits::{
    interface::CircuitTr,
    layered_circuit::{
        LayeredCircuit,
        primitives::{Evaluation, Gate, GateOp, Layer},
    },
};
use criterion::{Criterion, criterion_group, criterion_main};
use libra::{proof::LibraProof, prover::prove, verifier::verify};
use p3_field::{AbstractField, extension::BinomialExtensionField};
use p3_mersenne_31::Mersenne31 as F;
use rand::Rng;

type E = BinomialExtensionField<F, 3>;

// Builds a random circuit given input size
fn build_random_circuit(input_size: usize) -> LayeredCircuit {
    assert!(
        input_size.is_power_of_two(),
        "Input size should be a power of 2"
    );

    let n_layers = input_size.ilog2();

    let mut layers: Vec<Layer> = Vec::with_capacity(n_layers as usize);

    let mut gates_in_layer = input_size;

    for _ in 0..n_layers {
        let mut gates = vec![];
        for i in 0..gates_in_layer / 2 {
            let op = if rand::rng().random_bool(0.5) {
                GateOp::Add
            } else {
                GateOp::Mul
            };
            let gate = Gate::new(op, [i * 2, (i * 2) + 1]);
            gates.push(gate);
        }

        layers.push(Layer::new(gates));
        gates_in_layer /= 2;
    }

    LayeredCircuit::new(layers)
}

// Given input size, setup creates a circuit and inputs
// and evaluates the circuit to get the output
// Returns the circuit, input and output
pub fn setup(input_size: usize) -> (LayeredCircuit, Vec<F>, Evaluation<F>) {
    let circuit = build_random_circuit(input_size);

    let input = rand::random_iter::<u8>()
        .take(input_size)
        .map(|val| F::from_canonical_usize(val as usize))
        .collect::<Vec<F>>();

    let output = circuit.excecute(&input);

    (circuit, input, output)
}

fn benchmark(c: &mut Criterion) {
    c.bench_function("prove_n_verify_input_64", |b| {
        // TODO: fix bug for input greater that 8
        let (circuit, input, output) = setup(8);
        b.iter(|| {
            let proof: LibraProof<F, E> = prove(&circuit, output.clone());
            let _ = verify(&circuit, proof, input.clone());
        });
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
