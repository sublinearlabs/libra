# Libra

A Rust implementation of the [Libra](https://eprint.iacr.org/2019/317.pdf) zero-knowledge proof protocol for verifiable computation on layered circuits.

## Overview

Libra is an efficient zero-knowledge argument system that enables a prover to convince a verifier that they correctly executed a computation represented as a layered arithmetic circuit. This implementation provides:

- **Two-phase sumcheck protocol** for efficient verification
- **Support for layered circuits** with addition and multiplication gates
- **Integration with Plonky3** field arithmetic and extensions
- **Non-interactive proofs** via Fiat-Shamir transformation

## Project Structure

- `src/proof.rs` - Libra proof data structures
- `src/libra_sumcheck.rs` - Two-phase Libra sumcheck implementation
- `src/prover.rs` - Proof generation logic
- `src/verifier.rs` - Proof verification logic
- `src/utils.rs` - Utility functions and algorithms
- `src/tests.rs` - Comprehensive test suite

## Getting Started

### Prerequisites

- Rust 1.70 or later
- Cargo

### Dependencies

Add to your `Cargo.toml`:

```toml
[dependencies]
libra = { git = "https://github.com/sublinearlabs/libra.git" }
circuits = { git = "https://github.com/sublinearlabs/sl-core.git" }
p3-mersenne-31 = "0.2.0"
p3-field = "0.2.0"
```

## Usage

### Basic Example

```rust
use circuits::{
    interface::CircuitTr,
    layered_circuit::{
        LayeredCircuit,
        primitives::{Gate, GateOp, Layer},
    },
};
use p3_mersenne_31::Mersenne31;
use p3_field::extension::BinomialExtensionField;
use libra::{prover::prove, verifier::verify, proof::LibraProof};

type F = Mersenne31;
type E = BinomialExtensionField<Mersenne31, 3>;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create a layered circuit
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

    // Prepare input
    let input: Vec<F> = [1, 2, 3, 2, 1, 2, 4, 1]
        .into_iter()
        .map(F::from_canonical_usize)
        .collect();

    // Execute the circuit
    let output = circuit.execute(&input);

    // Generate proof
    let proof: LibraProof<F, E> = prove(&circuit, output);

    // Verify proof
    let is_valid = verify(&circuit, proof, input)?;
    
    println!("Proof verification: {}", is_valid);
    Ok(())
}
```

## Testing

Run the test suite:

```bash
cargo test
```

Run with output:

```bash
cargo test -- --nocapture
```

Run specific tests:

```bash
cargo test test_libra_protocol
```

## Performance

The Libra protocol provides:
- **Prover time**: O(C)
- **Verifier time**: O(d log C)
- **Proof size**: O(d log C)
- **Memory usage**: Linear in circuit size
where C is circuit size and d is the circuit depth

## Contributing

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

### Development

Format code:
```bash
cargo fmt
```

Run clippy:
```bash
cargo clippy --all-targets --all-features -- -D warnings
```

## References

- [Original Libra Paper](https://eprint.iacr.org/2019/317.pdf)
- [Plonky3 Framework](https://github.com/Plonky3/Plonky3)

## Acknowledgements

We acknowledge the awesome work of the [Plonky3](https://github.com/Plonky3/Plonky3) team and the original Libra authors.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.