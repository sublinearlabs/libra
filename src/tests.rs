use std::rc::Rc;

use circuits::{
    interface::CircuitTr,
    layered_circuit::{
        LayeredCircuit,
        primitives::{Gate, GateOp, Layer},
    },
};
use p3_field::{AbstractExtensionField, AbstractField, extension::BinomialExtensionField};
use p3_mersenne_31::Mersenne31;
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, utils::generate_eq, vpoly::VPoly};
use sum_check::{SumCheck, interface::SumCheckInterface};
use transcript::Transcript;

use crate::{
    libra_sumcheck::prove_libra_sumcheck,
    proof::LibraProof,
    prover::prove,
    utils::{
        ProveLibraInput, igz_n_to_1_fold, initialize_phase_one, initialize_phase_two,
        prepare_phase_one_params,
    },
    verifier::verify,
};

type F = Mersenne31;

type E = BinomialExtensionField<Mersenne31, 3>;

type Mle = VPoly<F, E>;

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
        .map(F::from_canonical_usize)
        .collect::<Vec<F>>();

    let output = circuit.excecute(&input);

    let proof: LibraProof<F, E> = prove(&circuit, output);

    let verify = verify(&circuit, proof, input);

    assert!(verify.unwrap());
}

#[test]
fn test_prove_libra_sumcheck() {
    let g = Fields::from_u32_vec(vec![3]);

    let add_i = vec![(0, 0, 1)];

    let mul_i = vec![(1, 2, 3)];

    let w_i_plus_one_poly =
        MultilinearPoly::new_from_vec(2, Fields::from_u32_vec(vec![6, 6, 6, 16]));

    // Traditional poly
    let mut add_i_eval = vec![0; 32];
    add_i_eval[1] = 1;
    let add_i_bln = MultilinearPoly::new_from_vec(
        5,
        add_i_eval
            .into_iter()
            .map(|val| Fields::<F, E>::Base(F::new(val)))
            .collect(),
    )
    .partial_evaluate(&[Fields::Base(F::new(3))]);

    let mut expected_add_i = vec![Fields::Extension(E::from_base(F::new(0))); 16];
    expected_add_i[1] = Fields::<F, E>::Extension(E::from_base(-F::new(2)));

    assert_eq!(add_i_bln.evaluations, expected_add_i);

    let mut mul_i_eval = vec![0; 32];
    mul_i_eval[27] = 1;
    let mul_i_bln = MultilinearPoly::new_from_vec(
        5,
        mul_i_eval
            .into_iter()
            .map(|val| Fields::Base(F::new(val)))
            .collect(),
    )
    .partial_evaluate(&[Fields::Base(F::new(3))]);

    let mut expected_mul_i = vec![Fields::Extension(E::from_base(F::new(0))); 16];
    expected_mul_i[11] = Fields::<F, E>::Extension(E::from_base(F::new(3)));

    assert_eq!(mul_i_bln.evaluations, expected_mul_i);

    let mut transcript = Transcript::<F, E>::init();

    let igz = generate_eq(&g);

    let (mul_ahg, add_b_ahg, add_c_ahg) =
        prepare_phase_one_params(&igz, &add_i, &mul_i, &w_i_plus_one_poly.evaluations);

    let wb_bln = MultilinearPoly::new_from_vec(
        4,
        vec![6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 16, 16, 16, 16]
            .into_iter()
            .map(|val| Fields::<F, E>::Base(F::new(val)))
            .collect(),
    );

    let wc_bln = MultilinearPoly::new_from_vec(
        4,
        vec![6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16]
            .into_iter()
            .map(|val| Fields::Base(F::new(val)))
            .collect(),
    );

    let claimed_sum = VPoly::new(
        vec![add_i_bln.clone(), mul_i_bln.clone(), wb_bln, wc_bln],
        2,
        Rc::new(|data: &[Fields<F, E>]| {
            (data[0] * (data[2] + data[3])) + (data[1] * data[2] * data[3])
        }),
    )
    .sum_over_hypercube();

    let (proof, wb, wc) = prove_libra_sumcheck(
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

    let mut transcript = Transcript::<F, E>::init();

    let (claimed_sum, challenges) = SumCheck::<F, E, Mle>::verify_partial(&proof, &mut transcript);

    let verifier_wb = &challenges[0..challenges.len() / 2];
    let verifier_wc = &challenges[&challenges.len() / 2..];

    let (rb, rc) = (
        proof.challenges[..proof.challenges.len() / 2].to_vec(),
        proof.challenges[proof.challenges.len() / 2..].to_vec(),
    );
    assert_eq!(rb, verifier_wb);
    assert_eq!(rc, verifier_wc);

    let evaluated_wb = w_i_plus_one_poly.evaluate(verifier_wb);
    let evaluated_wc = w_i_plus_one_poly.evaluate(verifier_wc);

    assert_eq!(wb, evaluated_wb);
    assert_eq!(wc, evaluated_wc);

    let evaluated_add_i = add_i_bln.evaluate(&challenges);
    let evaluated_muli = mul_i_bln.evaluate(&challenges);

    let expected_claimed_sum = (evaluated_add_i * (evaluated_wb + evaluated_wc))
        + (evaluated_muli * (evaluated_wb * evaluated_wc));

    assert_eq!(claimed_sum, expected_claimed_sum.to_extension_field());
}

#[test]
fn test_prove_alpha_beta_folding() {
    let rb = Fields::from_u32_vec(vec![2]);
    let rc = Fields::from_u32_vec(vec![4]);
    let alpha_n_beta = Fields::from_u32_vec(vec![3, 5]);

    let add_i = vec![(0, 0, 1)];

    let mul_i = vec![(1, 2, 3)];

    let w_i_plus_one_poly =
        MultilinearPoly::new_from_vec(2, Fields::from_u32_vec(vec![6, 6, 6, 16]));

    // Traditional poly
    let mut add_i_eval = vec![0; 32];
    add_i_eval[1] = 1;

    let add_i_poly = MultilinearPoly::new_from_vec(
        5,
        add_i_eval
            .into_iter()
            .map(|val| Fields::<F, E>::Base(F::new(val)))
            .collect(),
    );

    let add_rb_alpha = add_i_poly
        .partial_evaluate(&rb)
        .evaluations
        .iter()
        .map(|val| *val * alpha_n_beta[0])
        .collect::<Vec<Fields<F, E>>>();
    let add_rc_beta = add_i_poly
        .partial_evaluate(&rc)
        .evaluations
        .iter()
        .map(|val| *val * alpha_n_beta[1])
        .collect::<Vec<Fields<F, E>>>();
    let comb_add = add_rb_alpha
        .iter()
        .zip(add_rc_beta)
        .map(|(lhs, rhs)| *lhs + rhs)
        .collect::<Vec<Fields<F, E>>>();

    let mut mul_i_eval = vec![0; 32];
    mul_i_eval[27] = 1;

    let mul_i_poly = MultilinearPoly::new_from_vec(
        5,
        mul_i_eval
            .into_iter()
            .map(|val| Fields::Base(F::new(val)))
            .collect(),
    );

    let mul_rb_alpha = mul_i_poly
        .partial_evaluate(&rb)
        .evaluations
        .iter()
        .map(|val| *val * alpha_n_beta[0])
        .collect::<Vec<Fields<F, E>>>();
    let mul_rc_beta = mul_i_poly
        .partial_evaluate(&rc)
        .evaluations
        .iter()
        .map(|val| *val * alpha_n_beta[1])
        .collect::<Vec<Fields<F, E>>>();
    let comb_mul = mul_rb_alpha
        .iter()
        .zip(mul_rc_beta)
        .map(|(lhs, rhs)| *lhs + rhs)
        .collect::<Vec<Fields<F, E>>>();

    let new_addi_bln = MultilinearPoly::new_from_vec(4, comb_add);

    let new_muli_bln = MultilinearPoly::new_from_vec(4, comb_mul);

    let mut transcript = Transcript::<F, E>::init();

    let igz = igz_n_to_1_fold::<F, E>(&[&rb, &rc], &alpha_n_beta);

    let (mul_ahg, add_b_ahg, add_c_ahg) =
        prepare_phase_one_params(&igz, &add_i, &mul_i, &w_i_plus_one_poly.evaluations);

    let wb_bln = MultilinearPoly::new_from_vec(
        4,
        vec![6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 16, 16, 16, 16]
            .into_iter()
            .map(|val| Fields::<F, E>::Base(F::new(val)))
            .collect(),
    );

    let wc_bln = MultilinearPoly::new_from_vec(
        4,
        vec![6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16, 6, 6, 6, 16]
            .into_iter()
            .map(|val| Fields::Base(F::new(val)))
            .collect(),
    );

    let claimed_sum = VPoly::new(
        vec![new_addi_bln.clone(), new_muli_bln.clone(), wb_bln, wc_bln],
        2,
        Rc::new(|data: &[Fields<F, E>]| {
            (data[0] * (data[2] + data[3])) + (data[1] * data[2] * data[3])
        }),
    )
    .sum_over_hypercube();

    let (proof, wb, wc) = prove_libra_sumcheck(
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

    let mut transcript = Transcript::<F, E>::init();

    let (claimed_sum, challenges) = SumCheck::<F, E, Mle>::verify_partial(&proof, &mut transcript);

    let verifier_wb = &challenges[0..challenges.len() / 2];
    let verifier_wc = &challenges[&challenges.len() / 2..];

    let (rb, rc) = (
        proof.challenges[..proof.challenges.len() / 2].to_vec(),
        proof.challenges[proof.challenges.len() / 2..].to_vec(),
    );

    assert_eq!(rb, verifier_wb);
    assert_eq!(rc, verifier_wc);

    let evaluated_wb = w_i_plus_one_poly.evaluate(verifier_wb);
    let evaluated_wc = w_i_plus_one_poly.evaluate(verifier_wc);

    assert_eq!(wb, evaluated_wb);
    assert_eq!(wc, evaluated_wc);

    let evaluated_add_i = new_addi_bln.evaluate(&challenges);
    let evaluated_muli = new_muli_bln.evaluate(&challenges);

    let expected_claimed_sum = (evaluated_add_i * (evaluated_wb + evaluated_wc))
        + (evaluated_muli * (evaluated_wb * evaluated_wc));

    assert_eq!(claimed_sum, expected_claimed_sum.to_extension_field());
}

#[test]
fn test_precompute() {
    let challenges = Fields::<F, E>::from_u32_vec(vec![1, 3, 5]);

    let precomputed = generate_eq(&challenges);

    let expected = [
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        Fields::Extension(E::from_base(F::from_canonical_usize(8))),
        -Fields::Extension(E::from_base(F::from_canonical_usize(10))),
        -Fields::Extension(E::from_base(F::from_canonical_usize(12))),
        Fields::Extension(E::from_base(F::from_canonical_usize(15))),
    ];

    assert_eq!(precomputed, expected);
}

#[test]
fn test_build_ahg() {
    //
    //       12      30      56      90
    //       *       *       *       *
    //     /   \   /   \   /   \   /   \
    //     3   4   5   6   7   8   9   10
    //

    // values (3,5) were used to generate the Igz table
    // (1-a)(1-b) = (1-3)(1-5) = 8
    // (1-a)b = (1-3) 5 = -10
    // a(1-b) = 3 (1-5) = -12
    // ab = 3*5 = 15

    let igz = [
        Fields::<F, E>::from_u32(8),
        -Fields::from_u32(10),
        -Fields::from_u32(12),
        Fields::from_u32(15),
    ];

    // f(out, left, right) in the sparse form
    let f1 = vec![(0, 0, 1), (1, 2, 3), (2, 4, 5), (3, 6, 7)];

    let f3 = Fields::<F, E>::from_u32_vec(vec![3, 4, 5, 6, 7, 8, 9, 10]);

    let ahg = initialize_phase_one(&igz, &f1, &f3);

    let expected = [
        Fields::Extension(E::from_base(F::from_canonical_u32(32))),
        Fields::Extension(E::from_base(F::from_canonical_u32(0))),
        -Fields::Extension(E::from_base(F::from_canonical_u32(60))),
        Fields::Extension(E::from_base(F::from_canonical_u32(0))),
        -Fields::Extension(E::from_base(F::from_canonical_u32(96))),
        Fields::Extension(E::from_base(F::from_canonical_u32(0))),
        Fields::Extension(E::from_base(F::from_canonical_u32(150))),
        Fields::Extension(E::from_base(F::from_canonical_u32(0))),
    ];

    assert_eq!(ahg, expected);
}

#[test]
fn test_build_af1() {
    //
    //       12      30      56      90
    //       *       *       *       *
    //     /   \   /   \   /   \   /   \
    //     3   4   5   6   7   8   9   10
    //

    // values (3,5) were used to generate the Igz table
    // (1-a)(1-b) = (1-3)(1-5) = 8
    // (1-a)b = (1-3) 5 = -10
    // a(1-b) = 3 (1-5) = -12
    // ab = 3*5 = 15

    let igz = [
        Fields::<F, E>::from_u32(8),
        -Fields::from_u32(10),
        -Fields::from_u32(12),
        Fields::from_u32(15),
    ];

    // values (4,7,3) were used to generate the Iux table
    // (1-a)(1-b)(1-c) = (1-4)(1-7)(1-3) = -36
    // (1-a)(1-b)c = (1-4)(1-7)3 = 54
    // (1-a)b(1-c) = (1-4)7(1-3) = 42
    // (1-a)b*c = (1-4)*7*3 = -63
    // a(1-b)(1-c) = 4*(1-7)*(1-3) = 48
    // a(1-b)c = 4*(1-7)*3 = -72
    // a*b(1-c) = 4*7*(1-3) = -56
    // a*b*c = 4*7*3 = 84

    let iux = [
        -Fields::from_u32(36),
        Fields::from_u32(54),
        Fields::from_u32(42),
        -Fields::from_u32(63),
        Fields::from_u32(48),
        -Fields::from_u32(72),
        -Fields::from_u32(56),
        Fields::from_u32(84),
    ];

    // f(out, left, right) in the sparse form
    let f1 = vec![(0, 0, 1), (1, 2, 3), (2, 4, 5), (3, 6, 7)];

    let af1 = initialize_phase_two(&igz, &iux, &f1);

    let expected = [
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        -Fields::Extension(E::from_base(F::from_canonical_usize(288))),
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        -Fields::Extension(E::from_base(F::from_canonical_usize(420))),
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        -Fields::Extension(E::from_base(F::from_canonical_usize(576))),
        Fields::Extension(E::from_base(F::from_canonical_usize(0))),
        -Fields::Extension(E::from_base(F::from_canonical_usize(840))),
    ];

    assert_eq!(af1, expected);
}
