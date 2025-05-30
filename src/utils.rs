use circuits::layered_circuit::utils::get_gate_properties;
use p3_field::{ExtensionField, Field};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, vpoly::VPoly};
use std::rc::Rc;
use sum_check::primitives::SumCheckProof;

pub struct ProveLibraInput<'a, F: Field, E: ExtensionField<F>> {
    pub claimed_sum: &'a Fields<F, E>,
    pub igz: &'a [E],
    pub mul_ahg: &'a [E],
    pub add_b_ahg: &'a [E],
    pub add_c_ahg: &'a [E],
    pub add_i: &'a [(usize, usize, usize)],
    pub mul_i: &'a [(usize, usize, usize)],
    pub w_i_plus_one_poly: &'a MultilinearPoly<F, E>,
}

pub struct EvalNewAddNMulInput<'a, F: Field, E: ExtensionField<F>> {
    pub add_i: &'a [(usize, usize, usize)],
    pub mul_i: &'a [(usize, usize, usize)],
    pub alpha_n_beta: &'a [Fields<F, E>],
    pub rb: &'a [Fields<F, E>],
    pub rc: &'a [Fields<F, E>],
    pub bc: &'a [Fields<F, E>],
    pub wb: &'a Fields<F, E>,
    pub wc: &'a Fields<F, E>,
}

pub(crate) fn generate_eq<F: Field, E: ExtensionField<F>>(points: &[E]) -> Vec<E> {
    let mut res = vec![E::one()];

    for point in points {
        let mut v = vec![];
        for val in &res {
            v.push(*val * (E::one() - *point));
            v.push(*val * *point);
        }
        res = v;
    }

    res
}

pub(crate) fn fold_igz<F: Field, E: ExtensionField<F>>(
    rb: &[E],
    rc: &[E],
    alpha_n_beta: &[E],
) -> Vec<E> {
    // get Igz for rb and rc
    let alpha_rb_igz: Vec<E> = generate_eq(rb)
        .iter()
        .map(|val| *val * alpha_n_beta[0])
        .collect::<Vec<E>>();
    let beta_rc_igz: Vec<E> = generate_eq(rc)
        .iter()
        .map(|val| *val * alpha_n_beta[1])
        .collect::<Vec<E>>();

    // Build and return new Igz
    alpha_rb_igz
        .iter()
        .zip(&beta_rc_igz)
        .map(|(rhs, lhs)| *rhs + *lhs)
        .collect::<Vec<E>>()
}

// Algorithm 4
pub(crate) fn initialize_phase_one<F: Field, E: ExtensionField<F>>(
    igz: &[E],
    f1: &[(usize, usize, usize)],
    f3: &[F],
) -> Vec<E> {
    let mut res = vec![E::zero(); f3.len()];

    for (z, x, y) in f1 {
        // It is assumed the operation poly outputs 1 where there is a valid gate
        res[*x] += igz[*z] * f3[*y];
    }

    res
}

// Algorithm 5
pub(crate) fn initialize_phase_two<F: Field, E: ExtensionField<F>>(
    igz: &[E],
    iux: &[E],
    f1: &[(usize, usize, usize)],
) -> Vec<E> {
    let mut res = vec![E::zero(); iux.len()];

    for (z, x, y) in f1 {
        // It is assumed the operation poly outputs 1 where there is a valid gate
        res[*y] += igz[*z] * iux[*x];
    }

    res
}

// Combines a vector of sumcheck proofs into one sumcheck proof
pub fn combine_sumcheck_proofs<F: Field, E: ExtensionField<F>>(
    sumcheck_proofs: Vec<SumCheckProof<F, E>>,
) -> SumCheckProof<F, E> {
    sumcheck_proofs
        .into_iter()
        .reduce(|mut acc, val| {
            acc.round_polynomials
                .extend_from_slice(&val.round_polynomials);
            acc
        })
        .unwrap()
}

pub(crate) fn prepare_phase_one_params<F: Field, E: ExtensionField<F>>(
    igz: &[E],
    add_i: &[(usize, usize, usize)],
    mul_i: &[(usize, usize, usize)],
    w_i_plus_one: &[F],
) -> (Vec<E>, Vec<E>, Vec<E>) {
    let ident = vec![F::one(); w_i_plus_one.len()];

    // Build Ahg for mul, add_b and add_c
    let mul_ahg = initialize_phase_one(&igz, mul_i, w_i_plus_one);

    let add_b_ahg = initialize_phase_one(&igz, add_i, &ident);

    let add_c_ahg = initialize_phase_one(&igz, add_i, w_i_plus_one);

    (mul_ahg, add_b_ahg, add_c_ahg)
}

// hg(x)
pub(crate) fn build_phase_one_libra_sumcheck_poly<F: Field, E: ExtensionField<F>>(
    mul_ahg: &[E],
    add_b_ahg: &[E],
    add_c_ahg: &[E],
    w_i_plus_one_poly: &MultilinearPoly<F, E>,
) -> VPoly<F, E> {
    let n_vars = w_i_plus_one_poly.num_vars();

    VPoly::new(
        vec![
            MultilinearPoly::new_from_vec(
                n_vars,
                mul_ahg
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_b_ahg
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_c_ahg
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            w_i_plus_one_poly.clone(),
        ],
        2,
        n_vars,
        Rc::new(|data: &[Fields<F, E>]| (data[3] * (data[0] + data[1])) + data[2]),
    )
}

pub(crate) fn prepare_phase_two_params<F: Field, E: ExtensionField<F>>(
    igz: &[E],
    u: &[E],
    add_i: &[(usize, usize, usize)],
    mul_i: &[(usize, usize, usize)],
) -> (Vec<E>, Vec<E>) {
    let iux = generate_eq(u);

    // Build Af1 for mul and add
    let mul_af1 = initialize_phase_two(igz, &iux, mul_i);

    let add_af1 = initialize_phase_two(igz, &iux, add_i);

    (mul_af1, add_af1)
}

pub(crate) fn build_phase_two_libra_sumcheck_poly<F: Field, E: ExtensionField<F>>(
    mul_af1: &[E],
    add_af1: &[E],
    wb: &E,
    w_i_plus_one_poly: &MultilinearPoly<F, E>,
) -> VPoly<F, E> {
    let n_vars = w_i_plus_one_poly.num_vars();

    VPoly::new(
        vec![
            MultilinearPoly::new_from_vec(
                n_vars,
                mul_af1
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_af1
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                vec![wb; w_i_plus_one_poly.evaluations.len()]
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(**val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            w_i_plus_one_poly.clone(),
        ],
        2,
        n_vars,
        Rc::new(|data: &[Fields<F, E>]| {
            (data[0] * data[2] * data[3]) + (data[1] * (data[2] + data[3]))
        }),
    )
}

pub struct SparsePoly<F: Field, E: ExtensionField<F>> {
    // contains a vec of tuple of index and evaluation
    pub n_vars: usize,
    pub evals: Vec<(usize, Fields<F, E>)>,
}

impl<F: Field, E: ExtensionField<F>> SparsePoly<F, E> {
    pub fn new(n_vars: usize, evals: Vec<(usize, Fields<F, E>)>) -> Self {
        Self { n_vars, evals }
    }

    pub fn evaluate(&self, points: &[Fields<F, E>]) -> Fields<F, E> {
        let basis = generate_eq(
            &points
                .iter()
                .map(|val| val.to_extension_field())
                .collect::<Vec<E>>(),
        );

        self.evals
            .iter()
            .fold(Fields::from_u32(0), |mut acc, (index, val)| {
                acc = acc + (Fields::Extension(basis[*index]) * *val);
                acc
            })
    }
}

pub fn to_sparse_poly<F: Field, E: ExtensionField<F>>(
    gates: &[(usize, usize, usize)],
    layer_index: usize,
    n_vars: usize,
) -> SparsePoly<F, E> {
    // convert gate tuple to index and value pairs
    let valid_gate_index_and_value = gates
        .iter()
        .map(|(a, b, c)| {
            (
                get_gate_properties(*a, *b, *c, layer_index),
                Fields::from_u32(1),
            )
        })
        .collect::<Vec<(usize, Fields<F, E>)>>();
    SparsePoly::new(n_vars, valid_gate_index_and_value)
}

pub(crate) fn eval_layer_mle_given_wb_n_wc<F: Field, E: ExtensionField<F>>(
    add_i: &[(usize, usize, usize)],
    mul_i: &[(usize, usize, usize)],
    challenges: &[Fields<F, E>],
    wb: &Fields<F, E>,
    wc: &Fields<F, E>,
    layer_index: usize,
    n_vars: usize,
) -> Fields<F, E> {
    let addi_poly = to_sparse_poly(add_i, layer_index, n_vars);
    let muli_poly = to_sparse_poly(mul_i, layer_index, n_vars);

    (addi_poly.evaluate(challenges) * (*wb + *wc)) + (muli_poly.evaluate(challenges) * (*wb * *wc))
}

pub(crate) fn eval_new_addi_n_muli_at_rb_bc_n_rc_bc<F: Field, E: ExtensionField<F>>(
    input: EvalNewAddNMulInput<'_, F, E>,
    layer_index: usize,
    n_vars: usize,
) -> Fields<F, E> {
    let addi_poly = to_sparse_poly(input.add_i, layer_index, n_vars);
    let muli_poly = to_sparse_poly(input.mul_i, layer_index, n_vars);

    let rb_bc = [input.rb, input.bc].concat();

    let rc_bc = [input.rc, input.bc].concat();

    let addi_rb_b_c = addi_poly.evaluate(&rb_bc);
    let addi_rc_b_c = addi_poly.evaluate(&rc_bc);
    let muli_rb_b_c = muli_poly.evaluate(&rb_bc);
    let muli_rc_b_c = muli_poly.evaluate(&rc_bc);

    let new_addi = (input.alpha_n_beta[0] * addi_rb_b_c) + (input.alpha_n_beta[1] * addi_rc_b_c);
    let new_muli = (input.alpha_n_beta[0] * muli_rb_b_c) + (input.alpha_n_beta[1] * muli_rc_b_c);

    (new_addi * (*input.wb + *input.wc)) + (new_muli * (*input.wb * *input.wc))
}

#[cfg(test)]
mod tests {
    use p3_field::{AbstractExtensionField, AbstractField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;

    use crate::utils::{generate_eq, initialize_phase_one, initialize_phase_two};

    #[test]
    fn test_precompute() {
        let challenges: Vec<BinomialExtensionField<Mersenne31, 3>> = [1, 3, 5]
            .into_iter()
            .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(Mersenne31::new(val)))
            .collect();

        let precomputed =
            generate_eq::<Mersenne31, BinomialExtensionField<Mersenne31, 3>>(&challenges);

        let expected: Vec<BinomialExtensionField<Mersenne31, 3>> = [
            Mersenne31::zero(),
            Mersenne31::zero(),
            Mersenne31::zero(),
            Mersenne31::zero(),
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(BinomialExtensionField::<Mersenne31, 3>::from_base)
        .collect();

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

        let igz: Vec<_> = [
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(BinomialExtensionField::<Mersenne31, 3>::from_base)
        .collect();

        // f(out, left, right) in the sparse form
        let f1 = vec![(0, 0, 1), (1, 2, 3), (2, 4, 5), (3, 6, 7)];

        let f3 = vec![
            Mersenne31::from_canonical_usize(3),
            Mersenne31::from_canonical_usize(4),
            Mersenne31::from_canonical_usize(5),
            Mersenne31::from_canonical_usize(6),
            Mersenne31::from_canonical_usize(7),
            Mersenne31::from_canonical_usize(8),
            Mersenne31::from_canonical_usize(9),
            Mersenne31::from_canonical_usize(10),
        ];

        let ahg = initialize_phase_one(&igz, &f1, &f3);

        let expected: Vec<_> = [
            Mersenne31::from_canonical_usize(32),
            Mersenne31::zero(),
            -Mersenne31::from_canonical_usize(60),
            Mersenne31::zero(),
            -Mersenne31::from_canonical_usize(96),
            Mersenne31::zero(),
            Mersenne31::from_canonical_usize(150),
            Mersenne31::zero(),
        ]
        .into_iter()
        .map(BinomialExtensionField::<Mersenne31, 3>::from_base)
        .collect();

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
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(BinomialExtensionField::<Mersenne31, 3>::from_base)
        .collect::<Vec<BinomialExtensionField<Mersenne31, 3>>>();

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
            -Mersenne31::from_canonical_usize(36),
            Mersenne31::from_canonical_usize(54),
            Mersenne31::from_canonical_usize(42),
            -Mersenne31::from_canonical_usize(63),
            Mersenne31::from_canonical_usize(48),
            -Mersenne31::from_canonical_usize(72),
            -Mersenne31::from_canonical_usize(56),
            Mersenne31::from_canonical_usize(84),
        ]
        .into_iter()
        .map(BinomialExtensionField::<Mersenne31, 3>::from_base)
        .collect::<Vec<BinomialExtensionField<Mersenne31, 3>>>();

        // f(out, left, right) in the sparse form
        let f1 = vec![(0, 0, 1), (1, 2, 3), (2, 4, 5), (3, 6, 7)];

        let af1 = initialize_phase_two::<Mersenne31, BinomialExtensionField<Mersenne31, 3>>(
            &igz, &iux, &f1,
        );

        let expected: Vec<_> = [
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(288),
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(420),
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(576),
            Mersenne31::from_canonical_usize(0),
            -Mersenne31::from_canonical_usize(840),
        ]
        .into_iter()
        .map(BinomialExtensionField::<Mersenne31, 3>::from_base)
        .collect();

        assert_eq!(af1, expected);
    }
}
