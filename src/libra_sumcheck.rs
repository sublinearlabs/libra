use std::rc::Rc;

use p3_field::{ExtensionField, Field, PrimeField32};
use poly::{Fields, MultilinearExtension, mle::MultilinearPoly, vpoly::VPoly};
use sum_check::{SumCheck, SumCheckInterface, SumCheckProof};
use transcript::Transcript;

use crate::utils::{
    combine_sumcheck_proofs, generate_eq, initialize_phase_one, initialize_phase_two,
};

pub fn prove_libra_sumcheck<F: Field + PrimeField32, E: ExtensionField<F>>(
    g: &Vec<E>,
    add_i: &Vec<(usize, usize, usize)>,
    mul_i: &Vec<(usize, usize, usize)>,
    w_i_plus_one: &Vec<F>,
    claimed_sum: &E,
    transcript: &mut Transcript<F, E>,
) -> (SumCheckProof<F, E>, Vec<E>, Vec<E>, E, E) {
    let igz = generate_eq(&g);

    let ident = vec![F::one(); w_i_plus_one.len()];

    let ident_ex = vec![E::one(); w_i_plus_one.len()];

    let n_vars = (w_i_plus_one.len() as f64).log2() as usize;

    // f2
    let w_i_plus_one_poly = MultilinearPoly::new_from_vec(
        n_vars,
        w_i_plus_one
            .iter()
            .map(|val| Fields::<F, E>::Base(*val))
            .collect::<Vec<Fields<F, E>>>(),
    );

    // Build Ahg for mul, add_b and add_c
    let mul_ahg = initialize_phase_one(&igz, &mul_i, &w_i_plus_one);
    dbg!(&mul_ahg);

    // Can this be removed in the first phase?
    let add_b_ahg = initialize_phase_one(&igz, &add_i, &ident);
    dbg!(&add_b_ahg);

    let add_c_ahg = initialize_phase_one(&igz, &add_i, &w_i_plus_one);
    dbg!(&add_c_ahg);

    // Ahg
    let poly = VPoly::new(
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
            MultilinearPoly::new_from_vec(
                n_vars,
                w_i_plus_one
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(E::from_base(*val)))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
        ],
        2,
        n_vars,
        // TODO: verify this
        Rc::new(|data: &[Fields<F, E>]| (data[0] + data[1] + data[2]) * data[3]),
    );

    // section 3.3.1 of the libra paper
    // let poly = VPoly::new(vec![w_i_plus_one_poly, poly_ahg], 2, n_vars, Rc::new(|data: &[Fields<F, E>]| data[0] * data[1]));

    let phase_one_claimed_sum = poly.sum_over_hypercube();

    dbg!(&phase_one_claimed_sum);

    let (phase_one_sumcheck_proof, u) =
        SumCheck::prove_partial(phase_one_claimed_sum, &poly, transcript).unwrap();

    let wb: E = w_i_plus_one_poly
        .evaluate(
            &u.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        )
        .to_extension_field();

    let wb_poly_evals = vec![wb; w_i_plus_one.len()];

    // Prepare parameters for phase two
    let iux = generate_eq(&u);

    // Build Af1 for mul, add_b and add_c
    let mul_af1 = initialize_phase_two(&igz, &iux, &mul_i);

    // let add_b_af1 = initialize_phase_two(&igz, &iux, &add_i);

    let add_c_af1 = initialize_phase_two(&igz, &ident_ex, &add_i);

    let poly = VPoly::new(
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
                wb_poly_evals
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                add_c_af1
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(*val))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
            MultilinearPoly::new_from_vec(
                n_vars,
                w_i_plus_one
                    .iter()
                    .map(|val| Fields::<F, E>::Extension(E::from_base(*val)))
                    .collect::<Vec<Fields<F, E>>>(),
            ),
        ],
        2,
        n_vars,
        Rc::new(|data: &[Fields<F, E>]| (data[0] + data[1] + data[2]) * data[3]),
    );

    let phase_two_claimed_sum = poly.sum_over_hypercube();

    dbg!(&phase_two_claimed_sum);

    let (phase_two_sumcheck_proof, v) =
        SumCheck::prove_partial(phase_two_claimed_sum, &poly, transcript).unwrap();

    let wc = w_i_plus_one_poly
        .evaluate(
            &v.iter()
                .map(|val| Fields::Extension(*val))
                .collect::<Vec<Fields<F, E>>>(),
        )
        .to_extension_field();

    dbg!(&n_vars);
    dbg!(&claimed_sum);
    dbg!(&phase_one_sumcheck_proof.claimed_sum);
    dbg!(&phase_two_sumcheck_proof.claimed_sum);
    dbg!(
        phase_one_sumcheck_proof.round_polynomials[0][0].to_extension_field()
            + phase_one_sumcheck_proof.round_polynomials[0][1].to_extension_field()
    );

    // let sumcheck_proof =
    //     combine_sumcheck_proofs(vec![phase_one_sumcheck_proof, phase_two_sumcheck_proof]);

    // dbg!(&sumcheck_proof.round_polynomials.len());

    // Question???
    // Are we to send the two sumcheck proofs?
    // I suspect we are to combine them
    // TODO: Determine the right way to combine them
    (phase_one_sumcheck_proof, u, v, wb, wc)
}

#[cfg(test)]
mod tests {
    use p3_field::{AbstractExtensionField, AbstractField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;
    use poly::{Fields, MultilinearExtension, mle::MultilinearPoly};
    use sum_check::{SumCheck, SumCheckInterface};
    use transcript::Transcript;

    use super::prove_libra_sumcheck;

    #[test]
    fn test_prove_libra_sumcheck() {
        let g: Vec<BinomialExtensionField<Mersenne31, 3>> =
            vec![BinomialExtensionField::from_base(Mersenne31::new(3))];

        let add_i = vec![(0, 0, 1)];

        let mul_i = vec![(1, 2, 3)];

        let w_i_plus_one = vec![
            Mersenne31::from_canonical_usize(6),
            Mersenne31::from_canonical_usize(6),
            Mersenne31::from_canonical_usize(6),
            Mersenne31::from_canonical_usize(16),
        ];

        // ???
        let claimed_sum: BinomialExtensionField<Mersenne31, 3> =
            BinomialExtensionField::from_base(Mersenne31::new(66));

        let mut transcript: Transcript<Mersenne31, BinomialExtensionField<Mersenne31, 3>> =
            Transcript::<Mersenne31, BinomialExtensionField<Mersenne31, 3>>::init();

        let (proof, rb, rc, wb, wc) = prove_libra_sumcheck(
            &g,
            &add_i,
            &mul_i,
            &w_i_plus_one,
            &claimed_sum,
            &mut transcript,
        );

        let mut transcript: Transcript<Mersenne31, BinomialExtensionField<Mersenne31, 3>> =
            Transcript::<Mersenne31, BinomialExtensionField<Mersenne31, 3>>::init();

        // ???
        // let polynomial =

        // let verify = SumCheck::verify(polynomial, &proof, &mut transcript);

        dbg!(proof.round_polynomials);

        // assert!(verify.unwrap());
    }
}
