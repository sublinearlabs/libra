use p3_field::ExtensionField;

pub fn generate_eq<F: ExtensionField<F>>(points: &Vec<F>) -> Vec<F> {
    let mut res = vec![F::one()];

    for point in points {
        let mut v = vec![];
        for val in &res {
            v.push(*val * (F::one() - *point));
            v.push(*val * *point);
        }
        res = v;
    }

    res
}

#[cfg(test)]
mod tests {
    use p3_field::{AbstractExtensionField, AbstractField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;

    use crate::utils::generate_eq;

    #[test]
    fn test_precompute() {
        let challenges: Vec<BinomialExtensionField<Mersenne31, 3>> = [1, 3, 5]
            .into_iter()
            .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(Mersenne31::new(val)))
            .collect();

        let precomputed = generate_eq(&challenges);

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
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        assert_eq!(precomputed, expected);
    }
}
