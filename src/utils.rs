use p3_field::{ExtensionField, Field};

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

// Algorithm 4
pub fn build_ahg<F: Field, E: ExtensionField<F>>(
    igz: Vec<E>,
    f1: Vec<(usize, usize, usize)>,
    f3: Vec<F>,
) -> Vec<E> {
    let mut res = vec![E::zero(); f3.len()];

    for (z, x, y) in f1 {
        // It is assumed the operation poly outputs 1 where there is a valid gate
        res[x] += igz[z] * f3[y];
    }

    res
}

#[cfg(test)]
mod tests {
    use p3_field::{AbstractExtensionField, AbstractField, extension::BinomialExtensionField};
    use p3_mersenne_31::Mersenne31;

    use crate::utils::generate_eq;

    use super::build_ahg;

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
            Mersenne31::from_canonical_usize(8),
            -Mersenne31::from_canonical_usize(10),
            -Mersenne31::from_canonical_usize(12),
            Mersenne31::from_canonical_usize(15),
        ]
        .into_iter()
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
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

        let ahg = build_ahg(igz, f1, f3);

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
        .map(|val| BinomialExtensionField::<Mersenne31, 3>::from_base(val))
        .collect();

        assert_eq!(ahg, expected);
    }
}
