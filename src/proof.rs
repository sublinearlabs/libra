use p3_field::{ExtensionField, Field};
use poly::Fields;
use sum_check::primitives::SumCheckProof;

pub struct LibraProof<F: Field, E: ExtensionField<F>> {
    pub circuit_output: Vec<Fields<F, E>>,
    pub sumcheck_proofs: Vec<SumCheckProof<F, E>>,
    pub wbs: Vec<Fields<F, E>>,
    pub wcs: Vec<Fields<F, E>>,
}

impl<F: Field, E: ExtensionField<F>> LibraProof<F, E> {
    pub fn new(
        output: Vec<Fields<F, E>>,
        sumcheck_proofs: Vec<SumCheckProof<F, E>>,
        wbs: Vec<Fields<F, E>>,
        wcs: Vec<Fields<F, E>>,
    ) -> LibraProof<F, E> {
        LibraProof {
            circuit_output: output,
            sumcheck_proofs,
            wbs,
            wcs,
        }
    }
}
