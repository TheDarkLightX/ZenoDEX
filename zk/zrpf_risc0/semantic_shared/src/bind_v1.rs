use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{CommitmentV3, V1AdapterSemanticLeafOpeningV1};

use crate::{
    DisclosedStructuralLevelOneV1, DisclosedV1AdapterLeafV1, SemanticEpochCompositionErrorV1,
    SemanticEpochCompositionInputV1, SemanticGuestInputV1, SemanticRecompositionErrorV1,
    SemanticRecompositionInputV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticGuestBindingErrorV1 {
    ZeroSemanticOpening { subtree: usize, child: usize },
    Disclosure(SemanticRecompositionErrorV1),
    Composition(SemanticEpochCompositionErrorV1),
}

impl fmt::Display for SemanticGuestBindingErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroSemanticOpening { subtree, child } => {
                write!(formatter, "semantic opening {subtree}:{child} is zero")
            }
            Self::Disclosure(error) => write!(formatter, "semantic disclosure rejected: {error}"),
            Self::Composition(error) => {
                write!(formatter, "semantic composition input rejected: {error}")
            }
        }
    }
}

/// Converts bounded raw guest framing into profile-bound disclosure values.
///
/// This function authenticates no receipt. Authority-bearing guests and hosts
/// must verify every exact L1 claim first. Keeping this conversion separate
/// makes the verify-before-interpret ordering visible at the call site.
pub fn bind_semantic_guest_input_after_level_one_verification_v1(
    raw: &SemanticGuestInputV1,
) -> Result<SemanticEpochCompositionInputV1, SemanticGuestBindingErrorV1> {
    let mut level_one_nodes = Vec::with_capacity(raw.level_one_disclosures().len());
    for (subtree, raw_level_one) in raw.level_one_disclosures().iter().enumerate() {
        let mut leaves = Vec::with_capacity(raw_level_one.leaves().len());
        for (child, raw_leaf) in raw_level_one.leaves().iter().enumerate() {
            let opening = CommitmentV3::new(raw_leaf.semantic_opening())
                .map_err(|_| SemanticGuestBindingErrorV1::ZeroSemanticOpening { subtree, child })?;
            leaves.push(
                DisclosedV1AdapterLeafV1::new(
                    raw_leaf.journal_bytes().to_vec(),
                    V1AdapterSemanticLeafOpeningV1::new(opening),
                )
                .map_err(SemanticGuestBindingErrorV1::Disclosure)?,
            );
        }
        level_one_nodes.push(
            DisclosedStructuralLevelOneV1::new(raw_level_one.journal_bytes().to_vec(), leaves)
                .map_err(SemanticGuestBindingErrorV1::Disclosure)?,
        );
    }
    let recomposition = SemanticRecompositionInputV1::new(level_one_nodes)
        .map_err(SemanticGuestBindingErrorV1::Disclosure)?;
    SemanticEpochCompositionInputV1::new(raw.expected_self_image_id(), recomposition)
        .map_err(SemanticGuestBindingErrorV1::Composition)
}
