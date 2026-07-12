use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{CommitmentV3, V1AdapterSemanticLeafOpeningV1};

use crate::{
    DisclosedStructuralLevelOneV1, DisclosedV1AdapterLeafV1, SemanticEpochCompositionInputV2,
    SemanticGuestInputV2, SemanticRecompositionErrorV1, SemanticRecompositionInputV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticGuestBindingErrorV2 {
    ZeroSemanticOpening { subtree: usize, child: usize },
    Disclosure(SemanticRecompositionErrorV1),
}

impl fmt::Display for SemanticGuestBindingErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroSemanticOpening { subtree, child } => {
                write!(formatter, "semantic V2 opening {subtree}:{child} is zero")
            }
            Self::Disclosure(error) => {
                write!(formatter, "semantic V2 disclosure rejected: {error}")
            }
        }
    }
}

/// Converts canonical V2 framing after every exact L1 receipt has been
/// authenticated. No runtime self-image value exists in this transition.
pub fn bind_semantic_guest_input_after_level_one_verification_v2(
    raw: &SemanticGuestInputV2,
) -> Result<SemanticEpochCompositionInputV2, SemanticGuestBindingErrorV2> {
    let mut level_one_nodes = Vec::with_capacity(raw.level_one_disclosures().len());
    for (subtree, raw_level_one) in raw.level_one_disclosures().iter().enumerate() {
        let mut leaves = Vec::with_capacity(raw_level_one.leaves().len());
        for (child, raw_leaf) in raw_level_one.leaves().iter().enumerate() {
            let opening = CommitmentV3::new(raw_leaf.semantic_opening())
                .map_err(|_| SemanticGuestBindingErrorV2::ZeroSemanticOpening { subtree, child })?;
            leaves.push(
                DisclosedV1AdapterLeafV1::new(
                    raw_leaf.journal_bytes().to_vec(),
                    V1AdapterSemanticLeafOpeningV1::new(opening),
                )
                .map_err(SemanticGuestBindingErrorV2::Disclosure)?,
            );
        }
        level_one_nodes.push(
            DisclosedStructuralLevelOneV1::new(raw_level_one.journal_bytes().to_vec(), leaves)
                .map_err(SemanticGuestBindingErrorV2::Disclosure)?,
        );
    }
    let recomposition = SemanticRecompositionInputV1::new(level_one_nodes)
        .map_err(SemanticGuestBindingErrorV2::Disclosure)?;
    Ok(SemanticEpochCompositionInputV2::new(recomposition))
}
