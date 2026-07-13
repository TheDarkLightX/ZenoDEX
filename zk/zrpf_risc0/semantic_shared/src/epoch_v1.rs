use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{
    semantic_epoch_manifest_root_v1, NodeJournalV3, ProgramIdV3, ProposedSemanticEpochV1,
    SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
    SemanticEpochErrorV1, SemanticEpochProposalInputV1,
};
use zenodex_zrpf_risc0_aggregate_shared::{
    recompose_expected_structural_aggregate_v1, StructuralAggregateErrorV1,
    StructuralAggregateInputV1, StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;

use crate::{
    recompose_profile_bound_semantic_leaves_v1, SemanticRecompositionErrorV1,
    SemanticRecompositionInputV1, SemanticRecompositionPolicyV1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticEpochCompositionPolicyV1 {
    expected_adapter_image_id: [u32; 8],
    expected_level_one_image_id: [u32; 8],
    expected_level_two_image_id: [u32; 8],
}

impl SemanticEpochCompositionPolicyV1 {
    pub fn new(
        expected_adapter_image_id: [u32; 8],
        expected_level_one_image_id: [u32; 8],
        expected_level_two_image_id: [u32; 8],
    ) -> Result<Self, SemanticEpochCompositionErrorV1> {
        SemanticRecompositionPolicyV1::new(expected_adapter_image_id, expected_level_one_image_id)
            .map_err(SemanticEpochCompositionErrorV1::SemanticRecomposition)?;
        if expected_level_two_image_id.iter().all(|word| *word == 0) {
            return Err(SemanticEpochCompositionErrorV1::ZeroLevelTwoImageId);
        }
        Ok(Self {
            expected_adapter_image_id,
            expected_level_one_image_id,
            expected_level_two_image_id,
        })
    }

    pub const fn expected_adapter_image_id(self) -> [u32; 8] {
        self.expected_adapter_image_id
    }

    pub const fn expected_level_one_image_id(self) -> [u32; 8] {
        self.expected_level_one_image_id
    }

    pub const fn expected_level_two_image_id(self) -> [u32; 8] {
        self.expected_level_two_image_id
    }

    fn semantic_recomposition_policy(
        self,
    ) -> Result<SemanticRecompositionPolicyV1, SemanticEpochCompositionErrorV1> {
        SemanticRecompositionPolicyV1::new(
            self.expected_adapter_image_id,
            self.expected_level_one_image_id,
        )
        .map_err(SemanticEpochCompositionErrorV1::SemanticRecomposition)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticEpochCompositionInputV1 {
    expected_semantic_self_image_id: [u32; 8],
    recomposition: SemanticRecompositionInputV1,
}

impl SemanticEpochCompositionInputV1 {
    pub fn new(
        expected_semantic_self_image_id: [u32; 8],
        recomposition: SemanticRecompositionInputV1,
    ) -> Result<Self, SemanticEpochCompositionErrorV1> {
        if expected_semantic_self_image_id
            .iter()
            .all(|word| *word == 0)
        {
            return Err(SemanticEpochCompositionErrorV1::ZeroSemanticImageId);
        }
        Ok(Self {
            expected_semantic_self_image_id,
            recomposition,
        })
    }

    pub const fn expected_semantic_self_image_id(&self) -> [u32; 8] {
        self.expected_semantic_self_image_id
    }

    pub const fn recomposition(&self) -> &SemanticRecompositionInputV1 {
        &self.recomposition
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticEpochCompositionProjectionV1 {
    proposal: ProposedSemanticEpochV1,
    structural_level_two_journal: NodeJournalV3,
}

impl SemanticEpochCompositionProjectionV1 {
    pub const fn proposal(&self) -> &ProposedSemanticEpochV1 {
        &self.proposal
    }

    pub const fn structural_level_two_journal(&self) -> &NodeJournalV3 {
        &self.structural_level_two_journal
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticEpochCompositionErrorV1 {
    ZeroSemanticImageId,
    ZeroLevelTwoImageId,
    SemanticRecomposition(SemanticRecompositionErrorV1),
    StructuralLevelTwo(StructuralAggregateErrorV1),
    ProgramDerivation(&'static str),
    Protocol(SemanticEpochErrorV1),
    StructuralProtocol(zenodex_zrpf_protocol_v3::ZrpfErrorV3),
}

impl fmt::Display for SemanticEpochCompositionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroSemanticImageId => formatter.write_str("semantic guest image ID is zero"),
            Self::ZeroLevelTwoImageId => {
                formatter.write_str("structural level-two image ID is zero")
            }
            Self::SemanticRecomposition(error) => {
                write!(formatter, "semantic leaf recomposition rejected: {error}")
            }
            Self::StructuralLevelTwo(error) => {
                write!(
                    formatter,
                    "structural level-two recomposition rejected: {error}"
                )
            }
            Self::ProgramDerivation(field) => {
                write!(formatter, "semantic program derivation failed: {field}")
            }
            Self::Protocol(error) => write!(formatter, "semantic proposal rejected: {error}"),
            Self::StructuralProtocol(error) => {
                write!(formatter, "structural journal operation rejected: {error}")
            }
        }
    }
}

/// Deterministically recomposes a structural L2 journal and its semantic epoch
/// proposal from bounded disclosed journals.
///
/// This pure function authenticates no receipt. The structural proof-tree root
/// binds the concrete L1 grouping. The semantic epoch root is derived from the
/// flattened profile-bound leaves and remains independent of valid grouping.
pub fn recompose_expected_semantic_epoch_v1(
    input: &SemanticEpochCompositionInputV1,
    policy: SemanticEpochCompositionPolicyV1,
) -> Result<SemanticEpochCompositionProjectionV1, SemanticEpochCompositionErrorV1> {
    let leaves = recompose_profile_bound_semantic_leaves_v1(
        input.recomposition(),
        policy.semantic_recomposition_policy()?,
    )
    .map_err(SemanticEpochCompositionErrorV1::SemanticRecomposition)?;
    let level_one_journal_bytes: Vec<Vec<u8>> = input
        .recomposition()
        .level_one_nodes()
        .iter()
        .map(|node| node.level_one_journal_bytes().to_vec())
        .collect();
    let level_two = recompose_expected_structural_aggregate_v1(
        &StructuralAggregateInputV1 {
            expected_self_image_id: policy.expected_level_two_image_id,
            child_journal_bytes: level_one_journal_bytes,
        },
        StructuralAggregatePolicyV1::level_two_level_one_children(
            policy.expected_level_one_image_id,
        ),
    )
    .map_err(SemanticEpochCompositionErrorV1::StructuralLevelTwo)?;
    let proof_tree_root = level_two
        .journal
        .canonical_hash()
        .map_err(SemanticEpochCompositionErrorV1::StructuralProtocol)?;
    let semantic_program_id =
        program_id(input.expected_semantic_self_image_id, "semantic_program_id")?;
    let dependencies = dependency_programs(policy)?;
    let manifest = semantic_epoch_manifest_root_v1(semantic_program_id, &dependencies)
        .map_err(SemanticEpochCompositionErrorV1::Protocol)?;
    let proposal = ProposedSemanticEpochV1::derive(SemanticEpochProposalInputV1 {
        leaves,
        proof_tree_root,
        scope: level_two.journal.scope().clone(),
        actual_program_id: semantic_program_id,
        program_manifest_root: manifest,
    })
    .map_err(SemanticEpochCompositionErrorV1::Protocol)?;
    Ok(SemanticEpochCompositionProjectionV1 {
        proposal,
        structural_level_two_journal: level_two.journal,
    })
}

/// Enters the pure semantic composer after the caller has authenticated every
/// exact L1 claim under `policy.expected_level_one_image_id()`.
pub fn compose_semantic_epoch_after_level_one_verification_v1(
    input: &SemanticEpochCompositionInputV1,
    policy: SemanticEpochCompositionPolicyV1,
) -> Result<SemanticEpochCompositionProjectionV1, SemanticEpochCompositionErrorV1> {
    recompose_expected_semantic_epoch_v1(input, policy)
}

fn dependency_programs(
    policy: SemanticEpochCompositionPolicyV1,
) -> Result<SemanticEpochDependencyProgramsV1, SemanticEpochCompositionErrorV1> {
    Ok(SemanticEpochDependencyProgramsV1::new(
        SemanticEpochDependencyProgramsInputV1 {
            adapter_program_id: program_id(policy.expected_adapter_image_id, "adapter_program_id")?,
            level_one_program_id: program_id(
                policy.expected_level_one_image_id,
                "level_one_program_id",
            )?,
            level_two_program_id: program_id(
                policy.expected_level_two_image_id,
                "level_two_program_id",
            )?,
        },
    ))
}

fn program_id(
    words: [u32; 8],
    field: &'static str,
) -> Result<ProgramIdV3, SemanticEpochCompositionErrorV1> {
    program_id_from_risc0_words_v3(words)
        .map_err(|_| SemanticEpochCompositionErrorV1::ProgramDerivation(field))
}
