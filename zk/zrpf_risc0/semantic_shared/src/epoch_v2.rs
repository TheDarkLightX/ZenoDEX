use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{
    semantic_epoch_dependency_manifest_root_v2, NodeJournalV3, ProgramIdV3,
    ProposedSemanticEpochV2, SemanticEpochDependencyProgramsInputV1,
    SemanticEpochDependencyProgramsV1, SemanticEpochErrorV2, SemanticEpochProposalInputV2,
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
pub struct SemanticEpochCompositionPolicyV2 {
    expected_adapter_image_id: [u32; 8],
    expected_level_one_image_id: [u32; 8],
    expected_level_two_image_id: [u32; 8],
}

impl SemanticEpochCompositionPolicyV2 {
    pub fn new(
        expected_adapter_image_id: [u32; 8],
        expected_level_one_image_id: [u32; 8],
        expected_level_two_image_id: [u32; 8],
    ) -> Result<Self, SemanticEpochCompositionErrorV2> {
        SemanticRecompositionPolicyV1::new(expected_adapter_image_id, expected_level_one_image_id)
            .map_err(SemanticEpochCompositionErrorV2::SemanticRecomposition)?;
        if expected_level_two_image_id.iter().all(|word| *word == 0) {
            return Err(SemanticEpochCompositionErrorV2::ZeroLevelTwoImageId);
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
    ) -> Result<SemanticRecompositionPolicyV1, SemanticEpochCompositionErrorV2> {
        SemanticRecompositionPolicyV1::new(
            self.expected_adapter_image_id,
            self.expected_level_one_image_id,
        )
        .map_err(SemanticEpochCompositionErrorV2::SemanticRecomposition)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticEpochCompositionInputV2 {
    recomposition: SemanticRecompositionInputV1,
}

impl SemanticEpochCompositionInputV2 {
    pub const fn new(recomposition: SemanticRecompositionInputV1) -> Self {
        Self { recomposition }
    }

    pub const fn recomposition(&self) -> &SemanticRecompositionInputV1 {
        &self.recomposition
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticEpochCompositionProjectionV2 {
    proposal: ProposedSemanticEpochV2,
    structural_level_two_journal: NodeJournalV3,
}

impl SemanticEpochCompositionProjectionV2 {
    pub const fn proposal(&self) -> &ProposedSemanticEpochV2 {
        &self.proposal
    }

    pub const fn structural_level_two_journal(&self) -> &NodeJournalV3 {
        &self.structural_level_two_journal
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticEpochCompositionErrorV2 {
    ZeroLevelTwoImageId,
    SemanticRecomposition(SemanticRecompositionErrorV1),
    StructuralLevelTwo(StructuralAggregateErrorV1),
    ProgramDerivation(&'static str),
    Protocol(SemanticEpochErrorV2),
    StructuralProtocol(zenodex_zrpf_protocol_v3::ZrpfErrorV3),
}

impl fmt::Display for SemanticEpochCompositionErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroLevelTwoImageId => {
                formatter.write_str("structural level-two image ID is zero")
            }
            Self::SemanticRecomposition(error) => {
                write!(
                    formatter,
                    "semantic V2 leaf recomposition rejected: {error}"
                )
            }
            Self::StructuralLevelTwo(error) => {
                write!(
                    formatter,
                    "semantic V2 structural recomposition rejected: {error}"
                )
            }
            Self::ProgramDerivation(field) => {
                write!(formatter, "semantic V2 program derivation failed: {field}")
            }
            Self::Protocol(error) => write!(formatter, "semantic V2 proposal rejected: {error}"),
            Self::StructuralProtocol(error) => {
                write!(
                    formatter,
                    "semantic V2 structural journal rejected: {error}"
                )
            }
        }
    }
}

/// Recompose the V2 semantic statement. Runtime image identity is absent from
/// both the input and the resulting proof-neutral proposal.
pub fn recompose_expected_semantic_epoch_v2(
    input: &SemanticEpochCompositionInputV2,
    policy: SemanticEpochCompositionPolicyV2,
) -> Result<SemanticEpochCompositionProjectionV2, SemanticEpochCompositionErrorV2> {
    let leaves = recompose_profile_bound_semantic_leaves_v1(
        input.recomposition(),
        policy.semantic_recomposition_policy()?,
    )
    .map_err(SemanticEpochCompositionErrorV2::SemanticRecomposition)?;
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
    .map_err(SemanticEpochCompositionErrorV2::StructuralLevelTwo)?;
    let proof_tree_root = level_two
        .journal
        .canonical_hash()
        .map_err(SemanticEpochCompositionErrorV2::StructuralProtocol)?;
    let dependencies = dependency_programs(policy)?;
    let dependency_manifest_root = semantic_epoch_dependency_manifest_root_v2(&dependencies)
        .map_err(SemanticEpochCompositionErrorV2::Protocol)?;
    let proposal = ProposedSemanticEpochV2::derive(SemanticEpochProposalInputV2 {
        leaves,
        proof_tree_root,
        scope: level_two.journal.scope().clone(),
        dependency_manifest_root,
    })
    .map_err(SemanticEpochCompositionErrorV2::Protocol)?;
    Ok(SemanticEpochCompositionProjectionV2 {
        proposal,
        structural_level_two_journal: level_two.journal,
    })
}

/// Enters V2 composition after every exact L1 receipt has been authenticated.
pub fn compose_semantic_epoch_after_level_one_verification_v2(
    input: &SemanticEpochCompositionInputV2,
    policy: SemanticEpochCompositionPolicyV2,
) -> Result<SemanticEpochCompositionProjectionV2, SemanticEpochCompositionErrorV2> {
    recompose_expected_semantic_epoch_v2(input, policy)
}

pub fn semantic_epoch_dependency_programs_v2(
    policy: SemanticEpochCompositionPolicyV2,
) -> Result<SemanticEpochDependencyProgramsV1, SemanticEpochCompositionErrorV2> {
    dependency_programs(policy)
}

fn dependency_programs(
    policy: SemanticEpochCompositionPolicyV2,
) -> Result<SemanticEpochDependencyProgramsV1, SemanticEpochCompositionErrorV2> {
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
) -> Result<ProgramIdV3, SemanticEpochCompositionErrorV2> {
    program_id_from_risc0_words_v3(words)
        .map_err(|_| SemanticEpochCompositionErrorV2::ProgramDerivation(field))
}
