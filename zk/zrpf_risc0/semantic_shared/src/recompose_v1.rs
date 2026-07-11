use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v3, encode_node_journal_v3, ExpectedV1AdapterLeafIdentityV1,
    NodeJournalV3, NodeKindV3, NodeLevelV3, ProfileIdV3, ProgramIdV3, ProposedSemanticLeafV1,
};
use zenodex_zrpf_risc0_aggregate_shared::{
    recompose_expected_structural_aggregate_v1, StructuralAggregateInputV1,
    StructuralAggregatePolicyV1, STRUCTURAL_AGGREGATE_LEVEL_ONE_PROFILE_V1,
};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};

use crate::{
    DisclosedStructuralLevelOneV1, SemanticRecompositionErrorV1, SemanticRecompositionInputV1,
    SemanticRecompositionPolicyV1,
};

/// Reconstructs profile-bound semantic leaf proposals from disclosed journals.
///
/// This pure kernel authenticates no receipt. A guest must first verify every
/// exact L1 claim. Each authenticated L1 proof establishes its adapter-child
/// claims, while exact recomposition below binds the disclosed adapter journals
/// to that authenticated L1 journal. The resulting values remain proposals
/// until the guest completes and the outer verifier authenticates its receipt.
pub fn recompose_profile_bound_semantic_leaves_v1(
    input: &SemanticRecompositionInputV1,
    policy: SemanticRecompositionPolicyV1,
) -> Result<Vec<ProposedSemanticLeafV1>, SemanticRecompositionErrorV1> {
    input.validate_bounds()?;
    let expected = ExpectedIdentitiesV1::derive(policy)?;
    let mut leaves = Vec::new();
    let mut previous_subtree: Option<(u64, u64)> = None;

    for (subtree_index, disclosure) in input.level_one_nodes().iter().enumerate() {
        let level_one = decode_level_one(disclosure, subtree_index, expected)?;
        enforce_subtree_order(&level_one, subtree_index, previous_subtree)?;
        let subtree_leaves = recompose_one_subtree(SubtreeContextV1 {
            disclosure,
            expected_level_one: &level_one,
            subtree: subtree_index,
            expected,
        })?;
        for leaf in subtree_leaves {
            reject_global_duplicate(&leaves, &leaf)?;
            leaves.push(leaf);
        }
        previous_subtree = Some((
            level_one.partition().start(),
            level_one.partition().end_exclusive(),
        ));
    }
    Ok(leaves)
}

#[derive(Clone, Copy)]
struct ExpectedIdentitiesV1 {
    policy: SemanticRecompositionPolicyV1,
    adapter_identity: ExpectedV1AdapterLeafIdentityV1,
    level_one_program_id: ProgramIdV3,
    level_one_profile_id: ProfileIdV3,
}

impl ExpectedIdentitiesV1 {
    fn derive(policy: SemanticRecompositionPolicyV1) -> Result<Self, SemanticRecompositionErrorV1> {
        let adapter_program_id = program_id_from_risc0_words_v3(policy.expected_adapter_image_id())
            .map_err(|_| SemanticRecompositionErrorV1::Derivation("adapter_program_id"))?;
        let adapter_identity = ExpectedV1AdapterLeafIdentityV1::new(adapter_program_id)
            .map_err(|_| SemanticRecompositionErrorV1::Derivation("adapter_identity"))?;
        let level_one_program_id =
            program_id_from_risc0_words_v3(policy.expected_level_one_image_id())
                .map_err(|_| SemanticRecompositionErrorV1::Derivation("level_one_program_id"))?;
        let level_one_profile_id = profile_id_v3(STRUCTURAL_AGGREGATE_LEVEL_ONE_PROFILE_V1)
            .map_err(|_| SemanticRecompositionErrorV1::Derivation("level_one_profile_id"))?;
        Ok(Self {
            policy,
            adapter_identity,
            level_one_program_id,
            level_one_profile_id,
        })
    }
}

#[derive(Clone, Copy)]
struct SubtreeContextV1<'a> {
    disclosure: &'a DisclosedStructuralLevelOneV1,
    expected_level_one: &'a NodeJournalV3,
    subtree: usize,
    expected: ExpectedIdentitiesV1,
}

fn decode_level_one(
    disclosure: &DisclosedStructuralLevelOneV1,
    subtree: usize,
    expected: ExpectedIdentitiesV1,
) -> Result<NodeJournalV3, SemanticRecompositionErrorV1> {
    let journal = decode_exact_node_journal_v3(disclosure.level_one_journal_bytes())
        .map_err(|_| SemanticRecompositionErrorV1::LevelOneJournalDecode { subtree })?;
    if journal.node_kind() != NodeKindV3::Aggregate {
        return Err(SemanticRecompositionErrorV1::LevelOneAggregateRequired { subtree });
    }
    if journal.node_level() != NodeLevelV3::new(1)? {
        return Err(SemanticRecompositionErrorV1::LevelOneLevelMismatch { subtree });
    }
    if journal.actual_program_id() != expected.level_one_program_id {
        return Err(SemanticRecompositionErrorV1::LevelOneProgramMismatch { subtree });
    }
    if journal.proof_profile_id() != expected.level_one_profile_id {
        return Err(SemanticRecompositionErrorV1::LevelOneProfileMismatch { subtree });
    }
    Ok(journal)
}

fn enforce_subtree_order(
    level_one: &NodeJournalV3,
    subtree: usize,
    previous: Option<(u64, u64)>,
) -> Result<(), SemanticRecompositionErrorV1> {
    let start = level_one.partition().start();
    match previous {
        None if start != 0 => Err(SemanticRecompositionErrorV1::PartitionMustStartAtZero),
        Some((previous_start, _)) if start <= previous_start => {
            Err(SemanticRecompositionErrorV1::NonCanonicalSubtreeOrder { subtree })
        }
        Some((_, previous_end)) if start != previous_end => {
            Err(SemanticRecompositionErrorV1::NonContiguousSubtrees { subtree })
        }
        _ => Ok(()),
    }
}

fn recompose_one_subtree(
    context: SubtreeContextV1<'_>,
) -> Result<Vec<ProposedSemanticLeafV1>, SemanticRecompositionErrorV1> {
    let (decoded_children, child_bytes) =
        decode_ordered_children(context.disclosure, context.subtree)?;
    require_exact_level_one_recomposition(context, child_bytes)?;
    project_semantic_leaves(context, &decoded_children)
}

fn decode_ordered_children(
    disclosure: &DisclosedStructuralLevelOneV1,
    subtree: usize,
) -> Result<(Vec<NodeJournalV3>, Vec<Vec<u8>>), SemanticRecompositionErrorV1> {
    let mut decoded_children = Vec::with_capacity(disclosure.adapter_leaves().len());
    let mut child_bytes = Vec::with_capacity(disclosure.adapter_leaves().len());
    let mut previous_child: Option<(u64, u64)> = None;

    for (child_index, disclosed_leaf) in disclosure.adapter_leaves().iter().enumerate() {
        let journal =
            decode_exact_node_journal_v3(disclosed_leaf.journal_bytes()).map_err(|_| {
                SemanticRecompositionErrorV1::AdapterJournalDecode {
                    subtree,
                    child: child_index,
                }
            })?;
        enforce_child_order(&journal, subtree, child_index, previous_child)?;
        previous_child = Some((
            journal.partition().start(),
            journal.partition().end_exclusive(),
        ));
        decoded_children.push(journal);
        child_bytes.push(disclosed_leaf.journal_bytes().to_vec());
    }
    Ok((decoded_children, child_bytes))
}

fn require_exact_level_one_recomposition(
    context: SubtreeContextV1<'_>,
    child_bytes: Vec<Vec<u8>>,
) -> Result<(), SemanticRecompositionErrorV1> {
    let projection = recompose_expected_structural_aggregate_v1(
        &StructuralAggregateInputV1 {
            expected_self_image_id: context.expected.policy.expected_level_one_image_id(),
            child_journal_bytes: child_bytes,
        },
        StructuralAggregatePolicyV1::level_one_adapter_children(
            context.expected.policy.expected_adapter_image_id(),
        ),
    )
    .map_err(
        |error| SemanticRecompositionErrorV1::StructuralRecomposition {
            subtree: context.subtree,
            error,
        },
    )?;
    let canonical_recomposition = encode_node_journal_v3(&projection.journal)?;
    if canonical_recomposition.as_slice() != context.disclosure.level_one_journal_bytes()
        || projection.journal != *context.expected_level_one
    {
        return Err(SemanticRecompositionErrorV1::LevelOneJournalMismatch {
            subtree: context.subtree,
        });
    }
    Ok(())
}

fn project_semantic_leaves(
    context: SubtreeContextV1<'_>,
    decoded_children: &[NodeJournalV3],
) -> Result<Vec<ProposedSemanticLeafV1>, SemanticRecompositionErrorV1> {
    let mut semantic_leaves = Vec::with_capacity(decoded_children.len());
    for (child_index, (journal, disclosed_leaf)) in decoded_children
        .iter()
        .zip(context.disclosure.adapter_leaves())
        .enumerate()
    {
        let semantic_leaf = ProposedSemanticLeafV1::bind_v1_adapter_journal(
            journal,
            disclosed_leaf.semantic_opening(),
            &context.expected.adapter_identity,
        )
        .map_err(|error| SemanticRecompositionErrorV1::SemanticProjection {
            subtree: context.subtree,
            child: child_index,
            error,
        })?;
        semantic_leaves.push(semantic_leaf);
    }
    Ok(semantic_leaves)
}

fn enforce_child_order(
    journal: &NodeJournalV3,
    subtree: usize,
    child: usize,
    previous: Option<(u64, u64)>,
) -> Result<(), SemanticRecompositionErrorV1> {
    let start = journal.partition().start();
    match previous {
        Some((previous_start, _)) if start <= previous_start => {
            Err(SemanticRecompositionErrorV1::NonCanonicalChildOrder { subtree, child })
        }
        Some((_, previous_end)) if start != previous_end => {
            Err(SemanticRecompositionErrorV1::NonContiguousChildren { subtree, child })
        }
        _ => Ok(()),
    }
}

fn reject_global_duplicate(
    accepted: &[ProposedSemanticLeafV1],
    candidate: &ProposedSemanticLeafV1,
) -> Result<(), SemanticRecompositionErrorV1> {
    for prior in accepted {
        if prior.semantic_source_id() == candidate.semantic_source_id() {
            return Err(SemanticRecompositionErrorV1::DuplicateSemanticSource);
        }
        if prior.source_claim_id() == candidate.source_claim_id() {
            return Err(SemanticRecompositionErrorV1::DuplicateSourceClaim);
        }
        if prior.task_id() == candidate.task_id() {
            return Err(SemanticRecompositionErrorV1::DuplicateTask);
        }
    }
    Ok(())
}
