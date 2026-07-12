use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v3, CommitmentV3, ExpectedV1AdapterLeafIdentityV1,
    NodeJournalInputV4, NodeJournalV4, ProposedSemanticLeafV1, V1AdapterSemanticLeafOpeningV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    propose_spot_value_subtree_v2, semantic_subtree_v2_from_spot_summary,
    spot_residual_application_statement_hash_v4,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;

use crate::{
    decode_exact_spot_value_leaf_witness_v4, risc0_proof_system_id_v4,
    risc0_succinct_receipt_security_profile_id_v4, risc0_verifier_parameters_root_v4,
    spot_value_leaf_manifest_root_v4, spot_value_leaf_profile_id_v4, RawSpotValueLeafInputV4,
    SpotValueLeafProposalErrorV4, PINNED_V1_ADAPTER_IMAGE_ID_A,
};

/// Deterministically propose a V4 value leaf from bounded disclosures.
///
/// This pure function authenticates no receipt. An authority-bearing guest
/// must verify `raw.adapter_journal_bytes()` under
/// [`PINNED_V1_ADAPTER_IMAGE_ID_A`]
/// before entering this function. The outer verifier must then authenticate
/// the resulting V4 receipt and bind the circular self-image field.
pub fn propose_spot_value_leaf_v4(
    raw: &RawSpotValueLeafInputV4,
) -> Result<NodeJournalV4, SpotValueLeafProposalErrorV4> {
    let adapter_program_id = program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A)
        .map_err(|_| SpotValueLeafProposalErrorV4::Derivation("adapter_program_id"))?;
    let structural = decode_exact_node_journal_v3(raw.adapter_journal_bytes())?;
    let expected_adapter = ExpectedV1AdapterLeafIdentityV1::new(adapter_program_id)?;
    let witness = decode_exact_spot_value_leaf_witness_v4(raw.witness_bytes())?;
    let semantic_opening = CommitmentV3::new(witness.semantic_opening())?;
    let semantic_leaf = ProposedSemanticLeafV1::bind_v1_adapter_journal(
        &structural,
        V1AdapterSemanticLeafOpeningV1::new(semantic_opening),
        &expected_adapter,
    )?;
    let summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&semantic_leaf),
        core::slice::from_ref(witness.value_opening()),
        witness.policy(),
    )?;
    let semantic_subtree = semantic_subtree_v2_from_spot_summary(&summary)?;
    let application_statement_hash =
        spot_residual_application_statement_hash_v4(&semantic_subtree)?;
    let actual_program_id = program_id_from_risc0_words_v3(raw.expected_self_image_id())
        .map_err(|_| SpotValueLeafProposalErrorV4::Derivation("self_program_id"))?;
    let proof_profile_id = spot_value_leaf_profile_id_v4()?;
    let proof_system_id = risc0_proof_system_id_v4()?;
    let receipt_security_profile_id = risc0_succinct_receipt_security_profile_id_v4()?;
    let verifier_parameters_root = risc0_verifier_parameters_root_v4()?;
    let program_manifest_root =
        spot_value_leaf_manifest_root_v4(actual_program_id, adapter_program_id)?;

    Ok(NodeJournalV4::new(NodeJournalInputV4 {
        structural,
        semantic_subtree,
        application_statement_hash,
        proof_profile_id,
        actual_program_id,
        proof_system_id,
        receipt_security_profile_id,
        verifier_parameters_root,
        program_manifest_root,
        child_semantic_journal_hashes: alloc::vec![],
    })?)
}
