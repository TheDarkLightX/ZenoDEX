use std::collections::BTreeSet;

use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, recursive_cross_shard_messages_root_v1,
    recursive_receipt_ids_root_v1, RecursiveAssetDeltaRowV1, RecursiveEffectSummaryV1,
    RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, CommitmentV3, LeafNodeInputV3, NodeJournalInputV4, NodeJournalV3,
    NodeJournalV4, ProfileIdV3, ProgramIdV3, SemanticSubtreeInputV2, SemanticSubtreeV2,
    SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2,
};
use zenodex_zrpf_risc0_semantic_shared::{
    canonical_spot_asset_name_v1, spot_residual_application_statement_hash_v4,
    SpotRepresentedValuePolicyV1, SpotValueLeafOpeningV1,
};
use zenodex_zrpf_risc0_shared::{
    project_policy_bound_v1_journal, SourceKindV1, PINNED_SPOT_LEAF_IMAGE_ID_V1,
};
use zenodex_zrpf_risc0_value_node_shared::{
    encode_spot_value_leaf_witness_v4, propose_spot_value_leaf_v4, RawSpotValueLeafInputV4,
    SpotValueLeafWitnessV4, PINNED_V1_ADAPTER_IMAGE_ID_A, RISC0_RECEIPT_HASHFN_POSEIDON2_V1,
    RISC0_RESOLVE_CONTROL_ID_V1, RISC0_SUCCINCT_RECEIPT_KIND_V1,
    RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1, RISC0_VERIFIER_PARAMETERS_DIGEST_V1,
};

use super::{
    validate_authenticated_spot_value_leaf_journal_v4, AuthenticatedSpotValueLeafReceiptV4,
    SpotValueLeafIdentityFieldV4, VerifiedSpotValueLeafReceiptErrorV4,
};
use crate::{
    VerifiedNodeReceiptErrorV3, MAX_CANONICAL_RECEIPT_BYTES_V3, RECEIPT_CONTROL_ID_V1,
    RECEIPT_HASHFN_POSEIDON2_V1, RECEIPT_KIND_SUCCINCT_V1, RECEIPT_VERIFIER_PARAMETERS_V1,
    ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
};

const SELF_IMAGE_ID: [u32; 8] = [91, 92, 93, 94, 95, 96, 97, 98];
const POLICY_HASH: [u8; 32] = [80; 32];
const LANE_ID: &str = "spot-value-verifier-lane";

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn ordinary_row(atoms: u128) -> RecursiveAssetDeltaRowV1 {
    RecursiveAssetDeltaRowV1 {
        asset_id: canonical_spot_asset_name_v1([0; 32]),
        debit_atoms: atoms,
        credit_atoms: 0,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0; 32],
    }
}

fn summary(
    rows: &[RecursiveAssetDeltaRowV1],
    seed: u8,
    policy_hash: [u8; 32],
) -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: LANE_ID.to_owned(),
        lane_kind: "spot".to_owned(),
        chain_id: "zenodex-value-verifier-test".to_owned(),
        epoch_id: 81,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_owned(),
        risc0_image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
        statement_hash: root(seed),
        pre_state_root: root(10),
        post_state_root: root(11),
        tx_root: root(seed.wrapping_add(20)),
        evidence_root: root(2),
        receipt_root: root(3),
        accepted_receipts_root: empty_receipts,
        rejected_receipts_root: empty_receipts,
        asset_delta_root: recursive_asset_delta_root_v1(rows).unwrap(),
        cross_shard_outbox_root: empty_messages,
        cross_shard_inbox_root: empty_messages,
        write_set_root: root(4),
        public_policy_hash: policy_hash,
        feature_suite_hash: root(81),
        dependency_lock_hash: root(82),
        toolchain_lock_hash: root(83),
    }
}

fn journal(seed: u8, atoms: u128) -> NodeJournalV4 {
    journal_for_policy(seed, atoms, POLICY_HASH)
}

fn journal_for_policy(seed: u8, atoms: u128, policy_hash: [u8; 32]) -> NodeJournalV4 {
    let rows = vec![ordinary_row(atoms)];
    let source = summary(&rows, seed, policy_hash);
    let source_bytes = postcard::to_allocvec(&source).unwrap();
    let projection = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &source_bytes,
        0,
        PINNED_V1_ADAPTER_IMAGE_ID_A,
    )
    .unwrap();
    let semantic_opening = projection
        .source_binding
        .canonical_hash()
        .unwrap()
        .into_bytes();
    let structural_bytes = encode_node_journal_v3(&projection.journal).unwrap();
    let witness = SpotValueLeafWitnessV4::new(
        semantic_opening,
        SpotValueLeafOpeningV1::new(
            LANE_ID.to_owned(),
            source.pre_state_root,
            source.post_state_root,
            rows,
        )
        .unwrap(),
        SpotRepresentedValuePolicyV1::new(policy_hash, vec![]).unwrap(),
    )
    .unwrap();
    let raw = RawSpotValueLeafInputV4::new(
        SELF_IMAGE_ID,
        structural_bytes,
        encode_spot_value_leaf_witness_v4(&witness).unwrap(),
    )
    .unwrap();
    propose_spot_value_leaf_v4(&raw).unwrap()
}

fn rebuild(journal: &NodeJournalV4, mutate: impl FnOnce(&mut NodeJournalInputV4)) -> NodeJournalV4 {
    let mut input = NodeJournalInputV4 {
        structural: journal.structural().clone(),
        semantic_subtree: journal.semantic_subtree().clone(),
        application_statement_hash: journal.application_statement_hash(),
        proof_profile_id: journal.proof_profile_id(),
        actual_program_id: journal.actual_program_id(),
        proof_system_id: journal.proof_system_id(),
        receipt_security_profile_id: journal.receipt_security_profile_id(),
        verifier_parameters_root: journal.verifier_parameters_root(),
        program_manifest_root: journal.program_manifest_root(),
        child_semantic_journal_hashes: journal.child_semantic_journal_hashes().to_vec(),
    };
    mutate(&mut input);
    NodeJournalV4::new(input).unwrap()
}

fn rebuild_structural(
    structural: &NodeJournalV3,
    mutate: impl FnOnce(&mut LeafNodeInputV3),
) -> NodeJournalV3 {
    let mut input = LeafNodeInputV3 {
        task_id: structural.task_id(),
        partition: structural.partition(),
        operation_count: structural.operation_count(),
        count_unit_id: structural.count_unit_id(),
        scope: structural.scope().clone(),
        proof_profile_id: structural.proof_profile_id(),
        actual_program_id: structural.actual_program_id(),
        node_statement_hash: structural.node_statement_hash(),
        program_manifest_root: structural.program_manifest_root(),
        commitments: structural.commitments().clone(),
    };
    mutate(&mut input);
    NodeJournalV3::new_leaf(input).unwrap()
}

fn with_structural(journal: &NodeJournalV4, structural: NodeJournalV3) -> NodeJournalV4 {
    rebuild(journal, |input| input.structural = structural)
}

fn with_mutated_leaf_record(
    journal: &NodeJournalV4,
    mutate: impl FnOnce(&mut SemanticValueLeafRecordInputV2),
) -> NodeJournalV4 {
    let subtree = journal.semantic_subtree();
    let record = &subtree.leaf_records()[0];
    let mut record_input = SemanticValueLeafRecordInputV2 {
        partition: record.partition(),
        semantic_leaf_hash: record.semantic_leaf_hash(),
        source_claim_id: record.source_claim_id(),
        semantic_source_id: record.semantic_source_id(),
        task_id: record.task_id(),
        pre_state_vector_root: record.pre_state_vector_root(),
        post_state_vector_root: record.post_state_vector_root(),
        transaction_root: record.transaction_root(),
        effect_root: record.effect_root(),
        asset_delta_root: record.asset_delta_root(),
        raw_pre_state_root: record.raw_pre_state_root(),
        raw_post_state_root: record.raw_post_state_root(),
    };
    mutate(&mut record_input);
    let mutated_record = SemanticValueLeafRecordV2::new(record_input).unwrap();
    let mutated_subtree = SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: subtree.value_profile_id(),
        accounting_domain_id: subtree.accounting_domain_id(),
        atoms_unit_id: subtree.atoms_unit_id(),
        state_root_scheme_id: subtree.state_root_scheme_id(),
        scope_hash: subtree.scope_hash(),
        lane_id_hash: subtree.lane_id_hash(),
        partition: subtree.partition(),
        raw_subtree_pre_state_root: subtree.raw_subtree_pre_state_root(),
        raw_subtree_post_state_root: subtree.raw_subtree_post_state_root(),
        represented_row_count: subtree.represented_row_count(),
        leaf_records: vec![mutated_record],
        authority_grants_root: subtree.authority_grants_root(),
        asset_flows: subtree.asset_flows().to_vec(),
        authority_uses: subtree.authority_uses().to_vec(),
    })
    .unwrap();
    let application_statement_hash =
        spot_residual_application_statement_hash_v4(&mutated_subtree).unwrap();
    rebuild(journal, |input| {
        input.semantic_subtree = mutated_subtree;
        input.application_statement_hash = application_statement_hash;
    })
}

fn hex32(value: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for byte in value {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

#[test]
fn pure_policy_accepts_the_exact_guest_proposal() {
    validate_authenticated_spot_value_leaf_journal_v4(&journal(1, 10), SELF_IMAGE_ID).unwrap();
}

#[test]
fn verified_self_image_is_independently_bound() {
    assert_eq!(
        validate_authenticated_spot_value_leaf_journal_v4(&journal(1, 10), [1; 8]),
        Err(VerifiedSpotValueLeafReceiptErrorV4::ProgramIdMismatch)
    );
}

#[test]
fn every_v4_backend_identity_and_residual_statement_is_rederived() {
    let baseline = journal(1, 10);
    let foreign = CommitmentV3::new(root(240)).unwrap();
    let cases = [
        (
            rebuild(&baseline, |input| {
                input.proof_profile_id = ProfileIdV3::new(root(240)).unwrap();
            }),
            SpotValueLeafIdentityFieldV4::ProofProfileId,
        ),
        (
            rebuild(&baseline, |input| input.proof_system_id = foreign),
            SpotValueLeafIdentityFieldV4::ProofSystemId,
        ),
        (
            rebuild(&baseline, |input| {
                input.receipt_security_profile_id = foreign;
            }),
            SpotValueLeafIdentityFieldV4::ReceiptSecurityProfileId,
        ),
        (
            rebuild(&baseline, |input| input.verifier_parameters_root = foreign),
            SpotValueLeafIdentityFieldV4::VerifierParametersRoot,
        ),
        (
            rebuild(&baseline, |input| input.program_manifest_root = foreign),
            SpotValueLeafIdentityFieldV4::ProgramManifestRoot,
        ),
        (
            rebuild(&baseline, |input| {
                input.application_statement_hash = foreign
            }),
            SpotValueLeafIdentityFieldV4::ApplicationStatementHash,
        ),
    ];

    for (candidate, field) in cases {
        assert_eq!(
            validate_authenticated_spot_value_leaf_journal_v4(&candidate, SELF_IMAGE_ID),
            Err(VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(field))
        );
    }
}

#[test]
fn every_embedded_adapter_identity_and_leaf_shape_is_rederived() {
    let baseline = journal(1, 10);
    let structural = baseline.structural();
    let foreign = CommitmentV3::new(root(240)).unwrap();
    let cases = [
        (
            with_structural(
                &baseline,
                rebuild_structural(structural, |input| {
                    input.actual_program_id = ProgramIdV3::new(root(240)).unwrap();
                }),
            ),
            SpotValueLeafIdentityFieldV4::AdapterProgramId,
        ),
        (
            with_structural(
                &baseline,
                rebuild_structural(structural, |input| {
                    input.proof_profile_id = ProfileIdV3::new(root(240)).unwrap();
                }),
            ),
            SpotValueLeafIdentityFieldV4::AdapterProfileId,
        ),
        (
            with_structural(
                &baseline,
                rebuild_structural(structural, |input| input.program_manifest_root = foreign),
            ),
            SpotValueLeafIdentityFieldV4::AdapterManifestRoot,
        ),
        (
            with_structural(
                &baseline,
                rebuild_structural(structural, |input| input.count_unit_id = foreign),
            ),
            SpotValueLeafIdentityFieldV4::AdapterCountUnitId,
        ),
        (
            with_structural(
                &baseline,
                rebuild_structural(structural, |input| input.operation_count = 2),
            ),
            SpotValueLeafIdentityFieldV4::LeafShape,
        ),
    ];

    for (candidate, field) in cases {
        assert_eq!(
            validate_authenticated_spot_value_leaf_journal_v4(&candidate, SELF_IMAGE_ID),
            Err(VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(field))
        );
    }
}

#[test]
fn self_consistent_public_policy_variants_remain_residual_non_authority() {
    let baseline = journal_for_policy(1, 10, POLICY_HASH);
    let alternate = journal_for_policy(1, 10, root(79));

    validate_authenticated_spot_value_leaf_journal_v4(&baseline, SELF_IMAGE_ID).unwrap();
    validate_authenticated_spot_value_leaf_journal_v4(&alternate, SELF_IMAGE_ID).unwrap();
    assert_ne!(
        baseline.structural().scope().public_policy_hash(),
        alternate.structural().scope().public_policy_hash()
    );
    assert_ne!(
        baseline.canonical_hash().unwrap(),
        alternate.canonical_hash().unwrap()
    );
}

#[test]
fn structural_and_semantic_leaf_substitution_rejects() {
    let left = journal(1, 10);
    let right = journal(2, 11);
    let mixed = NodeJournalV4::new(NodeJournalInputV4 {
        structural: left.structural().clone(),
        semantic_subtree: right.semantic_subtree().clone(),
        application_statement_hash: right.application_statement_hash(),
        proof_profile_id: right.proof_profile_id(),
        actual_program_id: right.actual_program_id(),
        proof_system_id: right.proof_system_id(),
        receipt_security_profile_id: right.receipt_security_profile_id(),
        verifier_parameters_root: right.verifier_parameters_root(),
        program_manifest_root: right.program_manifest_root(),
        child_semantic_journal_hashes: vec![],
    })
    .unwrap();

    assert!(matches!(
        validate_authenticated_spot_value_leaf_journal_v4(&mixed, SELF_IMAGE_ID),
        Err(VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(
            SpotValueLeafIdentityFieldV4::AdapterSemanticBinding
                | SpotValueLeafIdentityFieldV4::LeafRecordBinding
        ))
    ));
}

#[test]
fn every_duplicated_structural_commitment_in_the_leaf_record_is_bound() {
    let baseline = journal(1, 10);
    let foreign = CommitmentV3::new(root(240)).unwrap();
    let candidates = [
        with_mutated_leaf_record(&baseline, |record| {
            record.pre_state_vector_root = foreign;
        }),
        with_mutated_leaf_record(&baseline, |record| {
            record.post_state_vector_root = foreign;
        }),
        with_mutated_leaf_record(&baseline, |record| {
            record.effect_root = foreign;
        }),
        with_mutated_leaf_record(&baseline, |record| {
            record.asset_delta_root = foreign;
        }),
    ];

    for candidate in candidates {
        assert_eq!(
            validate_authenticated_spot_value_leaf_journal_v4(&candidate, SELF_IMAGE_ID),
            Err(VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(
                SpotValueLeafIdentityFieldV4::LeafRecordBinding
            ))
        );
    }
}

#[test]
fn receipt_boundary_rejects_empty_oversized_zero_image_and_fake_receipts() {
    assert_eq!(
        AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(&[], SELF_IMAGE_ID)
            .err(),
        Some(VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::EmptyReceiptBytes
        ))
    );
    let oversized = vec![0; MAX_CANONICAL_RECEIPT_BYTES_V3 + 1];
    assert_eq!(
        AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(
            &oversized,
            SELF_IMAGE_ID,
        )
        .err(),
        Some(VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptBytesTooLarge {
                actual: MAX_CANONICAL_RECEIPT_BYTES_V3 + 1,
                maximum: MAX_CANONICAL_RECEIPT_BYTES_V3,
            }
        ))
    );
    assert_eq!(
        AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(b"{}", [0; 8]).err(),
        Some(VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ZeroExpectedImageId
        ))
    );

    let receipt = Receipt::try_from(FakeReceipt::new(ReceiptClaim::ok(
        SELF_IMAGE_ID,
        zenodex_zrpf_protocol_v3::encode_node_journal_v4(&journal(1, 10)).unwrap(),
    )))
    .unwrap();
    let bytes = serde_json::to_vec(&receipt).unwrap();
    assert_eq!(
        AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(
            &bytes,
            SELF_IMAGE_ID,
        )
        .err(),
        Some(VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::NonSuccinctReceipt
        ))
    );
}

#[test]
fn receipt_profile_constants_match_the_v4_committed_profile() {
    assert_eq!(
        ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
        RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1
    );
    assert_eq!(RECEIPT_KIND_SUCCINCT_V1, RISC0_SUCCINCT_RECEIPT_KIND_V1);
    assert_eq!(
        RECEIPT_HASHFN_POSEIDON2_V1,
        RISC0_RECEIPT_HASHFN_POSEIDON2_V1
    );
    assert_eq!(
        RECEIPT_VERIFIER_PARAMETERS_V1,
        hex32(RISC0_VERIFIER_PARAMETERS_DIGEST_V1)
    );
    assert_eq!(RECEIPT_CONTROL_ID_V1, hex32(RISC0_RESOLVE_CONTROL_ID_V1));
}

#[test]
fn verifier_reject_codes_and_identity_fields_are_stable_and_unique() {
    let errors = [
        VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
        ),
        VerifiedSpotValueLeafReceiptErrorV4::JournalDecodeFailed,
        VerifiedSpotValueLeafReceiptErrorV4::ProgramIdMismatch,
        VerifiedSpotValueLeafReceiptErrorV4::GovernedDerivationFailed(
            SpotValueLeafIdentityFieldV4::LeafShape,
        ),
        VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(
            SpotValueLeafIdentityFieldV4::LeafShape,
        ),
        VerifiedSpotValueLeafReceiptErrorV4::ClaimBindingFailed,
        VerifiedSpotValueLeafReceiptErrorV4::ExpectedJournalEncodingFailed,
        VerifiedSpotValueLeafReceiptErrorV4::JournalBytesMismatch,
    ];
    let codes = errors
        .iter()
        .map(|error| error.code())
        .collect::<BTreeSet<_>>();
    assert_eq!(codes.len(), errors.len());

    let fields = [
        SpotValueLeafIdentityFieldV4::LeafShape,
        SpotValueLeafIdentityFieldV4::AdapterProgramId,
        SpotValueLeafIdentityFieldV4::AdapterProfileId,
        SpotValueLeafIdentityFieldV4::AdapterManifestRoot,
        SpotValueLeafIdentityFieldV4::AdapterCountUnitId,
        SpotValueLeafIdentityFieldV4::AdapterSemanticBinding,
        SpotValueLeafIdentityFieldV4::LeafRecordBinding,
        SpotValueLeafIdentityFieldV4::ProofProfileId,
        SpotValueLeafIdentityFieldV4::ProofSystemId,
        SpotValueLeafIdentityFieldV4::ReceiptSecurityProfileId,
        SpotValueLeafIdentityFieldV4::VerifierParametersRoot,
        SpotValueLeafIdentityFieldV4::ProgramManifestRoot,
        SpotValueLeafIdentityFieldV4::ApplicationStatementHash,
    ];
    let names = fields
        .iter()
        .map(ToString::to_string)
        .collect::<BTreeSet<_>>();
    assert_eq!(names.len(), fields.len());
}
