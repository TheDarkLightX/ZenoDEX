use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, recursive_authority_scope_root_v1,
    recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
    RecursiveAssetDeltaRowV1, RecursiveEffectSummaryV1, RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, CommitmentV3, NodeJournalV3, MAX_NODE_JOURNAL_BYTES_V3,
};
use zenodex_zrpf_risc0_semantic_shared::{
    canonical_spot_asset_name_v1, spot_residual_application_statement_hash_v4,
    SpotMintAuthorityGrantV1, SpotRepresentedValuePolicyV1, SpotValueLeafOpeningV1,
    CANONICAL_SPOT_ASSET_NAME_BYTES_V1, MAX_SPOT_ASSET_ROWS_PER_LEAF_V1, MAX_SPOT_LANE_ID_BYTES_V1,
    MAX_SPOT_MINT_GRANTS_V1,
};
use zenodex_zrpf_risc0_shared::{
    program_id_from_risc0_words_v3, project_policy_bound_v1_journal, SourceKindV1,
    PINNED_SPOT_LEAF_IMAGE_ID_V1,
};
use zenodex_zrpf_risc0_value_node_shared::{
    decode_exact_raw_spot_value_leaf_input_v4, decode_exact_spot_value_leaf_witness_v4,
    encode_raw_spot_value_leaf_input_v4, encode_spot_value_leaf_witness_v4,
    propose_spot_value_leaf_v4, risc0_proof_system_id_v4,
    risc0_succinct_receipt_security_profile_id_v4, risc0_verifier_parameters_root_v4,
    spot_value_leaf_manifest_root_v4, spot_value_leaf_profile_id_v4, RawSpotValueLeafInputV4,
    SpotValueLeafInputErrorV4, SpotValueLeafProposalErrorV4, SpotValueLeafWitnessV4,
    MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4, MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4,
    PINNED_V1_ADAPTER_IMAGE_ID_A, RISC0_RESOLVE_CONTROL_ID_V1,
    RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1, RISC0_VERIFIER_PARAMETERS_DIGEST_V1,
    SPOT_VALUE_LEAF_INPUT_SCHEMA_V4, SPOT_VALUE_LEAF_WITNESS_SCHEMA_V4,
};

const POLICY_HASH: [u8; 32] = [80; 32];
const SELF_IMAGE_ID: [u32; 8] = [91, 92, 93, 94, 95, 96, 97, 98];
const LANE_ID: &str = "spot-value-lane-0";

struct LeafFixture {
    structural: NodeJournalV3,
    witness: SpotValueLeafWitnessV4,
    raw: RawSpotValueLeafInputV4,
}

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn ordinary_row(asset_id: [u8; 32], debit_atoms: u128) -> RecursiveAssetDeltaRowV1 {
    RecursiveAssetDeltaRowV1 {
        asset_id: canonical_spot_asset_name_v1(asset_id),
        debit_atoms,
        credit_atoms: 0,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0; 32],
    }
}

fn mint_row(asset_id: [u8; 32], atoms: u128) -> RecursiveAssetDeltaRowV1 {
    let asset_name = canonical_spot_asset_name_v1(asset_id);
    let authority_root = recursive_authority_scope_root_v1(
        POLICY_HASH,
        "spot",
        &asset_name,
        RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    )
    .unwrap();
    RecursiveAssetDeltaRowV1 {
        asset_id: asset_name,
        debit_atoms: 0,
        credit_atoms: atoms,
        authorized_mint_atoms: atoms,
        authorized_burn_atoms: 0,
        authority_root,
    }
}

fn mint_grant(asset_id: [u8; 32], cap: u128) -> SpotMintAuthorityGrantV1 {
    let asset_name = canonical_spot_asset_name_v1(asset_id);
    let authority_root = recursive_authority_scope_root_v1(
        POLICY_HASH,
        "spot",
        &asset_name,
        RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    )
    .unwrap();
    SpotMintAuthorityGrantV1::new(asset_id, authority_root, cap).unwrap()
}

fn summary(rows: &[RecursiveAssetDeltaRowV1]) -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: LANE_ID.to_owned(),
        lane_kind: "spot".to_owned(),
        chain_id: "zenodex-value-leaf-test".to_owned(),
        epoch_id: 71,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_owned(),
        risc0_image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
        statement_hash: root(1),
        pre_state_root: root(10),
        post_state_root: root(11),
        tx_root: root(21),
        evidence_root: root(2),
        receipt_root: root(3),
        accepted_receipts_root: empty_receipts,
        rejected_receipts_root: empty_receipts,
        asset_delta_root: recursive_asset_delta_root_v1(rows).unwrap(),
        cross_shard_outbox_root: empty_messages,
        cross_shard_inbox_root: empty_messages,
        write_set_root: root(4),
        public_policy_hash: POLICY_HASH,
        feature_suite_hash: root(81),
        dependency_lock_hash: root(82),
        toolchain_lock_hash: root(83),
    }
}

fn fixture() -> LeafFixture {
    fixture_with_adapter_image(PINNED_V1_ADAPTER_IMAGE_ID_A)
}

fn fixture_with_adapter_image(adapter_image_id: [u32; 8]) -> LeafFixture {
    let rows = vec![ordinary_row([0; 32], 10)];
    fixture_with_rows_and_policy(
        adapter_image_id,
        rows,
        SpotRepresentedValuePolicyV1::new(POLICY_HASH, vec![]).unwrap(),
    )
}

fn fixture_with_rows_and_policy(
    adapter_image_id: [u32; 8],
    rows: Vec<RecursiveAssetDeltaRowV1>,
    policy: SpotRepresentedValuePolicyV1,
) -> LeafFixture {
    let source = summary(&rows);
    let source_bytes = postcard::to_allocvec(&source).unwrap();
    let projection =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &source_bytes, 0, adapter_image_id)
            .unwrap();
    let semantic_opening = projection
        .source_binding
        .canonical_hash()
        .unwrap()
        .into_bytes();
    let structural = projection.journal;
    let witness = SpotValueLeafWitnessV4::new(
        semantic_opening,
        SpotValueLeafOpeningV1::new(
            LANE_ID.to_owned(),
            source.pre_state_root,
            source.post_state_root,
            rows,
        )
        .unwrap(),
        policy,
    )
    .unwrap();
    let raw = RawSpotValueLeafInputV4::new(
        SELF_IMAGE_ID,
        encode_node_journal_v3(&structural).unwrap(),
        encode_spot_value_leaf_witness_v4(&witness).unwrap(),
    )
    .unwrap();
    LeafFixture {
        structural,
        witness,
        raw,
    }
}

fn framed_hash(domain: &[u8], fields: &[&[u8]]) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    for field in fields {
        hasher.update(u32::try_from(field.len()).unwrap().to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
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
fn exact_codecs_round_trip_and_reject_every_truncated_prefix() {
    let fixture = fixture();
    let witness_bytes = encode_spot_value_leaf_witness_v4(&fixture.witness).unwrap();
    let raw_bytes = encode_raw_spot_value_leaf_input_v4(&fixture.raw).unwrap();

    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&witness_bytes).unwrap(),
        fixture.witness
    );
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&raw_bytes).unwrap(),
        fixture.raw
    );
    for end in 0..witness_bytes.len() {
        assert!(decode_exact_spot_value_leaf_witness_v4(&witness_bytes[..end]).is_err());
    }
    for end in 0..raw_bytes.len() {
        assert!(decode_exact_raw_spot_value_leaf_input_v4(&raw_bytes[..end]).is_err());
    }
}

#[test]
fn codecs_reject_trailing_oversized_zero_and_wrong_schema_inputs() {
    let fixture = fixture();
    let mut witness_bytes = encode_spot_value_leaf_witness_v4(&fixture.witness).unwrap();
    witness_bytes.push(0);
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&witness_bytes),
        Err(SpotValueLeafInputErrorV4::TrailingBytes)
    );
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&vec![0; MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 + 1]),
        Err(SpotValueLeafInputErrorV4::InputTooLarge {
            actual: MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 + 1,
            maximum: MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4,
        })
    );

    let mut raw_bytes = encode_raw_spot_value_leaf_input_v4(&fixture.raw).unwrap();
    raw_bytes.push(0);
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&raw_bytes),
        Err(SpotValueLeafInputErrorV4::TrailingBytes)
    );
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&vec![0; MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4 + 1]),
        Err(SpotValueLeafInputErrorV4::InputTooLarge {
            actual: MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4 + 1,
            maximum: MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4,
        })
    );
    assert_eq!(
        RawSpotValueLeafInputV4::new([0; 8], vec![1], vec![1]),
        Err(SpotValueLeafInputErrorV4::ZeroSelfImageId)
    );
    assert_eq!(
        RawSpotValueLeafInputV4::new(SELF_IMAGE_ID, vec![], vec![1]),
        Err(SpotValueLeafInputErrorV4::InvalidAdapterJournalLength(0))
    );
    assert_eq!(
        RawSpotValueLeafInputV4::new(SELF_IMAGE_ID, vec![1], vec![]),
        Err(SpotValueLeafInputErrorV4::InvalidWitnessLength(0))
    );

    let mut wrong_outer_schema = encode_raw_spot_value_leaf_input_v4(&fixture.raw).unwrap();
    wrong_outer_schema[..2].copy_from_slice(&(SPOT_VALUE_LEAF_INPUT_SCHEMA_V4 + 1).to_be_bytes());
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&wrong_outer_schema),
        Err(SpotValueLeafInputErrorV4::InvalidSchema(
            SPOT_VALUE_LEAF_INPUT_SCHEMA_V4 + 1
        ))
    );
    let mut wrong_witness_schema = encode_spot_value_leaf_witness_v4(&fixture.witness).unwrap();
    wrong_witness_schema[..2]
        .copy_from_slice(&(SPOT_VALUE_LEAF_WITNESS_SCHEMA_V4 + 1).to_be_bytes());
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&wrong_witness_schema),
        Err(SpotValueLeafInputErrorV4::InvalidSchema(
            SPOT_VALUE_LEAF_WITNESS_SCHEMA_V4 + 1
        ))
    );
}

#[test]
fn witness_codec_preserves_precise_lane_asset_and_utf8_rejects() {
    let fixture = fixture();
    let baseline = encode_spot_value_leaf_witness_v4(&fixture.witness).unwrap();

    let mut zero_lane = baseline.clone();
    zero_lane[34..36].copy_from_slice(&0u16.to_be_bytes());
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&zero_lane),
        Err(SpotValueLeafInputErrorV4::InvalidLaneLength(0))
    );

    let mut invalid_utf8 = baseline.clone();
    invalid_utf8[36] = 0xff;
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&invalid_utf8),
        Err(SpotValueLeafInputErrorV4::InvalidUtf8)
    );

    let row_count_offset = 36 + LANE_ID.len() + 64;
    let first_asset_length_offset = row_count_offset + 1;
    let mut zero_asset = baseline;
    zero_asset[first_asset_length_offset..first_asset_length_offset + 2]
        .copy_from_slice(&0u16.to_be_bytes());
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&zero_asset),
        Err(SpotValueLeafInputErrorV4::InvalidAssetIdLength { row: 0, length: 0 })
    );
}

#[test]
fn declared_witness_lengths_and_counts_reject_before_payload_allocation() {
    let fixture = fixture();
    let witness = encode_spot_value_leaf_witness_v4(&fixture.witness).unwrap();

    let mut zero_opening = witness.clone();
    zero_opening[2..34].fill(0);
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&zero_opening),
        Err(SpotValueLeafInputErrorV4::InvalidSemanticOpening)
    );

    let mut overlong_lane = witness.clone();
    overlong_lane[34..36].copy_from_slice(
        &u16::try_from(MAX_SPOT_LANE_ID_BYTES_V1 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&overlong_lane),
        Err(SpotValueLeafInputErrorV4::InvalidLaneLength(
            MAX_SPOT_LANE_ID_BYTES_V1 + 1
        ))
    );

    let row_count_offset = 36 + LANE_ID.len() + 64;
    let mut too_many_rows = witness.clone();
    too_many_rows[row_count_offset] = u8::try_from(MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 + 1).unwrap();
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&too_many_rows),
        Err(SpotValueLeafInputErrorV4::InvalidRowCount(
            MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 + 1
        ))
    );

    let asset_length_offset = row_count_offset + 1;
    let mut overlong_asset = witness.clone();
    overlong_asset[asset_length_offset..asset_length_offset + 2].copy_from_slice(
        &u16::try_from(CANONICAL_SPOT_ASSET_NAME_BYTES_V1 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&overlong_asset),
        Err(SpotValueLeafInputErrorV4::InvalidAssetIdLength {
            row: 0,
            length: CANONICAL_SPOT_ASSET_NAME_BYTES_V1 + 1,
        })
    );

    let mut too_many_grants = witness;
    *too_many_grants.last_mut().unwrap() = u8::try_from(MAX_SPOT_MINT_GRANTS_V1 + 1).unwrap();
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&too_many_grants),
        Err(SpotValueLeafInputErrorV4::InvalidGrantCount(
            MAX_SPOT_MINT_GRANTS_V1 + 1
        ))
    );
}

#[test]
fn declared_outer_lengths_reject_before_payload_allocation() {
    let fixture = fixture();
    let mut outer = encode_raw_spot_value_leaf_input_v4(&fixture.raw).unwrap();
    let oversized_journal = MAX_NODE_JOURNAL_BYTES_V3 + 1;
    outer[34..36].copy_from_slice(&u16::try_from(oversized_journal).unwrap().to_be_bytes());
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&outer),
        Err(SpotValueLeafInputErrorV4::InvalidAdapterJournalLength(
            oversized_journal
        ))
    );

    let mut outer = encode_raw_spot_value_leaf_input_v4(&fixture.raw).unwrap();
    let witness_length_offset = 36 + fixture.raw.adapter_journal_bytes().len();
    outer[witness_length_offset..witness_length_offset + 2].copy_from_slice(
        &u16::try_from(MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&outer),
        Err(SpotValueLeafInputErrorV4::InvalidWitnessLength(
            MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 + 1
        ))
    );
}

#[test]
fn maximum_witness_and_outer_frame_hit_the_exact_governed_caps() {
    let grants = (1..=MAX_SPOT_MINT_GRANTS_V1)
        .map(|index| {
            let asset_id = [u8::try_from(index).unwrap(); 32];
            let asset_name = canonical_spot_asset_name_v1(asset_id);
            let authority_root = recursive_authority_scope_root_v1(
                POLICY_HASH,
                "spot",
                &asset_name,
                RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
            )
            .unwrap();
            SpotMintAuthorityGrantV1::new(asset_id, authority_root, u128::MAX).unwrap()
        })
        .collect();
    let rows = (0..MAX_SPOT_ASSET_ROWS_PER_LEAF_V1)
        .map(|index| ordinary_row([u8::try_from(index + 129).unwrap(); 32], 1))
        .collect();
    let witness = SpotValueLeafWitnessV4::new(
        root(200),
        SpotValueLeafOpeningV1::new(
            "a".repeat(MAX_SPOT_LANE_ID_BYTES_V1),
            root(201),
            root(202),
            rows,
        )
        .unwrap(),
        SpotRepresentedValuePolicyV1::new(POLICY_HASH, grants).unwrap(),
    )
    .unwrap();
    let witness_bytes = encode_spot_value_leaf_witness_v4(&witness).unwrap();
    assert_eq!(witness_bytes.len(), MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4);
    assert_eq!(
        decode_exact_spot_value_leaf_witness_v4(&witness_bytes).unwrap(),
        witness
    );

    let raw = RawSpotValueLeafInputV4::new(
        SELF_IMAGE_ID,
        vec![1; MAX_NODE_JOURNAL_BYTES_V3],
        witness_bytes,
    )
    .unwrap();
    let raw_bytes = encode_raw_spot_value_leaf_input_v4(&raw).unwrap();
    assert_eq!(raw_bytes.len(), MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4);
    assert_eq!(
        decode_exact_raw_spot_value_leaf_input_v4(&raw_bytes).unwrap(),
        raw
    );
    assert_eq!(CANONICAL_SPOT_ASSET_NAME_BYTES_V1, 66);
}

#[test]
fn pure_leaf_proposal_binds_exact_structural_semantic_and_backend_identities() {
    let fixture = fixture();
    let journal = propose_spot_value_leaf_v4(&fixture.raw).unwrap();

    assert_eq!(journal.structural(), &fixture.structural);
    assert_eq!(journal.semantic_subtree().leaf_count(), 1);
    assert_eq!(
        journal.semantic_subtree().partition(),
        fixture.structural.partition()
    );
    assert_eq!(
        journal.application_statement_hash(),
        spot_residual_application_statement_hash_v4(journal.semantic_subtree()).unwrap()
    );
    assert_eq!(
        journal.actual_program_id(),
        program_id_from_risc0_words_v3(SELF_IMAGE_ID).unwrap()
    );
    assert_eq!(
        journal.proof_profile_id(),
        spot_value_leaf_profile_id_v4().unwrap()
    );
    assert_eq!(
        journal.proof_system_id(),
        risc0_proof_system_id_v4().unwrap()
    );
    assert_eq!(
        journal.receipt_security_profile_id(),
        risc0_succinct_receipt_security_profile_id_v4().unwrap()
    );
    assert_eq!(
        journal.verifier_parameters_root(),
        risc0_verifier_parameters_root_v4().unwrap()
    );
    assert_eq!(
        journal.program_manifest_root(),
        spot_value_leaf_manifest_root_v4(
            program_id_from_risc0_words_v3(SELF_IMAGE_ID).unwrap(),
            program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A).unwrap(),
        )
        .unwrap()
    );
    assert!(journal.child_semantic_journal_hashes().is_empty());
    journal.validate().unwrap();
}

#[test]
fn ordinary_leaf_codec_and_identity_vectors_are_fixed() {
    let fixture = fixture();
    let journal = propose_spot_value_leaf_v4(&fixture.raw).unwrap();

    assert_eq!(
        hex32(*journal.proof_profile_id().as_bytes()),
        "83f7cda73c7b2f144ba0eb3f63817665222d6da5f66bb76496465749c0cc86e0"
    );
    assert_eq!(
        hex32(journal.program_manifest_root().into_bytes()),
        "bd2ee75771ef77918aa53758e0236fc6edde1a61d5f56dcd4b00367111acf3b6"
    );
    assert_eq!(
        hex32(journal.semantic_statement_hash().into_bytes()),
        "10af311ba14175d52e261dad86a520ea7f68f46134bc4067c096748e21b2b0bc"
    );
    assert_eq!(
        hex32(journal.canonical_hash().unwrap().into_bytes()),
        "0f0a813fa603d2f22faa0fc0d8c1081183681ee312656cd1586ed82aa308495e"
    );
    assert_eq!(
        hex32(Sha256::digest(encode_spot_value_leaf_witness_v4(&fixture.witness).unwrap()).into()),
        "186bc337a73a59a1ebebf9f25d466f336384afbd10ba87e5a3cc71196d9cb25a"
    );
    assert_eq!(
        hex32(Sha256::digest(encode_raw_spot_value_leaf_input_v4(&fixture.raw).unwrap()).into()),
        "8eacfadf4bf004e9ceb4ac604dba33fcd098c05aaf6b480788b9c497dd9a3d2c"
    );
}

#[test]
fn locally_policy_validated_mint_preserves_exact_flow_and_authority_use() {
    let asset_id = [7; 32];
    let atoms = 41u128;
    let grant = mint_grant(asset_id, atoms);
    let expected_authority_root = grant.legacy_authority_root();
    let fixture = fixture_with_rows_and_policy(
        PINNED_V1_ADAPTER_IMAGE_ID_A,
        vec![mint_row(asset_id, atoms)],
        SpotRepresentedValuePolicyV1::new(POLICY_HASH, vec![grant]).unwrap(),
    );
    let journal = propose_spot_value_leaf_v4(&fixture.raw).unwrap();
    let subtree = journal.semantic_subtree();

    assert_eq!(subtree.asset_flows().len(), 1);
    let flow = subtree.asset_flows()[0];
    assert_eq!(flow.asset_id(), asset_id);
    assert_eq!(flow.outflow_atoms(), 0);
    assert_eq!(flow.inflow_atoms(), atoms);
    assert_eq!(flow.issued_atoms(), atoms);
    assert_eq!(flow.destroyed_atoms(), 0);
    assert_eq!(subtree.authority_uses().len(), 1);
    let authority_use = subtree.authority_uses()[0];
    assert_eq!(
        authority_use.source_claim_id(),
        subtree.leaf_records()[0].source_claim_id()
    );
    assert_eq!(authority_use.leaf_ordinal(), 0);
    assert_eq!(authority_use.asset_id(), asset_id);
    assert_eq!(authority_use.atoms(), atoms);
    assert_eq!(
        authority_use.legacy_authority_root().into_bytes(),
        expected_authority_root
    );
}

#[test]
fn caller_proposed_self_image_changes_identity_without_changing_opened_semantics() {
    let fixture = fixture();
    let alternate_image = [101, 102, 103, 104, 105, 106, 107, 108];
    let alternate_raw = RawSpotValueLeafInputV4::new(
        alternate_image,
        fixture.raw.adapter_journal_bytes().to_vec(),
        fixture.raw.witness_bytes().to_vec(),
    )
    .unwrap();
    let baseline = propose_spot_value_leaf_v4(&fixture.raw).unwrap();
    let alternate = propose_spot_value_leaf_v4(&alternate_raw).unwrap();

    assert_eq!(baseline.structural(), alternate.structural());
    assert_eq!(baseline.semantic_subtree(), alternate.semantic_subtree());
    assert_eq!(
        baseline.application_statement_hash(),
        alternate.application_statement_hash()
    );
    assert_ne!(baseline.actual_program_id(), alternate.actual_program_id());
    assert_ne!(
        baseline.program_manifest_root(),
        alternate.program_manifest_root()
    );
    assert_ne!(baseline.verifier_id(), alternate.verifier_id());
    assert_ne!(
        baseline.semantic_statement_hash(),
        alternate.semantic_statement_hash()
    );
    assert_ne!(
        baseline.canonical_hash().unwrap(),
        alternate.canonical_hash().unwrap()
    );
}

#[test]
fn wrong_adapter_identity_and_wrong_semantic_opening_reject() {
    let fixture = fixture();
    let wrong_adapter = fixture_with_adapter_image([1; 8]);
    assert!(matches!(
        propose_spot_value_leaf_v4(&wrong_adapter.raw),
        Err(SpotValueLeafProposalErrorV4::SemanticLeaf(_))
    ));

    let wrong_witness = SpotValueLeafWitnessV4::new(
        root(250),
        fixture.witness.value_opening().clone(),
        fixture.witness.policy().clone(),
    )
    .unwrap();
    let wrong_raw = RawSpotValueLeafInputV4::new(
        SELF_IMAGE_ID,
        fixture.raw.adapter_journal_bytes().to_vec(),
        encode_spot_value_leaf_witness_v4(&wrong_witness).unwrap(),
    )
    .unwrap();
    assert!(matches!(
        propose_spot_value_leaf_v4(&wrong_raw),
        Err(SpotValueLeafProposalErrorV4::SemanticLeaf(_))
    ));
}

#[test]
fn witness_asset_rows_must_open_the_adapter_committed_root() {
    let fixture = fixture();
    let wrong_witness = SpotValueLeafWitnessV4::new(
        fixture.witness.semantic_opening(),
        SpotValueLeafOpeningV1::new(
            LANE_ID.to_owned(),
            root(10),
            root(11),
            vec![ordinary_row([0; 32], 11)],
        )
        .unwrap(),
        fixture.witness.policy().clone(),
    )
    .unwrap();
    let wrong_raw = RawSpotValueLeafInputV4::new(
        SELF_IMAGE_ID,
        fixture.raw.adapter_journal_bytes().to_vec(),
        encode_spot_value_leaf_witness_v4(&wrong_witness).unwrap(),
    )
    .unwrap();

    assert!(matches!(
        propose_spot_value_leaf_v4(&wrong_raw),
        Err(SpotValueLeafProposalErrorV4::SpotValue(_))
    ));
}

#[test]
fn proof_and_receipt_profile_hashes_match_independent_framed_mirrors() {
    assert_eq!(
        risc0_proof_system_id_v4().unwrap(),
        framed_hash(
            b"zenodex.zrpf.proof_system_id.v4",
            &[b"risc0-zkvm", b"3.0.5", b"rv32im"]
        )
    );
    assert_eq!(
        risc0_succinct_receipt_security_profile_id_v4().unwrap(),
        framed_hash(
            b"zenodex.zrpf.receipt_security_profile_id.v4",
            &[
                RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1.as_bytes(),
                b"succinct",
                &RISC0_VERIFIER_PARAMETERS_DIGEST_V1,
                b"poseidon2",
                &RISC0_RESOLVE_CONTROL_ID_V1,
            ]
        )
    );
    assert_eq!(
        risc0_verifier_parameters_root_v4().unwrap().into_bytes(),
        RISC0_VERIFIER_PARAMETERS_DIGEST_V1
    );
    assert_eq!(
        hex32(risc0_proof_system_id_v4().unwrap().into_bytes()),
        "e50d53fa218d5ef299c96f4c76182d7e144bc923ad18278f030edb0b2fbb850f"
    );
    assert_eq!(
        hex32(
            risc0_succinct_receipt_security_profile_id_v4()
                .unwrap()
                .into_bytes()
        ),
        "15264e10072ca2647a9da89be4234114b372fa8920d2032133333374b2e81072"
    );
}
