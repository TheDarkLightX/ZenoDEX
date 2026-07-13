use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_epoch_certificate_v1, encode_settlement_epoch_certificate_v1,
    ApplicationIdV3, CommitmentV3, DomainIdV3, ProfileIdV3, SettlementEpochCertificateErrorV1,
    SettlementEpochCertificateInputV1, SettlementEpochCertificateV1, SettlementSemanticRootV1,
    MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1, SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
};

const JOURNAL_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.settlement_epoch_certificate_journal.v1";

fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

fn certificate_input() -> SettlementEpochCertificateInputV1 {
    SettlementEpochCertificateInputV1 {
        certificate_version: SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
        application_id: ApplicationIdV3::new(bytes(1)).unwrap(),
        chain_or_domain_id: DomainIdV3::new(bytes(2)).unwrap(),
        epoch_id: 7,
        semantic_profile_id: ProfileIdV3::new(bytes(3)).unwrap(),
        semantic_journal_hash: commitment(4),
        semantic_claim_binding: commitment(5),
        proof_tree_root: commitment(6),
        semantic_root: SettlementSemanticRootV1::SemanticEpoch(commitment(7)),
        economic_action_batch_commitment: commitment(8),
        economic_action_ids_root: commitment(9),
        action_authorization_bindings_root: commitment(10),
        authorization_grant_spends_root: commitment(11),
        consumed_object_ids_root: commitment(12),
        settlement_effect_plan_commitment: commitment(13),
        pre_state_root: commitment(14),
        post_state_root: commitment(15),
        cell_writes_root: commitment(16),
        asset_effects_root: commitment(17),
        messages_root: commitment(18),
        carries_root: commitment(19),
        rewards_root: commitment(20),
        public_policy_hash: commitment(21),
        data_availability_certificate_root: commitment(22),
        schedule_certificate_root: commitment(23),
        carry_continuity_certificate_root: commitment(24),
        dependency_manifest_root: commitment(25),
    }
}

fn certificate() -> SettlementEpochCertificateV1 {
    SettlementEpochCertificateV1::new(certificate_input()).unwrap()
}

fn update_domain(hasher: &mut Sha256, domain: &[u8]) {
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
}

fn update_commitment(hasher: &mut Sha256, value: CommitmentV3) {
    hasher.update(value.as_bytes());
}

fn manual_journal_hash(value: &SettlementEpochCertificateV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    update_domain(&mut hasher, JOURNAL_HASH_DOMAIN_V1);
    hasher.update(value.certificate_version().to_be_bytes());
    hasher.update(value.application_id().as_bytes());
    hasher.update(value.chain_or_domain_id().as_bytes());
    hasher.update(value.epoch_id().to_be_bytes());
    hasher.update(value.semantic_profile_id().as_bytes());
    for root in [
        value.semantic_journal_hash(),
        value.semantic_claim_binding(),
        value.proof_tree_root(),
    ] {
        update_commitment(&mut hasher, root);
    }
    match value.semantic_root() {
        SettlementSemanticRootV1::SemanticEpoch(root) => {
            hasher.update([0]);
            update_commitment(&mut hasher, root);
        }
        SettlementSemanticRootV1::ValueSubtree(root) => {
            hasher.update([1]);
            update_commitment(&mut hasher, root);
        }
    }
    for root in [
        value.economic_action_batch_commitment(),
        value.economic_action_ids_root(),
        value.action_authorization_bindings_root(),
        value.authorization_grant_spends_root(),
        value.consumed_object_ids_root(),
        value.settlement_effect_plan_commitment(),
        value.pre_state_root(),
        value.post_state_root(),
        value.cell_writes_root(),
        value.asset_effects_root(),
        value.messages_root(),
        value.carries_root(),
        value.rewards_root(),
        value.public_policy_hash(),
        value.data_availability_certificate_root(),
        value.schedule_certificate_root(),
        value.carry_continuity_certificate_root(),
        value.dependency_manifest_root(),
    ] {
        update_commitment(&mut hasher, root);
    }
    hasher.finalize().into()
}

fn mutated_hash(mutate: impl FnOnce(&mut SettlementEpochCertificateInputV1)) -> CommitmentV3 {
    let mut input = certificate_input();
    mutate(&mut input);
    SettlementEpochCertificateV1::new(input)
        .unwrap()
        .canonical_journal_hash()
        .unwrap()
}

#[test]
fn canonical_journal_hash_matches_independent_fixed_width_preimage() {
    let value = certificate();
    let expected = [
        0x31, 0xfe, 0x77, 0x82, 0xd5, 0xe8, 0x82, 0xbb, 0x9f, 0xd6, 0x2e, 0xee, 0xeb, 0x39, 0x3a,
        0xc1, 0x09, 0x46, 0xb7, 0xe1, 0x5b, 0xc3, 0xa5, 0xa6, 0x9c, 0x51, 0xc8, 0xa0, 0x50, 0x67,
        0x1b, 0x9e,
    ];

    assert_eq!(
        value.canonical_journal_hash().unwrap().into_bytes(),
        manual_journal_hash(&value)
    );
    assert_eq!(manual_journal_hash(&value), expected);
}

#[test]
fn every_fixed_field_and_semantic_root_kind_changes_the_journal_hash() {
    let baseline = certificate().canonical_journal_hash().unwrap();
    let mutations = [
        mutated_hash(|v| v.application_id = ApplicationIdV3::new(bytes(240)).unwrap()),
        mutated_hash(|v| v.chain_or_domain_id = DomainIdV3::new(bytes(240)).unwrap()),
        mutated_hash(|v| v.epoch_id += 1),
        mutated_hash(|v| v.semantic_profile_id = ProfileIdV3::new(bytes(240)).unwrap()),
        mutated_hash(|v| v.semantic_journal_hash = commitment(240)),
        mutated_hash(|v| v.semantic_claim_binding = commitment(240)),
        mutated_hash(|v| v.proof_tree_root = commitment(240)),
        mutated_hash(|v| v.semantic_root = SettlementSemanticRootV1::ValueSubtree(commitment(7))),
        mutated_hash(|v| v.economic_action_batch_commitment = commitment(240)),
        mutated_hash(|v| v.economic_action_ids_root = commitment(240)),
        mutated_hash(|v| v.action_authorization_bindings_root = commitment(240)),
        mutated_hash(|v| v.authorization_grant_spends_root = commitment(240)),
        mutated_hash(|v| v.consumed_object_ids_root = commitment(240)),
        mutated_hash(|v| v.settlement_effect_plan_commitment = commitment(240)),
        mutated_hash(|v| v.pre_state_root = commitment(240)),
        mutated_hash(|v| v.post_state_root = commitment(240)),
        mutated_hash(|v| v.cell_writes_root = commitment(240)),
        mutated_hash(|v| v.asset_effects_root = commitment(240)),
        mutated_hash(|v| v.messages_root = commitment(240)),
        mutated_hash(|v| v.carries_root = commitment(240)),
        mutated_hash(|v| v.rewards_root = commitment(240)),
        mutated_hash(|v| v.public_policy_hash = commitment(240)),
        mutated_hash(|v| v.data_availability_certificate_root = commitment(240)),
        mutated_hash(|v| v.schedule_certificate_root = commitment(240)),
        mutated_hash(|v| v.carry_continuity_certificate_root = commitment(240)),
        mutated_hash(|v| v.dependency_manifest_root = commitment(240)),
    ];

    assert!(mutations.into_iter().all(|value| value != baseline));
}

#[test]
fn exact_codec_round_trips_both_closed_semantic_root_variants() {
    for semantic_root in [
        SettlementSemanticRootV1::SemanticEpoch(commitment(7)),
        SettlementSemanticRootV1::ValueSubtree(commitment(26)),
    ] {
        let mut input = certificate_input();
        input.epoch_id = u64::MAX;
        input.semantic_root = semantic_root;
        let value = SettlementEpochCertificateV1::new(input).unwrap();
        let encoded = encode_settlement_epoch_certificate_v1(&value).unwrap();

        assert!(!encoded.is_empty());
        assert!(encoded.len() <= MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1);
        assert_eq!(
            decode_exact_settlement_epoch_certificate_v1(&encoded),
            Ok(value)
        );
    }
}

#[test]
fn unchanged_state_scope_rejects_before_a_certificate_exists() {
    let mut input = certificate_input();
    input.post_state_root = input.pre_state_root;

    assert_eq!(
        SettlementEpochCertificateV1::new(input),
        Err(SettlementEpochCertificateErrorV1::UnchangedStateRoot)
    );
}

#[test]
fn exact_codec_rejects_empty_truncated_trailing_oversized_and_nonminimal_bytes() {
    assert_eq!(
        decode_exact_settlement_epoch_certificate_v1(&[]),
        Err(SettlementEpochCertificateErrorV1::EmptyInput)
    );
    let encoded = encode_settlement_epoch_certificate_v1(&certificate()).unwrap();
    for end in 1..encoded.len() {
        assert!(decode_exact_settlement_epoch_certificate_v1(&encoded[..end]).is_err());
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_settlement_epoch_certificate_v1(&trailing),
        Err(SettlementEpochCertificateErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_settlement_epoch_certificate_v1(&vec![
            0;
            MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1
                + 1
        ]),
        Err(SettlementEpochCertificateErrorV1::InputTooLarge { .. })
    ));

    assert_eq!(encoded[0], 1);
    let mut nonminimal_version = vec![0x81, 0x00];
    nonminimal_version.extend_from_slice(&encoded[1..]);
    assert!(matches!(
        decode_exact_settlement_epoch_certificate_v1(&nonminimal_version),
        Err(SettlementEpochCertificateErrorV1::PostcardDecode
            | SettlementEpochCertificateErrorV1::NonCanonicalEncoding)
    ));
}

#[test]
fn stale_unknown_zero_scope_and_zero_root_wire_values_reject() {
    let mut stale = certificate_input();
    stale.certificate_version += 1;
    assert_eq!(
        SettlementEpochCertificateV1::new(stale.clone()),
        Err(SettlementEpochCertificateErrorV1::InvalidVersion(2))
    );
    let stale_bytes = postcard::to_allocvec(&stale).unwrap();
    assert!(decode_exact_settlement_epoch_certificate_v1(&stale_bytes).is_err());

    let value = certificate();
    let mut unknown = serde_json::to_value(value).unwrap();
    unknown["runtime_image_id"] = serde_json::json!(vec![9_u8; 32]);
    assert!(serde_json::from_value::<SettlementEpochCertificateV1>(unknown).is_err());

    let mut unknown_root_kind = serde_json::to_value(certificate()).unwrap();
    unknown_root_kind["semantic_root"] =
        serde_json::json!({"future_semantic_root": vec![9_u8; 32]});
    assert!(serde_json::from_value::<SettlementEpochCertificateV1>(unknown_root_kind).is_err());

    for field in ["application_id", "post_state_root"] {
        let mut zero = serde_json::to_value(certificate()).unwrap();
        zero[field] = serde_json::json!(vec![0_u8; 32]);
        assert!(serde_json::from_value::<SettlementEpochCertificateV1>(zero).is_err());
    }
}
