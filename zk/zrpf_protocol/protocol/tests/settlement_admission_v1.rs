use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_admission_journal_v1, encode_settlement_admission_journal_v1,
    encode_settlement_effect_plan_v2, encode_settlement_epoch_certificate_v1, ApplicationIdV3,
    AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2, AuthorizationGrantIdV1,
    AuthorizationScopeIdV1, AuthorizationSubjectIdV1, AuthorizedEconomicActionV1, CommitmentV3,
    DomainIdV3, EconomicActionBatchV1, EconomicActionRecordInputV1, EconomicActionRecordV1,
    EconomicActionTypeIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2, ProfileIdV3,
    SettlementAdmissionJournalErrorV1, SettlementAdmissionJournalV1, SettlementEffectPlanInputV2,
    SettlementEffectPlanV2, SettlementEpochCertificateInputV1, SettlementEpochCertificateV1,
    SettlementSemanticRootV1, ValueHashV2, MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
    SETTLEMENT_ADMISSION_FIXED_BYTES_V1, SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1,
    SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1, SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
};

const CERTIFICATE_ID_DOMAIN_V1: &[u8] = b"zenodex.zrpf.settlement_certificate_id.v1";
const HEADER_BYTES: usize = 22;
const BASELINE_TEST_NONCE_LABEL: &[u8] = b"base-action-nonce";
const DISTINCT_TEST_NONCE_LABEL: &[u8] = b"first-action-nonce";

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn deterministic_test_nonce(label: &[u8]) -> u64 {
    u64::try_from(label.len()).unwrap()
}

fn action(
    nonce: u64,
    semantics: u8,
    effect: u8,
    consumed: Vec<CommitmentV3>,
) -> AuthorizedEconomicActionV1 {
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        action_type_id: EconomicActionTypeIdV1::new([3; 32]).unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([4; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([5; 32]).unwrap(),
        authorization_nonce: nonce,
        valid_from_epoch: 20,
        valid_through_epoch: 30,
        pre_state_root: commitment(6),
        action_semantics_hash: commitment(semantics),
        effect_commitment: commitment(effect),
        consumed_object_ids: consumed,
    })
    .unwrap();
    AuthorizedEconomicActionV1::new(
        record,
        AuthorizationGrantIdV1::new([u8::try_from(nonce).unwrap(); 32]).unwrap(),
    )
    .unwrap()
}

fn write(action: &AuthorizedEconomicActionV1, seed: u8) -> LedgerCellWriteV2 {
    LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: action.action_id().unwrap(),
        cell_key: commitment(seed),
        pre_value_hash: ValueHashV2::new([seed.wrapping_add(1); 32]),
        post_value_hash: ValueHashV2::new([seed.wrapping_add(2); 32]),
    })
    .unwrap()
}

fn effect(action: &AuthorizedEconomicActionV1, seed: u8, amount: u128) -> AssetEffectV2 {
    AssetEffectV2::new(AssetEffectInputV2 {
        kind: AssetEffectKindV2::OrdinaryTransfer,
        economic_action_id: action.action_id().unwrap(),
        asset_id: commitment(seed),
        debit_atoms: amount,
        credit_atoms: amount,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_scope_id: None,
        action_authorization_binding: None,
    })
    .unwrap()
}

fn plan() -> SettlementEffectPlanV2 {
    let first_nonce = deterministic_test_nonce(BASELINE_TEST_NONCE_LABEL);
    let second_nonce = deterministic_test_nonce(DISTINCT_TEST_NONCE_LABEL);
    assert_ne!(first_nonce, second_nonce);
    let first = action(first_nonce, 7, 8, vec![commitment(60), commitment(61)]);
    let second = action(second_nonce, 9, 10, vec![commitment(62)]);
    let batch =
        EconomicActionBatchV1::new(25, commitment(6), vec![second.clone(), first.clone()]).unwrap();
    SettlementEffectPlanV2::new(SettlementEffectPlanInputV2 {
        source_semantic_journal_hash: commitment(50),
        public_policy_hash: commitment(51),
        post_state_root: commitment(52),
        economic_action_batch: batch,
        ledger_cell_writes: vec![write(&second, 31), write(&first, 30)],
        asset_effects: vec![effect(&second, 41, 11), effect(&first, 40, 10)],
        message_effects: Vec::new(),
        carry_effects: Vec::new(),
        reward_effects: Vec::new(),
    })
    .unwrap()
}

fn certificate_input(plan: &SettlementEffectPlanV2) -> SettlementEpochCertificateInputV1 {
    let batch = plan.economic_action_batch();
    SettlementEpochCertificateInputV1 {
        certificate_version: SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
        application_id: batch.application_id(),
        chain_or_domain_id: batch.chain_or_domain_id(),
        epoch_id: batch.epoch_id(),
        semantic_profile_id: ProfileIdV3::new([70; 32]).unwrap(),
        semantic_journal_hash: plan.source_semantic_journal_hash(),
        semantic_claim_binding: commitment(71),
        proof_tree_root: commitment(72),
        semantic_root: SettlementSemanticRootV1::ValueSubtree(commitment(73)),
        economic_action_batch_commitment: batch.canonical_commitment().unwrap(),
        economic_action_ids_root: batch.action_ids_root(),
        action_authorization_bindings_root: batch.action_authorization_bindings_root(),
        authorization_grant_spends_root: batch.authorization_grant_spends_root(),
        consumed_object_ids_root: batch.consumed_object_ids_root(),
        settlement_effect_plan_commitment: plan.canonical_commitment().unwrap(),
        pre_state_root: batch.pre_state_root(),
        post_state_root: plan.post_state_root(),
        cell_writes_root: plan.cell_writes_root(),
        asset_effects_root: plan.asset_effects_root(),
        messages_root: plan.message_effects_root(),
        carries_root: plan.carry_effects_root(),
        rewards_root: plan.reward_effects_root(),
        public_policy_hash: plan.public_policy_hash(),
        data_availability_certificate_root: commitment(74),
        schedule_certificate_root: commitment(75),
        carry_continuity_certificate_root: commitment(76),
        dependency_manifest_root: commitment(77),
    }
}

fn certificate(plan: &SettlementEffectPlanV2) -> SettlementEpochCertificateV1 {
    SettlementEpochCertificateV1::new(certificate_input(plan)).unwrap()
}

fn fixture() -> (
    SettlementEpochCertificateV1,
    SettlementEffectPlanV2,
    SettlementAdmissionJournalV1,
) {
    let plan = plan();
    let certificate = certificate(&plan);
    let journal = SettlementAdmissionJournalV1::derive(&certificate, &plan).unwrap();
    (certificate, plan, journal)
}

fn write_u16(bytes: &mut Vec<u8>, value: u16) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn write_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn write_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn write_commitment(bytes: &mut Vec<u8>, value: CommitmentV3) {
    bytes.extend_from_slice(value.as_bytes());
}

fn manual_encode(journal: &SettlementAdmissionJournalV1) -> Vec<u8> {
    let total = SETTLEMENT_ADMISSION_FIXED_BYTES_V1
        + journal.certificate_bytes().len()
        + journal.effect_plan_bytes().len();
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1);
    write_u16(&mut bytes, SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1);
    write_u32(&mut bytes, u32::try_from(total).unwrap());
    write_u32(
        &mut bytes,
        u32::try_from(journal.certificate_bytes().len()).unwrap(),
    );
    write_u32(
        &mut bytes,
        u32::try_from(journal.effect_plan_bytes().len()).unwrap(),
    );
    bytes.extend_from_slice(journal.certificate_bytes());
    bytes.extend_from_slice(journal.effect_plan_bytes());
    bytes.extend_from_slice(&journal.certificate_sha256());
    bytes.extend_from_slice(&journal.effect_plan_sha256());
    write_u16(&mut bytes, journal.certificate_version());
    write_u16(&mut bytes, journal.effect_plan_version());
    bytes.extend_from_slice(journal.application_id().as_bytes());
    bytes.extend_from_slice(journal.chain_or_domain_id().as_bytes());
    write_u64(&mut bytes, journal.epoch_id());
    bytes.extend_from_slice(journal.semantic_profile_id().as_bytes());
    for root in [
        journal.semantic_journal_hash(),
        journal.semantic_claim_binding(),
        journal.proof_tree_root(),
    ] {
        write_commitment(&mut bytes, root);
    }
    match journal.semantic_root() {
        SettlementSemanticRootV1::SemanticEpoch(root) => {
            bytes.push(0);
            write_commitment(&mut bytes, root);
        }
        SettlementSemanticRootV1::ValueSubtree(root) => {
            bytes.push(1);
            write_commitment(&mut bytes, root);
        }
    }
    for root in [
        journal.dependency_manifest_root(),
        journal.public_policy_hash(),
        journal.economic_action_batch_commitment(),
        journal.settlement_effect_plan_commitment(),
        journal.economic_action_ids_root(),
        journal.action_authorization_bindings_root(),
        journal.authorization_grant_spends_root(),
        journal.consumed_object_ids_root(),
    ] {
        write_commitment(&mut bytes, root);
    }
    write_u32(&mut bytes, journal.action_count());
    write_u32(&mut bytes, journal.consumed_object_count());
    for root in [
        journal.pre_state_root(),
        journal.post_state_root(),
        journal.cell_writes_root(),
        journal.asset_effects_root(),
        journal.messages_root(),
        journal.carries_root(),
        journal.rewards_root(),
        journal.data_availability_certificate_root(),
        journal.schedule_certificate_root(),
        journal.carry_continuity_certificate_root(),
        journal.settlement_certificate_id(),
        journal.certificate_commitment(),
    ] {
        write_commitment(&mut bytes, root);
    }
    assert_eq!(bytes.len(), total);
    bytes
}

fn manual_certificate_id(certificate_bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(
        u16::try_from(CERTIFICATE_ID_DOMAIN_V1.len())
            .unwrap()
            .to_be_bytes(),
    );
    hasher.update(CERTIFICATE_ID_DOMAIN_V1);
    hasher.update(
        u32::try_from(certificate_bytes.len())
            .unwrap()
            .to_be_bytes(),
    );
    hasher.update(certificate_bytes);
    hasher.finalize().into()
}

#[test]
fn derived_journal_binds_exact_objects_counts_and_admission_fields() {
    let (certificate, plan, journal) = fixture();
    assert_eq!(journal.action_count(), 2);
    assert_eq!(journal.consumed_object_count(), 3);
    assert_eq!(
        journal.certificate_bytes(),
        encode_settlement_epoch_certificate_v1(&certificate).unwrap()
    );
    assert_eq!(
        journal.effect_plan_bytes(),
        encode_settlement_effect_plan_v2(&plan).unwrap()
    );
    assert_eq!(
        journal.pre_state_root(),
        plan.economic_action_batch().pre_state_root()
    );
    assert_eq!(journal.post_state_root(), plan.post_state_root());
    assert_eq!(
        journal.settlement_certificate_id().into_bytes(),
        manual_certificate_id(journal.certificate_bytes())
    );
    assert_eq!(
        journal.certificate_commitment(),
        certificate.canonical_journal_hash().unwrap()
    );
    assert_eq!(journal.data_availability_certificate_root(), commitment(74));
    assert_eq!(journal.schedule_certificate_root(), commitment(75));
    assert_eq!(journal.carry_continuity_certificate_root(), commitment(76));
}

#[test]
fn fixed_width_frame_matches_independent_golden_vector() {
    let (_, _, journal) = fixture();
    let encoded = encode_settlement_admission_journal_v1(&journal).unwrap();
    assert_eq!(encoded, manual_encode(&journal));
    assert_eq!(encoded.len(), 3_407);
    assert_eq!(
        Sha256::digest(&encoded).as_slice(),
        &[
            0x17, 0xa8, 0x8a, 0x15, 0x90, 0xf1, 0x60, 0x66, 0x0c, 0xfd, 0xfe, 0xeb, 0x14, 0x3d,
            0x7c, 0xd5, 0x38, 0x01, 0xc0, 0x40, 0x83, 0xc4, 0xa1, 0x87, 0xba, 0x28, 0xe6, 0x2e,
            0x6e, 0x70, 0x41, 0x72,
        ]
    );
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&encoded),
        Ok(journal)
    );
}

#[test]
fn every_certificate_to_plan_disagreement_rejects_before_journal_construction() {
    type Mutation = fn(&mut SettlementEpochCertificateInputV1);
    let plan = plan();
    let cases: [(&str, Mutation); 18] = [
        ("application_id", |value| {
            value.application_id = ApplicationIdV3::new([90; 32]).unwrap()
        }),
        ("chain_or_domain_id", |value| {
            value.chain_or_domain_id = DomainIdV3::new([90; 32]).unwrap()
        }),
        ("epoch_id", |value| value.epoch_id += 1),
        ("semantic_journal_hash", |value| {
            value.semantic_journal_hash = commitment(90)
        }),
        ("economic_action_batch_commitment", |value| {
            value.economic_action_batch_commitment = commitment(90)
        }),
        ("economic_action_ids_root", |value| {
            value.economic_action_ids_root = commitment(90)
        }),
        ("action_authorization_bindings_root", |value| {
            value.action_authorization_bindings_root = commitment(90)
        }),
        ("authorization_grant_spends_root", |value| {
            value.authorization_grant_spends_root = commitment(90)
        }),
        ("consumed_object_ids_root", |value| {
            value.consumed_object_ids_root = commitment(90)
        }),
        ("settlement_effect_plan_commitment", |value| {
            value.settlement_effect_plan_commitment = commitment(90)
        }),
        ("pre_state_root", |value| {
            value.pre_state_root = commitment(90)
        }),
        ("post_state_root", |value| {
            value.post_state_root = commitment(90)
        }),
        ("cell_writes_root", |value| {
            value.cell_writes_root = commitment(90)
        }),
        ("asset_effects_root", |value| {
            value.asset_effects_root = commitment(90)
        }),
        ("messages_root", |value| {
            value.messages_root = commitment(90)
        }),
        ("carries_root", |value| value.carries_root = commitment(90)),
        ("rewards_root", |value| value.rewards_root = commitment(90)),
        ("public_policy_hash", |value| {
            value.public_policy_hash = commitment(90)
        }),
    ];
    for (field, mutate) in cases {
        let mut input = certificate_input(&plan);
        mutate(&mut input);
        let certificate = SettlementEpochCertificateV1::new(input).unwrap();
        assert_eq!(
            SettlementAdmissionJournalV1::derive(&certificate, &plan),
            Err(SettlementAdmissionJournalErrorV1::CertificatePlanMismatch(
                field
            ))
        );
    }
}

#[test]
fn exact_decoder_rejects_outer_framing_hash_and_duplicate_field_mutations() {
    let (_, _, journal) = fixture();
    let encoded = encode_settlement_admission_journal_v1(&journal).unwrap();
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&[]),
        Err(SettlementAdmissionJournalErrorV1::EmptyInput)
    );
    let mut truncated = encoded.clone();
    truncated.pop();
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&truncated),
        Err(SettlementAdmissionJournalErrorV1::TruncatedInput)
    );
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&trailing),
        Err(SettlementAdmissionJournalErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_settlement_admission_journal_v1(&vec![
            0;
            MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1
                + 1
        ]),
        Err(SettlementAdmissionJournalErrorV1::InputTooLarge { .. })
    ));

    let mut wrong_magic = encoded.clone();
    wrong_magic[0] ^= 1;
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&wrong_magic),
        Err(SettlementAdmissionJournalErrorV1::InvalidMagic)
    );
    let mut wrong_version = encoded.clone();
    wrong_version[8..10].copy_from_slice(&2_u16.to_be_bytes());
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&wrong_version),
        Err(SettlementAdmissionJournalErrorV1::InvalidVersion(2))
    );
    let mut wrong_inner_length = encoded.clone();
    let certificate_len = u32::try_from(journal.certificate_bytes().len()).unwrap();
    wrong_inner_length[14..18].copy_from_slice(&(certificate_len + 1).to_be_bytes());
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&wrong_inner_length),
        Err(SettlementAdmissionJournalErrorV1::FrameLengthMismatch)
    );

    let certificate_len = journal.certificate_bytes().len();
    let plan_len = journal.effect_plan_bytes().len();
    let certificate_hash_offset = HEADER_BYTES + certificate_len + plan_len;
    let mut certificate_hash_mutation = encoded.clone();
    certificate_hash_mutation[certificate_hash_offset] ^= 1;
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&certificate_hash_mutation),
        Err(SettlementAdmissionJournalErrorV1::CertificateHashMismatch)
    );
    let mut plan_hash_mutation = encoded.clone();
    plan_hash_mutation[certificate_hash_offset + 32] ^= 1;
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&plan_hash_mutation),
        Err(SettlementAdmissionJournalErrorV1::EffectPlanHashMismatch)
    );
    let mut duplicated_field_mutation = encoded.clone();
    let last = duplicated_field_mutation.last_mut().unwrap();
    *last ^= 1;
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&duplicated_field_mutation),
        Err(SettlementAdmissionJournalErrorV1::DuplicatedFieldMismatch)
    );
}

#[test]
fn decoder_revalidates_inner_certificate_canonicality_and_duplicated_fields() {
    let (certificate, _, journal) = fixture();
    let encoded = encode_settlement_admission_journal_v1(&journal).unwrap();
    let certificate_len = journal.certificate_bytes().len();
    let plan_len = journal.effect_plan_bytes().len();

    let mut alternative_input = certificate.to_input();
    alternative_input.semantic_claim_binding = commitment(99);
    let alternative = SettlementEpochCertificateV1::new(alternative_input).unwrap();
    let alternative_bytes = encode_settlement_epoch_certificate_v1(&alternative).unwrap();
    assert_eq!(alternative_bytes.len(), certificate_len);
    let mut duplicate_mismatch = encoded.clone();
    duplicate_mismatch[HEADER_BYTES..HEADER_BYTES + certificate_len]
        .copy_from_slice(&alternative_bytes);
    let certificate_hash_offset = HEADER_BYTES + certificate_len + plan_len;
    duplicate_mismatch[certificate_hash_offset..certificate_hash_offset + 32]
        .copy_from_slice(&Sha256::digest(&alternative_bytes));
    assert_eq!(
        decode_exact_settlement_admission_journal_v1(&duplicate_mismatch),
        Err(SettlementAdmissionJournalErrorV1::DuplicatedFieldMismatch)
    );

    let mut inner_trailing = Vec::with_capacity(encoded.len() + 1);
    inner_trailing.extend_from_slice(&encoded[..HEADER_BYTES + certificate_len]);
    inner_trailing.push(0);
    inner_trailing.extend_from_slice(&encoded[HEADER_BYTES + certificate_len..]);
    let total = u32::try_from(inner_trailing.len()).unwrap().to_be_bytes();
    inner_trailing[10..14].copy_from_slice(&total);
    let framed_certificate_len = u32::try_from(certificate_len + 1).unwrap().to_be_bytes();
    inner_trailing[14..18].copy_from_slice(&framed_certificate_len);
    let hash_offset = certificate_hash_offset + 1;
    let inner_certificate = &inner_trailing[HEADER_BYTES..HEADER_BYTES + certificate_len + 1];
    let hash = Sha256::digest(inner_certificate);
    inner_trailing[hash_offset..hash_offset + 32].copy_from_slice(&hash);
    assert!(matches!(
        decode_exact_settlement_admission_journal_v1(&inner_trailing),
        Err(SettlementAdmissionJournalErrorV1::Certificate(_))
    ));

    let plan_start = HEADER_BYTES + certificate_len;
    let plan_end = plan_start + plan_len;
    let mut plan_trailing = Vec::with_capacity(encoded.len() + 1);
    plan_trailing.extend_from_slice(&encoded[..plan_end]);
    plan_trailing.push(0);
    plan_trailing.extend_from_slice(&encoded[plan_end..]);
    let total = u32::try_from(plan_trailing.len()).unwrap().to_be_bytes();
    plan_trailing[10..14].copy_from_slice(&total);
    let framed_plan_len = u32::try_from(plan_len + 1).unwrap().to_be_bytes();
    plan_trailing[18..22].copy_from_slice(&framed_plan_len);
    let certificate_hash_offset = plan_end + 1;
    let inner_plan = &plan_trailing[plan_start..plan_end + 1];
    let plan_hash = Sha256::digest(inner_plan);
    plan_trailing[certificate_hash_offset + 32..certificate_hash_offset + 64]
        .copy_from_slice(&plan_hash);
    assert!(matches!(
        decode_exact_settlement_admission_journal_v1(&plan_trailing),
        Err(SettlementAdmissionJournalErrorV1::EffectPlan(_))
    ));
}
