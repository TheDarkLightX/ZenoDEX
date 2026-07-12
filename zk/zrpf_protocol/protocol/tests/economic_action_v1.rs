use serde::Serialize;
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_authorization_consumption_nullifier_v1,
    decode_exact_authorization_grant_spend_nullifier_v1, decode_exact_economic_action_record_v1,
    encode_authorization_consumption_nullifier_v1, encode_authorization_grant_spend_nullifier_v1,
    encode_economic_action_record_v1, ApplicationIdV3, AuthorizationConsumptionNullifierV1,
    AuthorizationGrantIdV1, AuthorizationGrantSpendNullifierV1, AuthorizationScopeIdV1,
    AuthorizationSubjectIdV1, CommitmentV3, DomainIdV3, EconomicActionErrorV1,
    EconomicActionRecordInputV1, EconomicActionRecordV1, EconomicActionTypeIdV1,
    MAX_AUTHORIZATION_GRANT_SPEND_NULLIFIER_BYTES_V1, MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
    MAX_ECONOMIC_ACTION_RECORD_BYTES_V1,
};

const ACTION_ID_DOMAIN_V1: &[u8] = b"zenodex.zrpf.economic_action_id.v1";
const NULLIFIER_DOMAIN_V1: &[u8] = b"zenodex.zrpf.authorization_consumption_nullifier.v1";
const GRANT_SPEND_NULLIFIER_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.authorization_grant_spend_nullifier.v1";

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn indexed_commitment(index: usize) -> CommitmentV3 {
    let mut bytes = [91; 32];
    bytes[28..].copy_from_slice(&(index as u32 + 1).to_be_bytes());
    CommitmentV3::new(bytes).unwrap()
}

fn base_input(consumed_object_ids: Vec<CommitmentV3>) -> EconomicActionRecordInputV1 {
    EconomicActionRecordInputV1 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        action_type_id: EconomicActionTypeIdV1::new([3; 32]).unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([4; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([5; 32]).unwrap(),
        authorization_nonce: 17,
        valid_from_epoch: 21,
        valid_through_epoch: 34,
        pre_state_root: commitment(6),
        action_semantics_hash: commitment(7),
        effect_commitment: commitment(8),
        consumed_object_ids,
    }
}

fn record(consumed_object_ids: Vec<CommitmentV3>) -> EconomicActionRecordV1 {
    EconomicActionRecordV1::new(base_input(consumed_object_ids)).unwrap()
}

fn prefixed_domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut bytes = [0; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    bytes
}

fn manual_action_id(record: &EconomicActionRecordV1) -> [u8; 32] {
    let mut hasher = prefixed_domain_hasher(ACTION_ID_DOMAIN_V1);
    hasher.update(record.record_version().to_be_bytes());
    hasher.update(record.application_id().as_bytes());
    hasher.update(record.chain_or_domain_id().as_bytes());
    hasher.update(record.action_type_id().as_bytes());
    hasher.update(record.authorization_subject_id().as_bytes());
    hasher.update(record.authorization_scope_id().as_bytes());
    hasher.update(record.authorization_nonce().to_be_bytes());
    hasher.update(record.valid_from_epoch().to_be_bytes());
    hasher.update(record.valid_through_epoch().to_be_bytes());
    hasher.update(record.pre_state_root().as_bytes());
    hasher.update(record.action_semantics_hash().as_bytes());
    hasher.update(record.effect_commitment().as_bytes());
    hasher.update(
        u32::try_from(record.consumed_object_ids().len())
            .unwrap()
            .to_be_bytes(),
    );
    for object_id in record.consumed_object_ids() {
        hasher.update(object_id.as_bytes());
    }
    hasher.finalize().into()
}

fn manual_nullifier(record: &EconomicActionRecordV1, grant_id: AuthorizationGrantIdV1) -> [u8; 32] {
    let action_id = record.canonical_id().unwrap();
    let mut hasher = prefixed_domain_hasher(NULLIFIER_DOMAIN_V1);
    hasher.update(1_u16.to_be_bytes());
    hasher.update(record.application_id().as_bytes());
    hasher.update(record.chain_or_domain_id().as_bytes());
    hasher.update(action_id.as_bytes());
    hasher.update(record.authorization_subject_id().as_bytes());
    hasher.update(grant_id.as_bytes());
    hasher.update(record.authorization_scope_id().as_bytes());
    hasher.update(record.authorization_nonce().to_be_bytes());
    hasher.update(record.pre_state_root().as_bytes());
    hasher.finalize().into()
}

fn manual_grant_spend_nullifier(
    record: &EconomicActionRecordV1,
    grant_id: AuthorizationGrantIdV1,
) -> [u8; 32] {
    let mut hasher = prefixed_domain_hasher(GRANT_SPEND_NULLIFIER_DOMAIN_V1);
    hasher.update(1_u16.to_be_bytes());
    hasher.update(record.application_id().as_bytes());
    hasher.update(record.chain_or_domain_id().as_bytes());
    hasher.update(grant_id.as_bytes());
    hasher.update(record.authorization_nonce().to_be_bytes());
    hasher.finalize().into()
}

#[derive(Clone, Copy)]
struct RepresentationNoise<'a> {
    proof_program: &'a str,
    receipt_encoding: &'a str,
    intent_salt: &'a [u8],
    signature_bytes: &'a [u8],
}

fn derive_ignoring_representation(
    record: &EconomicActionRecordV1,
    grant_id: AuthorizationGrantIdV1,
    noise: RepresentationNoise<'_>,
) -> ([u8; 32], [u8; 32], [u8; 32]) {
    core::hint::black_box((
        noise.proof_program,
        noise.receipt_encoding,
        noise.intent_salt,
        noise.signature_bytes,
    ));
    (
        record.canonical_id().unwrap().into_bytes(),
        AuthorizationConsumptionNullifierV1::derive(record, grant_id)
            .unwrap()
            .into_bytes(),
        AuthorizationGrantSpendNullifierV1::derive(record, grant_id)
            .unwrap()
            .into_bytes(),
    )
}

#[derive(Serialize)]
struct RawEconomicActionRecordV1 {
    record_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    action_type_id: EconomicActionTypeIdV1,
    authorization_subject_id: AuthorizationSubjectIdV1,
    authorization_scope_id: AuthorizationScopeIdV1,
    authorization_nonce: u64,
    valid_from_epoch: u64,
    valid_through_epoch: u64,
    pre_state_root: CommitmentV3,
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
    consumed_object_ids: Vec<CommitmentV3>,
}

fn raw_record(consumed_object_ids: Vec<CommitmentV3>) -> RawEconomicActionRecordV1 {
    let input = base_input(Vec::new());
    RawEconomicActionRecordV1 {
        record_version: 1,
        application_id: input.application_id,
        chain_or_domain_id: input.chain_or_domain_id,
        action_type_id: input.action_type_id,
        authorization_subject_id: input.authorization_subject_id,
        authorization_scope_id: input.authorization_scope_id,
        authorization_nonce: input.authorization_nonce,
        valid_from_epoch: input.valid_from_epoch,
        valid_through_epoch: input.valid_through_epoch,
        pre_state_root: input.pre_state_root,
        action_semantics_hash: input.action_semantics_hash,
        effect_commitment: input.effect_commitment,
        consumed_object_ids,
    }
}

#[test]
fn canonical_hash_preimages_match_the_independent_field_order() {
    let record = record(vec![indexed_commitment(2), indexed_commitment(0)]);
    let grant_id = AuthorizationGrantIdV1::new([9; 32]).unwrap();

    assert_eq!(
        record.canonical_id().unwrap().into_bytes(),
        manual_action_id(&record)
    );
    assert_eq!(
        AuthorizationConsumptionNullifierV1::derive(&record, grant_id)
            .unwrap()
            .into_bytes(),
        manual_nullifier(&record, grant_id)
    );
    assert_eq!(
        AuthorizationGrantSpendNullifierV1::derive(&record, grant_id)
            .unwrap()
            .into_bytes(),
        manual_grant_spend_nullifier(&record, grant_id)
    );
}

#[test]
fn canonical_hashes_match_the_shared_fixed_vector() {
    let record = record(Vec::new());
    let grant_id = AuthorizationGrantIdV1::new([9; 32]).unwrap();

    assert_eq!(
        record.canonical_id().unwrap().into_bytes(),
        hex_32("8613bdc85d4618ed79c0d927c107b4682423091f8d1856251ad9e355a6525143")
    );
    assert_eq!(
        AuthorizationConsumptionNullifierV1::derive(&record, grant_id)
            .unwrap()
            .into_bytes(),
        hex_32("03c908ee0fd74c394865c11453a51a0b059bfb35ceb62956beb00c00d49ff913")
    );
    assert_eq!(
        AuthorizationGrantSpendNullifierV1::derive(&record, grant_id)
            .unwrap()
            .into_bytes(),
        hex_32("1f5970f7f3ba7ec6dd111b488f0229256aa683c032111f950e08293c7ac63c38")
    );
}

#[test]
fn proof_receipt_salt_and_signature_representations_do_not_change_identity() {
    let record = record(vec![indexed_commitment(0), indexed_commitment(1)]);
    let grant_id = AuthorizationGrantIdV1::new([9; 32]).unwrap();
    let representations = [
        RepresentationNoise {
            proof_program: "risc0-image-a",
            receipt_encoding: "postcard-succinct-a",
            intent_salt: b"salt-a",
            signature_bytes: b"signature-a",
        },
        RepresentationNoise {
            proof_program: "sp1-program-b",
            receipt_encoding: "json-groth16-b",
            intent_salt: b"salt-b",
            signature_bytes: b"signature-b",
        },
    ];

    let first = derive_ignoring_representation(&record, grant_id, representations[0]);
    let second = derive_ignoring_representation(&record, grant_id, representations[1]);

    assert_eq!(first, second);
}

#[test]
fn consumed_objects_are_sorted_canonically_and_input_order_is_irrelevant() {
    let first = indexed_commitment(0);
    let second = indexed_commitment(1);
    let third = indexed_commitment(2);

    let unsorted = record(vec![third, first, second]);
    let sorted = record(vec![first, second, third]);

    assert_eq!(unsorted, sorted);
    assert_eq!(unsorted.consumed_object_ids(), &[first, second, third]);
    assert_eq!(unsorted.canonical_id(), sorted.canonical_id());
}

#[test]
fn duplicate_consumed_objects_reject_instead_of_collapsing() {
    let duplicate = indexed_commitment(0);

    assert_eq!(
        EconomicActionRecordV1::new(base_input(vec![duplicate, duplicate])).unwrap_err(),
        EconomicActionErrorV1::DuplicateConsumedObject
    );
}

#[test]
fn every_semantic_record_field_separates_the_action_id() {
    let baseline_input = base_input(vec![indexed_commitment(0)]);
    let baseline_id = EconomicActionRecordV1::new(baseline_input.clone())
        .unwrap()
        .canonical_id()
        .unwrap();
    let mut variants = Vec::new();

    let mut changed = baseline_input.clone();
    changed.application_id = ApplicationIdV3::new([41; 32]).unwrap();
    variants.push(("application_id", changed));
    let mut changed = baseline_input.clone();
    changed.chain_or_domain_id = DomainIdV3::new([42; 32]).unwrap();
    variants.push(("chain_or_domain_id", changed));
    let mut changed = baseline_input.clone();
    changed.action_type_id = EconomicActionTypeIdV1::new([43; 32]).unwrap();
    variants.push(("action_type_id", changed));
    let mut changed = baseline_input.clone();
    changed.authorization_subject_id = AuthorizationSubjectIdV1::new([44; 32]).unwrap();
    variants.push(("authorization_subject_id", changed));
    let mut changed = baseline_input.clone();
    changed.authorization_scope_id = AuthorizationScopeIdV1::new([45; 32]).unwrap();
    variants.push(("authorization_scope_id", changed));
    let mut changed = baseline_input.clone();
    changed.authorization_nonce += 1;
    variants.push(("authorization_nonce", changed));
    let mut changed = baseline_input.clone();
    changed.valid_from_epoch += 1;
    variants.push(("valid_from_epoch", changed));
    let mut changed = baseline_input.clone();
    changed.valid_through_epoch += 1;
    variants.push(("valid_through_epoch", changed));
    let mut changed = baseline_input.clone();
    changed.pre_state_root = commitment(46);
    variants.push(("pre_state_root", changed));
    let mut changed = baseline_input.clone();
    changed.action_semantics_hash = commitment(47);
    variants.push(("action_semantics_hash", changed));
    let mut changed = baseline_input.clone();
    changed.effect_commitment = commitment(48);
    variants.push(("effect_commitment", changed));
    let mut changed = baseline_input;
    changed.consumed_object_ids = vec![indexed_commitment(1)];
    variants.push(("consumed_object_ids", changed));

    for (field, input) in variants {
        let changed_id = EconomicActionRecordV1::new(input)
            .unwrap()
            .canonical_id()
            .unwrap();
        assert_ne!(baseline_id, changed_id, "field did not separate: {field}");
    }
}

#[test]
fn grant_and_action_separate_authorization_consumption_nullifiers() {
    let first_record = record(vec![indexed_commitment(0)]);
    let mut changed_input = base_input(vec![indexed_commitment(0)]);
    changed_input.authorization_nonce += 1;
    let second_record = EconomicActionRecordV1::new(changed_input).unwrap();
    let first_grant = AuthorizationGrantIdV1::new([9; 32]).unwrap();
    let second_grant = AuthorizationGrantIdV1::new([10; 32]).unwrap();

    let baseline = AuthorizationConsumptionNullifierV1::derive(&first_record, first_grant).unwrap();

    assert_ne!(
        baseline,
        AuthorizationConsumptionNullifierV1::derive(&first_record, second_grant).unwrap()
    );
    assert_ne!(
        baseline,
        AuthorizationConsumptionNullifierV1::derive(&second_record, first_grant).unwrap()
    );
    assert_eq!(
        baseline,
        AuthorizationConsumptionNullifierV1::derive(&first_record, first_grant).unwrap()
    );
}

#[test]
fn grant_spend_nullifier_separates_exactly_its_governed_key_fields() {
    let baseline_input = base_input(Vec::new());
    let baseline_record = EconomicActionRecordV1::new(baseline_input.clone()).unwrap();
    let first_grant = AuthorizationGrantIdV1::new([9; 32]).unwrap();
    let second_grant = AuthorizationGrantIdV1::new([10; 32]).unwrap();
    let baseline =
        AuthorizationGrantSpendNullifierV1::derive(&baseline_record, first_grant).unwrap();

    let mut changed_application = baseline_input.clone();
    changed_application.application_id = ApplicationIdV3::new([41; 32]).unwrap();
    let mut changed_domain = baseline_input.clone();
    changed_domain.chain_or_domain_id = DomainIdV3::new([42; 32]).unwrap();
    let mut changed_nonce = baseline_input;
    changed_nonce.authorization_nonce += 1;

    for changed_record in [changed_application, changed_domain, changed_nonce]
        .map(EconomicActionRecordV1::new)
        .map(Result::unwrap)
    {
        assert_ne!(
            baseline,
            AuthorizationGrantSpendNullifierV1::derive(&changed_record, first_grant).unwrap()
        );
    }
    assert_ne!(
        baseline,
        AuthorizationGrantSpendNullifierV1::derive(&baseline_record, second_grant).unwrap()
    );
}

#[test]
fn grant_spend_nullifier_blocks_action_field_aliases_for_one_grant_nonce() {
    let baseline_input = base_input(Vec::new());
    let baseline_record = EconomicActionRecordV1::new(baseline_input.clone()).unwrap();
    let grant_id = AuthorizationGrantIdV1::new([9; 32]).unwrap();
    let baseline_action_id = baseline_record.canonical_id().unwrap();
    let baseline_binding =
        AuthorizationConsumptionNullifierV1::derive(&baseline_record, grant_id).unwrap();
    let baseline_spend =
        AuthorizationGrantSpendNullifierV1::derive(&baseline_record, grant_id).unwrap();
    let mut variants = Vec::new();

    let mut changed = baseline_input.clone();
    changed.action_type_id = EconomicActionTypeIdV1::new([43; 32]).unwrap();
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.authorization_subject_id = AuthorizationSubjectIdV1::new([44; 32]).unwrap();
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.authorization_scope_id = AuthorizationScopeIdV1::new([45; 32]).unwrap();
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.valid_from_epoch += 1;
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.valid_through_epoch += 1;
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.pre_state_root = commitment(46);
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.action_semantics_hash = commitment(47);
    variants.push(changed);
    let mut changed = baseline_input.clone();
    changed.effect_commitment = commitment(48);
    variants.push(changed);
    let mut changed = baseline_input;
    changed.consumed_object_ids = vec![indexed_commitment(1)];
    variants.push(changed);

    for input in variants {
        let changed_record = EconomicActionRecordV1::new(input).unwrap();
        assert_ne!(baseline_action_id, changed_record.canonical_id().unwrap());
        assert_ne!(
            baseline_binding,
            AuthorizationConsumptionNullifierV1::derive(&changed_record, grant_id).unwrap()
        );
        assert_eq!(
            baseline_spend,
            AuthorizationGrantSpendNullifierV1::derive(&changed_record, grant_id).unwrap()
        );
    }
}

#[test]
fn constructors_enforce_zero_range_and_collection_bounds() {
    assert!(matches!(
        EconomicActionTypeIdV1::new([0; 32]),
        Err(EconomicActionErrorV1::ZeroIdentifier("action_type_id"))
    ));
    assert!(matches!(
        AuthorizationSubjectIdV1::new([0; 32]),
        Err(EconomicActionErrorV1::ZeroIdentifier(
            "authorization_subject_id"
        ))
    ));

    let mut invalid_range = base_input(Vec::new());
    invalid_range.valid_from_epoch = 35;
    invalid_range.valid_through_epoch = 34;
    assert_eq!(
        EconomicActionRecordV1::new(invalid_range).unwrap_err(),
        EconomicActionErrorV1::InvalidValidityRange
    );

    let maximum = (0..MAX_CONSUMED_OBJECTS_PER_ACTION_V1)
        .map(indexed_commitment)
        .collect::<Vec<_>>();
    assert_eq!(
        EconomicActionRecordV1::new(base_input(maximum))
            .unwrap()
            .consumed_object_ids()
            .len(),
        MAX_CONSUMED_OBJECTS_PER_ACTION_V1
    );

    let oversized = (0..=MAX_CONSUMED_OBJECTS_PER_ACTION_V1)
        .map(indexed_commitment)
        .collect();
    assert_eq!(
        EconomicActionRecordV1::new(base_input(oversized)).unwrap_err(),
        EconomicActionErrorV1::TooManyConsumedObjects {
            actual: MAX_CONSUMED_OBJECTS_PER_ACTION_V1 + 1,
            maximum: MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
        }
    );
}

#[test]
fn exact_codecs_round_trip_and_reject_trailing_oversized_and_noncanonical_bytes() {
    let first = indexed_commitment(0);
    let second = indexed_commitment(1);
    let record = record(vec![second, first]);
    let bytes = encode_economic_action_record_v1(&record).unwrap();

    assert_eq!(
        decode_exact_economic_action_record_v1(&bytes).unwrap(),
        record
    );

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_economic_action_record_v1(&trailing).unwrap_err(),
        EconomicActionErrorV1::TrailingBytes
    );
    assert!(matches!(
        decode_exact_economic_action_record_v1(&vec![0; MAX_ECONOMIC_ACTION_RECORD_BYTES_V1 + 1]),
        Err(EconomicActionErrorV1::InputTooLarge { .. })
    ));
    assert_eq!(
        decode_exact_economic_action_record_v1(&[]).unwrap_err(),
        EconomicActionErrorV1::EmptyInput
    );
    for end in 1..bytes.len() {
        assert!(decode_exact_economic_action_record_v1(&bytes[..end]).is_err());
    }

    let noncanonical = postcard::to_allocvec(&raw_record(vec![second, first])).unwrap();
    assert_eq!(
        decode_exact_economic_action_record_v1(&noncanonical).unwrap_err(),
        EconomicActionErrorV1::NonCanonicalEncoding
    );

    let mut claimed_oversized_sequence = postcard::to_allocvec(&raw_record(Vec::new())).unwrap();
    assert_eq!(claimed_oversized_sequence.pop(), Some(0));
    claimed_oversized_sequence
        .extend(postcard::to_allocvec(&(MAX_CONSUMED_OBJECTS_PER_ACTION_V1 + 1)).unwrap());
    assert!(decode_exact_economic_action_record_v1(&claimed_oversized_sequence).is_err());
}

#[test]
fn exact_nullifier_codec_rejects_zero_and_trailing_bytes() {
    let record = record(Vec::new());
    let grant_id = AuthorizationGrantIdV1::new([9; 32]).unwrap();
    let nullifier = AuthorizationConsumptionNullifierV1::derive(&record, grant_id).unwrap();
    let bytes = encode_authorization_consumption_nullifier_v1(nullifier).unwrap();

    assert_eq!(
        decode_exact_authorization_consumption_nullifier_v1(&bytes).unwrap(),
        nullifier
    );
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_authorization_consumption_nullifier_v1(&trailing).unwrap_err(),
        EconomicActionErrorV1::TrailingBytes
    );
    assert!(matches!(
        AuthorizationConsumptionNullifierV1::new([0; 32]),
        Err(EconomicActionErrorV1::ZeroIdentifier(
            "authorization_consumption_nullifier"
        ))
    ));
    let canonical = encode_authorization_consumption_nullifier_v1(nullifier).unwrap();
    for end in 1..canonical.len() {
        assert!(decode_exact_authorization_consumption_nullifier_v1(&canonical[..end]).is_err());
    }
}

#[test]
fn exact_grant_spend_nullifier_codec_is_bounded_and_fail_closed() {
    let record = record(Vec::new());
    let grant_id = AuthorizationGrantIdV1::new([9; 32]).unwrap();
    let nullifier = AuthorizationGrantSpendNullifierV1::derive(&record, grant_id).unwrap();
    let bytes = encode_authorization_grant_spend_nullifier_v1(nullifier).unwrap();

    assert_eq!(
        decode_exact_authorization_grant_spend_nullifier_v1(&bytes).unwrap(),
        nullifier
    );
    assert_eq!(
        decode_exact_authorization_grant_spend_nullifier_v1(&[]).unwrap_err(),
        EconomicActionErrorV1::EmptyInput
    );
    assert!(decode_exact_authorization_grant_spend_nullifier_v1(&[0; 32]).is_err());
    for end in 1..bytes.len() {
        assert!(decode_exact_authorization_grant_spend_nullifier_v1(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_authorization_grant_spend_nullifier_v1(&trailing).unwrap_err(),
        EconomicActionErrorV1::TrailingBytes
    );
    assert!(matches!(
        decode_exact_authorization_grant_spend_nullifier_v1(
            &[0; MAX_AUTHORIZATION_GRANT_SPEND_NULLIFIER_BYTES_V1 + 1]
        ),
        Err(EconomicActionErrorV1::InputTooLarge { .. })
    ));
    assert!(matches!(
        AuthorizationGrantSpendNullifierV1::new([0; 32]),
        Err(EconomicActionErrorV1::ZeroIdentifier(
            "authorization_grant_spend_nullifier"
        ))
    ));
}

#[test]
fn json_wire_rejects_unknown_fields_and_duplicate_consumed_objects() {
    let record = record(vec![indexed_commitment(0)]);
    let mut unknown = serde_json::to_value(&record).unwrap();
    unknown["proof_program_id"] = serde_json::json!(vec![77; 32]);
    assert!(serde_json::from_value::<EconomicActionRecordV1>(unknown).is_err());

    let duplicate = indexed_commitment(0);
    let mut duplicate_wire = serde_json::to_value(&record).unwrap();
    duplicate_wire["consumed_object_ids"] =
        serde_json::json!([duplicate.into_bytes(), duplicate.into_bytes()]);
    let error = serde_json::from_value::<EconomicActionRecordV1>(duplicate_wire).unwrap_err();
    assert!(error.to_string().contains("duplicate consumed object"));

    let mut stale_version = serde_json::to_value(&record).unwrap();
    stale_version["record_version"] = serde_json::json!(2);
    let error = serde_json::from_value::<EconomicActionRecordV1>(stale_version).unwrap_err();
    assert!(error
        .to_string()
        .contains("invalid economic action record version: 2"));
}
