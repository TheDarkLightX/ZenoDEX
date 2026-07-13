use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_value_transfer_set_v2, decode_exact_value_transfer_v2,
    encode_value_transfer_set_v2, encode_value_transfer_v2, ApplicationIdV3, CommitmentV3,
    DomainIdV3, ValueTransferErrorV2, ValueTransferInputV2, ValueTransferKindV2,
    ValueTransferSetV2, ValueTransferV2, MAX_VALUE_TRANSFERS_PER_SET_V2,
    MAX_VALUE_TRANSFER_ACTION_INDEX_V2, MAX_VALUE_TRANSFER_SET_BYTES_V2,
};

const VALUE_TRANSFER_ID_DOMAIN_V2: &[u8] = b"zenodex.zrpf.value_transfer_id.v2";
type InputMutation = fn(&mut ValueTransferInputV2);

fn commitment(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).expect("fixture commitment is nonzero")
}

fn application(byte: u8) -> ApplicationIdV3 {
    ApplicationIdV3::new([byte; 32]).expect("fixture application is nonzero")
}

fn domain(byte: u8) -> DomainIdV3 {
    DomainIdV3::new([byte; 32]).expect("fixture domain is nonzero")
}

fn input(seed: u8, action_index: u32) -> ValueTransferInputV2 {
    ValueTransferInputV2 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        epoch_id: 7,
        action_index,
        kind: ValueTransferKindV2::CollateralDeposit,
        action_hash: commitment(seed),
        source_lane_id: commitment(20),
        destination_lane_id: commitment(21),
        asset_id: commitment(22),
        amount_atoms: 500,
        sender_scope_hash: commitment(23),
        recipient_scope_hash: commitment(24),
        source_state_transition_hash: commitment(25),
        source_receipt_claim_hash: commitment(26),
        deadline_epoch: 9,
    }
}

fn transfer(seed: u8, action_index: u32) -> ValueTransferV2 {
    ValueTransferV2::new(input(seed, action_index)).expect("fixture transfer is valid")
}

#[test]
fn exact_transfer_and_set_codecs_round_trip() {
    let first = transfer(10, 0);
    let second = transfer(11, 1);
    let transfer_bytes = encode_value_transfer_v2(&first).expect("transfer encodes");
    assert_eq!(
        decode_exact_value_transfer_v2(&transfer_bytes).expect("transfer decodes"),
        first
    );

    let set = ValueTransferSetV2::new(vec![second, first]).expect("set is canonicalized");
    let set_bytes = encode_value_transfer_set_v2(&set).expect("set encodes");
    assert_eq!(
        decode_exact_value_transfer_set_v2(&set_bytes).expect("set decodes"),
        set
    );
}

#[test]
fn transfer_identity_binds_every_field() {
    let baseline_input = input(10, 0);
    let baseline = ValueTransferV2::new(baseline_input.clone())
        .expect("baseline is valid")
        .canonical_id()
        .expect("baseline ID derives");
    let mutations: [InputMutation; 15] = [
        |value| value.application_id = application(3),
        |value| value.chain_or_domain_id = domain(4),
        |value| value.epoch_id = 8,
        |value| value.action_index = 1,
        |value| value.kind = ValueTransferKindV2::CollateralWithdrawal,
        |value| value.action_hash = commitment(31),
        |value| value.source_lane_id = commitment(32),
        |value| value.destination_lane_id = commitment(33),
        |value| value.asset_id = commitment(34),
        |value| value.amount_atoms = 501,
        |value| value.sender_scope_hash = commitment(35),
        |value| value.recipient_scope_hash = commitment(36),
        |value| value.source_state_transition_hash = commitment(37),
        |value| value.source_receipt_claim_hash = commitment(38),
        |value| value.deadline_epoch = 10,
    ];
    for mutate in mutations {
        let mut changed = baseline_input.clone();
        mutate(&mut changed);
        let changed_id = ValueTransferV2::new(changed)
            .expect("field mutation remains structurally valid")
            .canonical_id()
            .expect("changed ID derives");
        assert_ne!(changed_id, baseline);
    }
}

#[test]
fn transfer_identity_matches_independent_preimage() {
    let transfer = transfer(10, 0);
    let mut hasher = Sha256::new();
    hasher.update(
        u16::try_from(VALUE_TRANSFER_ID_DOMAIN_V2.len())
            .expect("domain length fits")
            .to_be_bytes(),
    );
    hasher.update(VALUE_TRANSFER_ID_DOMAIN_V2);
    hasher.update(transfer.application_id().as_bytes());
    hasher.update(transfer.chain_or_domain_id().as_bytes());
    hasher.update(transfer.epoch_id().to_be_bytes());
    hasher.update(transfer.action_index().to_be_bytes());
    hasher.update([transfer.kind().tag()]);
    hasher.update(transfer.action_hash().as_bytes());
    hasher.update(transfer.source_lane_id().as_bytes());
    hasher.update(transfer.destination_lane_id().as_bytes());
    hasher.update(transfer.asset_id().as_bytes());
    hasher.update(transfer.amount_atoms().to_be_bytes());
    hasher.update(transfer.sender_scope_hash().as_bytes());
    hasher.update(transfer.recipient_scope_hash().as_bytes());
    hasher.update(transfer.source_state_transition_hash().as_bytes());
    hasher.update(transfer.source_receipt_claim_hash().as_bytes());
    hasher.update(transfer.deadline_epoch().to_be_bytes());
    assert_eq!(
        transfer
            .canonical_id()
            .expect("canonical transfer ID derives")
            .into_bytes(),
        <[u8; 32]>::from(hasher.finalize())
    );
}

#[test]
fn invalid_amount_route_deadline_and_action_index_reject() {
    let mut zero_amount = input(10, 0);
    zero_amount.amount_atoms = 0;
    assert_eq!(
        ValueTransferV2::new(zero_amount),
        Err(ValueTransferErrorV2::ZeroAmount)
    );

    let mut loopback = input(10, 0);
    loopback.destination_lane_id = loopback.source_lane_id;
    assert_eq!(
        ValueTransferV2::new(loopback),
        Err(ValueTransferErrorV2::InvalidRoute)
    );

    let mut stale = input(10, 0);
    stale.deadline_epoch = stale.epoch_id - 1;
    assert_eq!(
        ValueTransferV2::new(stale),
        Err(ValueTransferErrorV2::DeadlineBeforeEpoch)
    );

    let mut oversized_index = input(10, MAX_VALUE_TRANSFER_ACTION_INDEX_V2 + 1);
    assert_eq!(
        ValueTransferV2::new(oversized_index.clone()),
        Err(ValueTransferErrorV2::ActionIndexOutOfRange {
            actual: MAX_VALUE_TRANSFER_ACTION_INDEX_V2 + 1,
            maximum: MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
        })
    );
    oversized_index.action_index = MAX_VALUE_TRANSFER_ACTION_INDEX_V2;
    ValueTransferV2::new(oversized_index).expect("maximum action index is accepted");
}

#[test]
fn set_is_order_independent_and_roots_bind_sources() {
    let first = transfer(10, 0);
    let second = transfer(11, 1);
    let forward =
        ValueTransferSetV2::new(vec![first.clone(), second.clone()]).expect("forward set is valid");
    let reverse = ValueTransferSetV2::new(vec![second, first]).expect("reverse set is valid");
    assert_eq!(forward, reverse);
    assert_eq!(
        forward.canonical_root().expect("root derives"),
        reverse.canonical_root().expect("root derives")
    );

    let mut changed_source = input(11, 1);
    changed_source.source_receipt_claim_hash = commitment(90);
    let changed = ValueTransferSetV2::new(vec![
        transfer(10, 0),
        ValueTransferV2::new(changed_source).expect("changed transfer is valid"),
    ])
    .expect("changed set is valid");
    assert_ne!(
        forward.source_claims_root().expect("source root derives"),
        changed.source_claims_root().expect("source root derives")
    );
    assert_ne!(
        forward.canonical_root().expect("canonical root derives"),
        changed.canonical_root().expect("canonical root derives")
    );
}

#[test]
fn duplicate_identity_and_action_binding_reject() {
    let first = transfer(10, 0);
    assert_eq!(
        ValueTransferSetV2::new(vec![first.clone(), first]),
        Err(ValueTransferErrorV2::DuplicateTransfer)
    );

    let first = transfer(10, 0);
    let mut alternate_route = input(10, 0);
    alternate_route.destination_lane_id = commitment(40);
    let alternate_route =
        ValueTransferV2::new(alternate_route).expect("alternate route is structurally valid");
    assert_eq!(
        ValueTransferSetV2::new(vec![first, alternate_route]),
        Err(ValueTransferErrorV2::DuplicateActionBinding)
    );
}

#[test]
fn mixed_scope_and_epoch_reject() {
    let first = transfer(10, 0);
    let mut different_scope = input(11, 1);
    different_scope.application_id = application(9);
    assert_eq!(
        ValueTransferSetV2::new(vec![
            first.clone(),
            ValueTransferV2::new(different_scope).expect("record is individually valid"),
        ]),
        Err(ValueTransferErrorV2::ScopeMismatch)
    );

    let mut different_epoch = input(11, 1);
    different_epoch.epoch_id = 8;
    assert_eq!(
        ValueTransferSetV2::new(vec![
            first,
            ValueTransferV2::new(different_epoch).expect("record is individually valid"),
        ]),
        Err(ValueTransferErrorV2::EpochMismatch)
    );
}

#[test]
fn bounded_decoder_rejects_trailing_oversized_and_unknown_kind_inputs() {
    let transfer = transfer(10, 0);
    let mut trailing = encode_value_transfer_v2(&transfer).expect("transfer encodes");
    trailing.push(0);
    assert_eq!(
        decode_exact_value_transfer_v2(&trailing),
        Err(ValueTransferErrorV2::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_value_transfer_set_v2(&vec![0; MAX_VALUE_TRANSFER_SET_BYTES_V2 + 1]),
        Err(ValueTransferErrorV2::InputTooLarge { .. })
    ));

    let mut value = serde_json::to_value(transfer).expect("transfer renders as JSON");
    value["kind"] = serde_json::json!(99);
    assert!(serde_json::from_value::<ValueTransferV2>(value).is_err());
}

#[test]
fn transfer_count_cap_is_enforced_before_set_construction() {
    let transfers = (0..=MAX_VALUE_TRANSFERS_PER_SET_V2)
        .map(|index| {
            let action_index = u32::try_from(index).expect("fixture index fits u32");
            transfer(
                u8::try_from((index % 240) + 1).expect("fixture seed fits u8"),
                action_index,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        ValueTransferSetV2::new(transfers),
        Err(ValueTransferErrorV2::TooManyTransfers {
            actual: MAX_VALUE_TRANSFERS_PER_SET_V2 + 1,
            maximum: MAX_VALUE_TRANSFERS_PER_SET_V2,
        })
    );
}
