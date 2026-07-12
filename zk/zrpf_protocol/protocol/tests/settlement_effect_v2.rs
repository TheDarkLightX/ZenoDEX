use serde::Serialize;
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_effect_plan_v2, encode_settlement_effect_plan_v2, ApplicationIdV3,
    AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2, AuthorizationGrantIdV1,
    AuthorizationScopeIdV1, AuthorizationSubjectIdV1, AuthorizedEconomicActionV1,
    CarryEffectInputV2, CarryEffectKindV2, CarryEffectV2, CommitmentV3, DomainIdV3,
    EconomicActionBatchV1, EconomicActionRecordInputV1, EconomicActionRecordV1,
    EconomicActionTypeIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2, MessageEffectInputV2,
    MessageEffectKindV2, MessageEffectV2, RewardEffectInputV2, RewardEffectV2,
    SettlementEffectErrorV2, SettlementEffectPlanInputV2, SettlementEffectPlanV2, ValueHashV2,
    MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2, MAX_SETTLEMENT_EFFECT_ROWS_V2,
};

const CELL_WRITE_DOMAIN_V2: &[u8] = b"zenodex.zrpf.ledger_cell_write.v2";
const ASSET_EFFECT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.asset_effect.v2";
const CELL_WRITES_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.ledger_cell_writes_root.v2";
const ASSET_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.asset_effects_root.v2";
const MESSAGE_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.message_effects_root.v2";
const CARRY_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.carry_effects_root.v2";
const REWARD_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.reward_effects_root.v2";
const PLAN_COMMITMENT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.settlement_effect_plan.v2";

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn value_hash(seed: u8) -> ValueHashV2 {
    ValueHashV2::new([seed; 32])
}

fn hex_32(value: &str) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    bytes
}

fn action_record(nonce: u64, semantics: u8, effect: u8) -> EconomicActionRecordV1 {
    EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
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
        consumed_object_ids: Vec::new(),
    })
    .unwrap()
}

fn authorized_action(nonce: u64, semantics: u8, effect: u8) -> AuthorizedEconomicActionV1 {
    AuthorizedEconomicActionV1::new(
        action_record(nonce, semantics, effect),
        AuthorizationGrantIdV1::new([9; 32]).unwrap(),
    )
    .unwrap()
}

fn action_batch(actions: Vec<AuthorizedEconomicActionV1>) -> EconomicActionBatchV1 {
    EconomicActionBatchV1::new(25, commitment(6), actions).unwrap()
}

fn cell_write(action: &AuthorizedEconomicActionV1, cell: u8) -> LedgerCellWriteV2 {
    LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: action.action_id().unwrap(),
        cell_key: commitment(cell),
        pre_value_hash: value_hash(cell.wrapping_add(1)),
        post_value_hash: value_hash(cell.wrapping_add(2)),
    })
    .unwrap()
}

fn ordinary_effect(action: &AuthorizedEconomicActionV1, asset: u8, amount: u128) -> AssetEffectV2 {
    AssetEffectV2::new(AssetEffectInputV2 {
        kind: AssetEffectKindV2::OrdinaryTransfer,
        economic_action_id: action.action_id().unwrap(),
        asset_id: commitment(asset),
        debit_atoms: amount,
        credit_atoms: amount,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_scope_id: None,
        action_authorization_binding: None,
    })
    .unwrap()
}

fn authorized_effect(
    action: &AuthorizedEconomicActionV1,
    kind: AssetEffectKindV2,
    asset: u8,
    amount: u128,
) -> AssetEffectV2 {
    let (debit, credit, mint, burn) = match kind {
        AssetEffectKindV2::AuthorizedMint => (0, amount, amount, 0),
        AssetEffectKindV2::AuthorizedBurn => (amount, 0, 0, amount),
        AssetEffectKindV2::AuthorizedReward => (amount, amount, 0, 0),
        AssetEffectKindV2::OrdinaryTransfer => panic!("test helper requires authorized kind"),
    };
    AssetEffectV2::new(AssetEffectInputV2 {
        kind,
        economic_action_id: action.action_id().unwrap(),
        asset_id: commitment(asset),
        debit_atoms: debit,
        credit_atoms: credit,
        authorized_mint_atoms: mint,
        authorized_burn_atoms: burn,
        authority_scope_id: Some(action.record().authorization_scope_id()),
        action_authorization_binding: Some(action.action_authorization_binding().unwrap()),
    })
    .unwrap()
}

fn plan_input(
    actions: Vec<AuthorizedEconomicActionV1>,
    writes: Vec<LedgerCellWriteV2>,
    effects: Vec<AssetEffectV2>,
) -> SettlementEffectPlanInputV2 {
    SettlementEffectPlanInputV2 {
        source_semantic_journal_hash: commitment(50),
        public_policy_hash: commitment(51),
        post_state_root: commitment(52),
        economic_action_batch: action_batch(actions),
        ledger_cell_writes: writes,
        asset_effects: effects,
        message_effects: Vec::new(),
        carry_effects: Vec::new(),
        reward_effects: Vec::new(),
    }
}

fn ordinary_plan() -> SettlementEffectPlanV2 {
    let action = authorized_action(17, 7, 8);
    SettlementEffectPlanV2::new(plan_input(
        vec![action.clone()],
        vec![cell_write(&action, 30)],
        vec![ordinary_effect(&action, 40, 10)],
    ))
    .unwrap()
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn manual_cell_hash(row: &LedgerCellWriteV2) -> [u8; 32] {
    let mut hasher = domain_hasher(CELL_WRITE_DOMAIN_V2);
    hasher.update(row.economic_action_id().as_bytes());
    hasher.update(row.cell_key().as_bytes());
    hasher.update(row.pre_value_hash().as_bytes());
    hasher.update(row.post_value_hash().as_bytes());
    hasher.finalize().into()
}

fn manual_asset_id(row: &AssetEffectV2) -> [u8; 32] {
    let kind = match row.kind() {
        AssetEffectKindV2::OrdinaryTransfer => 0,
        AssetEffectKindV2::AuthorizedMint => 1,
        AssetEffectKindV2::AuthorizedBurn => 2,
        AssetEffectKindV2::AuthorizedReward => 3,
    };
    let mut hasher = domain_hasher(ASSET_EFFECT_DOMAIN_V2);
    hasher.update([kind]);
    hasher.update(row.economic_action_id().as_bytes());
    hasher.update(row.asset_id().as_bytes());
    for amount in [
        row.debit_atoms(),
        row.credit_atoms(),
        row.authorized_mint_atoms(),
        row.authorized_burn_atoms(),
    ] {
        hasher.update(amount.to_be_bytes());
    }
    match (row.authority_scope_id(), row.action_authorization_binding()) {
        (Some(scope), Some(binding)) => {
            hasher.update([1]);
            hasher.update(scope.as_bytes());
            hasher.update(binding.as_bytes());
        }
        (None, None) => hasher.update([0]),
        _ => panic!("validated row has paired authority"),
    }
    hasher.finalize().into()
}

fn manual_root(domain: &[u8], values: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = domain_hasher(domain);
    hasher.update(u32::try_from(values.len()).unwrap().to_be_bytes());
    for value in values {
        hasher.update(value);
    }
    hasher.finalize().into()
}

fn manual_plan_commitment(plan: &SettlementEffectPlanV2) -> [u8; 32] {
    let mut hasher = domain_hasher(PLAN_COMMITMENT_DOMAIN_V2);
    hasher.update(plan.plan_version().to_be_bytes());
    hasher.update(
        plan.economic_action_batch()
            .canonical_commitment()
            .unwrap()
            .as_bytes(),
    );
    hasher.update(plan.source_semantic_journal_hash().as_bytes());
    hasher.update(plan.public_policy_hash().as_bytes());
    hasher.update(plan.post_state_root().as_bytes());
    for root in [
        plan.cell_writes_root(),
        plan.asset_effects_root(),
        plan.message_effects_root(),
        plan.carry_effects_root(),
        plan.reward_effects_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    hasher.finalize().into()
}

#[test]
fn ordinary_plan_roots_match_independent_preimage_reconstruction() {
    let plan = ordinary_plan();
    let cell_hash = manual_cell_hash(&plan.ledger_cell_writes()[0]);
    let effect_hash = manual_asset_id(&plan.asset_effects()[0]);
    assert_eq!(
        plan.cell_writes_root().into_bytes(),
        manual_root(CELL_WRITES_ROOT_DOMAIN_V2, &[cell_hash])
    );
    assert_eq!(
        plan.asset_effects_root().into_bytes(),
        manual_root(ASSET_EFFECTS_ROOT_DOMAIN_V2, &[effect_hash])
    );
    assert_eq!(
        plan.message_effects_root().into_bytes(),
        manual_root(MESSAGE_EFFECTS_ROOT_DOMAIN_V2, &[])
    );
    assert_eq!(
        plan.carry_effects_root().into_bytes(),
        manual_root(CARRY_EFFECTS_ROOT_DOMAIN_V2, &[])
    );
    assert_eq!(
        plan.reward_effects_root().into_bytes(),
        manual_root(REWARD_EFFECTS_ROOT_DOMAIN_V2, &[])
    );
    assert_eq!(
        plan.canonical_commitment().unwrap().into_bytes(),
        manual_plan_commitment(&plan)
    );
    assert_eq!(
        plan.canonical_commitment().unwrap().into_bytes(),
        hex_32("da34e94f4a45ca88957e1a403d36c650b3addbf901e0aa2a785d19ffb706bd75")
    );
}

#[test]
fn plan_construction_is_order_independent() {
    let first = authorized_action(17, 7, 8);
    let second = authorized_action(18, 10, 11);
    let first_write = cell_write(&first, 30);
    let second_write = cell_write(&second, 31);
    let first_effect = ordinary_effect(&first, 40, 10);
    let second_effect = ordinary_effect(&second, 41, 11);
    let forward = SettlementEffectPlanV2::new(plan_input(
        vec![first.clone(), second.clone()],
        vec![first_write.clone(), second_write.clone()],
        vec![first_effect.clone(), second_effect.clone()],
    ))
    .unwrap();
    let reverse = SettlementEffectPlanV2::new(plan_input(
        vec![second, first],
        vec![second_write, first_write],
        vec![second_effect, first_effect],
    ))
    .unwrap();
    assert_eq!(forward, reverse);
    assert_eq!(
        forward.canonical_commitment().unwrap(),
        reverse.canonical_commitment().unwrap()
    );
}

#[test]
fn authorized_mint_and_burn_use_exact_batch_authority() {
    for (nonce, kind) in [
        (17, AssetEffectKindV2::AuthorizedMint),
        (18, AssetEffectKindV2::AuthorizedBurn),
    ] {
        let action = authorized_action(nonce, u8::try_from(nonce).unwrap(), 8);
        let plan = SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![cell_write(&action, u8::try_from(nonce).unwrap() + 20)],
            vec![authorized_effect(&action, kind, 40, 7)],
        ))
        .unwrap();
        assert_eq!(plan.asset_effects()[0].kind(), kind);
    }
}

#[test]
fn authorization_scope_and_binding_substitution_reject() {
    let action = authorized_action(17, 7, 8);
    let mut effect = authorized_effect(&action, AssetEffectKindV2::AuthorizedMint, 40, 7);
    let mut json = serde_json::to_value(&effect).unwrap();
    json["authority_scope_id"] = serde_json::json!(vec![77; 32]);
    effect = serde_json::from_value(json).unwrap();
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![cell_write(&action, 30)],
            vec![effect],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::AuthorizationMismatch
    );
}

#[test]
fn one_atom_imbalance_and_u128_accumulation_overflow_reject() {
    let action = authorized_action(17, 7, 8);
    let imbalanced = AssetEffectV2::new(AssetEffectInputV2 {
        kind: AssetEffectKindV2::OrdinaryTransfer,
        economic_action_id: action.action_id().unwrap(),
        asset_id: commitment(40),
        debit_atoms: 10,
        credit_atoms: 9,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_scope_id: None,
        action_authorization_binding: None,
    })
    .unwrap();
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![cell_write(&action, 30)],
            vec![imbalanced],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::AssetConservationViolation
    );

    let second = authorized_action(18, 10, 11);
    let effects = vec![
        ordinary_effect(&action, 40, u128::MAX),
        ordinary_effect(&second, 40, 1),
    ];
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone(), second.clone()],
            vec![cell_write(&action, 30), cell_write(&second, 31)],
            effects,
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::ArithmeticOverflow("asset_total")
    );
}

#[test]
fn message_and_carry_pair_exactly() {
    let action = authorized_action(17, 7, 8);
    let effect = ordinary_effect(&action, 40, 10);
    let message = MessageEffectV2::new(MessageEffectInputV2 {
        economic_action_id: action.action_id().unwrap(),
        asset_effect_id: effect.canonical_id().unwrap(),
        source_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        destination_domain_id: DomainIdV3::new([60; 32]).unwrap(),
        asset_id: commitment(40),
        amount_atoms: 10,
        kind: MessageEffectKindV2::OutboxEnqueue,
    })
    .unwrap();
    let carry = CarryEffectV2::new(CarryEffectInputV2 {
        economic_action_id: action.action_id().unwrap(),
        message_id: message.canonical_id().unwrap(),
        asset_id: commitment(40),
        amount_atoms: 10,
        kind: CarryEffectKindV2::Lock,
    })
    .unwrap();
    let mut input = plan_input(
        vec![action.clone()],
        vec![cell_write(&action, 30)],
        vec![effect],
    );
    input.message_effects = vec![message.clone()];
    input.carry_effects = vec![carry];
    assert_eq!(
        SettlementEffectPlanV2::new(input.clone())
            .unwrap()
            .message_effects()
            .len(),
        1
    );
    input.carry_effects.clear();
    assert_eq!(
        SettlementEffectPlanV2::new(input).unwrap_err(),
        SettlementEffectErrorV2::MessageCarryMismatch
    );
}

#[test]
fn authorized_reward_binds_effect_write_and_batch_authority() {
    let action = authorized_action(17, 7, 8);
    let write = cell_write(&action, 30);
    let effect = authorized_effect(&action, AssetEffectKindV2::AuthorizedReward, 40, 7);
    let reward = RewardEffectV2::new(RewardEffectInputV2 {
        economic_action_id: action.action_id().unwrap(),
        asset_effect_id: effect.canonical_id().unwrap(),
        recipient_cell_key: write.cell_key(),
        asset_id: effect.asset_id(),
        amount_atoms: 7,
        authority_scope_id: action.record().authorization_scope_id(),
        action_authorization_binding: action.action_authorization_binding().unwrap(),
    })
    .unwrap();
    let mut input = plan_input(vec![action], vec![write], vec![effect]);
    input.reward_effects = vec![reward];
    let plan = SettlementEffectPlanV2::new(input.clone()).unwrap();
    assert_eq!(plan.reward_effects().len(), 1);
    input.reward_effects.clear();
    assert_eq!(
        SettlementEffectPlanV2::new(input).unwrap_err(),
        SettlementEffectErrorV2::RewardMismatch
    );
}

#[test]
fn exact_codec_rejects_trailing_truncated_oversized_and_root_substitution() {
    let plan = ordinary_plan();
    let bytes = encode_settlement_effect_plan_v2(&plan).unwrap();
    assert_eq!(
        decode_exact_settlement_effect_plan_v2(&bytes).unwrap(),
        plan
    );
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_settlement_effect_plan_v2(&trailing).unwrap_err(),
        SettlementEffectErrorV2::TrailingBytes
    );
    assert_eq!(
        decode_exact_settlement_effect_plan_v2(&[]).unwrap_err(),
        SettlementEffectErrorV2::EmptyInput
    );
    assert!(matches!(
        decode_exact_settlement_effect_plan_v2(&vec![0; MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 + 1]),
        Err(SettlementEffectErrorV2::InputTooLarge { .. })
    ));
    for end in 1..bytes.len() {
        assert!(decode_exact_settlement_effect_plan_v2(&bytes[..end]).is_err());
    }
    let mut substituted = serde_json::to_value(&plan).unwrap();
    substituted["asset_effects_root"] = serde_json::json!(vec![99; 32]);
    let error = serde_json::from_value::<SettlementEffectPlanV2>(substituted).unwrap_err();
    assert!(error
        .to_string()
        .contains("settlement commitment mismatch: asset_effects_root"));
}

#[test]
fn wire_decoding_revalidates_record_constructors_and_unknown_fields() {
    let plan = ordinary_plan();
    let mut unknown = serde_json::to_value(&plan).unwrap();
    unknown["settlement_authority"] = serde_json::json!(true);
    assert!(serde_json::from_value::<SettlementEffectPlanV2>(unknown).is_err());

    let action = authorized_action(17, 7, 8);
    let effect = ordinary_effect(&action, 40, 10);
    let message = MessageEffectV2::new(MessageEffectInputV2 {
        economic_action_id: action.action_id().unwrap(),
        asset_effect_id: effect.canonical_id().unwrap(),
        source_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        destination_domain_id: DomainIdV3::new([60; 32]).unwrap(),
        asset_id: commitment(40),
        amount_atoms: 10,
        kind: MessageEffectKindV2::OutboxEnqueue,
    })
    .unwrap();
    let mut invalid_message = serde_json::to_value(message).unwrap();
    invalid_message["amount_atoms"] = serde_json::json!(0);
    assert!(serde_json::from_value::<MessageEffectV2>(invalid_message).is_err());
}

#[test]
fn collection_bound_rejects_before_duplicate_analysis() {
    let action = authorized_action(17, 7, 8);
    let writes = (0..=MAX_SETTLEMENT_EFFECT_ROWS_V2)
        .map(|index| {
            LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
                economic_action_id: action.action_id().unwrap(),
                cell_key: {
                    let mut bytes = [70; 32];
                    bytes[24..].copy_from_slice(&u64::try_from(index + 1).unwrap().to_be_bytes());
                    CommitmentV3::new(bytes).unwrap()
                },
                pre_value_hash: value_hash(1),
                post_value_hash: value_hash(2),
            })
            .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            writes,
            vec![ordinary_effect(&action, 40, 10)],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::CollectionTooLarge {
            field: "ledger_cell_writes",
            actual: MAX_SETTLEMENT_EFFECT_ROWS_V2 + 1,
            maximum: MAX_SETTLEMENT_EFFECT_ROWS_V2,
        }
    );
}

#[test]
fn record_shapes_and_action_coverage_fail_closed() {
    let action = authorized_action(17, 7, 8);
    assert_eq!(
        LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
            economic_action_id: action.action_id().unwrap(),
            cell_key: commitment(30),
            pre_value_hash: value_hash(1),
            post_value_hash: value_hash(1),
        })
        .unwrap_err(),
        SettlementEffectErrorV2::NonChangingValue
    );
    assert_eq!(
        AssetEffectV2::new(AssetEffectInputV2 {
            kind: AssetEffectKindV2::OrdinaryTransfer,
            economic_action_id: action.action_id().unwrap(),
            asset_id: commitment(40),
            debit_atoms: 1,
            credit_atoms: 1,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_scope_id: Some(action.record().authorization_scope_id()),
            action_authorization_binding: Some(action.action_authorization_binding().unwrap()),
        })
        .unwrap_err(),
        SettlementEffectErrorV2::UnexpectedAuthority
    );
    let missing_write = plan_input(
        vec![action.clone()],
        Vec::new(),
        vec![ordinary_effect(&action, 40, 1)],
    );
    assert_eq!(
        SettlementEffectPlanV2::new(missing_write).unwrap_err(),
        SettlementEffectErrorV2::EmptyCollection("ledger_cell_writes")
    );
    let other = authorized_action(18, 10, 11);
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![cell_write(&action, 30)],
            vec![ordinary_effect(&other, 40, 1)],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::UnknownAction
    );
}

#[test]
fn duplicate_rows_and_authorization_reuse_reject() {
    let action = authorized_action(17, 7, 8);
    let write = cell_write(&action, 30);
    let effect = ordinary_effect(&action, 40, 1);
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![write.clone(), write],
            vec![effect.clone()],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::DuplicateCellWrite
    );
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![cell_write(&action, 30)],
            vec![effect.clone(), effect],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::DuplicateAssetEffect
    );
    assert_eq!(
        SettlementEffectPlanV2::new(plan_input(
            vec![action.clone()],
            vec![cell_write(&action, 30)],
            vec![
                authorized_effect(&action, AssetEffectKindV2::AuthorizedMint, 40, 1),
                authorized_effect(&action, AssetEffectKindV2::AuthorizedMint, 41, 1),
            ],
        ))
        .unwrap_err(),
        SettlementEffectErrorV2::AuthorizationReused
    );
}

#[derive(Serialize)]
struct NonCanonicalPlanWire {
    plan_version: u16,
    source_semantic_journal_hash: CommitmentV3,
    public_policy_hash: CommitmentV3,
    post_state_root: CommitmentV3,
    economic_action_batch: EconomicActionBatchV1,
    ledger_cell_writes: Vec<LedgerCellWriteV2>,
    asset_effects: Vec<AssetEffectV2>,
    message_effects: Vec<MessageEffectV2>,
    carry_effects: Vec<CarryEffectV2>,
    reward_effects: Vec<RewardEffectV2>,
    cell_writes_root: CommitmentV3,
    asset_effects_root: CommitmentV3,
    message_effects_root: CommitmentV3,
    carry_effects_root: CommitmentV3,
    reward_effects_root: CommitmentV3,
}

#[test]
fn exact_decoder_rejects_noncanonical_row_order() {
    let first = authorized_action(17, 7, 8);
    let second = authorized_action(18, 10, 11);
    let plan = SettlementEffectPlanV2::new(plan_input(
        vec![first.clone(), second.clone()],
        vec![cell_write(&first, 30), cell_write(&second, 31)],
        vec![
            ordinary_effect(&first, 40, 10),
            ordinary_effect(&second, 41, 11),
        ],
    ))
    .unwrap();
    let mut writes = plan.ledger_cell_writes().to_vec();
    let mut effects = plan.asset_effects().to_vec();
    writes.reverse();
    effects.reverse();
    let bytes = postcard::to_allocvec(&NonCanonicalPlanWire {
        plan_version: plan.plan_version(),
        source_semantic_journal_hash: plan.source_semantic_journal_hash(),
        public_policy_hash: plan.public_policy_hash(),
        post_state_root: plan.post_state_root(),
        economic_action_batch: plan.economic_action_batch().clone(),
        ledger_cell_writes: writes,
        asset_effects: effects,
        message_effects: plan.message_effects().to_vec(),
        carry_effects: plan.carry_effects().to_vec(),
        reward_effects: plan.reward_effects().to_vec(),
        cell_writes_root: plan.cell_writes_root(),
        asset_effects_root: plan.asset_effects_root(),
        message_effects_root: plan.message_effects_root(),
        carry_effects_root: plan.carry_effects_root(),
        reward_effects_root: plan.reward_effects_root(),
    })
    .unwrap();
    assert!(decode_exact_settlement_effect_plan_v2(&bytes).is_err());
}
