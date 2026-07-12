use tau_state_proof_risc0_shared::PerpsNpActionV1;
use zenodex_zrpf_perps_source_finality_reference_v1::{
    decode_exact_proposed_perps_collateral_rows_v1, derive_proposed_perps_collateral_rows_v1,
    encode_proposed_perps_collateral_rows_v1, perps_counterparty_actor_scope_v1,
    proposed_transfer_input_for_perps_action_v1, PerpsCollateralReferenceContextV1,
    PerpsSourceFinalityReferenceErrorV1, ProposedSourceEvidenceV1, MAX_PERPS_COLLATERAL_ROWS_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_value_transfer_set_v2, ApplicationIdV3, CommitmentV3, DomainIdV3, ValueTransferErrorV2,
    ValueTransferSetV2, ValueTransferV2,
};

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap()
}

fn context() -> PerpsCollateralReferenceContextV1 {
    PerpsCollateralReferenceContextV1::new(
        ApplicationIdV3::new([1; 32]).unwrap(),
        DomainIdV3::new([2; 32]).unwrap(),
        41,
        commitment(10),
        commitment(20),
        43,
    )
    .unwrap()
}

fn actions() -> Vec<PerpsNpActionV1> {
    vec![
        PerpsNpActionV1::DepositCollateral {
            pubkey: "wallet-a".to_string(),
            asset: "USDC".to_string(),
            amount_e8: 300_000_000,
            nonce: 7,
            collateral_binding: None,
        },
        PerpsNpActionV1::WithdrawCollateral {
            pubkey: "wallet-b".to_string(),
            asset: "USDC".to_string(),
            amount_e8: 200_000_000,
            nonce: 9,
        },
    ]
}

fn transfer(
    context: PerpsCollateralReferenceContextV1,
    action_index: u32,
    action: &PerpsNpActionV1,
    seed: u8,
) -> ValueTransferV2 {
    let counterparty_actor = match action {
        PerpsNpActionV1::InitMarket { .. } => "insurance-funder",
        PerpsNpActionV1::DepositCollateral { pubkey, .. }
        | PerpsNpActionV1::WithdrawCollateral { pubkey, .. } => pubkey,
        PerpsNpActionV1::SubmitIntent { .. } | PerpsNpActionV1::RunEpoch { .. } => "unsupported",
    };
    ValueTransferV2::new(
        proposed_transfer_input_for_perps_action_v1(
            context,
            action_index,
            action,
            ProposedSourceEvidenceV1::new(
                commitment(seed),
                commitment(seed + 1),
                perps_counterparty_actor_scope_v1(counterparty_actor).unwrap(),
            ),
        )
        .unwrap(),
    )
    .unwrap()
}

fn transfer_bytes(
    context: PerpsCollateralReferenceContextV1,
    actions: &[PerpsNpActionV1],
) -> Vec<u8> {
    let set = ValueTransferSetV2::new(vec![
        transfer(context, 0, &actions[0], 30),
        transfer(context, 1, &actions[1], 40),
    ])
    .unwrap();
    encode_value_transfer_set_v2(&set).unwrap()
}

fn insurance_seed_action(amount_e8: i128) -> PerpsNpActionV1 {
    PerpsNpActionV1::InitMarket {
        market_id: "market-a".to_string(),
        collateral_asset: "USDC".to_string(),
        index_price_e8: 100_000_000,
        params: Default::default(),
        insurance_seed_e8: amount_e8,
    }
}

#[test]
fn deposit_and_withdraw_derive_two_one_sided_legs_each_and_conserve() {
    let context = context();
    let actions = actions();
    let proposal = derive_proposed_perps_collateral_rows_v1(
        context,
        &actions,
        &transfer_bytes(context, &actions),
    )
    .unwrap();

    assert_eq!(proposal.rows().len(), 4);
    let total_debit = proposal
        .rows()
        .iter()
        .map(|row| row.debit_atoms())
        .sum::<u128>();
    let total_credit = proposal
        .rows()
        .iter()
        .map(|row| row.credit_atoms())
        .sum::<u128>();
    assert_eq!(total_debit, 500_000_000);
    assert_eq!(total_credit, total_debit);

    let deposit_rows = proposal
        .rows()
        .iter()
        .filter(|row| row.action_index() == 0)
        .collect::<Vec<_>>();
    assert_eq!(deposit_rows.len(), 2);
    assert!(deposit_rows.iter().any(|row| {
        row.lane_id() == context.counterparty_lane_id()
            && row.debit_atoms() == 300_000_000
            && row.credit_atoms() == 0
    }));
    assert!(deposit_rows.iter().any(|row| {
        row.lane_id() == context.perps_lane_id()
            && row.credit_atoms() == 300_000_000
            && row.debit_atoms() == 0
    }));

    let withdrawal_rows = proposal
        .rows()
        .iter()
        .filter(|row| row.action_index() == 1)
        .collect::<Vec<_>>();
    assert!(withdrawal_rows.iter().any(|row| {
        row.lane_id() == context.perps_lane_id()
            && row.debit_atoms() == 200_000_000
            && row.credit_atoms() == 0
    }));
    assert!(withdrawal_rows.iter().any(|row| {
        row.lane_id() == context.counterparty_lane_id()
            && row.credit_atoms() == 200_000_000
            && row.debit_atoms() == 0
    }));
}

#[test]
fn exact_canonical_codec_roundtrips_and_rejects_trailing_bytes() {
    let context = context();
    let actions = actions();
    let proposal = derive_proposed_perps_collateral_rows_v1(
        context,
        &actions,
        &transfer_bytes(context, &actions),
    )
    .unwrap();
    let encoded = encode_proposed_perps_collateral_rows_v1(&proposal).unwrap();
    assert_eq!(
        decode_exact_proposed_perps_collateral_rows_v1(&encoded).unwrap(),
        proposal
    );

    let mut trailing = encoded;
    trailing.push(0);
    assert_eq!(
        decode_exact_proposed_perps_collateral_rows_v1(&trailing),
        Err(PerpsSourceFinalityReferenceErrorV1::TrailingBytes)
    );
}

#[test]
fn insurance_seed_derives_external_debit_and_perps_credit() {
    let context = context();
    let actions = vec![insurance_seed_action(100_000_000)];
    let set = ValueTransferSetV2::new(vec![transfer(context, 0, &actions[0], 30)]).unwrap();
    let proposal = derive_proposed_perps_collateral_rows_v1(
        context,
        &actions,
        &encode_value_transfer_set_v2(&set).unwrap(),
    )
    .unwrap();
    assert_eq!(proposal.rows().len(), 2);
    assert_eq!(
        proposal.transfer_set().transfers()[0].sender_scope_hash(),
        perps_counterparty_actor_scope_v1("insurance-funder").unwrap()
    );
    assert!(proposal.rows().iter().any(|row| {
        row.lane_id() == context.counterparty_lane_id() && row.debit_atoms() == 100_000_000
    }));
    assert!(proposal.rows().iter().any(|row| {
        row.lane_id() == context.perps_lane_id() && row.credit_atoms() == 100_000_000
    }));
}

#[test]
fn deposit_helper_rejects_counterparty_scope_other_than_action_pubkey() {
    let actions = actions();
    assert_eq!(
        proposed_transfer_input_for_perps_action_v1(
            context(),
            0,
            &actions[0],
            ProposedSourceEvidenceV1::new(
                commitment(30),
                commitment(31),
                perps_counterparty_actor_scope_v1("other-wallet").unwrap(),
            ),
        ),
        Err(PerpsSourceFinalityReferenceErrorV1::InvalidAction {
            action_index: 0,
            field: "counterparty_actor_scope_hash",
        })
    );
}

#[test]
fn proposed_seed_funder_and_source_evidence_change_transfer_identity() {
    let context = context();
    let action = insurance_seed_action(100_000_000);
    let first = transfer(context, 0, &action, 30);
    let second_input = proposed_transfer_input_for_perps_action_v1(
        context,
        0,
        &action,
        ProposedSourceEvidenceV1::new(
            commitment(40),
            commitment(41),
            perps_counterparty_actor_scope_v1("other-funder").unwrap(),
        ),
    )
    .unwrap();
    let second = ValueTransferV2::new(second_input).unwrap();

    assert_ne!(
        first.canonical_id().unwrap(),
        second.canonical_id().unwrap()
    );
}

#[test]
fn zero_insurance_seed_does_not_manufacture_a_transfer() {
    assert_eq!(
        proposed_transfer_input_for_perps_action_v1(
            context(),
            0,
            &insurance_seed_action(0),
            ProposedSourceEvidenceV1::new(
                commitment(30),
                commitment(31),
                perps_counterparty_actor_scope_v1("insurance-funder").unwrap(),
            ),
        ),
        Err(PerpsSourceFinalityReferenceErrorV1::UnsupportedAction { action_index: 0 })
    );
}

#[test]
fn missing_transfer_rejects_before_rows_are_exposed() {
    let context = context();
    let actions = actions();
    let set = ValueTransferSetV2::new(vec![transfer(context, 0, &actions[0], 30)]).unwrap();
    let bytes = encode_value_transfer_set_v2(&set).unwrap();
    assert_eq!(
        derive_proposed_perps_collateral_rows_v1(context, &actions, &bytes),
        Err(PerpsSourceFinalityReferenceErrorV1::MissingTransfer { action_index: 1 })
    );
}

#[test]
fn duplicate_action_transfer_is_rejected_by_the_canonical_transfer_set() {
    let context = context();
    let action = &actions()[0];
    assert_eq!(
        ValueTransferSetV2::new(vec![
            transfer(context, 0, action, 30),
            transfer(context, 0, action, 40),
        ]),
        Err(ValueTransferErrorV2::DuplicateActionBinding)
    );
}

#[test]
fn two_distinct_transfer_kinds_cannot_reuse_one_action_index() {
    let context = context();
    let actions = actions();
    let set = ValueTransferSetV2::new(vec![
        transfer(context, 0, &actions[0], 30),
        transfer(context, 0, &actions[1], 40),
    ])
    .unwrap();
    assert_eq!(
        derive_proposed_perps_collateral_rows_v1(
            context,
            &actions,
            &encode_value_transfer_set_v2(&set).unwrap(),
        ),
        Err(PerpsSourceFinalityReferenceErrorV1::DuplicateTransferForAction { action_index: 0 })
    );
}

#[test]
fn wrong_counterparty_lane_rejects() {
    let context = context();
    let actions = actions();
    let mut bad = proposed_transfer_input_for_perps_action_v1(
        context,
        0,
        &actions[0],
        ProposedSourceEvidenceV1::new(
            commitment(30),
            commitment(31),
            perps_counterparty_actor_scope_v1("wallet-a").unwrap(),
        ),
    )
    .unwrap();
    bad.source_lane_id = commitment(99);
    let set = ValueTransferSetV2::new(vec![
        ValueTransferV2::new(bad).unwrap(),
        transfer(context, 1, &actions[1], 40),
    ])
    .unwrap();
    assert_eq!(
        derive_proposed_perps_collateral_rows_v1(
            context,
            &actions,
            &encode_value_transfer_set_v2(&set).unwrap(),
        ),
        Err(PerpsSourceFinalityReferenceErrorV1::WrongCounterparty { action_index: 0 })
    );
}

#[test]
fn action_amount_and_scope_substitutions_reject() {
    let context = context();
    let actions = actions();
    let baseline = proposed_transfer_input_for_perps_action_v1(
        context,
        0,
        &actions[0],
        ProposedSourceEvidenceV1::new(
            commitment(30),
            commitment(31),
            perps_counterparty_actor_scope_v1("wallet-a").unwrap(),
        ),
    )
    .unwrap();
    let mutations = [
        {
            let mut value = baseline.clone();
            value.amount_atoms += 1;
            (value, "amount_atoms")
        },
        {
            let mut value = baseline.clone();
            value.action_hash = commitment(90);
            (value, "action_hash")
        },
        {
            let mut value = baseline.clone();
            value.asset_id = commitment(91);
            (value, "asset_id")
        },
        {
            let mut value = baseline.clone();
            value.sender_scope_hash = commitment(92);
            (value, "sender_scope_hash")
        },
        {
            let mut value = baseline;
            value.deadline_epoch += 1;
            (value, "deadline_epoch")
        },
    ];
    for (mutated, field) in mutations {
        let set = ValueTransferSetV2::new(vec![
            ValueTransferV2::new(mutated).unwrap(),
            transfer(context, 1, &actions[1], 40),
        ])
        .unwrap();
        assert_eq!(
            derive_proposed_perps_collateral_rows_v1(
                context,
                &actions,
                &encode_value_transfer_set_v2(&set).unwrap(),
            ),
            Err(PerpsSourceFinalityReferenceErrorV1::TransferMismatch {
                action_index: 0,
                field,
            })
        );
    }
}

#[test]
fn missing_duplicate_and_unbalanced_rows_fail_closed_on_decode() {
    let context = context();
    let actions = actions();
    let proposal = derive_proposed_perps_collateral_rows_v1(
        context,
        &actions,
        &transfer_bytes(context, &actions),
    )
    .unwrap();
    let canonical = serde_json::to_value(&proposal).unwrap();

    let mut missing = canonical.clone();
    missing["rows"].as_array_mut().unwrap().pop();
    assert!(serde_json::from_value::<
        zenodex_zrpf_perps_source_finality_reference_v1::ProposedPerpsCollateralRowsV1,
    >(missing)
    .is_err());

    let mut duplicate = canonical.clone();
    let row = duplicate["rows"][0].clone();
    duplicate["rows"].as_array_mut().unwrap().push(row);
    assert!(serde_json::from_value::<
        zenodex_zrpf_perps_source_finality_reference_v1::ProposedPerpsCollateralRowsV1,
    >(duplicate)
    .is_err());

    let mut unbalanced = canonical;
    unbalanced["rows"][0]["debit_atoms"] = serde_json::json!(1);
    assert!(serde_json::from_value::<
        zenodex_zrpf_perps_source_finality_reference_v1::ProposedPerpsCollateralRowsV1,
    >(unbalanced)
    .is_err());
}

#[test]
fn oversized_row_sequence_rejects_before_authority_is_exposed() {
    let context = context();
    let actions = actions();
    let proposal = derive_proposed_perps_collateral_rows_v1(
        context,
        &actions,
        &transfer_bytes(context, &actions),
    )
    .unwrap();
    let mut oversized = serde_json::to_value(&proposal).unwrap();
    let row = oversized["rows"][0].clone();
    let rows = oversized["rows"].as_array_mut().unwrap();
    rows.resize(MAX_PERPS_COLLATERAL_ROWS_V1 + 1, row);

    assert!(serde_json::from_value::<
        zenodex_zrpf_perps_source_finality_reference_v1::ProposedPerpsCollateralRowsV1,
    >(oversized)
    .is_err());
}

#[test]
fn source_declares_the_exact_non_claim_boundary() {
    let source = include_str!("../src/lib.rs");
    assert!(source.contains("authenticates no source receipt"));
    assert!(source.contains("external-chain finality remains unestablished"));
    assert!(source.contains("no source guest, receipt verification, transfer"));
    for forbidden in [
        "source_finality_verified",
        "external_chain_finality_verified",
        "settlement_authority = true",
        "production_authority = true",
    ] {
        assert!(!source.contains(forbidden));
    }
}
