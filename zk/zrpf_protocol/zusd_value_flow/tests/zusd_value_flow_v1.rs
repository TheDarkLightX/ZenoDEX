use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{ApplicationIdV3, CommitmentV3, DomainIdV3};
use zenodex_zrpf_zusd_value_flow_reference_v1::{
    decode_exact_proposed_zusd_value_flow_v1, encode_proposed_zusd_value_flow_v1,
    ProposedZusdSourceEvidenceV1, ProposedZusdValueFlowV1, ZusdValueEffectKindV1,
    ZusdValueFlowContextInputV1, ZusdValueFlowContextV1, ZusdValueFlowErrorV1,
    ZusdValueOperationInputV1, ZusdValueOperationKindV1, ZusdValueOperationV1,
    MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1, MAX_ZUSD_AMOUNT_ATOMS_V1,
    MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1, MAX_ZUSD_VALUE_FLOW_ROWS_V1,
};

const E8: u128 = 100_000_000;

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap()
}

fn context() -> ZusdValueFlowContextV1 {
    ZusdValueFlowContextV1::new(ZusdValueFlowContextInputV1 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        epoch_id: 41,
        zusd_asset_id: commitment(3),
        collateral_asset_id: commitment(4),
        stability_pool_scope_id: commitment(5),
        protocol_scope_id: commitment(6),
        mint_authority_scope_id: commitment(7),
        burn_authority_scope_id: commitment(8),
    })
    .unwrap()
}

fn evidence() -> ProposedZusdSourceEvidenceV1 {
    ProposedZusdSourceEvidenceV1::new(commitment(9), commitment(10))
}

fn op(input: ZusdValueOperationInputV1) -> ZusdValueOperationV1 {
    ZusdValueOperationV1::new(input).unwrap()
}

fn lifecycle_operations() -> Vec<ZusdValueOperationV1> {
    vec![
        op(ZusdValueOperationInputV1::DepositCollateral {
            action_index: 0,
            depositor_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            collateral_atoms: 1_000,
        }),
        op(ZusdValueOperationInputV1::WithdrawCollateral {
            action_index: 1,
            recipient_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            collateral_atoms: 250,
        }),
        op(ZusdValueOperationInputV1::MintZusd {
            action_index: 2,
            recipient_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            principal_atoms: 1_000,
            fee_bps: 100,
        }),
        op(ZusdValueOperationInputV1::RepayBurn {
            action_index: 3,
            payer_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            zusd_atoms: 300,
        }),
        op(ZusdValueOperationInputV1::StabilityPoolDeposit {
            action_index: 4,
            depositor_scope_id: commitment(20),
            zusd_atoms: 200,
        }),
        op(ZusdValueOperationInputV1::StabilityPoolWithdraw {
            action_index: 5,
            recipient_scope_id: commitment(20),
            zusd_atoms: 50,
        }),
        op(ZusdValueOperationInputV1::RedeemZusd {
            action_index: 6,
            redeemer_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            zusd_atoms: 200,
            oracle_price_e8: 2 * E8,
            redemption_fee_bps: 100,
            proposed_oracle_binding_hash: commitment(30),
        }),
        op(ZusdValueOperationInputV1::Liquidate {
            action_index: 7,
            vault_scope_id: commitment(21),
            liquidator_scope_id: commitment(22),
            debt_zusd_atoms: 400,
            collateral_atoms: 1_000,
            gas_comp_fixed_collateral_atoms: 50,
            gas_comp_bps: 100,
            proposed_oracle_binding_hash: commitment(31),
        }),
    ]
}

fn proposal() -> ProposedZusdValueFlowV1 {
    ProposedZusdValueFlowV1::new(context(), evidence(), lifecycle_operations()).unwrap()
}

#[test]
fn complete_lifecycle_derives_exact_integer_rows_and_conserves_each_asset() {
    let proposal = proposal();
    assert_eq!(proposal.rows().len(), 19);

    let mint_rows = proposal
        .rows()
        .iter()
        .filter(|row| row.action_index() == 2)
        .collect::<Vec<_>>();
    assert_eq!(mint_rows.len(), 2);
    assert_eq!(mint_rows[0].credit_atoms(), 1_000);
    assert_eq!(mint_rows[0].authorized_mint_atoms(), 1_000);
    assert_eq!(mint_rows[1].credit_atoms(), 10);
    assert_eq!(mint_rows[1].authorized_mint_atoms(), 10);

    let redeem_rows = proposal
        .rows()
        .iter()
        .filter(|row| row.action_index() == 6)
        .collect::<Vec<_>>();
    assert_eq!(redeem_rows.len(), 4);
    assert!(redeem_rows.iter().any(|row| {
        row.asset_id() == context().collateral_asset_id()
            && row.debit_atoms() == 100
            && row.account_scope_id() == commitment(21)
    }));
    assert!(redeem_rows.iter().any(|row| {
        row.asset_id() == context().collateral_asset_id()
            && row.credit_atoms() == 99
            && row.account_scope_id() == commitment(20)
    }));
    assert!(redeem_rows.iter().any(|row| {
        row.asset_id() == context().collateral_asset_id()
            && row.credit_atoms() == 1
            && row.account_scope_id() == context().protocol_scope_id()
    }));

    let liquidation_rows = proposal
        .rows()
        .iter()
        .filter(|row| row.action_index() == 7)
        .collect::<Vec<_>>();
    assert_eq!(liquidation_rows.len(), 4);
    assert!(liquidation_rows.iter().any(|row| {
        row.account_scope_id() == context().stability_pool_scope_id()
            && row.asset_id() == context().collateral_asset_id()
            && row.credit_atoms() == 940
    }));
    assert!(liquidation_rows.iter().any(|row| {
        row.account_scope_id() == commitment(22)
            && row.asset_id() == context().collateral_asset_id()
            && row.credit_atoms() == 60
    }));

    for asset_id in [context().zusd_asset_id(), context().collateral_asset_id()] {
        let totals = proposal
            .rows()
            .iter()
            .filter(|row| row.asset_id() == asset_id)
            .fold([0u128; 4], |mut totals, row| {
                totals[0] += row.debit_atoms();
                totals[1] += row.credit_atoms();
                totals[2] += row.authorized_mint_atoms();
                totals[3] += row.authorized_burn_atoms();
                totals
            });
        assert_eq!(totals[0] + totals[2], totals[1] + totals[3]);
    }
}

#[test]
fn operations_are_canonicalized_by_action_index() {
    let mut reversed = lifecycle_operations();
    reversed.reverse();
    let canonical = proposal();
    let reordered = ProposedZusdValueFlowV1::new(context(), evidence(), reversed).unwrap();
    assert_eq!(canonical, reordered);
    assert_eq!(
        encode_proposed_zusd_value_flow_v1(&canonical).unwrap(),
        encode_proposed_zusd_value_flow_v1(&reordered).unwrap()
    );
}

#[test]
fn duplicate_action_index_rejects_before_rows_are_exposed() {
    let operations = vec![
        op(ZusdValueOperationInputV1::DepositCollateral {
            action_index: 3,
            depositor_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            collateral_atoms: 10,
        }),
        op(ZusdValueOperationInputV1::RepayBurn {
            action_index: 3,
            payer_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            zusd_atoms: 10,
        }),
    ];
    assert_eq!(
        ProposedZusdValueFlowV1::new(context(), evidence(), operations),
        Err(ZusdValueFlowErrorV1::DuplicateActionIndex { action_index: 3 })
    );
}

#[test]
fn zero_alias_and_bound_violations_reject() {
    assert_eq!(
        ZusdValueOperationV1::new(ZusdValueOperationInputV1::DepositCollateral {
            action_index: 0,
            depositor_scope_id: commitment(20),
            vault_scope_id: commitment(20),
            collateral_atoms: 1,
        }),
        Err(ZusdValueFlowErrorV1::ScopeAlias { action_index: 0 })
    );
    assert_eq!(
        ZusdValueOperationV1::new(ZusdValueOperationInputV1::MintZusd {
            action_index: 0,
            recipient_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            principal_atoms: 0,
            fee_bps: 0,
        }),
        Err(ZusdValueFlowErrorV1::ZeroAmount { action_index: 0 })
    );
    assert_eq!(
        ZusdValueOperationV1::new(ZusdValueOperationInputV1::RedeemZusd {
            action_index: 0,
            redeemer_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            zusd_atoms: 1,
            oracle_price_e8: 0,
            redemption_fee_bps: 0,
            proposed_oracle_binding_hash: commitment(30),
        }),
        Err(ZusdValueFlowErrorV1::ZeroOraclePrice { action_index: 0 })
    );
    assert_eq!(
        ZusdValueOperationV1::new(ZusdValueOperationInputV1::Liquidate {
            action_index: 0,
            vault_scope_id: commitment(21),
            liquidator_scope_id: commitment(22),
            debt_zusd_atoms: 1,
            collateral_atoms: 1,
            gas_comp_fixed_collateral_atoms: 0,
            gas_comp_bps: 10_001,
            proposed_oracle_binding_hash: commitment(31),
        }),
        Err(ZusdValueFlowErrorV1::BasisPointsOutOfRange {
            action_index: 0,
            actual: 10_001,
        })
    );
    assert_eq!(
        ProposedZusdValueFlowV1::new(
            context(),
            evidence(),
            vec![op(ZusdValueOperationInputV1::RedeemZusd {
                action_index: 1,
                redeemer_scope_id: commitment(20),
                vault_scope_id: commitment(21),
                zusd_atoms: MAX_ZUSD_AMOUNT_ATOMS_V1,
                oracle_price_e8: 1,
                redemption_fee_bps: 0,
                proposed_oracle_binding_hash: commitment(30),
            })],
        ),
        Err(ZusdValueFlowErrorV1::AmountOutOfRange {
            action_index: 1,
            field: "redemption_gross",
        })
    );
}

#[test]
fn exact_rounding_matches_the_zusd_core_contract() {
    let operations = vec![
        op(ZusdValueOperationInputV1::MintZusd {
            action_index: 0,
            recipient_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            principal_atoms: 101,
            fee_bps: 1,
        }),
        op(ZusdValueOperationInputV1::RedeemZusd {
            action_index: 1,
            redeemer_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            zusd_atoms: 201,
            oracle_price_e8: 2 * E8,
            redemption_fee_bps: 1,
            proposed_oracle_binding_hash: commitment(30),
        }),
        op(ZusdValueOperationInputV1::Liquidate {
            action_index: 2,
            vault_scope_id: commitment(21),
            liquidator_scope_id: commitment(22),
            debt_zusd_atoms: 400,
            collateral_atoms: 1_001,
            gas_comp_fixed_collateral_atoms: 50,
            gas_comp_bps: 1,
            proposed_oracle_binding_hash: commitment(31),
        }),
    ];
    let proposal = ProposedZusdValueFlowV1::new(context(), evidence(), operations).unwrap();

    assert!(proposal.rows().iter().any(|row| {
        row.action_index() == 0
            && row.account_scope_id() == context().protocol_scope_id()
            && row.credit_atoms() == 1
    }));
    assert!(proposal.rows().iter().any(|row| {
        row.action_index() == 1
            && row.account_scope_id() == context().protocol_scope_id()
            && row.credit_atoms() == 1
    }));
    assert!(proposal.rows().iter().any(|row| {
        row.action_index() == 2
            && row.account_scope_id() == commitment(22)
            && row.credit_atoms() == 51
    }));
}

#[test]
fn fee_and_compensation_zero_paths_do_not_emit_zero_rows() {
    let operations = vec![
        op(ZusdValueOperationInputV1::MintZusd {
            action_index: 0,
            recipient_scope_id: commitment(20),
            vault_scope_id: commitment(21),
            principal_atoms: 100,
            fee_bps: 0,
        }),
        op(ZusdValueOperationInputV1::Liquidate {
            action_index: 1,
            vault_scope_id: commitment(21),
            liquidator_scope_id: commitment(22),
            debt_zusd_atoms: 50,
            collateral_atoms: 100,
            gas_comp_fixed_collateral_atoms: 0,
            gas_comp_bps: 0,
            proposed_oracle_binding_hash: commitment(31),
        }),
    ];
    let proposal = ProposedZusdValueFlowV1::new(context(), evidence(), operations).unwrap();
    assert_eq!(
        proposal
            .rows()
            .iter()
            .filter(|row| row.action_index() == 0)
            .count(),
        1
    );
    assert_eq!(
        proposal
            .rows()
            .iter()
            .filter(|row| row.action_index() == 1)
            .count(),
        3
    );
    assert!(proposal.rows().iter().all(|row| {
        row.debit_atoms() != 0
            || row.credit_atoms() != 0
            || row.authorized_mint_atoms() != 0
            || row.authorized_burn_atoms() != 0
    }));
}

#[test]
fn redeem_fee_that_consumes_gross_collateral_rejects() {
    let operation = op(ZusdValueOperationInputV1::RedeemZusd {
        action_index: 0,
        redeemer_scope_id: commitment(20),
        vault_scope_id: commitment(21),
        zusd_atoms: 2 * E8,
        oracle_price_e8: 2 * E8,
        redemption_fee_bps: 10_000,
        proposed_oracle_binding_hash: commitment(30),
    });
    assert_eq!(
        ProposedZusdValueFlowV1::new(context(), evidence(), vec![operation]),
        Err(ZusdValueFlowErrorV1::FeeConsumesCollateral { action_index: 0 })
    );
}

#[test]
fn source_and_oracle_substitution_change_canonical_identity_without_authenticating_them() {
    let baseline = proposal();
    let source_substitution = ProposedZusdValueFlowV1::new(
        context(),
        ProposedZusdSourceEvidenceV1::new(commitment(11), commitment(12)),
        lifecycle_operations(),
    )
    .unwrap();
    assert_ne!(
        baseline.canonical_commitment().unwrap(),
        source_substitution.canonical_commitment().unwrap()
    );

    let mut operations = lifecycle_operations();
    operations[6] = op(ZusdValueOperationInputV1::RedeemZusd {
        action_index: 6,
        redeemer_scope_id: commitment(20),
        vault_scope_id: commitment(21),
        zusd_atoms: 200,
        oracle_price_e8: 2 * E8,
        redemption_fee_bps: 100,
        proposed_oracle_binding_hash: commitment(32),
    });
    let oracle_substitution =
        ProposedZusdValueFlowV1::new(context(), evidence(), operations).unwrap();
    assert_ne!(
        baseline.operations()[6].canonical_id().unwrap(),
        oracle_substitution.operations()[6].canonical_id().unwrap()
    );
}

#[test]
fn exact_codec_roundtrips_and_rejects_trailing_bytes() {
    let proposal = proposal();
    let encoded = encode_proposed_zusd_value_flow_v1(&proposal).unwrap();
    assert_eq!(
        decode_exact_proposed_zusd_value_flow_v1(&encoded).unwrap(),
        proposal
    );
    let mut trailing = encoded;
    trailing.push(0);
    assert_eq!(
        decode_exact_proposed_zusd_value_flow_v1(&trailing),
        Err(ZusdValueFlowErrorV1::TrailingBytes)
    );
    let oversized = vec![0; MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_proposed_zusd_value_flow_v1(&oversized),
        Err(ZusdValueFlowErrorV1::InputTooLarge {
            actual: MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1 + 1,
            maximum: MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1,
        })
    );
}

#[test]
fn canonical_full_lifecycle_bytes_have_a_fixed_regression_vector() {
    let bytes = encode_proposed_zusd_value_flow_v1(&proposal()).unwrap();
    let digest: [u8; 32] = Sha256::digest(&bytes).into();
    assert_eq!(bytes.len(), 3_075);
    assert_eq!(
        digest,
        [
            219, 96, 117, 215, 175, 221, 146, 158, 226, 61, 237, 132, 122, 7, 130, 203, 182, 125,
            193, 152, 173, 29, 152, 104, 58, 6, 141, 145, 212, 57, 98, 241,
        ]
    );
}

#[test]
fn operation_identity_matches_an_independent_fixed_width_preimage() {
    let operation = &lifecycle_operations()[2];
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zrpf.zusd_value_operation.v1");
    hasher.update(1u16.to_be_bytes());
    hasher.update(2u32.to_be_bytes());
    hasher.update([ZusdValueOperationKindV1::MintZusd.tag()]);
    hasher.update(commitment(20).as_bytes());
    hasher.update(commitment(21).as_bytes());
    hasher.update(1_000u128.to_be_bytes());
    hasher.update(100u16.to_be_bytes());
    let expected = CommitmentV3::new(hasher.finalize().into()).unwrap();
    assert_eq!(operation.canonical_id().unwrap(), expected);
}

#[test]
fn missing_duplicate_mutated_and_unbalanced_rows_reject_on_decode() {
    let canonical = serde_json::to_value(proposal()).unwrap();

    let mut missing = canonical.clone();
    missing["rows"].as_array_mut().unwrap().pop();
    assert!(serde_json::from_value::<ProposedZusdValueFlowV1>(missing).is_err());

    let mut duplicate = canonical.clone();
    let row = duplicate["rows"][0].clone();
    duplicate["rows"].as_array_mut().unwrap().push(row);
    assert!(serde_json::from_value::<ProposedZusdValueFlowV1>(duplicate).is_err());

    let mut mutated = canonical.clone();
    mutated["rows"][0]["account_scope_id"] = serde_json::to_value(commitment(99)).unwrap();
    assert!(serde_json::from_value::<ProposedZusdValueFlowV1>(mutated).is_err());

    let mut operation_mutated = canonical.clone();
    operation_mutated["operations"][0]["input"]["DepositCollateral"]["collateral_atoms"] =
        serde_json::json!(999);
    assert!(serde_json::from_value::<ProposedZusdValueFlowV1>(operation_mutated).is_err());

    let mut unbalanced = canonical;
    unbalanced["rows"][0]["debit_atoms"] = serde_json::json!(999);
    assert!(serde_json::from_value::<ProposedZusdValueFlowV1>(unbalanced).is_err());
}

#[test]
fn operation_and_row_collection_bounds_fail_closed() {
    let operations = (0..=MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1)
        .map(|index| {
            op(ZusdValueOperationInputV1::DepositCollateral {
                action_index: u32::try_from(index).unwrap(),
                depositor_scope_id: commitment(20),
                vault_scope_id: commitment(21),
                collateral_atoms: 1,
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(
        ProposedZusdValueFlowV1::new(context(), evidence(), operations),
        Err(ZusdValueFlowErrorV1::TooManyOperations {
            actual: MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1 + 1,
            maximum: MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1,
        })
    );

    let mut oversized_operations = serde_json::to_value(proposal()).unwrap();
    let operation = oversized_operations["operations"][0].clone();
    oversized_operations["operations"]
        .as_array_mut()
        .unwrap()
        .resize(MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1 + 1, operation);
    oversized_operations["rows"] = serde_json::json!("malformed-later-field");
    let error = serde_json::from_value::<ProposedZusdValueFlowV1>(oversized_operations)
        .unwrap_err()
        .to_string();
    assert!(error.contains("operations"));

    let mut oversized_rows = serde_json::to_value(proposal()).unwrap();
    let row = oversized_rows["rows"][0].clone();
    oversized_rows["rows"]
        .as_array_mut()
        .unwrap()
        .resize(MAX_ZUSD_VALUE_FLOW_ROWS_V1 + 1, row);
    assert!(serde_json::from_value::<ProposedZusdValueFlowV1>(oversized_rows).is_err());
}

#[test]
fn exact_operation_and_row_maxima_are_accepted() {
    let operations = (0..MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1)
        .map(|index| {
            op(ZusdValueOperationInputV1::RedeemZusd {
                action_index: u32::try_from(index).unwrap(),
                redeemer_scope_id: commitment(20),
                vault_scope_id: commitment(21),
                zusd_atoms: 200,
                oracle_price_e8: 2 * E8,
                redemption_fee_bps: 100,
                proposed_oracle_binding_hash: commitment(30),
            })
        })
        .collect::<Vec<_>>();
    let proposal = ProposedZusdValueFlowV1::new(context(), evidence(), operations).unwrap();
    assert_eq!(
        proposal.operations().len(),
        MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1
    );
    assert_eq!(proposal.rows().len(), MAX_ZUSD_VALUE_FLOW_ROWS_V1);
    assert_eq!(
        decode_exact_proposed_zusd_value_flow_v1(
            &encode_proposed_zusd_value_flow_v1(&proposal).unwrap()
        )
        .unwrap(),
        proposal
    );
}

#[test]
fn every_operation_kind_and_effect_shape_is_present() {
    let proposal = proposal();
    let kinds = proposal
        .operations()
        .iter()
        .map(ZusdValueOperationV1::kind)
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        vec![
            ZusdValueOperationKindV1::DepositCollateral,
            ZusdValueOperationKindV1::WithdrawCollateral,
            ZusdValueOperationKindV1::MintZusd,
            ZusdValueOperationKindV1::RepayBurn,
            ZusdValueOperationKindV1::StabilityPoolDeposit,
            ZusdValueOperationKindV1::StabilityPoolWithdraw,
            ZusdValueOperationKindV1::RedeemZusd,
            ZusdValueOperationKindV1::Liquidate,
        ]
    );
    for row in proposal.rows() {
        match row.effect_kind() {
            ZusdValueEffectKindV1::OrdinaryDebit => {
                assert!(row.debit_atoms() > 0);
                assert_eq!(row.credit_atoms(), 0);
            }
            ZusdValueEffectKindV1::OrdinaryCredit => {
                assert!(row.credit_atoms() > 0);
                assert_eq!(row.debit_atoms(), 0);
            }
            ZusdValueEffectKindV1::AuthorizedMintCredit => {
                assert_eq!(row.credit_atoms(), row.authorized_mint_atoms());
                assert_eq!(
                    row.authority_scope_id(),
                    Some(context().mint_authority_scope_id())
                );
            }
            ZusdValueEffectKindV1::AuthorizedBurnDebit => {
                assert_eq!(row.debit_atoms(), row.authorized_burn_atoms());
                assert_eq!(
                    row.authority_scope_id(),
                    Some(context().burn_authority_scope_id())
                );
            }
        }
    }
}

#[test]
fn source_declares_exact_non_claims() {
    let source = include_str!("../src/lib.rs");
    for required in [
        "authenticates no receipt",
        "Oracle truth remains unestablished",
        "External collateral finality remains unestablished",
        "durable admission, settlement authority",
    ] {
        assert!(source.contains(required));
    }
    for forbidden in [
        "receipt_authentication_verified",
        "oracle_truth_verified",
        "settlement_authority = true",
        "production_authority = true",
    ] {
        assert!(!source.contains(forbidden));
    }
}
