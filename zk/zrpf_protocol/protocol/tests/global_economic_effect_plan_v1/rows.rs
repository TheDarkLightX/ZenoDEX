use super::support::*;

#[test]
fn closed_effect_registry_constructs_all_eleven_typed_variants() {
    // Arrange
    let scope = AuthorizationScopeIdV1::new([7; 32]).unwrap();
    let binding = ActionAuthorizationBindingIdV1::new([8; 32]).unwrap();

    // Act
    let rows = vec![
        GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
            lane_id: EconomicLaneIdV1::AssetTransfer,
            asset_id: root(1),
            source_id: root(2),
            destination_id: root(3),
            amount_atoms: 1,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::issue_burn(GlobalIssueBurnInputV1 {
            lane_id: EconomicLaneIdV1::ZusdMonetary,
            asset_id: root(1),
            kind: GlobalIssueBurnKindV1::Issue,
            bucket_id: root(4),
            amount_atoms: 1,
            authority_scope_id: scope,
            action_authorization_binding: binding,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::custody(GlobalCustodyEffectInputV1 {
            lane_id: EconomicLaneIdV1::ZusdMonetary,
            asset_id: root(1),
            custody_id: root(5),
            custody_pre_atoms: 10,
            custody_post_atoms: 12,
            claimant_entitlements_pre_atoms: 8,
            claimant_entitlements_post_atoms: 9,
            unencumbered_reserves_pre_atoms: 2,
            unencumbered_reserves_post_atoms: 3,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::liability(GlobalLiabilityEffectInputV1 {
            lane_id: EconomicLaneIdV1::ZusdMonetary,
            asset_id: root(1),
            liability_id: root(6),
            pre_atoms: 8,
            post_atoms: 9,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::reserve(GlobalReserveEffectInputV1 {
            lane_id: EconomicLaneIdV1::ZdexTokenomics,
            asset_id: root(1),
            reserve_id: root(7),
            pre_atoms: 5,
            post_atoms: 6,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::fee(GlobalFeeEffectInputV1 {
            lane_id: EconomicLaneIdV1::SpotLiquidity,
            asset_id: root(1),
            fee_id: root(8),
            charged_atoms: 3,
            allocated_atoms: 2,
            carried_residue_atoms: 1,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::reward_slash(GlobalRewardSlashInputV1 {
            lane_id: EconomicLaneIdV1::ProofRewards,
            asset_id: root(1),
            kind: GlobalRewardSlashKindV1::Reward,
            source_id: root(9),
            destination_id: root(10),
            amount_atoms: 1,
            authority_scope_id: scope,
            action_authorization_binding: binding,
        })
        .unwrap(),
        GlobalEconomicEffectRowV1::lane_write(
            EconomicLaneIdV1::AssetTransfer,
            root(11),
            root(12),
            root(13),
        )
        .unwrap(),
        GlobalEconomicEffectRowV1::occurrence_consumption(
            GlobalOccurrenceConsumptionKindV1::ConsumedObject,
            root(14),
        )
        .unwrap(),
        GlobalEconomicEffectRowV1::terminal_obligation(
            EconomicLaneIdV1::FarmIncentives,
            root(15),
            root(16),
            root(17),
        )
        .unwrap(),
        GlobalEconomicEffectRowV1::external_outbox_enqueue(GlobalExternalOutboxInputV1 {
            outbox_id: root(18),
            destination_domain_id: domain_id(19),
            asset_id: root(1),
            amount_atoms: 1,
            value_effect_id: root(20),
            payload_commitment: root(21),
        })
        .unwrap(),
    ];

    // Assert
    assert_eq!(
        rows.iter()
            .map(GlobalEconomicEffectRowV1::kind)
            .collect::<Vec<_>>(),
        vec![
            GlobalEconomicEffectKindV1::AccountMovement,
            GlobalEconomicEffectKindV1::IssueBurn,
            GlobalEconomicEffectKindV1::Custody,
            GlobalEconomicEffectKindV1::Liability,
            GlobalEconomicEffectKindV1::Reserve,
            GlobalEconomicEffectKindV1::Fee,
            GlobalEconomicEffectKindV1::RewardSlash,
            GlobalEconomicEffectKindV1::LaneWrite,
            GlobalEconomicEffectKindV1::OccurrenceConsumption,
            GlobalEconomicEffectKindV1::TerminalObligation,
            GlobalEconomicEffectKindV1::ExternalOutboxEnqueue,
        ]
    );
}

#[test]
fn amount_boundary_accepts_one_and_maximum_but_rejects_zero() {
    // Arrange / Act
    let zero = GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        asset_id: root(1),
        source_id: root(2),
        destination_id: root(3),
        amount_atoms: 0,
    });
    let one = transfer_body(1, vec![]);
    let maximum = transfer_body(u128::MAX, vec![]);

    // Assert
    assert_eq!(
        zero,
        Err(GlobalEconomicEffectPlanErrorV1::ZeroAmount(
            "account movement"
        ))
    );
    assert_eq!(one.reconciliations()[0].owned_and_custodied_post_atoms(), 1);
    assert_eq!(maximum.reconciliations()[0].supply_post_atoms(), u128::MAX);
}

#[test]
fn custody_and_fee_equations_reject_neighbor_mutations_and_overflow() {
    // Arrange / Act
    let custody_valid = GlobalEconomicEffectRowV1::custody(GlobalCustodyEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: root(1),
        custody_id: root(2),
        custody_pre_atoms: 10,
        custody_post_atoms: 11,
        claimant_entitlements_pre_atoms: 8,
        claimant_entitlements_post_atoms: 9,
        unencumbered_reserves_pre_atoms: 2,
        unencumbered_reserves_post_atoms: 2,
    });
    let custody_neighbor = GlobalEconomicEffectRowV1::custody(GlobalCustodyEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: root(1),
        custody_id: root(2),
        custody_pre_atoms: 10,
        custody_post_atoms: 11,
        claimant_entitlements_pre_atoms: 8,
        claimant_entitlements_post_atoms: 9,
        unencumbered_reserves_pre_atoms: 1,
        unencumbered_reserves_post_atoms: 2,
    });
    let custody_overflow = GlobalEconomicEffectRowV1::custody(GlobalCustodyEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: root(1),
        custody_id: root(2),
        custody_pre_atoms: u128::MAX,
        custody_post_atoms: 1,
        claimant_entitlements_pre_atoms: u128::MAX,
        claimant_entitlements_post_atoms: 1,
        unencumbered_reserves_pre_atoms: 1,
        unencumbered_reserves_post_atoms: 0,
    });
    let fee_valid = GlobalEconomicEffectRowV1::fee(GlobalFeeEffectInputV1 {
        lane_id: EconomicLaneIdV1::SpotLiquidity,
        asset_id: root(1),
        fee_id: root(3),
        charged_atoms: 10,
        allocated_atoms: 9,
        carried_residue_atoms: 1,
    });
    let fee_neighbor = GlobalEconomicEffectRowV1::fee(GlobalFeeEffectInputV1 {
        lane_id: EconomicLaneIdV1::SpotLiquidity,
        asset_id: root(1),
        fee_id: root(3),
        charged_atoms: 10,
        allocated_atoms: 8,
        carried_residue_atoms: 1,
    });

    // Assert
    assert!(custody_valid.is_ok());
    assert_eq!(
        custody_neighbor,
        Err(GlobalEconomicEffectPlanErrorV1::CustodyClaimMismatch)
    );
    assert_eq!(
        custody_overflow,
        Err(GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow(
            "effect_sum"
        ))
    );
    assert!(fee_valid.is_ok());
    assert_eq!(
        fee_neighbor,
        Err(GlobalEconomicEffectPlanErrorV1::FeeAllocationMismatch)
    );
}

#[test]
fn self_transfers_and_nonchanging_writes_are_unrepresentable() {
    // Arrange / Act
    let transfer = GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        asset_id: root(1),
        source_id: root(2),
        destination_id: root(2),
        amount_atoms: 1,
    });
    let liability = GlobalEconomicEffectRowV1::liability(GlobalLiabilityEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: root(1),
        liability_id: root(3),
        pre_atoms: 9,
        post_atoms: 9,
    });
    let reserve = GlobalEconomicEffectRowV1::reserve(GlobalReserveEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZdexTokenomics,
        asset_id: root(1),
        reserve_id: root(4),
        pre_atoms: 9,
        post_atoms: 9,
    });
    let write = GlobalEconomicEffectRowV1::lane_write(
        EconomicLaneIdV1::AssetTransfer,
        root(5),
        root(6),
        root(6),
    );

    // Assert
    assert_eq!(
        transfer,
        Err(GlobalEconomicEffectPlanErrorV1::SelfTransfer(
            "account movement"
        ))
    );
    assert_eq!(
        liability,
        Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
            "liability"
        ))
    );
    assert_eq!(
        reserve,
        Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
            "reserve"
        ))
    );
    assert_eq!(
        write,
        Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
            "lane write"
        ))
    );
}

#[test]
fn two_transitions_cannot_write_the_same_unsequenced_target() {
    // Arrange
    let asset = root(10);
    let target = root(20);
    let first = GlobalEconomicEffectRowV1::liability(GlobalLiabilityEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: asset,
        liability_id: target,
        pre_atoms: 5,
        post_atoms: 7,
    })
    .unwrap();
    let second = GlobalEconomicEffectRowV1::liability(GlobalLiabilityEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: asset,
        liability_id: target,
        pre_atoms: 7,
        post_atoms: 8,
    })
    .unwrap();

    // Act
    let result = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![first, second],
        reconciliations: vec![reconciliation(asset, 1, 1, 1, 1, 5, 8, 0, 0)],
    });

    // Assert
    assert_eq!(
        rejection(result),
        GlobalEconomicEffectPlanErrorV1::DuplicateWriteTarget("liability", target)
    );
}

#[test]
fn row_identity_binds_variant_lane_asset_and_amount() {
    // Arrange
    let base = transfer_row(root(10), 5);
    let amount = transfer_row(root(10), 6);
    let lane = GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
        lane_id: EconomicLaneIdV1::SpotLiquidity,
        asset_id: root(10),
        source_id: root(20),
        destination_id: root(21),
        amount_atoms: 5,
    })
    .unwrap();
    let asset = transfer_row(root(11), 5);

    // Act
    let ids = [base, amount, lane, asset].map(|row| row.canonical_id().unwrap());

    // Assert
    assert_eq!(
        ids.into_iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        4
    );
}
