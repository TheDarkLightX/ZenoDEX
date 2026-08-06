use super::support::*;

#[test]
fn issue_and_burn_drive_owned_and_supply_equations_exactly() {
    // Arrange
    let asset = root(10);
    let scope = AuthorizationScopeIdV1::new([7; 32]).unwrap();
    let binding = ActionAuthorizationBindingIdV1::new([8; 32]).unwrap();
    let issue = GlobalEconomicEffectRowV1::issue_burn(GlobalIssueBurnInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: asset,
        kind: GlobalIssueBurnKindV1::Issue,
        bucket_id: root(20),
        amount_atoms: 5,
        authority_scope_id: scope,
        action_authorization_binding: binding,
    })
    .unwrap();
    let burn = GlobalEconomicEffectRowV1::issue_burn(GlobalIssueBurnInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: asset,
        kind: GlobalIssueBurnKindV1::Burn,
        bucket_id: root(21),
        amount_atoms: 2,
        authority_scope_id: scope,
        action_authorization_binding: binding,
    })
    .unwrap();

    // Act
    let accepted = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![issue.clone(), burn.clone()],
        reconciliations: vec![reconciliation(asset, 100, 103, 80, 83, 0, 0, 0, 0)],
    });
    let owned_neighbor = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![issue.clone(), burn.clone()],
        reconciliations: vec![reconciliation(asset, 100, 102, 80, 83, 0, 0, 0, 0)],
    });
    let supply_neighbor = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![issue, burn],
        reconciliations: vec![reconciliation(asset, 100, 103, 80, 82, 0, 0, 0, 0)],
    });

    // Assert
    assert!(accepted.is_ok());
    assert_eq!(
        rejection(owned_neighbor),
        GlobalEconomicEffectPlanErrorV1::OwnedConservationViolation(asset)
    );
    assert_eq!(
        rejection(supply_neighbor),
        GlobalEconomicEffectPlanErrorV1::SupplyConservationViolation(asset)
    );
}

#[test]
fn liability_and_named_reserve_totals_reconcile_changed_bucket_deltas() {
    // Arrange
    let asset = root(10);
    let liability = GlobalEconomicEffectRowV1::liability(GlobalLiabilityEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: asset,
        liability_id: root(20),
        pre_atoms: 5,
        post_atoms: 8,
    })
    .unwrap();
    let reserve = GlobalEconomicEffectRowV1::reserve(GlobalReserveEffectInputV1 {
        lane_id: EconomicLaneIdV1::ZdexTokenomics,
        asset_id: asset,
        reserve_id: root(21),
        pre_atoms: 7,
        post_atoms: 6,
    })
    .unwrap();

    // Act
    let accepted = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![liability.clone(), reserve.clone()],
        reconciliations: vec![reconciliation(asset, 100, 100, 100, 100, 20, 23, 30, 29)],
    });
    let bad_liability = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![liability.clone(), reserve.clone()],
        reconciliations: vec![reconciliation(asset, 100, 100, 100, 100, 20, 22, 30, 29)],
    });
    let bad_reserve = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![liability, reserve],
        reconciliations: vec![reconciliation(asset, 100, 100, 100, 100, 20, 23, 30, 30)],
    });

    // Assert
    assert!(accepted.is_ok());
    assert_eq!(
        rejection(bad_liability),
        GlobalEconomicEffectPlanErrorV1::LiabilityReconciliationViolation(asset)
    );
    assert_eq!(
        rejection(bad_reserve),
        GlobalEconomicEffectPlanErrorV1::ReserveReconciliationViolation(asset)
    );
}

#[test]
fn every_asset_has_one_and_only_one_reconciliation() {
    // Arrange
    let first = transfer_row(root(10), 1);
    let second = transfer_row(root(11), 1);
    let first_reconciliation = reconciliation(root(10), 1, 1, 1, 1, 0, 0, 0, 0);
    let second_reconciliation = reconciliation(root(11), 1, 1, 1, 1, 0, 0, 0, 0);

    // Act
    let missing = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![first.clone(), second],
        reconciliations: vec![first_reconciliation],
    });
    let duplicate = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![first.clone()],
        reconciliations: vec![first_reconciliation, first_reconciliation],
    });
    let extra = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![first],
        reconciliations: vec![first_reconciliation, second_reconciliation],
    });

    // Assert
    assert_eq!(
        rejection(missing),
        GlobalEconomicEffectPlanErrorV1::MissingAssetReconciliation(root(11))
    );
    assert_eq!(
        rejection(duplicate),
        GlobalEconomicEffectPlanErrorV1::DuplicateAssetReconciliation(root(10))
    );
    assert_eq!(
        rejection(extra),
        GlobalEconomicEffectPlanErrorV1::ReconciliationWithoutEffect(root(11))
    );
}

#[test]
fn duplicate_effect_rows_reject_after_canonicalization() {
    // Arrange
    let row = transfer_row(root(10), 1);

    // Act
    let result = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![row.clone(), row],
        reconciliations: vec![reconciliation(root(10), 1, 1, 1, 1, 0, 0, 0, 0)],
    });

    // Assert
    assert_eq!(
        rejection(result),
        GlobalEconomicEffectPlanErrorV1::DuplicateEffect
    );
}

#[test]
fn arithmetic_overflow_in_aggregate_reconciliation_fails_closed() {
    // Arrange
    let asset = root(10);
    let first = transfer_row(asset, u128::MAX);
    let second = GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
        lane_id: EconomicLaneIdV1::SpotLiquidity,
        asset_id: asset,
        source_id: root(30),
        destination_id: root(31),
        amount_atoms: 1,
    })
    .unwrap();

    // Act
    let result = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(200),
        effects: vec![first, second],
        reconciliations: vec![reconciliation(asset, 1, 1, 1, 1, 0, 0, 0, 0)],
    });

    // Assert
    assert_eq!(
        rejection(result),
        GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow("account_debit")
    );
}

#[test]
fn semantic_commitment_excludes_action_derived_authority_and_outbox_reference_ids() {
    // Arrange
    let asset = root(10);
    let scope = AuthorizationScopeIdV1::new([7; 32]).unwrap();
    let first_binding = ActionAuthorizationBindingIdV1::new([8; 32]).unwrap();
    let second_binding = ActionAuthorizationBindingIdV1::new([9; 32]).unwrap();
    let issue = |binding| {
        GlobalEconomicEffectRowV1::issue_burn(GlobalIssueBurnInputV1 {
            lane_id: EconomicLaneIdV1::ExternalCustody,
            asset_id: asset,
            kind: GlobalIssueBurnKindV1::Issue,
            bucket_id: root(20),
            amount_atoms: 1,
            authority_scope_id: scope,
            action_authorization_binding: binding,
        })
        .unwrap()
    };
    let make_body = |issue: GlobalEconomicEffectRowV1| {
        let outbox =
            GlobalEconomicEffectRowV1::external_outbox_enqueue(GlobalExternalOutboxInputV1 {
                outbox_id: root(30),
                destination_domain_id: domain_id(3),
                asset_id: asset,
                amount_atoms: 1,
                value_effect_id: issue.canonical_id().unwrap(),
                payload_commitment: root(31),
            })
            .unwrap();
        GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
            post_state_root: state_root(200),
            effects: vec![issue, outbox],
            reconciliations: vec![reconciliation(asset, 10, 11, 10, 11, 0, 0, 0, 0)],
        })
        .unwrap()
    };

    // Act
    let first = make_body(issue(first_binding));
    let second = make_body(issue(second_binding));

    // Assert
    assert_ne!(first.effect_rows_root(), second.effect_rows_root());
    assert_eq!(
        first.effect_semantics_root(),
        second.effect_semantics_root()
    );
    assert_eq!(first.effect_commitment(), second.effect_commitment());
}
