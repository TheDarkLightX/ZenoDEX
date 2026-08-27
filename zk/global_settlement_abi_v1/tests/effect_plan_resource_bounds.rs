use zenodex_global_settlement_abi_v1::*;

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "resource-bound test root", false).unwrap()
}

fn empty_plan() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

#[test]
fn effect_plan_vector_bounds_accept_all_exact_maxima() {
    // Arrange
    let mut lanes = ALL_LANE_IDS_V1.to_vec();
    lanes.sort_by_key(|lane| format!("{lane:?}"));
    let plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: (0..MAX_EFFECT_PLAN_ROWS_V1)
            .map(|index| EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                principal: format!("principal-{index:04}"),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                delta_atoms: 1,
            })
            .collect(),
        asset_conservation: (0..MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1)
            .map(|index| AssetConservationRowV1 {
                asset: format!("ASSET-{index:03}"),
                owned_and_custodied_pre_atoms: 0,
                owned_and_custodied_post_atoms: 0,
                supply_pre_atoms: 0,
                supply_post_atoms: 0,
                authorized_issue_atoms: 0,
                authorized_burn_atoms: 0,
            })
            .collect(),
        fee_conservation: (0..MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1)
            .map(|index| FeeConservationRowV1 {
                asset: format!("FEE-{index:03}"),
                fee_charged_atoms: 0,
                current_allocations_atoms: 0,
                carried_residue_atoms: 0,
            })
            .collect(),
        lane_writes: lanes
            .into_iter()
            .map(|lane_id| LaneWriteV1 {
                lane_id,
                pre_root: root(1),
                post_root: root(2),
            })
            .collect(),
        occurrence_consumptions: (0..MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1)
            .map(|index| root(100 + u64::try_from(index).unwrap()))
            .collect(),
        external_outbox_enqueue: (0..MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1)
            .map(|index| ExternalOutboxEnqueueV1 {
                effect_id: root(10_000 + u64::try_from(index).unwrap()),
                destination_id: format!("registered-bridge-{index:04}"),
                payload_hash: root(20_000 + u64::try_from(index).unwrap()),
                adapter_profile_root: root(30_000),
            })
            .collect(),
    };

    // Act / Assert
    assert_eq!(plan.lane_writes.len(), MAX_EFFECT_PLAN_LANE_WRITES_V1);
    assert!(plan.validate().is_ok());
}

#[test]
fn each_effect_plan_vector_rejects_its_own_maximum_plus_one() {
    // Arrange / Act / Assert: every assertion independently kills one bound.
    let mut plan = empty_plan();
    plan.rows = vec![
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
            principal: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            delta_atoms: 1,
        };
        MAX_EFFECT_PLAN_ROWS_V1 + 1
    ];
    assert_eq!(
        plan.validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("economic effect plan rows")
    );

    let mut plan = empty_plan();
    plan.asset_conservation = vec![
        AssetConservationRowV1 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: 0,
            owned_and_custodied_post_atoms: 0,
            supply_pre_atoms: 0,
            supply_post_atoms: 0,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        };
        MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1 + 1
    ];
    assert_eq!(
        plan.validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("economic effect plan asset conservation rows")
    );

    let mut plan = empty_plan();
    plan.fee_conservation = vec![
        FeeConservationRowV1 {
            asset: "USD".to_owned(),
            fee_charged_atoms: 0,
            current_allocations_atoms: 0,
            carried_residue_atoms: 0,
        };
        MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1 + 1
    ];
    assert_eq!(
        plan.validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("economic effect plan fee conservation rows")
    );

    let mut plan = empty_plan();
    plan.lane_writes = vec![
        LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: root(1),
            post_root: root(2),
        };
        MAX_EFFECT_PLAN_LANE_WRITES_V1 + 1
    ];
    assert_eq!(
        plan.validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("economic effect plan lane writes")
    );

    let mut plan = empty_plan();
    plan.occurrence_consumptions = vec![root(1); MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1 + 1];
    assert_eq!(
        plan.validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("economic effect plan occurrence consumptions")
    );

    let mut plan = empty_plan();
    plan.external_outbox_enqueue = vec![
        ExternalOutboxEnqueueV1 {
            effect_id: root(1),
            destination_id: "registered-bridge".to_owned(),
            payload_hash: root(2),
            adapter_profile_root: root(3),
        };
        MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1 + 1
    ];
    assert_eq!(
        plan.validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("economic effect plan external outbox rows")
    );
}

#[test]
fn asset_lane_projection_rejects_each_maximum_plus_one_before_row_traversal() {
    let amount = EconomicAmountV1 {
        owner: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "accounts".to_owned(),
        amount_atoms: 1,
    };
    let projection = |balances, custody, supplies| AssetLaneStateProjectionV1 {
        schema: ASSET_LANE_STATE_PROJECTION_SCHEMA_V1.to_owned(),
        asset_policy_registry_root: root(1),
        fee_policy_registry_root: root(2),
        balances,
        custody,
        supplies,
    };

    // Arrange / Act / Assert: duplicate rows would fail ordering if traversal
    // occurred, so each exact InvalidBounds result proves early admission.
    assert_eq!(
        projection(
            vec![amount.clone(); MAX_ASSET_BALANCE_ROWS_V1 + 1],
            vec![],
            vec![]
        )
        .validate()
        .unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane balance rows")
    );
    let mut accounting_location = amount;
    accounting_location.custody_domain = "pool".to_owned();
    assert_eq!(
        projection(
            vec![],
            vec![accounting_location; MAX_ASSET_CUSTODY_ROWS_V1 + 1],
            vec![]
        )
        .validate()
        .unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane declared accounting-location rows")
    );
    assert_eq!(
        projection(
            vec![],
            vec![],
            vec![
                AssetSupplyV1 {
                    asset: "USD".to_owned(),
                    amount_atoms: 0,
                };
                MAX_ASSET_POLICY_ROWS_V1 + 1
            ]
        )
        .validate()
        .unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane supply rows")
    );
}

#[test]
fn asset_lane_projection_accepts_all_exact_resource_maxima() {
    // Arrange: 256 assets with 16 account rows and 16 declared
    // accounting-location rows each reach all three independent ceilings.
    let mut balances = Vec::with_capacity(MAX_ASSET_BALANCE_ROWS_V1);
    let mut accounting_locations = Vec::with_capacity(MAX_ASSET_CUSTODY_ROWS_V1);
    let mut supplies = Vec::with_capacity(MAX_ASSET_POLICY_ROWS_V1);
    for asset_index in 0..MAX_ASSET_POLICY_ROWS_V1 {
        let asset = format!("ASSET-{asset_index:03}");
        for owner_index in 0..16 {
            balances.push(EconomicAmountV1 {
                owner: format!("account-{owner_index:02}"),
                asset: asset.clone(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 1,
            });
            accounting_locations.push(EconomicAmountV1 {
                owner: format!("pool-{owner_index:02}"),
                asset: asset.clone(),
                custody_domain: "pools".to_owned(),
                amount_atoms: 1,
            });
        }
        supplies.push(AssetSupplyV1 {
            asset,
            amount_atoms: 32,
        });
    }
    let projection = AssetLaneStateProjectionV1 {
        schema: ASSET_LANE_STATE_PROJECTION_SCHEMA_V1.to_owned(),
        asset_policy_registry_root: root(1),
        fee_policy_registry_root: root(2),
        balances,
        custody: accounting_locations,
        supplies,
    };

    // Act
    let result = projection.validate();

    // Assert: changing any projection ceiling from `>` to `>=` rejects this
    // exact-limit witness.
    assert_eq!(projection.balances.len(), MAX_ASSET_BALANCE_ROWS_V1);
    assert_eq!(projection.custody.len(), MAX_ASSET_CUSTODY_ROWS_V1);
    assert_eq!(projection.supplies.len(), MAX_ASSET_POLICY_ROWS_V1);
    assert_eq!(result, Ok(()));
}
