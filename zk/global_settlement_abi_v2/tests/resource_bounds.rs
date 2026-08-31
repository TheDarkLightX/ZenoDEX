use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, validate_asset_state_asset_count_v2,
    validate_asset_state_balance_row_count_v2, validate_consumed_object_id_count_v2,
    validate_consumed_occurrence_count_v2, validate_rootable_asset_state_canonical_bytes_v2,
    AbiErrorV2, AssetClassV2, AssetLaneStateV2, AssetOriginKindV2, AssetOriginRecordV2,
    AssetOriginRegistrationPolicyV2, AssetOriginRegistryStateV2, AssetSupplyV2,
    AssetTransferPolicyV2, AssetTransferStateV2, EconomicAmountV2, EconomicCommandOccurrenceV2,
    ManagedAssetLifecyclePolicyV2, ManagedAssetLifecycleStateV2, RootV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2, ASSET_ORIGIN_REGISTRY_SCHEMA_V2, ASSET_TRANSFER_MODULE_SCHEMA_V2,
    GLOBAL_SETTLEMENT_ABI_V2, MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
    MAX_ASSETS_PER_ASSET_STATE_V2, MAX_ASSET_LANE_ASSETS_V2, MAX_ASSET_LANE_BALANCE_ROWS_V2,
    MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2, MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2, MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2, MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2, MAX_TOKEN_BYTES_V2,
};

fn root(value: u64) -> RootV2 {
    RootV2::parse(
        format!("0x{value:064x}"),
        "resource-bounds test root",
        false,
    )
    .expect("test roots are canonical")
}

// A valid origin registry has at most 256 rows. Each row has one bounded token,
// three fixed-width roots, and fixed enum/key syntax; JSON escaping can at most
// double a printable token. A 1 KiB row envelope and 1 KiB state envelope are
// conservative, including policy token, keys, quotes, commas, and brackets.
// Therefore the origin-registry byte ceiling is defense-in-depth and unreachable
// for structurally valid current V2 records.
const MAX_VALID_ORIGIN_REGISTRY_ROW_CANONICAL_BYTES_V2: usize = 1_024;
const MAX_VALID_ORIGIN_REGISTRY_STATE_OVERHEAD_CANONICAL_BYTES_V2: usize = 1_024;
const MAX_VALID_ORIGIN_REGISTRY_CANONICAL_BYTES_UPPER_BOUND_V2: usize =
    MAX_VALID_ORIGIN_REGISTRY_STATE_OVERHEAD_CANONICAL_BYTES_V2
        + MAX_ASSETS_PER_ASSET_STATE_V2 * MAX_VALID_ORIGIN_REGISTRY_ROW_CANONICAL_BYTES_V2;

fn origin_record(index: usize) -> AssetOriginRecordV2 {
    AssetOriginRecordV2 {
        asset: format!("A{index:03}"),
        origin_kind: AssetOriginKindV2::TAU_ORIGINATED,
        origin_root: root(1_000 + index as u64),
        transfer_policy_root: root(2_000 + index as u64),
        issue_policy_root: RootV2::zero(),
        decimals: u64::from(ASSET_ATOM_DECIMALS_V2),
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
    }
}

fn origin_registry(asset_count: usize) -> AssetOriginRegistryStateV2 {
    AssetOriginRegistryStateV2 {
        schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
        module_release_id: root(1),
        policy: AssetOriginRegistrationPolicyV2 {
            authority_subject: "governance".to_owned(),
            authority_grant_root: root(2),
            allow_native: false,
            allow_tau_originated: true,
        },
        assets: (0..asset_count).map(origin_record).collect(),
    }
}

fn transfer_policy(asset: String) -> AssetTransferPolicyV2 {
    AssetTransferPolicyV2 {
        asset,
        fee_owner: "fees".to_owned(),
        transfer_fee_atoms: 0,
        enabled: true,
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: None,
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
    }
}

fn transfer_state(asset_count: usize) -> AssetTransferStateV2 {
    let policies = (0..asset_count)
        .map(|index| transfer_policy(format!("A{index:03}")))
        .collect::<Vec<_>>();
    let supplies = policies
        .iter()
        .map(|policy| AssetSupplyV2 {
            asset: policy.asset.clone(),
            amount_atoms: 0,
        })
        .collect();
    AssetTransferStateV2 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(3),
        policies,
        balances: Vec::new(),
        supplies,
    }
}

fn managed_policy(asset: String) -> ManagedAssetLifecyclePolicyV2 {
    ManagedAssetLifecyclePolicyV2 {
        asset,
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: None,
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject: None,
        issue_authorization_root: None,
        burn_authorization_root: None,
        enabled: true,
    }
}

fn managed_state(asset_count: usize) -> ManagedAssetLifecycleStateV2 {
    let policies = (0..asset_count)
        .map(|index| managed_policy(format!("A{index:03}")))
        .collect::<Vec<_>>();
    let supplies = policies
        .iter()
        .map(|policy| AssetSupplyV2 {
            asset: policy.asset.clone(),
            amount_atoms: 0,
        })
        .collect();
    ManagedAssetLifecycleStateV2 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(4),
        policies,
        balances: Vec::new(),
        supplies,
    }
}

fn single_asset_transfer_state(balance_count: usize) -> AssetTransferStateV2 {
    AssetTransferStateV2 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(5),
        policies: vec![transfer_policy("USD".to_owned())],
        balances: (0..balance_count)
            .map(|index| EconomicAmountV2 {
                owner: format!("owner-{index:04}"),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: 1,
            })
            .collect(),
        supplies: vec![AssetSupplyV2 {
            asset: "USD".to_owned(),
            amount_atoms: balance_count as u128,
        }],
    }
}

fn occurrence(consumed_object_ids: Vec<String>) -> EconomicCommandOccurrenceV2 {
    EconomicCommandOccurrenceV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: "test-chain".to_owned(),
        deployment_root: root(10),
        height: 7,
        tx_index: 1,
        op_index: 2,
        command_kind: "test-command".to_owned(),
        command_body_hash: root(11),
        route_release_id: root(12),
        subject_id: "alice".to_owned(),
        grant_root: root(13),
        nonce: 9,
        profile_root: root(14),
        pre_state_root: root(15),
        consumed_object_ids,
    }
}

#[test]
fn shared_limits_and_legacy_aliases_are_exact() {
    assert_eq!(MAX_ASSETS_PER_ASSET_STATE_V2, 256);
    assert_eq!(MAX_BALANCE_ROWS_PER_ASSET_STATE_V2, 4_096);
    assert_eq!(MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2, 1_048_576);
    assert_eq!(MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2, 64);
    assert_eq!(MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2, 64);
    assert_eq!(
        MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2,
        MAX_ASSETS_PER_ASSET_STATE_V2
    );
    assert_eq!(MAX_ASSET_LANE_ASSETS_V2, MAX_ASSETS_PER_ASSET_STATE_V2);
    assert_eq!(
        MAX_ASSET_LANE_BALANCE_ROWS_V2,
        MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
    );
    assert_eq!(
        MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2,
        MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    );
    assert_eq!(
        MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
        MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2
    );
}

#[test]
fn asset_count_bva_is_closed_before_deep_validation() {
    for count in [0, 1, 255, 256] {
        assert_eq!(
            origin_registry(count).validate(),
            Ok(()),
            "origin count {count}"
        );
        assert_eq!(
            transfer_state(count).validate(),
            Ok(()),
            "transfer count {count}"
        );
        assert_eq!(
            managed_state(count).validate(),
            Ok(()),
            "managed count {count}"
        );
        assert_eq!(
            validate_asset_state_asset_count_v2(count, "asset count BVA"),
            Ok(())
        );
    }
    assert_eq!(
        validate_asset_state_asset_count_v2(257, "asset count BVA"),
        Err(AbiErrorV2::InvalidBounds("asset count BVA"))
    );
    assert_eq!(
        origin_registry(257).validate(),
        Err(AbiErrorV2::InvalidBounds("asset origin registry assets"))
    );

    let poisoned_policy = AssetTransferPolicyV2 {
        asset: String::new(),
        ..transfer_policy("ignored".to_owned())
    };
    let poisoned_transfer = AssetTransferStateV2 {
        schema: "wrong-schema".to_owned(),
        module_release_id: RootV2::zero(),
        policies: vec![poisoned_policy; 257],
        balances: Vec::new(),
        supplies: Vec::new(),
    };
    assert_eq!(
        poisoned_transfer.validate(),
        Err(AbiErrorV2::InvalidBounds("asset transfer policies"))
    );

    let poisoned_managed_policy = ManagedAssetLifecyclePolicyV2 {
        asset: String::new(),
        ..managed_policy("ignored".to_owned())
    };
    let poisoned_managed = ManagedAssetLifecycleStateV2 {
        schema: "wrong-schema".to_owned(),
        module_release_id: RootV2::zero(),
        policies: vec![poisoned_managed_policy; 257],
        balances: Vec::new(),
        supplies: Vec::new(),
    };
    assert_eq!(
        poisoned_managed.validate(),
        Err(AbiErrorV2::InvalidBounds("managed asset policies"))
    );

    let poisoned_lane = AssetLaneStateV2 {
        schema: "wrong-schema".to_owned(),
        module_release_id: RootV2::zero(),
        origin_registry: origin_registry(257),
        transfer_policies: Vec::new(),
        managed_policies: Vec::new(),
        balances: Vec::new(),
        supplies: Vec::new(),
    };
    assert_eq!(
        poisoned_lane.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "asset lane origin registry assets"
        ))
    );
}

#[test]
fn balance_row_bva_is_closed_before_deep_validation() {
    for count in [0, 1, 4_095, 4_096] {
        assert_eq!(
            single_asset_transfer_state(count).validate(),
            Ok(()),
            "balance count {count}"
        );
        assert_eq!(
            validate_asset_state_balance_row_count_v2(count, "balance row BVA"),
            Ok(())
        );
    }
    assert_eq!(
        validate_asset_state_balance_row_count_v2(4_097, "balance row BVA"),
        Err(AbiErrorV2::InvalidBounds("balance row BVA"))
    );
    let mut poisoned = single_asset_transfer_state(4_097);
    poisoned.schema = "wrong-schema".to_owned();
    poisoned.module_release_id = RootV2::zero();
    poisoned.balances[0].owner = String::new();
    assert_eq!(
        poisoned.validate(),
        Err(AbiErrorV2::InvalidBounds("asset transfer balances"))
    );
}

#[test]
fn occurrence_and_refinement_bva_check_count_before_deep_validation() {
    for count in [0, 1, 63, 64] {
        let ids = (0..count)
            .map(|index| format!("object-{index:03}"))
            .collect();
        assert_eq!(
            occurrence(ids).validate(),
            Ok(()),
            "object-id count {count}"
        );
        assert_eq!(
            validate_consumed_object_id_count_v2(count, "object-id BVA"),
            Ok(())
        );
        assert_eq!(
            validate_consumed_occurrence_count_v2(count, "occurrence BVA"),
            Ok(())
        );
    }
    assert_eq!(
        validate_consumed_object_id_count_v2(65, "object-id BVA"),
        Err(AbiErrorV2::InvalidBounds("object-id BVA"))
    );
    assert_eq!(
        validate_consumed_occurrence_count_v2(65, "occurrence BVA"),
        Err(AbiErrorV2::InvalidBounds("occurrence BVA"))
    );

    let mut poisoned = occurrence(vec!["\npoison".to_owned(); 65]);
    poisoned.schema = "wrong-schema".to_owned();
    poisoned.deployment_root = RootV2::zero();
    assert_eq!(
        poisoned.validate(),
        Err(AbiErrorV2::InvalidBounds("occurrence consumed object ids"))
    );
}

fn maximal_but_structural_transfer_state() -> AssetTransferStateV2 {
    let padding = "x".repeat(156);
    let owner_padding = "y".repeat(154);
    let mut policies = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut supplies = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut balances = Vec::with_capacity(MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
    for asset_index in 0..MAX_ASSETS_PER_ASSET_STATE_V2 {
        let asset = format!("A{asset_index:03}{padding}");
        policies.push(AssetTransferPolicyV2 {
            asset: asset.clone(),
            fee_owner: format!("F{asset_index:03}{padding}"),
            transfer_fee_atoms: 0,
            enabled: true,
            asset_class: AssetClassV2::RegisteredOrdinaryToken,
            asset_origin_root: None,
            atom_decimals: ASSET_ATOM_DECIMALS_V2,
        });
        supplies.push(AssetSupplyV2 {
            asset: asset.clone(),
            amount_atoms: 16,
        });
        for owner_index in 0..16 {
            balances.push(EconomicAmountV2 {
                owner: format!("O{asset_index:03}{owner_index:02}{owner_padding}"),
                asset: asset.clone(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: 1,
            });
        }
    }
    AssetTransferStateV2 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(50),
        policies,
        balances,
        supplies,
    }
}

fn maximal_but_structural_managed_state() -> ManagedAssetLifecycleStateV2 {
    let padding = "x".repeat(156);
    let owner_padding = "y".repeat(154);
    let mut policies = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut supplies = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut balances = Vec::with_capacity(MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
    for asset_index in 0..MAX_ASSETS_PER_ASSET_STATE_V2 {
        let asset = format!("A{asset_index:03}{padding}");
        policies.push(ManagedAssetLifecyclePolicyV2 {
            asset: asset.clone(),
            asset_class: AssetClassV2::RegisteredOrdinaryToken,
            asset_origin_root: None,
            atom_decimals: ASSET_ATOM_DECIMALS_V2,
            issue_authority_subject: None,
            issue_authorization_root: None,
            burn_authorization_root: None,
            enabled: true,
        });
        supplies.push(AssetSupplyV2 {
            asset: asset.clone(),
            amount_atoms: 16,
        });
        for owner_index in 0..16 {
            balances.push(EconomicAmountV2 {
                owner: format!("O{asset_index:03}{owner_index:02}{owner_padding}"),
                asset: asset.clone(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: 1,
            });
        }
    }
    ManagedAssetLifecycleStateV2 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(51),
        policies,
        balances,
        supplies,
    }
}

fn maximal_but_structural_asset_lane_state() -> AssetLaneStateV2 {
    let padding = "x".repeat(156);
    let owner_padding = "y".repeat(154);
    let module_release_id = root(52);
    let mut assets = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut transfer_policies = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut supplies = Vec::with_capacity(MAX_ASSETS_PER_ASSET_STATE_V2);
    let mut balances = Vec::with_capacity(MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
    for asset_index in 0..MAX_ASSETS_PER_ASSET_STATE_V2 {
        let asset = format!("A{asset_index:03}{padding}");
        let origin_root = root(10_000 + asset_index as u64);
        assets.push(AssetOriginRecordV2 {
            asset: asset.clone(),
            origin_kind: AssetOriginKindV2::TAU_ORIGINATED,
            origin_root: origin_root.clone(),
            transfer_policy_root: root(20_000 + asset_index as u64),
            issue_policy_root: RootV2::zero(),
            decimals: u64::from(ASSET_ATOM_DECIMALS_V2),
            asset_class: AssetClassV2::RegisteredOrdinaryToken,
        });
        transfer_policies.push(AssetTransferPolicyV2 {
            asset: asset.clone(),
            fee_owner: format!("F{asset_index:03}{padding}"),
            transfer_fee_atoms: 0,
            enabled: true,
            asset_class: AssetClassV2::RegisteredOrdinaryToken,
            asset_origin_root: Some(origin_root),
            atom_decimals: ASSET_ATOM_DECIMALS_V2,
        });
        supplies.push(AssetSupplyV2 {
            asset: asset.clone(),
            amount_atoms: 16,
        });
        for owner_index in 0..16 {
            balances.push(EconomicAmountV2 {
                owner: format!("O{asset_index:03}{owner_index:02}{owner_padding}"),
                asset: asset.clone(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: 1,
            });
        }
    }
    AssetLaneStateV2 {
        schema: "zenodex/asset-lane-state/v2".to_owned(),
        module_release_id: module_release_id.clone(),
        origin_registry: AssetOriginRegistryStateV2 {
            schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
            module_release_id,
            policy: AssetOriginRegistrationPolicyV2 {
                authority_subject: "governance".to_owned(),
                authority_grant_root: root(53),
                allow_native: false,
                allow_tau_originated: true,
            },
            assets,
        },
        transfer_policies,
        managed_policies: Vec::new(),
        balances,
        supplies,
    }
}

fn maximally_sized_valid_origin_registry() -> AssetOriginRegistryStateV2 {
    let asset_padding = "x".repeat(MAX_TOKEN_BYTES_V2 - 4);
    AssetOriginRegistryStateV2 {
        schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
        module_release_id: root(54),
        policy: AssetOriginRegistrationPolicyV2 {
            authority_subject: "g".repeat(MAX_TOKEN_BYTES_V2),
            authority_grant_root: root(55),
            allow_native: false,
            allow_tau_originated: false,
        },
        assets: (0..MAX_ASSETS_PER_ASSET_STATE_V2)
            .map(|asset_index| AssetOriginRecordV2 {
                asset: format!("A{asset_index:03}{asset_padding}"),
                origin_kind: AssetOriginKindV2::TAU_ORIGINATED,
                origin_root: root(30_000 + asset_index as u64),
                transfer_policy_root: root(40_000 + asset_index as u64),
                issue_policy_root: RootV2::zero(),
                decimals: u64::from(ASSET_ATOM_DECIMALS_V2),
                asset_class: AssetClassV2::SealedBidPaymentOrInventory,
            })
            .collect(),
    }
}

#[test]
fn rootable_asset_state_byte_ceilings_and_origin_structural_envelope_hold() {
    assert_eq!(
        validate_rootable_asset_state_canonical_bytes_v2(
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
            "rootable byte BVA"
        ),
        Ok(())
    );
    assert_eq!(
        validate_rootable_asset_state_canonical_bytes_v2(
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 + 1,
            "rootable byte BVA"
        ),
        Err(AbiErrorV2::InvalidBounds("rootable byte BVA"))
    );

    let state = maximal_but_structural_transfer_state();
    assert!(
        canonical_bytes_v2(&state).expect("large state bytes").len()
            > MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    );
    assert_eq!(
        state.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "asset transfer state canonical encoding bytes"
        ))
    );

    let managed = maximal_but_structural_managed_state();
    assert!(
        canonical_bytes_v2(&managed)
            .expect("large managed-state bytes")
            .len()
            > MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    );
    assert_eq!(
        managed.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "managed asset lifecycle state canonical encoding bytes"
        ))
    );

    let lane = maximal_but_structural_asset_lane_state();
    assert!(
        canonical_bytes_v2(&lane)
            .expect("large aggregate lane bytes")
            .len()
            > MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    );
    assert_eq!(
        lane.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "asset lane state canonical encoding bytes"
        ))
    );

    assert!(
        MAX_VALID_ORIGIN_REGISTRY_CANONICAL_BYTES_UPPER_BOUND_V2
            < MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
        "origin registry structural ceilings must stay below the byte ceiling"
    );
    let origin = maximally_sized_valid_origin_registry();
    assert_eq!(
        origin.validate(),
        Ok(()),
        "maximal structurally valid origin registry"
    );
    assert_eq!(origin.assets.len(), MAX_ASSETS_PER_ASSET_STATE_V2);
    assert_eq!(origin.policy.authority_subject.len(), MAX_TOKEN_BYTES_V2);
    assert!(origin
        .assets
        .iter()
        .all(|row| row.asset.len() == MAX_TOKEN_BYTES_V2));
    let origin_bytes = canonical_bytes_v2(&origin).expect("maximal origin bytes");
    assert!(
        origin_bytes.len() <= MAX_VALID_ORIGIN_REGISTRY_CANONICAL_BYTES_UPPER_BOUND_V2,
        "maximal valid origin registry fits its conservative structural envelope"
    );
    assert!(origin_bytes.len() < MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2);

    let mut structurally_invalid = state;
    structurally_invalid.schema = "wrong-schema".to_owned();
    assert_eq!(
        structurally_invalid.validate(),
        Err(AbiErrorV2::InvalidSchema("asset transfer state"))
    );
}
