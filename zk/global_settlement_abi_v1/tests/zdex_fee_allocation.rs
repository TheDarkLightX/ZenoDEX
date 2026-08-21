use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, transition_zdex_fee_allocation_v1, AbiResultV1,
    EconomicEffectKindV1, RootV1, ZDEXFeeAllocationAcceptedV1, ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1, ZDEXFeeAllocationPolicyV1, ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeAllocationResultV1, ZDEXFeeDestinationAmountV1, ZDEXFeeShareV1, ZDEXFeeStateV1,
    ZDEX_FEE_DESTINATIONS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root")
}

fn policy(bps: [u16; 6]) -> ZDEXFeeAllocationPolicyV1 {
    ZDEXFeeAllocationPolicyV1 {
        shares: ZDEX_FEE_DESTINATIONS_V1
            .into_iter()
            .zip(bps)
            .map(|(destination, share_bps)| ZDEXFeeShareV1 {
                destination,
                share_bps,
            })
            .collect(),
    }
}

fn state(policy: &ZDEXFeeAllocationPolicyV1, ingress_atoms: u128) -> AbiResultV1<ZDEXFeeStateV1> {
    let state = ZDEXFeeStateV1 {
        fee_asset_id: root(40),
        policy_root: policy.policy_root()?,
        fee_ingress_atoms: ingress_atoms,
        unallocated_reserve_atoms: 700,
        destination_balances: ZDEX_FEE_DESTINATIONS_V1
            .into_iter()
            .zip([10, 20, 30, 40, 50, 60])
            .map(
                |(destination, allocation_atoms)| ZDEXFeeDestinationAmountV1 {
                    destination,
                    allocation_atoms,
                },
            )
            .collect(),
        owned_and_custodied_atoms: 1_000_000,
        supply_atoms: 1_000_000,
    };
    state.validate()?;
    Ok(state)
}

fn context(policy: &ZDEXFeeAllocationPolicyV1) -> AbiResultV1<ZDEXFeeAllocationContextV1> {
    Ok(ZDEXFeeAllocationContextV1 {
        chain_id: "zenodex-shadow".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 11,
        allocation_route_release_id: root(3),
        authorized_buyback_route_release_id: root(4),
        tokenomics_module_release_id: root(5),
        command_occurrence_id: root(6),
        policy_root: policy.policy_root()?,
    })
}

fn accepted(
    policy: &ZDEXFeeAllocationPolicyV1,
    pre_state: &ZDEXFeeStateV1,
    fee_atoms: u128,
) -> AbiResultV1<ZDEXFeeAllocationAcceptedV1> {
    match transition_zdex_fee_allocation_v1(
        &context(policy)?,
        pre_state,
        policy,
        &ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: fee_atoms,
        },
    )? {
        ZDEXFeeAllocationResultV1::Accepted(value) => Ok(*value),
        ZDEXFeeAllocationResultV1::Rejected(value) => {
            panic!("unexpected rejection: {:?}", value.code)
        }
    }
}

#[test]
fn candidate_policy_assigns_exact_budget_and_carries_residue() -> AbiResultV1<()> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let pre_state = state(&policy, 50_000)?;

    let result = accepted(&policy, &pre_state, 10_003)?;

    assert_eq!(
        result
            .occurrence
            .allocations
            .iter()
            .map(|row| row.allocation_atoms)
            .collect::<Vec<_>>(),
        vec![2_000, 0, 3_000, 1_000, 1_000, 500]
    );
    assert_eq!(result.occurrence.buyback_quote_atoms(), 2_000);
    assert_eq!(result.occurrence.carried_residue_atoms, 2_503);
    assert_eq!(result.post_state.fee_ingress_atoms, 39_997);
    assert_eq!(result.post_state.unallocated_reserve_atoms, 3_203);
    assert_eq!(
        result
            .post_state
            .destination_balances
            .iter()
            .map(|row| row.allocation_atoms)
            .collect::<Vec<_>>(),
        vec![2_010, 20, 3_030, 1_040, 1_050, 560]
    );
    Ok(())
}

#[test]
fn effect_projection_reconciles_fee_and_selected_balances() -> AbiResultV1<()> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let pre_state = state(&policy, 50_000)?;

    let result = accepted(&policy, &pre_state, 10_003)?;

    assert_eq!(
        result
            .effects
            .rows
            .iter()
            .filter(|row| row.kind == EconomicEffectKindV1::CUSTODY)
            .count(),
        1
    );
    assert_eq!(
        result
            .effects
            .rows
            .iter()
            .filter(|row| row.kind == EconomicEffectKindV1::FEE_ALLOCATION)
            .count(),
        5
    );
    assert_eq!(
        result
            .effects
            .rows
            .iter()
            .map(|row| row.delta_atoms)
            .sum::<i128>(),
        0
    );
    assert_eq!(result.effects.fee_conservation[0].fee_charged_atoms, 10_003);
    assert_eq!(
        result.effects.fee_conservation[0].current_allocations_atoms,
        7_500
    );
    assert_eq!(
        result.effects.fee_conservation[0].carried_residue_atoms,
        2_503
    );
    assert_eq!(
        pre_state.selected_balance_atoms()?,
        result.post_state.selected_balance_atoms()?
    );
    assert_eq!(
        result.occurrence.effect_plan_root,
        result.effects.effect_plan_root()?
    );
    Ok(())
}

#[test]
fn denominator_boundary_values_reconcile() -> AbiResultV1<()> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let pre_state = state(&policy, 50_000)?;

    for (fee_atoms, residue_atoms) in [(1, 1), (9_999, 2_504), (10_000, 2_500), (10_001, 2_501)] {
        let result = accepted(&policy, &pre_state, fee_atoms)?;
        let allocated: u128 = result
            .occurrence
            .allocations
            .iter()
            .map(|row| row.allocation_atoms)
            .sum();
        assert_eq!(
            allocated + result.occurrence.carried_residue_atoms,
            fee_atoms
        );
        assert_eq!(result.occurrence.carried_residue_atoms, residue_atoms);
    }
    Ok(())
}

#[test]
fn exhaustive_small_domain_conserves_each_policy() -> AbiResultV1<()> {
    for policy in [
        policy([2_000, 0, 3_000, 1_000, 1_000, 500]),
        policy([10_000, 0, 0, 0, 0, 0]),
        policy([1_667, 1_667, 1_667, 1_667, 1_666, 1_666]),
        policy([0, 0, 0, 0, 0, 0]),
    ] {
        policy.validate()?;
        let pre_state = state(&policy, 200)?;
        for fee_atoms in 1..=200 {
            let result = accepted(&policy, &pre_state, fee_atoms)?;
            let allocated: u128 = result
                .occurrence
                .allocations
                .iter()
                .map(|row| row.allocation_atoms)
                .sum();
            for (allocation, share) in result.occurrence.allocations.iter().zip(&policy.shares) {
                assert_eq!(
                    allocation.allocation_atoms,
                    fee_atoms * u128::from(share.share_bps) / 10_000
                );
            }
            assert_eq!(
                allocated + result.occurrence.carried_residue_atoms,
                fee_atoms
            );
            assert_eq!(
                pre_state.selected_balance_atoms()?,
                result.post_state.selected_balance_atoms()?
            );
        }
    }
    Ok(())
}

#[test]
fn domain_rejections_are_exact_noops() -> AbiResultV1<()> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let pre_state = ZDEXFeeStateV1 {
        fee_asset_id: root(40),
        policy_root: policy.policy_root()?,
        fee_ingress_atoms: i128::MAX as u128 + 1,
        unallocated_reserve_atoms: 0,
        destination_balances: ZDEX_FEE_DESTINATIONS_V1
            .into_iter()
            .map(|destination| ZDEXFeeDestinationAmountV1 {
                destination,
                allocation_atoms: 0,
            })
            .collect(),
        owned_and_custodied_atoms: i128::MAX as u128 + 1,
        supply_atoms: i128::MAX as u128 + 1,
    };
    pre_state.validate()?;
    for (fee_atoms, code) in [
        (0, ZDEXFeeAllocationRejectCodeV1::ZERO_FEE),
        (
            i128::MAX as u128 + 1,
            ZDEXFeeAllocationRejectCodeV1::EFFECT_WIDTH_EXCEEDED,
        ),
    ] {
        let result = transition_zdex_fee_allocation_v1(
            &context(&policy)?,
            &pre_state,
            &policy,
            &ZDEXFeeAllocationCommandV1 {
                fee_charged_atoms: fee_atoms,
            },
        )?;
        let ZDEXFeeAllocationResultV1::Rejected(rejected) = result else {
            panic!("expected rejection")
        };
        assert_eq!(rejected.code, code);
        assert_eq!(rejected.pre_state, rejected.post_state);
        assert!(rejected.effects.is_empty());
    }
    Ok(())
}

#[test]
fn insufficient_ingress_and_policy_drift_are_noops() -> AbiResultV1<()> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let pre_state = state(&policy, 3)?;
    let mut drifted_context = context(&policy)?;
    drifted_context.policy_root = root(99);

    for (context, fee_atoms, code) in [
        (
            context(&policy)?,
            4,
            ZDEXFeeAllocationRejectCodeV1::INSUFFICIENT_FEE_INGRESS,
        ),
        (
            drifted_context,
            1,
            ZDEXFeeAllocationRejectCodeV1::POLICY_MISMATCH,
        ),
    ] {
        let result = transition_zdex_fee_allocation_v1(
            &context,
            &pre_state,
            &policy,
            &ZDEXFeeAllocationCommandV1 {
                fee_charged_atoms: fee_atoms,
            },
        )?;
        let ZDEXFeeAllocationResultV1::Rejected(rejected) = result else {
            panic!("expected rejection")
        };
        assert_eq!(rejected.code, code);
        assert_eq!(rejected.pre_state, rejected.post_state);
        assert!(rejected.effects.is_empty());
    }
    Ok(())
}

#[test]
fn policy_requires_closed_order_and_bounded_total() {
    let mut reordered = candidate_zdex_fee_allocation_policy_v1();
    reordered.shares.swap(0, 1);
    assert!(reordered.validate().is_err());

    let overallocated = policy([10_000, 1, 0, 0, 0, 0]);
    assert!(overallocated.validate().is_err());

    let unknown_field = serde_json::from_value::<ZDEXFeeAllocationPolicyV1>(json!({
        "shares": [],
        "unexpected": true,
    }));
    assert!(unknown_field.is_err());
}

#[test]
fn occurrence_root_binds_authorized_buyback_route() -> AbiResultV1<()> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let pre_state = state(&policy, 50_000)?;
    let first = accepted(&policy, &pre_state, 10_003)?;
    let second = accepted(&policy, &pre_state, 10_003)?;
    let mut changed_context = context(&policy)?;
    changed_context.authorized_buyback_route_release_id = root(77);
    let changed = match transition_zdex_fee_allocation_v1(
        &changed_context,
        &pre_state,
        &policy,
        &ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: 10_003,
        },
    )? {
        ZDEXFeeAllocationResultV1::Accepted(value) => *value,
        ZDEXFeeAllocationResultV1::Rejected(value) => {
            panic!("unexpected rejection: {:?}", value.code)
        }
    };

    assert_eq!(
        policy.policy_root()?.as_str(),
        "0xd810507e5d15fd874a2e75b6f32b71b47174a799b8015301700e4554614032c2"
    );
    assert_eq!(
        first.pre_state.state_root()?.as_str(),
        "0x0a8970da266b0587f8b5f8e20cb410d95d947b6661ff01eb626430cb0406fffe"
    );
    assert_eq!(
        first.post_state.state_root()?.as_str(),
        "0xd0769fc96bd93c73b730d272ef2b7d3dd141756409177fd02db0bb425d2d4b4d"
    );
    assert_eq!(
        first.effects.effect_plan_root()?.as_str(),
        "0xe9a396bb00a9c8f09982ed5472dea6b4069b5f6fab76053ef1bc226927142c56"
    );
    assert_eq!(
        first.occurrence.occurrence_root()?.as_str(),
        "0x542ce727f7bff325c7a81d1fcd1e69e5c96a16b476605feabc2d7fa16928ac02"
    );
    assert_eq!(
        first.occurrence.occurrence_root()?,
        second.occurrence.occurrence_root()?
    );
    assert_ne!(
        first.occurrence.occurrence_root()?,
        changed.occurrence.occurrence_root()?
    );
    Ok(())
}

#[test]
fn complete_policy_allocates_every_atom_without_residue() -> AbiResultV1<()> {
    let policy = policy([10_000, 0, 0, 0, 0, 0]);
    let pre_state = state(&policy, 37)?;

    let result = accepted(&policy, &pre_state, 37)?;

    assert_eq!(result.occurrence.buyback_quote_atoms(), 37);
    assert_eq!(result.occurrence.carried_residue_atoms, 0);
    assert!(result
        .effects
        .rows
        .iter()
        .all(|row| row.kind != EconomicEffectKindV1::RESERVE));
    Ok(())
}

#[test]
fn governed_host_share_targets_only_aggregate_qualified_pool() -> AbiResultV1<()> {
    let policy = policy([0, 10_000, 0, 0, 0, 0]);
    let pre_state = state(&policy, 37)?;

    let result = accepted(&policy, &pre_state, 37)?;

    let host_effect = result
        .effects
        .rows
        .iter()
        .find(|row| row.kind == EconomicEffectKindV1::FEE_ALLOCATION)
        .expect("host allocation effect");
    assert_eq!(host_effect.principal, "protocol:fee-qualified-host-pool");
    assert_eq!(host_effect.delta_atoms, 37);
    assert_eq!(result.occurrence.allocations[1].allocation_atoms, 37);
    Ok(())
}
