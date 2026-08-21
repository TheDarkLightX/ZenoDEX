use zenodex_global_settlement_abi_v1::{
    build_zdex_tokenomics_fee_allocation_module_journal_v1,
    build_zdex_tokenomics_fee_allocation_private_port_v1, candidate_zdex_fee_allocation_policy_v1,
    compose_zdex_tokenomics_fee_allocation_lane_v1, transition_zdex_fee_allocation_v1, AbiResultV1,
    EconomicEffectKindV1, LaneIdV1, LaneWriteV1, RootV1, ZDEXAmountBucketV1,
    ZDEXFeeAllocationAcceptedV1, ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationResultV1, ZDEXFeeDestinationAmountV1, ZDEXFeeDestinationV1, ZDEXFeeStateV1,
    ZDEXSupplyStateV1, ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    ZDEXTokenomicsFeeAllocationLaneCandidateV1, ZDEXTokenomicsFeeAllocationPrivatePortV1,
    ZDEXTokenomicsLaneCompositionResultV1, ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1, ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1,
    ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).unwrap()
}

fn root_hex(value: &str) -> RootV1 {
    RootV1::parse(value, "golden root", false).unwrap()
}

fn fee_state(asset_ordinal: u64, policy_root: RootV1) -> ZDEXFeeStateV1 {
    let destinations = [
        ZDEXFeeDestinationV1::BUYBACK,
        ZDEXFeeDestinationV1::QUALIFIED_HOST_POOL,
        ZDEXFeeDestinationV1::TREASURY,
        ZDEXFeeDestinationV1::PROOF_REWARDS,
        ZDEXFeeDestinationV1::COVER_RESERVE,
        ZDEXFeeDestinationV1::LP_REBATES,
    ];
    ZDEXFeeStateV1 {
        fee_asset_id: root(asset_ordinal),
        policy_root,
        fee_ingress_atoms: 50_000,
        unallocated_reserve_atoms: 700,
        destination_balances: destinations
            .into_iter()
            .enumerate()
            .map(|(index, destination)| ZDEXFeeDestinationAmountV1 {
                destination,
                allocation_atoms: (index as u128 + 1) * 10,
            })
            .collect(),
        owned_and_custodied_atoms: 1_000_000,
        supply_atoms: 1_000_000,
    }
}

fn accepted() -> AbiResultV1<ZDEXFeeAllocationAcceptedV1> {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let context = ZDEXFeeAllocationContextV1 {
        chain_id: "zenodex-shadow".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 11,
        allocation_route_release_id: root(3),
        authorized_buyback_route_release_id: root(4),
        tokenomics_module_release_id: root(5),
        command_occurrence_id: root(6),
        policy_root: policy.policy_root()?,
    };
    match transition_zdex_fee_allocation_v1(
        &context,
        &fee_state(40, policy.policy_root()?),
        &policy,
        &ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: 10_003,
        },
    )? {
        ZDEXFeeAllocationResultV1::Accepted(value) => Ok(*value),
        ZDEXFeeAllocationResultV1::Rejected(value) => {
            panic!("fixture rejected: {:?}", value.code)
        }
    }
}

fn supply_state() -> ZDEXSupplyStateV1 {
    ZDEXSupplyStateV1 {
        asset_id: root(90),
        policy_root: root(91),
        decimals: 8,
        precision_epoch: 0,
        live_supply_atoms: 1_000,
        buckets: vec![ZDEXAmountBucketV1 {
            bucket_id: "wallet:alice".to_owned(),
            amount_atoms: 1_000,
        }],
        burn_budget_epoch: 5,
        remaining_epoch_burn_cap_atoms: 100,
    }
}

fn lane_state(target: ZDEXFeeStateV1) -> ZDEXTokenomicsLaneStateV1 {
    ZDEXTokenomicsLaneStateV1 {
        schema: ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1.to_owned(),
        supply_state: supply_state(),
        fee_allocation_states: vec![target, fee_state(41, root(50))],
        staking_state_root: root(31),
        host_claims_state_root: root(32),
        treasury_claims_state_root: root(33),
        proof_rewards_state_root: root(34),
        cover_reserve_state_root: root(35),
        lp_rebates_state_root: root(36),
    }
}

struct Fixture {
    context: ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    module: zenodex_global_settlement_abi_v1::LaneModuleTransitionJournalV1,
    port: ZDEXTokenomicsFeeAllocationPrivatePortV1,
    pre_state: ZDEXTokenomicsLaneStateV1,
    post_state: ZDEXTokenomicsLaneStateV1,
    allocation: ZDEXFeeAllocationAcceptedV1,
    policy: zenodex_global_settlement_abi_v1::ZDEXFeeAllocationPolicyV1,
}

impl Fixture {
    fn candidate(&self) -> ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_> {
        ZDEXTokenomicsFeeAllocationLaneCandidateV1 {
            context: &self.context,
            module_journal: &self.module,
            private_port: &self.port,
            pre_state: &self.pre_state,
            post_state: &self.post_state,
            allocation: &self.allocation,
            policy: &self.policy,
        }
    }
}

fn fixture() -> AbiResultV1<Fixture> {
    let allocation = accepted()?;
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let port = build_zdex_tokenomics_fee_allocation_private_port_v1(&allocation, &policy)?;
    let module =
        build_zdex_tokenomics_fee_allocation_module_journal_v1(&allocation, &policy, &port)?;
    let occurrence = &allocation.occurrence;
    let context = ZDEXTokenomicsFeeAllocationCoordinatorContextV1 {
        schema: ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: occurrence.writer_epoch,
        coordinator_release_id: root(7),
        allocation_route_release_id: occurrence.allocation_route_release_id.clone(),
        authorized_buyback_route_release_id: occurrence.authorized_buyback_route_release_id.clone(),
        tokenomics_module_release_id: occurrence.tokenomics_module_release_id.clone(),
        command_occurrence_id: occurrence.command_occurrence_id.clone(),
        policy_root: occurrence.policy_root.clone(),
    };
    Ok(Fixture {
        context,
        module,
        port,
        pre_state: lane_state(allocation.pre_state.clone()),
        post_state: lane_state(allocation.post_state.clone()),
        allocation,
        policy,
    })
}

#[test]
fn fee_substate_is_embedded_in_one_complete_lane_write() -> AbiResultV1<()> {
    // Arrange
    let fixture = fixture()?;

    // Act
    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate())?;

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(result) = result else {
        panic!("valid fee composition rejected")
    };
    assert_eq!(result.post_state, fixture.post_state);
    assert_eq!(
        result.lane_journal.pre_lane_root,
        fixture.pre_state.state_root()?
    );
    assert_eq!(
        result.lane_journal.post_lane_root,
        fixture.post_state.state_root()?
    );
    assert!(result.lane_journal.terminal_obligations_root.is_zero());
    assert_eq!(result.effects.lane_writes.len(), 1);
    assert_eq!(result.effects.rows, fixture.allocation.effects.rows);
    assert_eq!(
        result.effects.fee_conservation,
        fixture.allocation.effects.fee_conservation
    );
    assert_eq!(
        fixture.allocation.occurrence.occurrence_root()?,
        root_hex("0xc00e0d5f4f83c82a18ba0b552aa0129d497be0806b2f833541b937fae16fac4e")
    );
    assert_eq!(
        fixture.port.port_root()?,
        root_hex("0x532e46cd7be6a84d3b610c7ae362d81bca67ce6baffe14d80087824adaf211aa")
    );
    assert_eq!(
        fixture.module.journal_root()?,
        root_hex("0x3f9ff650e0d9e17de0535390db14c7cde561056f206fe62a5eb6da9890b99cf7")
    );
    assert_eq!(
        result.effects.effect_plan_root()?,
        root_hex("0x7e6b5578cc8279ab06cd812e4c2c882b7df4008a1e612e860a769149bb265ca0")
    );
    assert_eq!(
        result.lane_journal.journal_root()?,
        root_hex("0x0a2395ac0ad4a73d6fa2f8dc902541cfdf0b554c96657bc7dd64aa8178d59db6")
    );
    Ok(())
}

#[test]
fn partial_fee_substate_cannot_claim_complete_lane_roots() -> AbiResultV1<()> {
    // Arrange
    let mut fixture = fixture()?;
    fixture.module.pre_lane_root = fixture.allocation.pre_state.state_root()?;
    fixture.module.post_lane_root = fixture.allocation.post_state.state_root()?;

    // Act
    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate())?;

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(result) = result else {
        panic!("partial roots accepted")
    };
    assert_eq!(
        result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PARTIAL_LANE_ROOT_CLAIM
    );
    assert!(result.effects.is_empty());
    Ok(())
}

#[test]
fn unrelated_component_mutations_reject_as_exact_no_ops() -> AbiResultV1<()> {
    for mutation in 0..3 {
        // Arrange
        let mut fixture = fixture()?;
        match mutation {
            0 => fixture.post_state.supply_state.precision_epoch = 1,
            1 => fixture.post_state.fee_allocation_states[1].fee_ingress_atoms = 49_999,
            _ => fixture.post_state.staking_state_root = root(99),
        }

        // Act
        let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate())?;

        // Assert
        let ZDEXTokenomicsLaneCompositionResultV1::Rejected(result) = result else {
            panic!("unrelated mutation accepted")
        };
        assert_eq!(
            result.code,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::UNRELATED_STATE_MUTATION
        );
        assert_eq!(result.pre_lane_root, result.post_lane_root);
        assert!(result.effects.is_empty());
    }
    Ok(())
}

#[test]
fn wrong_target_post_substate_rejects_without_effects() -> AbiResultV1<()> {
    // Arrange
    let mut fixture = fixture()?;
    fixture.post_state.fee_allocation_states[0].fee_ingress_atoms = 40_000;

    // Act
    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate())?;

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(result) = result else {
        panic!("wrong target post-state accepted")
    };
    assert_eq!(
        result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::POST_SUBSTATE_MISMATCH
    );
    assert!(result.effects.is_empty());
    Ok(())
}

#[test]
fn route_and_module_receipt_substitutions_reject() -> AbiResultV1<()> {
    // Arrange / Act
    let mut route_fixture = fixture()?;
    route_fixture.context.allocation_route_release_id = root(98);
    let route_result = compose_zdex_tokenomics_fee_allocation_lane_v1(route_fixture.candidate())?;
    let mut receipt_fixture = fixture()?;
    receipt_fixture.module.receipt_root = root(99);
    let receipt_result =
        compose_zdex_tokenomics_fee_allocation_lane_v1(receipt_fixture.candidate())?;

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(route_result) = route_result else {
        panic!("wrong route accepted")
    };
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(receipt_result) = receipt_result else {
        panic!("wrong module receipt accepted")
    };
    assert_eq!(
        route_result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH
    );
    assert_eq!(
        receipt_result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RECEIPT_MISMATCH
    );
    assert!(route_result.effects.is_empty() && receipt_result.effects.is_empty());
    Ok(())
}

#[test]
fn sum_preserving_destination_shift_cannot_build_module_statement() -> AbiResultV1<()> {
    // Arrange
    let mut shifted = accepted()?;
    shifted.post_state.destination_balances[0].allocation_atoms += 1;
    shifted.post_state.destination_balances[2].allocation_atoms -= 1;
    let post_root = shifted.post_state.state_root()?;
    shifted.occurrence.post_lane_root = post_root;
    shifted.validate()?;

    // Act
    let result = build_zdex_tokenomics_fee_allocation_private_port_v1(
        &shifted,
        &candidate_zdex_fee_allocation_policy_v1(),
    );

    // Assert
    assert!(result.is_err());
    Ok(())
}

#[test]
fn coherent_forged_fee_split_cannot_refine_governed_policy() -> AbiResultV1<()> {
    // Arrange
    let mut shifted = accepted()?;
    shifted.occurrence.allocations[0].allocation_atoms += 1;
    shifted.occurrence.allocations[2].allocation_atoms -= 1;
    shifted.post_state.destination_balances[0].allocation_atoms += 1;
    shifted.post_state.destination_balances[2].allocation_atoms -= 1;
    for row in &mut shifted.effects.rows {
        if row.kind == EconomicEffectKindV1::FEE_ALLOCATION
            && row.principal == "protocol-fee-buyback-reserve"
        {
            row.delta_atoms += 1;
        } else if row.kind == EconomicEffectKindV1::FEE_ALLOCATION
            && row.principal == "protocol:fee-treasury"
        {
            row.delta_atoms -= 1;
        }
    }
    shifted.occurrence.post_lane_root = shifted.post_state.state_root()?;
    shifted.occurrence.effect_plan_root = shifted.effects.effect_plan_root()?;
    shifted.validate()?;

    // Act
    let result = build_zdex_tokenomics_fee_allocation_private_port_v1(
        &shifted,
        &candidate_zdex_fee_allocation_policy_v1(),
    );

    // Assert
    assert!(result.is_err());
    Ok(())
}

#[test]
fn partial_fee_substate_lane_write_cannot_build_module_statement() -> AbiResultV1<()> {
    // Arrange
    let mut partial = accepted()?;
    partial.effects.lane_writes = vec![LaneWriteV1 {
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        pre_root: partial.pre_state.state_root()?,
        post_root: partial.post_state.state_root()?,
    }];
    partial.occurrence.effect_plan_root = partial.effects.effect_plan_root()?;
    partial.validate()?;

    // Act
    let result = build_zdex_tokenomics_fee_allocation_private_port_v1(
        &partial,
        &candidate_zdex_fee_allocation_policy_v1(),
    );

    // Assert
    assert!(result.is_err());
    Ok(())
}

#[test]
fn post_construction_occurrence_mutation_is_revalidated_before_composition() -> AbiResultV1<()> {
    // Arrange
    let mut fixture = fixture()?;
    fixture.allocation.occurrence.schema = "wrong-schema".to_owned();

    // Act
    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate());

    // Assert
    assert!(result.is_err());
    Ok(())
}

#[test]
fn target_is_found_inside_the_maximal_fee_asset_registry() -> AbiResultV1<()> {
    // Arrange
    let mut fixture = fixture()?;
    fixture.pre_state.fee_allocation_states = (1..=64)
        .map(|ordinal| {
            if ordinal == 40 {
                fixture.allocation.pre_state.clone()
            } else {
                fee_state(ordinal, root(100 + ordinal))
            }
        })
        .collect();
    fixture.post_state.fee_allocation_states = (1..=64)
        .map(|ordinal| {
            if ordinal == 40 {
                fixture.allocation.post_state.clone()
            } else {
                fee_state(ordinal, root(100 + ordinal))
            }
        })
        .collect();

    // Act
    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate())?;

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(result) = result else {
        panic!("maximal fee registry rejected")
    };
    assert_eq!(result.post_state.fee_allocation_states.len(), 64);
    Ok(())
}

#[test]
fn each_context_binding_substitution_is_a_typed_noop() -> AbiResultV1<()> {
    for ordinal in 0..9 {
        // Arrange
        let mut fixture = fixture()?;
        let expected = match ordinal {
            0 => {
                fixture.context.chain_id = "other-chain".to_owned();
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH
            }
            1 => {
                fixture.context.deployment_root = root(71);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::DEPLOYMENT_MISMATCH
            }
            2 => {
                fixture.context.profile_root = root(72);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PROFILE_MISMATCH
            }
            3 => {
                fixture.context.writer_epoch = 12;
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRITER_EPOCH_MISMATCH
            }
            4 => {
                fixture.context.tokenomics_module_release_id = root(73);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RELEASE_MISMATCH
            }
            5 => {
                fixture.context.command_occurrence_id = root(74);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH
            }
            6 => {
                fixture.context.allocation_route_release_id = root(75);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH
            }
            7 => {
                fixture.context.authorized_buyback_route_release_id = root(76);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH
            }
            _ => {
                fixture.context.policy_root = root(77);
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::FEE_ALLOCATION_OCCURRENCE_MISMATCH
            }
        };

        // Act
        let result = compose_zdex_tokenomics_fee_allocation_lane_v1(fixture.candidate())?;

        // Assert
        let ZDEXTokenomicsLaneCompositionResultV1::Rejected(result) = result else {
            panic!("context substitution accepted")
        };
        assert_eq!(result.code, expected);
        assert_eq!(result.pre_lane_root, result.post_lane_root);
        assert!(result.effects.is_empty());
    }
    Ok(())
}

#[test]
fn private_port_terminal_and_effect_commitment_substitutions_reject() -> AbiResultV1<()> {
    // Arrange / Act
    let mut port_fixture = fixture()?;
    port_fixture.port.allocation_occurrence_root = root(81);
    let port_result = compose_zdex_tokenomics_fee_allocation_lane_v1(port_fixture.candidate())?;
    let mut terminal_fixture = fixture()?;
    terminal_fixture.module.terminal_obligations_root = root(82);
    let terminal_result =
        compose_zdex_tokenomics_fee_allocation_lane_v1(terminal_fixture.candidate())?;
    let mut effect_fixture = fixture()?;
    effect_fixture.module.effect_plan_root = root(83);
    let effect_result = compose_zdex_tokenomics_fee_allocation_lane_v1(effect_fixture.candidate())?;

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(port_result) = port_result else {
        panic!("wrong private port accepted")
    };
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(terminal_result) = terminal_result else {
        panic!("wrong terminal obligation accepted")
    };
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(effect_result) = effect_result else {
        panic!("wrong effect commitment accepted")
    };
    assert_eq!(
        port_result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PRIVATE_PORT_MISMATCH
    );
    assert_eq!(
        terminal_result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::TERMINAL_OBLIGATION_MISMATCH
    );
    assert_eq!(
        effect_result.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH
    );
    assert!(port_result.effects.is_empty());
    assert!(terminal_result.effects.is_empty());
    assert!(effect_result.effects.is_empty());
    Ok(())
}
