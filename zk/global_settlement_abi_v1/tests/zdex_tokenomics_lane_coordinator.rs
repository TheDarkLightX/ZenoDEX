use zenodex_global_settlement_abi_v1::{
    build_zdex_tokenomics_burn_private_port_v1, compose_zdex_tokenomics_burn_lane_v1,
    refine_zdex_burn_leaf_v1, transition_zdex_purchase_and_burn_v1,
    zdex_tokenomics_complete_lane_obligation_root_v1, LaneIdV1, LaneModuleTransitionJournalV1,
    RootV1, ZDEXAMMPurchaseJournalV1, ZDEXAmountBucketV1, ZDEXBurnRouteContextV1,
    ZDEXFeeDestinationAmountV1, ZDEXFeeDestinationV1, ZDEXFeeStateV1, ZDEXHyperdeflationPolicyV1,
    ZDEXPurchaseAndBurnCommandV1, ZDEXPurchaseAndBurnResultV1, ZDEXSupplyStateV1,
    ZDEXTokenomicsBurnCoordinatorContextV1, ZDEXTokenomicsBurnLaneCandidateV1,
    ZDEXTokenomicsLaneCompositionResultV1, ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1, GLOBAL_SETTLEMENT_ABI_V1, MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1,
    ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX tokenomics coordinator test root",
        false,
    )
    .unwrap()
}

fn root_hex(value: &str) -> RootV1 {
    RootV1::parse(value, "ZDEX tokenomics coordinator golden root", false).unwrap()
}

fn burn_projection() -> zenodex_global_settlement_abi_v1::ZDEXBurnLeafProjectionV1 {
    let policy = ZDEXHyperdeflationPolicyV1 {
        asset_id: root(1),
        retained_numerator: 9,
        retained_denominator: 10,
        maximum_decimals: 64,
        maximum_decimal_step: 8,
    };
    let purchase = ZDEXAMMPurchaseJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "tau-testnet".to_owned(),
        deployment_root: root(10),
        profile_root: root(11),
        writer_epoch: 7,
        route_release_id: root(2),
        command_occurrence_id: root(12),
        spot_module_release_id: root(13),
        issue_burn_policy_root: policy.policy_root().unwrap(),
        buyback_budget_occurrence_root: root(14),
        quote_asset_id: root(15),
        zdex_asset_id: policy.asset_id.clone(),
        quote_source_bucket_id: "protocol:buyback:quote".to_owned(),
        quote_pool_bucket_id: "pool:quote".to_owned(),
        zdex_pool_bucket_id: "pool:zdex".to_owned(),
        burn_bucket_id: "route:buyburn:source".to_owned(),
        quote_amount_in_atoms: 50,
        purchased_zdex_atoms: 100,
        quote_source_pre_atoms: 1000,
        quote_source_post_atoms: 950,
        quote_pool_pre_atoms: 200,
        quote_pool_post_atoms: 250,
        zdex_pool_pre_atoms: 600,
        zdex_pool_post_atoms: 500,
        burn_bucket_pre_atoms: 0,
        burn_bucket_post_atoms: 100,
        quote_owned_atoms: 1200,
        quote_supply_atoms: 2000,
        zdex_owned_atoms: 1000,
        zdex_supply_atoms: 1000,
        pre_spot_lane_root: root(16),
        post_spot_lane_root: root(17),
        effect_plan_root: RootV1::parse(
            "0x4be4052113d9a659b62fba88fa0385d814cb1ec8163b72182bae4b44bdd19a3c",
            "purchase effect root",
            false,
        )
        .unwrap(),
    };
    let pre_state = ZDEXSupplyStateV1 {
        asset_id: policy.asset_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        decimals: 8,
        precision_epoch: 0,
        live_supply_atoms: 1000,
        buckets: vec![
            ZDEXAmountBucketV1 {
                bucket_id: purchase.burn_bucket_id.clone(),
                amount_atoms: 100,
            },
            ZDEXAmountBucketV1 {
                bucket_id: "wallet:alice".to_owned(),
                amount_atoms: 900,
            },
        ],
        burn_budget_epoch: 5,
        remaining_epoch_burn_cap_atoms: 100,
    };
    let context = ZDEXBurnRouteContextV1 {
        route_release_id: purchase.route_release_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        purchase_occurrence_root: purchase.journal_root().unwrap(),
        burn_source_bucket_id: purchase.burn_bucket_id.clone(),
        purchased_zdex_atoms: 100,
        source_reserve_floor_atoms: 0,
        remaining_epoch_burn_cap_atoms: 100,
        route_safe_output_cap_atoms: 100,
        burn_budget_epoch: 5,
    };
    let command = ZDEXPurchaseAndBurnCommandV1 {
        expected_pre_state_root: pre_state.state_root().unwrap(),
        expected_precision_epoch: 0,
        expected_purchase_occurrence_root: purchase.journal_root().unwrap(),
        source_bucket_id: purchase.burn_bucket_id.clone(),
        purchased_zdex_atoms: 100,
    };
    let result =
        transition_zdex_purchase_and_burn_v1(&policy, &pre_state, &context, &command).unwrap();
    let ZDEXPurchaseAndBurnResultV1::Accepted(accepted) = result else {
        panic!("fixture transition must accept")
    };
    refine_zdex_burn_leaf_v1(&accepted, &purchase, &root(20)).unwrap()
}

fn fee_state() -> ZDEXFeeStateV1 {
    ZDEXFeeStateV1 {
        fee_asset_id: root(15),
        policy_root: root(30),
        fee_ingress_atoms: 1000,
        unallocated_reserve_atoms: 100,
        destination_balances: [
            ZDEXFeeDestinationV1::BUYBACK,
            ZDEXFeeDestinationV1::QUALIFIED_HOST_POOL,
            ZDEXFeeDestinationV1::TREASURY,
            ZDEXFeeDestinationV1::PROOF_REWARDS,
            ZDEXFeeDestinationV1::COVER_RESERVE,
            ZDEXFeeDestinationV1::LP_REBATES,
        ]
        .into_iter()
        .map(|destination| ZDEXFeeDestinationAmountV1 {
            destination,
            allocation_atoms: 0,
        })
        .collect(),
        owned_and_custodied_atoms: 2000,
        supply_atoms: 2000,
    }
}

fn lane_state(supply_state: ZDEXSupplyStateV1) -> ZDEXTokenomicsLaneStateV1 {
    ZDEXTokenomicsLaneStateV1 {
        schema: "zenodex/zdex-tokenomics-lane-state/v1".to_owned(),
        supply_state,
        fee_allocation_states: vec![fee_state()],
        staking_state_root: root(31),
        host_claims_state_root: root(32),
        treasury_claims_state_root: root(33),
        proof_rewards_state_root: root(34),
        cover_reserve_state_root: root(35),
        lp_rebates_state_root: root(36),
    }
}

struct Candidate {
    context: ZDEXTokenomicsBurnCoordinatorContextV1,
    module: LaneModuleTransitionJournalV1,
    port: zenodex_global_settlement_abi_v1::ZDEXTokenomicsBurnPrivatePortV1,
    pre_lane: ZDEXTokenomicsLaneStateV1,
    post_lane: ZDEXTokenomicsLaneStateV1,
    projection: zenodex_global_settlement_abi_v1::ZDEXBurnLeafProjectionV1,
}

fn candidate() -> Candidate {
    let projection = burn_projection();
    let journal = projection.journal();
    let effects = projection.effects();
    let port = build_zdex_tokenomics_burn_private_port_v1(journal, effects).unwrap();
    let module = LaneModuleTransitionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: journal.chain_id.clone(),
        deployment_root: journal.deployment_root.clone(),
        profile_root: journal.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        module_release_id: journal.tokenomics_module_release_id.clone(),
        command_occurrence_id: journal.command_occurrence_id.clone(),
        pre_lane_root: RootV1::parse(ZERO_ROOT_V1, "empty pre-lane root", true).unwrap(),
        post_lane_root: RootV1::parse(ZERO_ROOT_V1, "empty post-lane root", true).unwrap(),
        effect_plan_root: effects.effect_plan_root().unwrap(),
        private_port_root: port.port_root().unwrap(),
        receipt_root: root(41),
        terminal_obligations_root: zdex_tokenomics_complete_lane_obligation_root_v1().unwrap(),
    };
    let context = ZDEXTokenomicsBurnCoordinatorContextV1 {
        schema: "zenodex/zdex-tokenomics-burn-coordinator/v1".to_owned(),
        chain_id: journal.chain_id.clone(),
        deployment_root: journal.deployment_root.clone(),
        profile_root: journal.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
        coordinator_release_id: root(42),
        route_release_id: journal.route_release_id.clone(),
        tokenomics_module_release_id: journal.tokenomics_module_release_id.clone(),
        command_occurrence_id: journal.command_occurrence_id.clone(),
        issue_burn_policy_root: journal.issue_burn_policy_root.clone(),
    };
    Candidate {
        context,
        module,
        port,
        pre_lane: lane_state(projection.accepted().pre_state().clone()),
        post_lane: lane_state(projection.accepted().post_state().clone()),
        projection,
    }
}

fn lane_candidate(candidate: &Candidate) -> ZDEXTokenomicsBurnLaneCandidateV1<'_> {
    ZDEXTokenomicsBurnLaneCandidateV1 {
        context: &candidate.context,
        module_journal: &candidate.module,
        private_port: &candidate.port,
        pre_state: &candidate.pre_lane,
        post_state: &candidate.post_lane,
        burn_journal: candidate.projection.journal(),
        module_effects: candidate.projection.effects(),
    }
}

fn assert_typed_no_effect_rejection(
    candidate: ZDEXTokenomicsBurnLaneCandidateV1<'_>,
    expected: ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
) {
    let result = compose_zdex_tokenomics_burn_lane_v1(candidate).unwrap();
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) = result else {
        panic!("binding substitution must reject")
    };
    assert_eq!(rejected.code, expected);
    assert_eq!(rejected.pre_lane_root, rejected.post_lane_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn burn_substate_is_embedded_in_one_complete_tokenomics_lane_write() {
    // Arrange
    let candidate = candidate();

    // Act
    let result = compose_zdex_tokenomics_burn_lane_v1(lane_candidate(&candidate)).unwrap();

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) = result else {
        panic!("complete lane composition must accept")
    };
    assert_eq!(accepted.post_state, candidate.post_lane);
    assert_eq!(
        accepted.lane_journal.pre_lane_root,
        candidate.pre_lane.state_root().unwrap()
    );
    assert_eq!(
        accepted.lane_journal.post_lane_root,
        candidate.post_lane.state_root().unwrap()
    );
    assert!(accepted.lane_journal.terminal_obligations_root.is_zero());
    assert_eq!(
        accepted.effects.lane_writes,
        vec![accepted.expected_lane_write().unwrap().clone()]
    );
    assert_eq!(
        candidate.pre_lane.state_root().unwrap(),
        root_hex("0x13e77d130b8b5c1dfe49d5885cd7ee968d4fd4514a7af19b261d3e1b76d0e7ca")
    );
    assert_eq!(
        candidate.post_lane.state_root().unwrap(),
        root_hex("0xaf35a07a30050310c6343947ba773ebd4424a816418d5e03b17b68820cb5656b")
    );
    assert_eq!(
        candidate.port.port_root().unwrap(),
        root_hex("0x3599e1c7349810b87811902c2cfc367f9c791c9d16aead73c7280753dc24e619")
    );
    assert_eq!(
        candidate.module.journal_root().unwrap(),
        root_hex("0xbcf63554276350f9f76d4150fd033fd897fd57938238f669c3e29fad52122ee6")
    );
    assert_eq!(
        accepted.effects.effect_plan_root().unwrap(),
        root_hex("0x211aa4aa89fb7f65b422adfb8d1d0549f85b2fdfd83d4222d8285baf7dd534bc")
    );
    assert_eq!(
        accepted.lane_journal.journal_root().unwrap(),
        root_hex("0x19a31e3c73851451198350d031df6737ac4008b2ca30b47a50f3c1378cff31b7")
    );
}

#[test]
fn fee_state_registry_rejects_zero_duplicate_unsorted_and_excess_width() {
    // Arrange
    let candidate = candidate();
    let mut low = fee_state();
    low.fee_asset_id = root(90);
    let mut high = fee_state();
    high.fee_asset_id = root(91);

    // Act / Assert
    let mut invalid = candidate.pre_lane.clone();
    invalid.fee_allocation_states.clear();
    assert!(invalid.validate().is_err());

    invalid.fee_allocation_states = vec![low.clone(), low.clone()];
    assert!(invalid.validate().is_err());

    invalid.fee_allocation_states = vec![high, low.clone()];
    assert!(invalid.validate().is_err());

    invalid.fee_allocation_states = vec![low; MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1 + 1];
    assert!(invalid.validate().is_err());
}

#[test]
fn unrelated_component_mutation_rejects_without_effects() {
    // Arrange
    let candidate = candidate();
    let mut post = candidate.post_lane.clone();
    post.staking_state_root = root(99);

    // Act
    let result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
        post_state: &post,
        ..lane_candidate(&candidate)
    })
    .unwrap();

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) = result else {
        panic!("unrelated component mutation must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::UNRELATED_STATE_MUTATION
    );
    assert_eq!(rejected.pre_lane_root, rejected.post_lane_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn partial_substate_cannot_be_claimed_as_a_complete_lane_root() {
    // Arrange
    let candidate = candidate();
    let mut module = candidate.module.clone();
    module.pre_lane_root = candidate
        .projection
        .journal()
        .pre_tokenomics_burn_substate_root
        .clone();
    module.post_lane_root = candidate
        .projection
        .journal()
        .post_tokenomics_burn_substate_root
        .clone();

    // Act
    let result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
        module_journal: &module,
        ..lane_candidate(&candidate)
    })
    .unwrap();

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) = result else {
        panic!("partial lane-root claim must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PARTIAL_LANE_ROOT_CLAIM
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn private_port_and_post_substate_substitutions_reject() {
    // Arrange
    let candidate = candidate();
    let mut port = candidate.port.clone();
    port.post_burn_substate_root = root(98);
    let mut post = candidate.post_lane.clone();
    post.supply_state = candidate.pre_lane.supply_state.clone();

    // Act
    let port_result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
        private_port: &port,
        ..lane_candidate(&candidate)
    })
    .unwrap();
    let state_result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
        post_state: &post,
        ..lane_candidate(&candidate)
    })
    .unwrap();

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(port_reject) = port_result else {
        panic!("private-port substitution must reject")
    };
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(state_reject) = state_result else {
        panic!("post-substate substitution must reject")
    };
    assert_eq!(
        port_reject.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PRIVATE_PORT_MISMATCH
    );
    assert_eq!(
        state_reject.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::POST_SUBSTATE_MISMATCH
    );
}

#[test]
fn every_unrelated_component_commitment_is_preserved() {
    // Arrange / Act / Assert
    for index in 0_u8..7 {
        let candidate = candidate();
        let mut post = candidate.post_lane.clone();
        match index {
            0 => post.fee_allocation_states[0].fee_ingress_atoms = 999,
            1 => post.staking_state_root = root(99),
            2 => post.host_claims_state_root = root(99),
            3 => post.treasury_claims_state_root = root(99),
            4 => post.proof_rewards_state_root = root(99),
            5 => post.cover_reserve_state_root = root(99),
            6 => post.lp_rebates_state_root = root(99),
            _ => unreachable!(),
        }
        let result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
            post_state: &post,
            ..lane_candidate(&candidate)
        })
        .unwrap();
        let ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) = result else {
            panic!("unrelated component mutation must reject")
        };
        assert_eq!(
            rejected.code,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::UNRELATED_STATE_MUTATION
        );
        assert!(rejected.effects.is_empty());
    }
}

#[test]
fn route_release_substitution_has_a_closed_no_effect_rejection() {
    // Arrange
    let candidate = candidate();
    let mut context = candidate.context.clone();
    context.route_release_id = root(99);

    // Act
    let result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
        context: &context,
        ..lane_candidate(&candidate)
    })
    .unwrap();

    // Assert
    let ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) = result else {
        panic!("route substitution must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn each_coordinator_binding_substitution_is_a_typed_no_effect_rejection() {
    // Arrange
    let candidate = candidate();

    // Act / Assert
    let mut context = candidate.context.clone();
    context.chain_id = "other-testnet".to_owned();
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH,
    );

    let mut context = candidate.context.clone();
    context.deployment_root = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::DEPLOYMENT_MISMATCH,
    );

    let mut context = candidate.context.clone();
    context.profile_root = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PROFILE_MISMATCH,
    );

    let mut context = candidate.context.clone();
    context.writer_epoch += 1;
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRITER_EPOCH_MISMATCH,
    );

    let mut module = candidate.module.clone();
    module.lane_id = LaneIdV1::ASSET_TRANSFER;
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            module_journal: &module,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRONG_LANE,
    );

    let mut context = candidate.context.clone();
    context.tokenomics_module_release_id = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RELEASE_MISMATCH,
    );

    let mut context = candidate.context.clone();
    context.command_occurrence_id = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH,
    );

    let mut module = candidate.module.clone();
    module.terminal_obligations_root = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            module_journal: &module,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::TERMINAL_OBLIGATION_MISMATCH,
    );

    let mut context = candidate.context.clone();
    context.issue_burn_policy_root = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &context,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::BURN_JOURNAL_MISMATCH,
    );

    let mut module = candidate.module.clone();
    module.effect_plan_root = root(90);
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            module_journal: &module,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH,
    );

    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            pre_state: &candidate.post_lane,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PRE_SUBSTATE_MISMATCH,
    );
}

#[test]
fn self_consistent_leaf_totals_cannot_override_complete_lane_supply() {
    // Arrange
    let candidate = candidate();
    let mut forged_burn = candidate.projection.journal().clone();
    forged_burn.zdex_owned_pre_atoms = 2000;
    forged_burn.zdex_owned_post_atoms = 1900;
    let mut forged_effects = candidate.projection.effects().clone();
    forged_effects.asset_conservation[0].owned_and_custodied_pre_atoms = 2000;
    forged_effects.asset_conservation[0].owned_and_custodied_post_atoms = 1900;
    forged_burn.effect_plan_root = forged_effects.effect_plan_root().unwrap();
    let forged_port =
        build_zdex_tokenomics_burn_private_port_v1(&forged_burn, &forged_effects).unwrap();
    let mut forged_module = candidate.module.clone();
    forged_module.effect_plan_root = forged_effects.effect_plan_root().unwrap();
    forged_module.private_port_root = forged_port.port_root().unwrap();

    // Act / Assert
    assert_typed_no_effect_rejection(
        ZDEXTokenomicsBurnLaneCandidateV1 {
            module_journal: &forged_module,
            private_port: &forged_port,
            burn_journal: &forged_burn,
            module_effects: &forged_effects,
            ..lane_candidate(&candidate)
        },
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH,
    );
}
