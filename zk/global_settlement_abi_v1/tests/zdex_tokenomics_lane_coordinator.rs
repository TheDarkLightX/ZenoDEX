use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    bind_zdex_tokenomics_shadow_profile_v1, build_zdex_tokenomics_burn_module_journal_v1,
    build_zdex_tokenomics_burn_private_port_v1, canonical_bytes_v1,
    compose_zdex_tokenomics_burn_lane_v1, hash_global_v1, refine_zdex_burn_leaf_v1,
    transition_zdex_purchase_and_burn_v1, verify_zdex_burn_receipt_v1,
    verify_zdex_tokenomics_lane_receipt_v1, zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1, AbiErrorV1, AbiResultV1, EconomicCommandOccurrenceV1,
    EconomicProfileSnapshotV1, EvidenceStatusV1, LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1, LaneModuleTransitionJournalV1,
    LaneRegistryV1, ProfileStatusV1, ReceiptKindV1, ReleaseStatusV1, RootV1, RouteRegistryV1,
    RouteReleaseV1, VerifiedZDEXBurnV1, ZDEXAMMPurchaseJournalV1, ZDEXAmountBucketV1,
    ZDEXBurnReceiptCandidateV1, ZDEXBurnRouteContextV1, ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1, ZDEXFeeStateV1, ZDEXHyperdeflationPolicyV1, ZDEXLaneReceiptEnvelopeV1,
    ZDEXLaneSuccinctReceiptVerifierV1, ZDEXPurchaseAndBurnCommandV1, ZDEXPurchaseAndBurnResultV1,
    ZDEXSupplyStateV1, ZDEXTokenomicsBurnCoordinatorContextV1, ZDEXTokenomicsBurnLaneCandidateV1,
    ZDEXTokenomicsLaneCompositionResultV1, ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneReceiptCandidateV1, ZDEXTokenomicsLaneStateV1,
    ZDEXTokenomicsProfileRegistriesV1, ALL_LANE_IDS_V1, AMM_PURCHASE_OUTPUT_ROLE_V1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, ZDEX_BURN_INPUT_ROLE_V1,
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

fn shadow_lane_release(lane_id: LaneIdV1, ordinal: u64) -> LaneModuleReleaseV1 {
    let offset = ordinal * 16;
    let state_schema_root = root(100 + offset);
    let command_variants = vec![PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned()];
    let terminal_command_variants: Vec<String> = vec![];
    let guest_image_id = root(101 + offset);
    let specification_root = root(102 + offset);
    let source_root = root(103 + offset);
    let toolchain_root = root(104 + offset);
    let terminal_coverage_root = root(105 + offset);
    let migration_compatibility_root = root(106 + offset);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "state_schema_root": state_schema_root,
        "command_variants": command_variants,
        "terminal_command_variants": terminal_command_variants,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "terminal_coverage_root": terminal_coverage_root,
        "migration_compatibility_root": migration_compatibility_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        release_id: hash_global_v1("global-lane-module-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-shadow-test".to_owned(),
        state_schema_root,
        command_variants,
        terminal_command_variants,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        terminal_coverage_root,
        migration_compatibility_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: Vec::<EvidenceStatusV1>::new(),
    }
}

fn shadow_coordinator_release(lane_id: LaneIdV1, ordinal: u64) -> LaneCoordinatorReleaseV1 {
    let offset = ordinal * 16;
    let coordinator_schema_root = root(700 + offset);
    let guest_image_id = root(701 + offset);
    let specification_root = root(702 + offset);
    let source_root = root(703 + offset);
    let toolchain_root = root(704 + offset);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "coordinator_schema_root": coordinator_schema_root,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    LaneCoordinatorReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        coordinator_release_id: hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            &content,
        )
        .unwrap(),
        semantic_version: "1.0.0-shadow-test".to_owned(),
        coordinator_schema_root,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: vec![],
    }
}

fn shadow_buyback_route(
    spot: &LaneModuleReleaseV1,
    tokenomics: &LaneModuleReleaseV1,
    issue_burn_policy_root: &RootV1,
) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS];
    let module_release_ids = vec![spot.release_id.clone(), tokenomics.release_id.clone()];
    let dependency_roles = vec![
        AMM_PURCHASE_OUTPUT_ROLE_V1.to_owned(),
        ZDEX_BURN_INPUT_ROLE_V1.to_owned(),
    ];
    let port_schema_roots = vec![
        zdex_amm_purchase_port_schema_root_v1().unwrap(),
        zdex_burn_port_schema_root_v1().unwrap(),
    ];
    let guest_image_id = root(500);
    let specification_root = root(501);
    let source_root = root(502);
    let toolchain_root = root(503);
    let oracle_policy_root = root(504);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        "ordered_lanes": ordered_lanes,
        "module_release_ids": module_release_ids,
        "dependency_roles": dependency_roles,
        "port_schema_roots": port_schema_roots,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "oracle_policy_root": oracle_policy_root,
        "issue_burn_policy_root": issue_burn_policy_root,
        "max_cycles": 2_000_000,
        "max_journal_bytes": 65_536,
    });
    RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-shadow-test".to_owned(),
        command_kind: PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        oracle_policy_root,
        issue_burn_policy_root: issue_burn_policy_root.clone(),
        max_cycles: 2_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: vec![],
    }
}

struct ShadowProfile {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    route: RouteReleaseV1,
    tokenomics_release: LaneModuleReleaseV1,
}

fn shadow_profile(issue_burn_policy_root: &RootV1) -> ShadowProfile {
    let releases: Vec<_> = ALL_LANE_IDS_V1
        .iter()
        .enumerate()
        .map(|(index, lane_id)| shadow_lane_release(*lane_id, index as u64 + 1))
        .collect();
    let tokenomics_release = releases
        .iter()
        .find(|release| release.lane_id == LaneIdV1::ZDEX_TOKENOMICS)
        .unwrap()
        .clone();
    let spot_release = releases
        .iter()
        .find(|release| release.lane_id == LaneIdV1::SPOT_LIQUIDITY)
        .unwrap()
        .clone();
    let lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases,
    };
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| shadow_coordinator_release(*lane_id, index as u64 + 1))
            .collect(),
    };
    let route = shadow_buyback_route(&spot_release, &tokenomics_release, issue_burn_policy_root);
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: vec![route.clone()],
    };
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let proof_shape_root = root(810);
    let root_image_id = root(811);
    let verifier_registry_root = root(812);
    let migration_registry_root = root(813);
    let policy_registry_root = root(814);
    let terminal_registry_root = root(815);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": 7,
        "lane_registry_root": lane_registry_root,
        "lane_coordinator_registry_root": lane_coordinator_registry_root,
        "route_registry_root": route_registry_root,
        "proof_shape_root": proof_shape_root,
        "root_image_id": root_image_id,
        "verifier_registry_root": verifier_registry_root,
        "migration_registry_root": migration_registry_root,
        "policy_registry_root": policy_registry_root,
        "terminal_registry_root": terminal_registry_root,
    });
    let profile = EconomicProfileSnapshotV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        profile_id: hash_global_v1("global-economic-profile-content-v1", &content).unwrap(),
        authority_epoch: 7,
        lane_registry_root,
        lane_coordinator_registry_root,
        route_registry_root,
        proof_shape_root,
        root_image_id,
        verifier_registry_root,
        migration_registry_root,
        policy_registry_root,
        terminal_registry_root,
        status: ProfileStatusV1::SHADOW,
    };
    profile
        .validate_registries(&lanes, &coordinators, &routes)
        .unwrap();
    ShadowProfile {
        profile,
        lanes,
        coordinators,
        routes,
        route,
        tokenomics_release,
    }
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
    let module = build_zdex_tokenomics_burn_module_journal_v1(journal, effects, &port).unwrap();
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

struct AcceptingVerifier;

impl ZDEXLaneSuccinctReceiptVerifierV1 for AcceptingVerifier {
    fn verify_succinct_receipt(
        &self,
        _receipt_bytes: &[u8],
        _expected_image_id: &RootV1,
        _expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        Ok(())
    }
}

struct PanickingVerifier;

impl ZDEXLaneSuccinctReceiptVerifierV1 for PanickingVerifier {
    fn verify_succinct_receipt(
        &self,
        _receipt_bytes: &[u8],
        _expected_image_id: &RootV1,
        _expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        panic!("invalid coordinator input reached receipt verification")
    }
}

struct RejectingVerifier;

impl ZDEXLaneSuccinctReceiptVerifierV1 for RejectingVerifier {
    fn verify_succinct_receipt(
        &self,
        _receipt_bytes: &[u8],
        _expected_image_id: &RootV1,
        _expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        Err(AbiErrorV1::InvalidBinding(
            "test coordinator receipt rejection",
        ))
    }
}

struct ExactVerifier {
    receipt_bytes: Vec<u8>,
    image_id: RootV1,
    journal_bytes: Vec<u8>,
}

impl ZDEXLaneSuccinctReceiptVerifierV1 for ExactVerifier {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        if receipt_bytes != self.receipt_bytes
            || expected_image_id != &self.image_id
            || expected_journal_bytes != self.journal_bytes
        {
            return Err(AbiErrorV1::InvalidBinding(
                "tokenomics lane exact receipt binding mismatch",
            ));
        }
        Ok(())
    }
}

struct ReceiptFixture {
    profile: ShadowProfile,
    occurrence: EconomicCommandOccurrenceV1,
    context: ZDEXTokenomicsBurnCoordinatorContextV1,
    module: LaneModuleTransitionJournalV1,
    port: zenodex_global_settlement_abi_v1::ZDEXTokenomicsBurnPrivatePortV1,
    pre_lane: ZDEXTokenomicsLaneStateV1,
    post_lane: ZDEXTokenomicsLaneStateV1,
    burn: zenodex_global_settlement_abi_v1::ZDEXBurnJournalV1,
    effects: zenodex_global_settlement_abi_v1::GlobalEconomicEffectPlanV1,
    verified_burn: VerifiedZDEXBurnV1,
    receipt: ZDEXLaneReceiptEnvelopeV1,
}

impl ReceiptFixture {
    fn lane_candidate(&self) -> ZDEXTokenomicsBurnLaneCandidateV1<'_> {
        ZDEXTokenomicsBurnLaneCandidateV1 {
            context: &self.context,
            module_journal: &self.module,
            private_port: &self.port,
            pre_state: &self.pre_lane,
            post_state: &self.post_lane,
            burn_journal: &self.burn,
            module_effects: &self.effects,
        }
    }

    fn receipt_candidate(&self) -> ZDEXTokenomicsLaneReceiptCandidateV1<'_> {
        ZDEXTokenomicsLaneReceiptCandidateV1 {
            occurrence: &self.occurrence,
            lane_candidate: self.lane_candidate(),
            verified_burn: &self.verified_burn,
            receipt: &self.receipt,
        }
    }
}

fn receipt_fixture() -> ReceiptFixture {
    let base = candidate();
    let profile = shadow_profile(&base.pre_lane.supply_state.policy_root);
    let occurrence = EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: base.context.chain_id.clone(),
        deployment_root: base.context.deployment_root.clone(),
        height: 7,
        tx_index: 2,
        op_index: 1,
        command_kind: PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned(),
        route_release_id: profile.route.route_release_id.clone(),
        subject_id: "protocol-buyback-controller".to_owned(),
        grant_root: root(820),
        nonce: 9,
        profile_root: profile.profile.profile_id.clone(),
        pre_state_root: root(816),
        consumed_object_ids: vec![],
    };
    let occurrence_id = occurrence.occurrence_id().unwrap();
    let mut burn = base.projection.journal().clone();
    burn.profile_root = profile.profile.profile_id.clone();
    burn.route_release_id = profile.route.route_release_id.clone();
    burn.command_occurrence_id = occurrence_id;
    burn.tokenomics_module_release_id = profile.tokenomics_release.release_id.clone();
    burn.effect_plan_root = root(821);
    let mut effects = base.projection.effects().clone();
    effects.occurrence_consumptions = vec![burn.command_occurrence_id.clone()];
    burn.effect_plan_root = effects.effect_plan_root().unwrap();
    let port = build_zdex_tokenomics_burn_private_port_v1(&burn, &effects).unwrap();
    let module = build_zdex_tokenomics_burn_module_journal_v1(&burn, &effects, &port).unwrap();
    let coordinator = profile
        .coordinators
        .release_for(LaneIdV1::ZDEX_TOKENOMICS)
        .unwrap();
    let context = ZDEXTokenomicsBurnCoordinatorContextV1 {
        schema: "zenodex/zdex-tokenomics-burn-coordinator/v1".to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: profile.profile.profile_id.clone(),
        writer_epoch: profile.profile.authority_epoch,
        coordinator_release_id: coordinator.coordinator_release_id.clone(),
        route_release_id: profile.route.route_release_id.clone(),
        tokenomics_module_release_id: profile.tokenomics_release.release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id().unwrap(),
        issue_burn_policy_root: profile.route.issue_burn_policy_root.clone(),
    };
    let burn_receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"tokenomics-burn-leaf-receipt".to_vec(),
    };
    let verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1 {
            route_release: &profile.route,
            module_release: &profile.tokenomics_release,
            occurrence: &occurrence,
            journal: &burn,
            effects: &effects,
            receipt: &burn_receipt,
        },
        &AcceptingVerifier,
    )
    .unwrap();
    occurrence.validate().unwrap();
    ReceiptFixture {
        profile,
        occurrence,
        context,
        module,
        port,
        pre_lane: base.pre_lane,
        post_lane: base.post_lane,
        burn,
        effects,
        verified_burn,
        receipt: ZDEXLaneReceiptEnvelopeV1 {
            receipt_kind: ReceiptKindV1::SUCCINCT,
            receipt_bytes: b"tokenomics-coordinator-receipt".to_vec(),
        },
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
        root_hex("0x0b5ab6278d91be413bb56072a4210bd1a4b621d0379a85fe6e309cdd727471ca")
    );
    assert_eq!(
        accepted.effects.effect_plan_root().unwrap(),
        root_hex("0x211aa4aa89fb7f65b422adfb8d1d0549f85b2fdfd83d4222d8285baf7dd534bc")
    );
    assert_eq!(
        accepted.lane_journal.journal_root().unwrap(),
        root_hex("0x0f608f755e7fa941a454a49e4e92c86e1e5ca88589be2591a769d238b60ad6f3")
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
fn module_receipt_commitment_substitution_rejects_without_effects() {
    // Arrange
    let mut candidate = candidate();
    candidate.module.receipt_root = root(99);

    // Act / Assert
    assert_typed_no_effect_rejection(
        lane_candidate(&candidate),
        ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RECEIPT_MISMATCH,
    );
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
    let forged_module =
        build_zdex_tokenomics_burn_module_journal_v1(&forged_burn, &forged_effects, &forged_port)
            .unwrap();

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

#[test]
fn release_selected_coordinator_receipt_mints_exact_shadow_witness() {
    // Arrange
    let fixture = receipt_fixture();
    let governed = bind_zdex_tokenomics_shadow_profile_v1(
        &fixture.profile.profile.profile_id,
        fixture.profile.profile.authority_epoch,
        ZDEXTokenomicsProfileRegistriesV1 {
            profile: &fixture.profile.profile,
            lanes: &fixture.profile.lanes,
            coordinators: &fixture.profile.coordinators,
            routes: &fixture.profile.routes,
        },
    )
    .unwrap();
    let recomputed = compose_zdex_tokenomics_burn_lane_v1(fixture.lane_candidate()).unwrap();
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) = recomputed else {
        panic!("receipt fixture lane composition must accept")
    };
    assert_ne!(
        fixture.occurrence.pre_state_root,
        fixture.pre_lane.state_root().unwrap()
    );

    // Act
    let verified = verify_zdex_tokenomics_lane_receipt_v1(
        fixture.receipt_candidate(),
        &governed,
        &AcceptingVerifier,
    )
    .unwrap();

    // Assert
    assert_eq!(verified.profile_root(), &fixture.profile.profile.profile_id);
    assert_eq!(
        verified.route_release_id(),
        &fixture.profile.route.route_release_id
    );
    assert_eq!(
        verified.module_release_id(),
        &fixture.profile.tokenomics_release.release_id
    );
    assert_eq!(
        verified.module_image_id(),
        &fixture.profile.tokenomics_release.guest_image_id
    );
    assert_eq!(
        verified.lane_journal_root(),
        &accepted.lane_journal.journal_root().unwrap()
    );
    assert_eq!(
        verified.pre_lane_root(),
        &fixture.pre_lane.state_root().unwrap()
    );
    assert_eq!(
        verified.post_lane_root(),
        &fixture.post_lane.state_root().unwrap()
    );
    assert_eq!(verified.receipt_kind(), ReceiptKindV1::SUCCINCT);
    assert_eq!(
        verified.lane_journal_digest(),
        &RootV1::parse(
            format!(
                "0x{}",
                zenodex_global_settlement_abi_v1::hash_bytes_sha256_v1(
                    &canonical_bytes_v1(&accepted.lane_journal).unwrap()
                )
            ),
            "expected lane journal digest",
            false,
        )
        .unwrap()
    );
    assert_eq!(
        verified.binding_root().unwrap(),
        root_hex("0x0e281f45aa36ab86b9cf1a8c95c2456f0e4c3efa295af8bbab867107bb9b4458")
    );
}

#[test]
fn burn_lane_unrelated_root_substitution_requires_new_exact_receipt() {
    // Arrange
    let mut fixture = receipt_fixture();
    let original = compose_zdex_tokenomics_burn_lane_v1(fixture.lane_candidate()).unwrap();
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) = original else {
        panic!("receipt fixture lane composition must accept")
    };
    let verifier = ExactVerifier {
        receipt_bytes: fixture.receipt.receipt_bytes.clone(),
        image_id: fixture
            .profile
            .coordinators
            .release_for(LaneIdV1::ZDEX_TOKENOMICS)
            .unwrap()
            .guest_image_id
            .clone(),
        journal_bytes: canonical_bytes_v1(&accepted.lane_journal).unwrap(),
    };
    fixture.pre_lane.staking_state_root = root(999);
    fixture.post_lane.staking_state_root = root(999);
    let governed = bind_zdex_tokenomics_shadow_profile_v1(
        &fixture.profile.profile.profile_id,
        fixture.profile.profile.authority_epoch,
        ZDEXTokenomicsProfileRegistriesV1 {
            profile: &fixture.profile.profile,
            lanes: &fixture.profile.lanes,
            coordinators: &fixture.profile.coordinators,
            routes: &fixture.profile.routes,
        },
    )
    .unwrap();

    // Act
    let result =
        verify_zdex_tokenomics_lane_receipt_v1(fixture.receipt_candidate(), &governed, &verifier);

    // Assert
    assert_eq!(
        result,
        Err(AbiErrorV1::InvalidBinding(
            "tokenomics lane exact receipt binding mismatch"
        ))
    );
}

#[test]
fn coordinator_binding_substitution_rejects_before_receipt_verifier() {
    // Arrange
    let mut fixture = receipt_fixture();
    fixture.context.coordinator_release_id = root(999);
    let governed = bind_zdex_tokenomics_shadow_profile_v1(
        &fixture.profile.profile.profile_id,
        fixture.profile.profile.authority_epoch,
        ZDEXTokenomicsProfileRegistriesV1 {
            profile: &fixture.profile.profile,
            lanes: &fixture.profile.lanes,
            coordinators: &fixture.profile.coordinators,
            routes: &fixture.profile.routes,
        },
    )
    .unwrap();

    // Act
    let result = verify_zdex_tokenomics_lane_receipt_v1(
        fixture.receipt_candidate(),
        &governed,
        &PanickingVerifier,
    );

    // Assert
    assert_eq!(
        result,
        Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics governed candidate"
        ))
    );
}

#[test]
fn conditional_coordinator_receipt_rejects_without_verifier_call() {
    // Arrange
    let mut fixture = receipt_fixture();
    fixture.receipt.receipt_kind = ReceiptKindV1::CONDITIONAL;
    let governed = bind_zdex_tokenomics_shadow_profile_v1(
        &fixture.profile.profile.profile_id,
        fixture.profile.profile.authority_epoch,
        ZDEXTokenomicsProfileRegistriesV1 {
            profile: &fixture.profile.profile,
            lanes: &fixture.profile.lanes,
            coordinators: &fixture.profile.coordinators,
            routes: &fixture.profile.routes,
        },
    )
    .unwrap();

    // Act
    let result = verify_zdex_tokenomics_lane_receipt_v1(
        fixture.receipt_candidate(),
        &governed,
        &PanickingVerifier,
    );

    // Assert
    assert_eq!(
        result,
        Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics succinct receipt"
        ))
    );
}

#[test]
fn coordinator_receipt_verifier_rejection_produces_no_witness() {
    // Arrange
    let fixture = receipt_fixture();
    let governed = bind_zdex_tokenomics_shadow_profile_v1(
        &fixture.profile.profile.profile_id,
        fixture.profile.profile.authority_epoch,
        ZDEXTokenomicsProfileRegistriesV1 {
            profile: &fixture.profile.profile,
            lanes: &fixture.profile.lanes,
            coordinators: &fixture.profile.coordinators,
            routes: &fixture.profile.routes,
        },
    )
    .unwrap();

    // Act
    let result = verify_zdex_tokenomics_lane_receipt_v1(
        fixture.receipt_candidate(),
        &governed,
        &RejectingVerifier,
    );

    // Assert
    assert_eq!(
        result,
        Err(AbiErrorV1::InvalidBinding(
            "test coordinator receipt rejection"
        ))
    );
}
