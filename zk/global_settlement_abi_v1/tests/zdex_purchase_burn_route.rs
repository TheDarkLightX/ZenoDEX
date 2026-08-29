use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    bind_zdex_fee_allocation_shadow_profile_v1, bind_zdex_purchase_burn_shadow_profile_v1,
    build_zdex_tokenomics_fee_allocation_module_journal_v1,
    build_zdex_tokenomics_fee_allocation_private_port_v1, candidate_zdex_fee_allocation_policy_v1,
    canonical_bytes_v1, compose_zdex_purchase_burn_route_v1,
    compose_zdex_tokenomics_fee_allocation_lane_v1, hash_global_v1,
    transition_zdex_fee_allocation_v1, verify_zdex_amm_purchase_receipt_v1,
    verify_zdex_burn_receipt_v1, verify_zdex_fee_allocation_receipt_v1,
    verify_zdex_tokenomics_fee_lane_receipt_v1, zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1, zdex_fee_allocation_port_schema_root_v1,
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, AbiErrorV1, AbiResultV1,
    AssetConservationRowV1, EconomicCommandOccurrenceV1, EconomicEffectKindV1, EconomicEffectRowV1,
    EconomicPolicyBindingV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, EvidenceStatusV1,
    GlobalEconomicEffectPlanV1, GovernedZDEXFeeAllocationProfileV1, LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1, LaneRegistryV1, LaneWriteV1,
    ProfileStatusV1, ReceiptKindV1, ReleaseStatusV1, RootV1, RouteRegistryV1, RouteReleaseV1,
    VerifiedZDEXAMMPurchaseV1, VerifiedZDEXBurnV1, VerifiedZDEXFeeAllocationV1,
    ZDEXAMMPurchaseJournalV1, ZDEXAmountBucketV1, ZDEXBurnJournalV1, ZDEXBurnReceiptCandidateV1,
    ZDEXBuybackExecutionPolicyV1, ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1, ZDEXFeeAllocationPolicyV1, ZDEXFeeAllocationProfileRegistriesV1,
    ZDEXFeeAllocationReceiptCandidateV1, ZDEXFeeAllocationResultV1, ZDEXFeeDestinationAmountV1,
    ZDEXFeeStateV1, ZDEXLaneReceiptEnvelopeV1, ZDEXLaneSuccinctReceiptVerifierV1,
    ZDEXPurchaseBurnRouteCandidateV1, ZDEXPurchaseBurnRouteProfileRegistriesV1,
    ZDEXPurchaseBurnRouteRejectCodeV1, ZDEXPurchaseBurnRouteResultV1,
    ZDEXPurchaseReceiptCandidateV1, ZDEXSupplyStateV1,
    ZDEXTokenomicsFeeAllocationCoordinatorContextV1, ZDEXTokenomicsFeeAllocationLaneCandidateV1,
    ZDEXTokenomicsFeeLaneReceiptCandidateV1, ZDEXTokenomicsLaneCompositionResultV1,
    ZDEXTokenomicsLaneStateV1, ALL_LANE_IDS_V1, AMM_POOL_CUSTODY_DOMAIN_V1,
    FEE_ALLOCATION_OUTPUT_ROLE_V1, GLOBAL_SETTLEMENT_ABI_V1, PROTOCOL_BURN_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1, PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1, ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1,
    ZDEX_FEE_ALLOCATION_POLICY_KIND_V1, ZDEX_FEE_DESTINATIONS_V1, ZDEX_SUPPLY_PRINCIPAL_V1,
    ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1, ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn active_evidence() -> Vec<EvidenceStatusV1> {
    vec![
        EvidenceStatusV1::IMPLEMENTED,
        EvidenceStatusV1::MIGRATABLE,
        EvidenceStatusV1::MOUNTED,
        EvidenceStatusV1::NO_BYPASS,
        EvidenceStatusV1::PROVED,
        EvidenceStatusV1::RELEASE_BACKED,
        EvidenceStatusV1::SPECIFIED,
        EvidenceStatusV1::TERMINAL_COMPLETE,
        EvidenceStatusV1::TESTED,
    ]
}

fn lane_release(lane_id: LaneIdV1, ordinal: u64) -> LaneModuleReleaseV1 {
    let offset = ordinal * 16;
    let state_schema_root = root(100 + offset);
    let command_variants = if lane_id == LaneIdV1::ZDEX_TOKENOMICS {
        vec![
            PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned(),
            PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1.to_owned(),
        ]
    } else {
        vec![PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned()]
    };
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
    let release = LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        release_id: hash_global_v1("global-lane-module-release-content-v1", &content)
            .expect("release id"),
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
    };
    release.validate().expect("shadow release must validate");
    release
}

fn route_release(
    spot_release: &LaneModuleReleaseV1,
    burn_release: &LaneModuleReleaseV1,
) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS];
    let module_release_ids = vec![
        spot_release.release_id.clone(),
        burn_release.release_id.clone(),
    ];
    let dependency_roles = vec![
        "AMM_PURCHASE_OUTPUT".to_owned(),
        "ZDEX_BURN_INPUT".to_owned(),
    ];
    let port_schema_roots = vec![
        zdex_amm_purchase_port_schema_root_v1().expect("purchase port root"),
        zdex_burn_port_schema_root_v1().expect("burn port root"),
    ];
    let guest_image_id = root(500);
    let specification_root = root(501);
    let source_root = root(502);
    let toolchain_root = root(503);
    let oracle_policy_root = root(504);
    let issue_burn_policy_root = root(505);
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
    let route = RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content)
            .expect("route release id"),
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
        issue_burn_policy_root,
        max_cycles: 2_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: vec![],
    };
    route.validate().expect("shadow route must validate");
    route
}

fn allocation_route_release(burn_release: &LaneModuleReleaseV1) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::ZDEX_TOKENOMICS];
    let module_release_ids = vec![burn_release.release_id.clone()];
    let dependency_roles = vec![FEE_ALLOCATION_OUTPUT_ROLE_V1.to_owned()];
    let port_schema_roots =
        vec![zdex_fee_allocation_port_schema_root_v1().expect("fee-allocation port root")];
    let guest_image_id = root(510);
    let specification_root = root(511);
    let source_root = root(512);
    let toolchain_root = root(513);
    let oracle_policy_root = root(514);
    let issue_burn_policy_root = root(515);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
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
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    let route = RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content)
            .expect("allocation route release id"),
        semantic_version: "1.0.0-shadow-test".to_owned(),
        command_kind: PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        oracle_policy_root,
        issue_burn_policy_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: vec![],
    };
    route.validate().expect("allocation route must validate");
    route
}

fn coordinator_release(lane_id: LaneIdV1, ordinal: u64) -> LaneCoordinatorReleaseV1 {
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
    let release = LaneCoordinatorReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        coordinator_release_id: hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            &content,
        )
        .expect("coordinator release id"),
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
    };
    release
        .validate()
        .expect("shadow coordinator must validate");
    release
}

fn governed_shadow_profile(
    spot_release: &LaneModuleReleaseV1,
    tokenomics_release: &LaneModuleReleaseV1,
    buyback_route: &RouteReleaseV1,
    allocation_route: &RouteReleaseV1,
    policy_root: &RootV1,
    buyback_execution_policy_root: &RootV1,
) -> (
    EconomicProfileSnapshotV1,
    LaneRegistryV1,
    LaneCoordinatorRegistryV1,
    RouteRegistryV1,
    EconomicPolicyRegistryV1,
) {
    let lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| match lane_id {
                LaneIdV1::SPOT_LIQUIDITY => spot_release.clone(),
                LaneIdV1::ZDEX_TOKENOMICS => tokenomics_release.clone(),
                _ => lane_release(*lane_id, index as u64 + 11),
            })
            .collect(),
    };
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| coordinator_release(*lane_id, index as u64 + 1))
            .collect(),
    };
    let mut registered_routes = vec![buyback_route.clone(), allocation_route.clone()];
    registered_routes.sort_by(|left, right| left.command_kind.cmp(&right.command_kind));
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: registered_routes,
    };
    let policies = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![
            EconomicPolicyBindingV1 {
                policy_kind: ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1.to_owned(),
                command_kind: PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned(),
                policy_root: buyback_execution_policy_root.clone(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: ZDEX_FEE_ALLOCATION_POLICY_KIND_V1.to_owned(),
                command_kind: PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1.to_owned(),
                policy_root: policy_root.clone(),
            },
        ],
    };
    let lane_registry_root = lanes.registry_root().expect("lane registry root");
    let lane_coordinator_registry_root = coordinators
        .registry_root()
        .expect("coordinator registry root");
    let route_registry_root = routes.registry_root().expect("route registry root");
    let policy_registry_root = policies.registry_root().expect("policy registry root");
    let proof_shape_root = root(810);
    let root_image_id = root(811);
    let verifier_registry_root = root(812);
    let migration_registry_root = root(813);
    let terminal_registry_root = root(814);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": 11,
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
        profile_id: hash_global_v1("global-economic-profile-content-v1", &content)
            .expect("profile id"),
        authority_epoch: 11,
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
        .expect("shadow profile must bind registries");
    (profile, lanes, coordinators, routes, policies)
}

fn occurrence(
    route: &RouteReleaseV1,
    profile: &EconomicProfileSnapshotV1,
) -> EconomicCommandOccurrenceV1 {
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zenodex-shadow".to_owned(),
        deployment_root: root(1),
        height: 7,
        tx_index: 2,
        op_index: 1,
        command_kind: PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned(),
        command_body_hash: root(3),
        route_release_id: route.route_release_id.clone(),
        subject_id: "protocol-buyback-controller".to_owned(),
        grant_root: root(2),
        nonce: 9,
        profile_root: profile.profile_id.clone(),
        pre_state_root: root(4),
        consumed_object_ids: vec![],
    }
}

fn purchase_effects(journal: &ZDEXAMMPurchaseJournalV1) -> GlobalEconomicEffectPlanV1 {
    let mut plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::CUSTODY,
                principal: journal.quote_pool_bucket_id.clone(),
                asset: journal.quote_asset_id.to_string(),
                custody_domain: AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: journal.quote_amount_in_atoms as i128,
            },
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::CUSTODY,
                principal: journal.quote_source_bucket_id.clone(),
                asset: journal.quote_asset_id.to_string(),
                custody_domain: PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: -(journal.quote_amount_in_atoms as i128),
            },
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::CUSTODY,
                principal: journal.zdex_pool_bucket_id.clone(),
                asset: journal.zdex_asset_id.to_string(),
                custody_domain: AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: -(journal.purchased_zdex_atoms as i128),
            },
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::CUSTODY,
                principal: journal.burn_bucket_id.clone(),
                asset: journal.zdex_asset_id.to_string(),
                custody_domain: PROTOCOL_BURN_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: journal.purchased_zdex_atoms as i128,
            },
        ],
        asset_conservation: vec![
            AssetConservationRowV1 {
                asset: journal.quote_asset_id.to_string(),
                owned_and_custodied_pre_atoms: journal.quote_owned_atoms,
                owned_and_custodied_post_atoms: journal.quote_owned_atoms,
                supply_pre_atoms: journal.quote_supply_atoms,
                supply_post_atoms: journal.quote_supply_atoms,
                authorized_issue_atoms: 0,
                authorized_burn_atoms: 0,
            },
            AssetConservationRowV1 {
                asset: journal.zdex_asset_id.to_string(),
                owned_and_custodied_pre_atoms: journal.zdex_owned_atoms,
                owned_and_custodied_post_atoms: journal.zdex_owned_atoms,
                supply_pre_atoms: journal.zdex_supply_atoms,
                supply_post_atoms: journal.zdex_supply_atoms,
                authorized_issue_atoms: 0,
                authorized_burn_atoms: 0,
            },
        ],
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::SPOT_LIQUIDITY,
            pre_root: journal.pre_spot_lane_root.clone(),
            post_root: journal.post_spot_lane_root.clone(),
        }],
        occurrence_consumptions: vec![journal.command_occurrence_id.clone()],
        external_outbox_enqueue: vec![],
    };
    plan.rows.sort_by(|left, right| {
        (
            left.asset.as_str(),
            left.principal.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                right.asset.as_str(),
                right.principal.as_str(),
                right.custody_domain.as_str(),
            ))
    });
    plan.asset_conservation
        .sort_by(|left, right| left.asset.cmp(&right.asset));
    plan
}

fn burn_effects(journal: &ZDEXBurnJournalV1) -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::BURN,
                principal: ZDEX_SUPPLY_PRINCIPAL_V1.to_owned(),
                asset: journal.zdex_asset_id.to_string(),
                custody_domain: PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: -(journal.burned_zdex_atoms as i128),
            },
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::CUSTODY,
                principal: journal.burn_bucket_id.clone(),
                asset: journal.zdex_asset_id.to_string(),
                custody_domain: PROTOCOL_BURN_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: -(journal.burned_zdex_atoms as i128),
            },
        ],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: journal.zdex_asset_id.to_string(),
            owned_and_custodied_pre_atoms: journal.zdex_owned_pre_atoms,
            owned_and_custodied_post_atoms: journal.zdex_owned_post_atoms,
            supply_pre_atoms: journal.zdex_supply_pre_atoms,
            supply_post_atoms: journal.zdex_supply_post_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: journal.burned_zdex_atoms,
        }],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![journal.command_occurrence_id.clone()],
        external_outbox_enqueue: vec![],
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

struct RejectingVerifier;

impl ZDEXLaneSuccinctReceiptVerifierV1 for RejectingVerifier {
    fn verify_succinct_receipt(
        &self,
        _receipt_bytes: &[u8],
        _expected_image_id: &RootV1,
        _expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        Err(AbiErrorV1::InvalidBinding("test receipt rejection"))
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
        panic!("malformed receipt reached cryptographic verifier")
    }
}

struct Fixture {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    policies: EconomicPolicyRegistryV1,
    spot_release: LaneModuleReleaseV1,
    burn_release: LaneModuleReleaseV1,
    route: RouteReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    allocation_occurrence: EconomicCommandOccurrenceV1,
    fee_policy: ZDEXFeeAllocationPolicyV1,
    buyback_execution_policy: ZDEXBuybackExecutionPolicyV1,
    fee_state: ZDEXFeeStateV1,
    fee_post_state: ZDEXFeeStateV1,
    fee_effects: GlobalEconomicEffectPlanV1,
    buyback_budget_occurrence: ZDEXFeeAllocationOccurrenceV1,
    verified_buyback_budget: VerifiedZDEXFeeAllocationV1,
    purchase: ZDEXAMMPurchaseJournalV1,
    purchase_effects: GlobalEconomicEffectPlanV1,
    verified_purchase: VerifiedZDEXAMMPurchaseV1,
    burn: ZDEXBurnJournalV1,
    burn_effects: GlobalEconomicEffectPlanV1,
    verified_burn: VerifiedZDEXBurnV1,
}

fn fixture_with_fee_ingress(fee_ingress_atoms: u128) -> Fixture {
    let spot_release = lane_release(LaneIdV1::SPOT_LIQUIDITY, 1);
    let burn_release = lane_release(LaneIdV1::ZDEX_TOKENOMICS, 2);
    let route = route_release(&spot_release, &burn_release);
    let allocation_route = allocation_route_release(&burn_release);
    let fee_policy = candidate_zdex_fee_allocation_policy_v1();
    let fee_policy_root = fee_policy.policy_root().expect("fee policy root");
    let buyback_execution_policy = ZDEXBuybackExecutionPolicyV1 {
        schema: ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1.to_owned(),
        pool_id: root(602),
        pool_definition_root: root(603),
        quote_asset_id: root(600),
        zdex_asset_id: root(601),
    };
    let buyback_execution_policy_root = buyback_execution_policy
        .policy_root()
        .expect("buyback execution policy root");
    let (profile, lanes, coordinators, routes, policies) = governed_shadow_profile(
        &spot_release,
        &burn_release,
        &route,
        &allocation_route,
        &fee_policy_root,
        &buyback_execution_policy_root,
    );
    let mut occurrence = occurrence(&route, &profile);
    let occurrence_id = occurrence.occurrence_id().expect("occurrence id");
    let quote_pool_bucket_id = zdex_pool_reserve_principal_v1(
        &buyback_execution_policy.pool_id,
        &buyback_execution_policy.quote_asset_id,
    )
    .expect("quote reserve principal");
    let zdex_pool_bucket_id = zdex_pool_reserve_principal_v1(
        &buyback_execution_policy.pool_id,
        &buyback_execution_policy.zdex_asset_id,
    )
    .expect("ZDEX reserve principal");
    let burn_bucket_id = zdex_occurrence_burn_port_v1(
        &occurrence.profile_root,
        &route.route_release_id,
        &occurrence_id,
    )
    .expect("occurrence burn port");
    let mut purchase = ZDEXAMMPurchaseJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: 11,
        route_release_id: route.route_release_id.clone(),
        command_occurrence_id: occurrence_id,
        spot_module_release_id: spot_release.release_id.clone(),
        issue_burn_policy_root: route.issue_burn_policy_root.clone(),
        buyback_budget_occurrence_root: root(590),
        quote_asset_id: root(600),
        zdex_asset_id: root(601),
        quote_source_bucket_id: "protocol-fee-buyback-reserve".to_owned(),
        quote_pool_bucket_id,
        zdex_pool_bucket_id,
        burn_bucket_id,
        quote_amount_in_atoms: 125,
        purchased_zdex_atoms: 40,
        quote_source_pre_atoms: 1_000,
        quote_source_post_atoms: 875,
        quote_pool_pre_atoms: 2_000,
        quote_pool_post_atoms: 2_125,
        zdex_pool_pre_atoms: 500,
        zdex_pool_post_atoms: 460,
        burn_bucket_pre_atoms: 0,
        burn_bucket_post_atoms: 40,
        quote_owned_atoms: 10_000,
        quote_supply_atoms: 10_000,
        zdex_owned_atoms: 1_000,
        zdex_supply_atoms: 1_000,
        pre_spot_lane_root: root(610),
        post_spot_lane_root: root(611),
        effect_plan_root: root(900),
    };
    let fee_state = ZDEXFeeStateV1 {
        fee_asset_id: purchase.quote_asset_id.clone(),
        policy_root: fee_policy.policy_root().expect("fee policy root"),
        fee_ingress_atoms,
        unallocated_reserve_atoms: 0,
        destination_balances: ZDEX_FEE_DESTINATIONS_V1
            .into_iter()
            .map(|destination| ZDEXFeeDestinationAmountV1 {
                destination,
                allocation_atoms: 0,
            })
            .collect(),
        owned_and_custodied_atoms: purchase.quote_owned_atoms,
        supply_atoms: purchase.quote_supply_atoms,
    };
    let allocation_occurrence = EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        height: occurrence.height,
        tx_index: occurrence.tx_index,
        op_index: 0,
        command_kind: PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1.to_owned(),
        command_body_hash: root(6),
        route_release_id: allocation_route.route_release_id.clone(),
        subject_id: "protocol-fee-allocator".to_owned(),
        grant_root: root(5),
        nonce: 8,
        profile_root: occurrence.profile_root.clone(),
        pre_state_root: occurrence.pre_state_root.clone(),
        consumed_object_ids: vec![],
    };
    let fee_context = ZDEXFeeAllocationContextV1 {
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: purchase.writer_epoch,
        allocation_route_release_id: allocation_route.route_release_id.clone(),
        authorized_buyback_route_release_id: route.route_release_id.clone(),
        tokenomics_module_release_id: burn_release.release_id.clone(),
        command_occurrence_id: allocation_occurrence
            .occurrence_id()
            .expect("allocation occurrence id"),
        policy_root: fee_policy.policy_root().expect("fee policy root"),
    };
    let fee_accepted = match transition_zdex_fee_allocation_v1(
        &fee_context,
        &fee_state,
        &fee_policy,
        &ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: 625,
        },
    )
    .expect("fee allocation transition")
    {
        ZDEXFeeAllocationResultV1::Accepted(accepted) => accepted,
        ZDEXFeeAllocationResultV1::Rejected(rejected) => {
            panic!("fee allocation rejected: {:?}", rejected.code)
        }
    };
    let buyback_budget_occurrence = fee_accepted.occurrence.clone();
    assert_eq!(buyback_budget_occurrence.buyback_quote_atoms(), 125);
    let fee_receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"fee-allocation-receipt".to_vec(),
    };
    let governed_fee_profile = bind_zdex_fee_allocation_shadow_profile_v1(
        &profile.profile_id,
        profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &profile,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            policy_registry: &policies,
        },
    )
    .expect("fee-allocation profile must bind");
    let verified_buyback_budget = verify_zdex_fee_allocation_receipt_v1(
        ZDEXFeeAllocationReceiptCandidateV1 {
            occurrence: &allocation_occurrence,
            policy: &fee_policy,
            pre_state: &fee_state,
            post_state: &fee_accepted.post_state,
            journal: &fee_accepted.occurrence,
            effects: &fee_accepted.effects,
            receipt: &fee_receipt,
        },
        &governed_fee_profile,
        &AcceptingVerifier,
    )
    .expect("fee-allocation receipt must verify");
    purchase.buyback_budget_occurrence_root = buyback_budget_occurrence
        .occurrence_root()
        .expect("buyback budget occurrence root");
    occurrence.consumed_object_ids = vec![purchase.buyback_budget_occurrence_root.to_string()];
    purchase.command_occurrence_id = occurrence.occurrence_id().expect("bound occurrence id");
    purchase.burn_bucket_id = zdex_occurrence_burn_port_v1(
        &occurrence.profile_root,
        &route.route_release_id,
        &purchase.command_occurrence_id,
    )
    .expect("bound occurrence burn port");
    let purchase_effects = purchase_effects(&purchase);
    purchase.effect_plan_root = purchase_effects
        .effect_plan_root()
        .expect("purchase plan root");
    let purchase_receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"purchase-receipt".to_vec(),
    };
    let verified_purchase = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1 {
            route_release: &route,
            module_release: &spot_release,
            occurrence: &occurrence,
            journal: &purchase,
            effects: &purchase_effects,
            receipt: &purchase_receipt,
        },
        &AcceptingVerifier,
    )
    .expect("purchase receipt must verify");

    let mut burn = ZDEXBurnJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: purchase.writer_epoch,
        route_release_id: route.route_release_id.clone(),
        command_occurrence_id: purchase.command_occurrence_id.clone(),
        tokenomics_module_release_id: burn_release.release_id.clone(),
        issue_burn_policy_root: route.issue_burn_policy_root.clone(),
        buyback_budget_occurrence_root: purchase.buyback_budget_occurrence_root.clone(),
        authorized_quote_input_atoms: purchase.quote_amount_in_atoms,
        purchase_occurrence_root: purchase.journal_root().expect("purchase journal root"),
        route_context_root: root(619),
        zdex_asset_id: purchase.zdex_asset_id.clone(),
        burn_bucket_id: purchase.burn_bucket_id.clone(),
        burned_zdex_atoms: purchase.purchased_zdex_atoms,
        burn_bucket_pre_atoms: purchase.purchased_zdex_atoms,
        burn_bucket_post_atoms: 0,
        zdex_owned_pre_atoms: purchase.zdex_owned_atoms,
        zdex_owned_post_atoms: purchase.zdex_owned_atoms - purchase.purchased_zdex_atoms,
        zdex_supply_pre_atoms: purchase.zdex_supply_atoms,
        zdex_supply_post_atoms: purchase.zdex_supply_atoms - purchase.purchased_zdex_atoms,
        pre_tokenomics_burn_substate_root: root(620),
        post_tokenomics_burn_substate_root: root(621),
        effect_plan_root: root(901),
    };
    let burn_effects = burn_effects(&burn);
    burn.effect_plan_root = burn_effects.effect_plan_root().expect("burn plan root");
    let burn_receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"burn-receipt".to_vec(),
    };
    let verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1 {
            route_release: &route,
            module_release: &burn_release,
            occurrence: &occurrence,
            journal: &burn,
            effects: &burn_effects,
            receipt: &burn_receipt,
        },
        &AcceptingVerifier,
    )
    .expect("burn receipt must verify");

    Fixture {
        profile,
        lanes,
        coordinators,
        routes,
        policies,
        spot_release,
        burn_release,
        route,
        occurrence,
        allocation_occurrence,
        fee_policy,
        buyback_execution_policy,
        fee_state,
        fee_post_state: fee_accepted.post_state,
        fee_effects: fee_accepted.effects,
        buyback_budget_occurrence,
        verified_buyback_budget,
        purchase,
        purchase_effects,
        verified_purchase,
        burn,
        burn_effects,
        verified_burn,
    }
}

fn fixture() -> Fixture {
    fixture_with_fee_ingress(625)
}

fn compose(fixture: &Fixture) -> ZDEXPurchaseBurnRouteResultV1 {
    let governed_profile = bind_zdex_purchase_burn_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXPurchaseBurnRouteProfileRegistriesV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policies: &fixture.policies,
            buyback_execution_policy: &fixture.buyback_execution_policy,
        },
    )
    .expect("purchase-burn profile must bind");
    compose_zdex_purchase_burn_route_v1(ZDEXPurchaseBurnRouteCandidateV1 {
        governed_profile,
        route_release: &fixture.route,
        occurrence: &fixture.occurrence,
        buyback_budget_occurrence: &fixture.buyback_budget_occurrence,
        verified_buyback_budget: &fixture.verified_buyback_budget,
        purchase_journal: &fixture.purchase,
        purchase_effects: &fixture.purchase_effects,
        verified_purchase: &fixture.verified_purchase,
        burn_journal: &fixture.burn,
        burn_effects: &fixture.burn_effects,
        verified_burn: &fixture.verified_burn,
    })
    .expect("route composition must execute")
}

fn governed_fee_profile(fixture: &Fixture) -> GovernedZDEXFeeAllocationProfileV1<'_> {
    bind_zdex_fee_allocation_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policy_registry: &fixture.policies,
        },
    )
    .expect("fixture fee-allocation profile must bind")
}

fn reauthenticate_buyback_leaves(fixture: &mut Fixture) {
    let occurrence_id = fixture
        .occurrence
        .occurrence_id()
        .expect("mutated occurrence id");
    fixture.purchase.command_occurrence_id = occurrence_id.clone();
    fixture.purchase_effects = purchase_effects(&fixture.purchase);
    fixture.purchase.effect_plan_root = fixture
        .purchase_effects
        .effect_plan_root()
        .expect("mutated purchase effect root");
    fixture.burn.command_occurrence_id = occurrence_id;
    fixture.burn.purchase_occurrence_root = fixture
        .purchase
        .journal_root()
        .expect("mutated purchase journal root");
    fixture.burn_effects = burn_effects(&fixture.burn);
    fixture.burn.effect_plan_root = fixture
        .burn_effects
        .effect_plan_root()
        .expect("mutated burn effect root");
    let purchase_receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"rebound-purchase".to_vec(),
    };
    fixture.verified_purchase = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1 {
            route_release: &fixture.route,
            module_release: &fixture.spot_release,
            occurrence: &fixture.occurrence,
            journal: &fixture.purchase,
            effects: &fixture.purchase_effects,
            receipt: &purchase_receipt,
        },
        &AcceptingVerifier,
    )
    .expect("mutated purchase receipt must verify");
    let burn_receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"rebound-burn".to_vec(),
    };
    fixture.verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1 {
            route_release: &fixture.route,
            module_release: &fixture.burn_release,
            occurrence: &fixture.occurrence,
            journal: &fixture.burn,
            effects: &fixture.burn_effects,
            receipt: &burn_receipt,
        },
        &AcceptingVerifier,
    )
    .expect("mutated burn receipt must verify");
}

#[test]
fn rust_matches_python_golden_composition_root_and_effects() {
    let fixture = fixture();
    let ZDEXPurchaseBurnRouteResultV1::Accepted(accepted) = compose(&fixture) else {
        panic!("valid fixture must accept")
    };
    let composition = accepted
        .composition_journal_v2()
        .expect("composition journal V2");

    assert_eq!(
        composition
            .journal_root()
            .expect("composition root")
            .as_str(),
        "0x5b253eabc0f3f8d9a302fc9bfcaf9e9be84193786aa7c7230d37c0fb0c1f86be"
    );
    assert_eq!(
        composition.buyback_execution_policy_root,
        accepted.buyback_execution_policy_root
    );
    assert_eq!(
        zenodex_global_settlement_abi_v1::zdex_burn_port_schema_root_v1()
            .expect("burn substate port root")
            .as_str(),
        "0x744c54af6df7c8a4fa0c5e0b152e0139add14c337d7cbcf1c8062e8aa2fa5289"
    );
    assert_eq!(
        accepted.effects.occurrence_consumptions,
        vec![fixture.occurrence.occurrence_id().expect("occurrence id")]
    );
    assert_eq!(
        fixture.occurrence.consumed_object_ids,
        vec![fixture
            .buyback_budget_occurrence
            .occurrence_root()
            .expect("budget root")
            .to_string()]
    );
    assert_eq!(accepted.effects.lane_writes.len(), 1);
    assert_eq!(
        accepted.effects.lane_writes[0].lane_id,
        LaneIdV1::SPOT_LIQUIDITY
    );
    assert!(!accepted.terminal_obligations_root.is_zero());
    assert_eq!(
        accepted.terminal_obligations_root.as_str(),
        "0xb3a804a59299dd1349592fafec630720031217d4b3340a385a345d544d4b4553"
    );
    assert!(accepted
        .effects
        .rows
        .iter()
        .all(|row| row.principal != fixture.purchase.burn_bucket_id));
}

#[test]
fn composition_journal_v2_rejects_unknown_fields_and_wrong_cardinality() {
    // Arrange.
    let fixture = fixture();
    let ZDEXPurchaseBurnRouteResultV1::Accepted(accepted) = compose(&fixture) else {
        panic!("valid fixture must accept")
    };
    let journal = accepted
        .composition_journal_v2()
        .expect("composition journal V2");
    let mut unknown_field = serde_json::to_value(&journal).expect("journal must serialize");
    unknown_field
        .as_object_mut()
        .expect("journal JSON must be an object")
        .insert("caller_pool_override".to_owned(), json!(root(990)));
    let mut short = journal;
    short.ordered_lane_journal_roots.pop();

    // Act / Assert.
    assert!(
        serde_json::from_value::<
            zenodex_global_settlement_abi_v1::ZDEXPurchaseBurnRouteCompositionJournalV2,
        >(unknown_field)
        .is_err(),
        "unknown composition fields must reject"
    );
    assert!(
        short.validate().is_err(),
        "composition must bind exactly two lane journals"
    );
}

#[test]
fn owned_supply_baseline_equality_accepts_and_neighbors_reject_without_effects() {
    let control = fixture();
    assert!(matches!(
        compose(&control),
        ZDEXPurchaseBurnRouteResultV1::Accepted(_)
    ));

    for quote_mismatch in [true, false] {
        let mut fixture = fixture();
        if quote_mismatch {
            fixture.purchase.quote_supply_atoms -= 1;
        } else {
            fixture.purchase.zdex_supply_atoms -= 1;
        }
        reauthenticate_buyback_leaves(&mut fixture);

        let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = compose(&fixture) else {
            panic!("owned/supply baseline mismatch must reject")
        };
        assert_eq!(
            rejected.code,
            ZDEXPurchaseBurnRouteRejectCodeV1::CONSERVATION_HISTORY_DISCONNECTED
        );
        assert!(rejected.effects.is_empty());
    }
}

#[test]
fn foreign_route_rejects_governed_profile_without_effects() {
    let fixture = fixture();
    let foreign_tokenomics = lane_release(LaneIdV1::ZDEX_TOKENOMICS, 98);
    let foreign_route = route_release(&fixture.spot_release, &foreign_tokenomics);
    let governed_profile = bind_zdex_purchase_burn_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXPurchaseBurnRouteProfileRegistriesV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policies: &fixture.policies,
            buyback_execution_policy: &fixture.buyback_execution_policy,
        },
    )
    .expect("fixture purchase-burn profile must bind");

    let result = compose_zdex_purchase_burn_route_v1(ZDEXPurchaseBurnRouteCandidateV1 {
        governed_profile,
        route_release: &foreign_route,
        occurrence: &fixture.occurrence,
        buyback_budget_occurrence: &fixture.buyback_budget_occurrence,
        verified_buyback_budget: &fixture.verified_buyback_budget,
        purchase_journal: &fixture.purchase,
        purchase_effects: &fixture.purchase_effects,
        verified_purchase: &fixture.verified_purchase,
        burn_journal: &fixture.burn,
        burn_effects: &fixture.burn_effects,
        verified_burn: &fixture.verified_burn,
    })
    .expect("foreign route must produce a typed result");

    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = result else {
        panic!("foreign route must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::GOVERNED_PROFILE_MISMATCH
    );
    assert!(rejected.effects.rows.is_empty());
    assert!(rejected.effects.occurrence_consumptions.is_empty());
}

#[test]
fn caller_substituted_pool_buckets_reject_without_effects() {
    // Arrange: keep the governed route, assets, budget, and amounts unchanged,
    // while substituting only the two pool custody identities. Re-authentication
    // models structurally valid lane receipts for an alternate same-asset pool.
    let mut fixture = fixture();
    fixture.purchase.quote_pool_bucket_id = "pool:attacker-quote".to_owned();
    fixture.purchase.zdex_pool_bucket_id = "pool:attacker-zdex".to_owned();
    reauthenticate_buyback_leaves(&mut fixture);

    // Act.
    let result = compose(&fixture);

    // Assert: pool-selection authority belongs to governed policy, so a
    // substituted pool pair must fail closed and emit no economic effects.
    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = result else {
        panic!("caller-substituted pool buckets must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_EXECUTION_POLICY_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn same_pair_alternate_pool_rejects_without_effects() {
    // Arrange: authenticate both reserve principals for one alternate pool.
    let mut fixture = fixture();
    let alternate_pool = root(990);
    fixture.purchase.quote_pool_bucket_id =
        zdex_pool_reserve_principal_v1(&alternate_pool, &fixture.purchase.quote_asset_id)
            .expect("alternate quote reserve");
    fixture.purchase.zdex_pool_bucket_id =
        zdex_pool_reserve_principal_v1(&alternate_pool, &fixture.purchase.zdex_asset_id)
            .expect("alternate ZDEX reserve");
    reauthenticate_buyback_leaves(&mut fixture);

    // Act.
    let result = compose(&fixture);

    // Assert.
    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = result else {
        panic!("same-pair alternate pool must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_EXECUTION_POLICY_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn mixed_pool_reserve_keys_reject_without_effects() {
    // Arrange: splice one output reserve principal from another pool.
    let mut fixture = fixture();
    fixture.purchase.zdex_pool_bucket_id =
        zdex_pool_reserve_principal_v1(&root(990), &fixture.purchase.zdex_asset_id)
            .expect("alternate ZDEX reserve");
    reauthenticate_buyback_leaves(&mut fixture);

    // Act.
    let result = compose(&fixture);

    // Assert.
    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = result else {
        panic!("mixed-pool reserve keys must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_EXECUTION_POLICY_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn occurrence_scoped_burn_ports_are_distinct_and_deterministic() {
    // Arrange.
    let fixture = fixture();

    // Act.
    let first = zdex_occurrence_burn_port_v1(
        &fixture.occurrence.profile_root,
        &fixture.route.route_release_id,
        &fixture.purchase.command_occurrence_id,
    )
    .expect("first occurrence burn port");
    let second = zdex_occurrence_burn_port_v1(
        &fixture.occurrence.profile_root,
        &fixture.route.route_release_id,
        &root(991),
    )
    .expect("second occurrence burn port");

    // Assert.
    assert_eq!(first, fixture.purchase.burn_bucket_id);
    assert_ne!(first, second);
    assert_eq!(
        first,
        zdex_occurrence_burn_port_v1(
            &fixture.occurrence.profile_root,
            &fixture.route.route_release_id,
            &fixture.purchase.command_occurrence_id,
        )
        .expect("replayed occurrence burn port")
    );
}

#[test]
fn every_governed_buyback_resource_substitution_rejects_without_effects() {
    for field in [
        "quote_asset",
        "zdex_asset",
        "quote_pool",
        "zdex_pool",
        "burn_bucket",
    ] {
        // Arrange.
        let mut fixture = fixture();
        match field {
            "quote_asset" => fixture.purchase.quote_asset_id = root(991),
            "zdex_asset" => fixture.purchase.zdex_asset_id = root(992),
            "quote_pool" => {
                fixture.purchase.quote_pool_bucket_id = "pool:alternate-quote".to_owned()
            }
            "zdex_pool" => fixture.purchase.zdex_pool_bucket_id = "pool:alternate-zdex".to_owned(),
            "burn_bucket" => fixture.purchase.burn_bucket_id = "protocol:alternate-burn".to_owned(),
            _ => unreachable!("closed test mutation"),
        }
        reauthenticate_buyback_leaves(&mut fixture);

        // Act.
        let result = compose(&fixture);

        // Assert.
        let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = result else {
            panic!("governed buyback resource substitution must reject: {field}")
        };
        assert_eq!(
            rejected.code,
            ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_EXECUTION_POLICY_MISMATCH,
            "mutation: {field}"
        );
        assert!(rejected.effects.is_empty(), "mutation: {field}");
    }
}

#[test]
fn unregistered_buyback_execution_policy_rejects_profile_binding() {
    // Arrange.
    let fixture = fixture();
    let mut substituted = fixture.buyback_execution_policy.clone();
    substituted.pool_id = root(990);

    // Act.
    let error = bind_zdex_purchase_burn_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXPurchaseBurnRouteProfileRegistriesV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policies: &fixture.policies,
            buyback_execution_policy: &substituted,
        },
    )
    .err()
    .expect("unregistered buyback execution policy must reject");

    // Assert.
    assert!(error
        .to_string()
        .contains("ZDEX buyback execution policy binding"));
}

#[test]
fn shifted_fee_allocation_rejects_before_receipt_verification() {
    let fixture = fixture();
    let governed = governed_fee_profile(&fixture);
    let mut shifted = fixture.buyback_budget_occurrence.clone();
    shifted.allocations[0].allocation_atoms -= 1;
    shifted.allocations[2].allocation_atoms += 1;
    shifted
        .validate()
        .expect("sum-preserving mutant is structural");
    let receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"shifted-allocation".to_vec(),
    };

    let error = verify_zdex_fee_allocation_receipt_v1(
        ZDEXFeeAllocationReceiptCandidateV1 {
            occurrence: &fixture.allocation_occurrence,
            policy: &fixture.fee_policy,
            pre_state: &fixture.fee_state,
            post_state: &fixture.fee_post_state,
            journal: &shifted,
            effects: &fixture.fee_effects,
            receipt: &receipt,
        },
        &governed,
        &PanickingVerifier,
    )
    .expect_err("shifted allocation must reject before receipt verification");

    assert!(error
        .to_string()
        .contains("ZDEX fee-allocation journal or effects"));
}

#[test]
fn self_consistent_alternative_release_graph_rejects_trusted_profile_anchor() {
    let fixture = fixture();
    let alternative_tokenomics = lane_release(LaneIdV1::ZDEX_TOKENOMICS, 99);
    let alternative_buyback = route_release(&fixture.spot_release, &alternative_tokenomics);
    let alternative_allocation = allocation_route_release(&alternative_tokenomics);
    let policy_root = fixture.fee_policy.policy_root().expect("policy root");
    let (profile, lanes, coordinators, routes, policies) = governed_shadow_profile(
        &fixture.spot_release,
        &alternative_tokenomics,
        &alternative_buyback,
        &alternative_allocation,
        &policy_root,
        &fixture
            .buyback_execution_policy
            .policy_root()
            .expect("buyback execution policy root"),
    );

    let error = bind_zdex_fee_allocation_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &profile,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            policy_registry: &policies,
        },
    )
    .err()
    .expect("alternative release graph must reject");

    assert!(error.to_string().contains("expected profile"));

    let route_error = bind_zdex_purchase_burn_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXPurchaseBurnRouteProfileRegistriesV1 {
            profile: &profile,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            policies: &policies,
            buyback_execution_policy: &fixture.buyback_execution_policy,
        },
    )
    .err()
    .expect("alternative buyback route graph must reject");

    assert!(route_error.to_string().contains("expected profile"));
}

#[test]
fn profile_status_substitution_rejects_with_same_profile_id() {
    let fixture = fixture();
    let mut substituted = fixture.profile.clone();
    substituted.status = ProfileStatusV1::CANDIDATE;

    let error = bind_zdex_fee_allocation_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &substituted,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policy_registry: &fixture.policies,
        },
    )
    .err()
    .expect("profile status substitution must reject");

    assert!(error.to_string().contains("profile status"));
}

#[test]
fn wrong_expected_authority_epoch_rejects_trusted_profile_anchor() {
    let fixture = fixture();

    let error = bind_zdex_fee_allocation_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch + 1,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policy_registry: &fixture.policies,
        },
    )
    .err()
    .expect("wrong trusted authority epoch must reject");

    assert!(error.to_string().contains("expected authority epoch"));
}

#[test]
fn trusted_profile_rejects_each_independently_substituted_release_registry() {
    let fixture = fixture();
    let mut lanes = fixture.lanes.clone();
    lanes.releases[0] = lane_release(lanes.releases[0].lane_id, 991);
    let mut coordinators = fixture.coordinators.clone();
    coordinators.releases[0] = coordinator_release(coordinators.releases[0].lane_id, 992);
    let mut routes = fixture.routes.clone();
    routes.routes[0].status = ReleaseStatusV1::CANDIDATE;

    for (label, candidate_lanes, candidate_coordinators, candidate_routes) in [
        ("lanes", &lanes, &fixture.coordinators, &fixture.routes),
        (
            "coordinators",
            &fixture.lanes,
            &coordinators,
            &fixture.routes,
        ),
        ("routes", &fixture.lanes, &fixture.coordinators, &routes),
    ] {
        let error = bind_zdex_fee_allocation_shadow_profile_v1(
            &fixture.profile.profile_id,
            fixture.profile.authority_epoch,
            ZDEXFeeAllocationProfileRegistriesV1 {
                profile: &fixture.profile,
                lanes: candidate_lanes,
                coordinators: candidate_coordinators,
                routes: candidate_routes,
                policy_registry: &fixture.policies,
            },
        )
        .err()
        .unwrap_or_else(|| panic!("{label} registry substitution must reject"));

        assert!(
            error.to_string().contains("registry"),
            "unexpected {label} registry error: {error}"
        );
    }
}

#[test]
fn policy_registry_substitution_rejects_before_receipt_verification() {
    let fixture = fixture();
    let substituted = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![EconomicPolicyBindingV1 {
            policy_kind: ZDEX_FEE_ALLOCATION_POLICY_KIND_V1.to_owned(),
            command_kind: PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1.to_owned(),
            policy_root: root(999),
        }],
    };

    let error = bind_zdex_fee_allocation_shadow_profile_v1(
        &fixture.profile.profile_id,
        fixture.profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            policy_registry: &substituted,
        },
    )
    .err()
    .expect("policy registry substitution must reject");

    assert!(error.to_string().contains("policy registry"));
}

#[test]
fn profile_coordinate_substitutions_reject_before_receipt_verification() {
    let fixture = fixture();
    let governed = governed_fee_profile(&fixture);
    let receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"profile-coordinate".to_vec(),
    };
    let mut wrong_occurrence = fixture.allocation_occurrence.clone();
    wrong_occurrence.profile_root = root(998);
    let wrong_occurrence_result = verify_zdex_fee_allocation_receipt_v1(
        ZDEXFeeAllocationReceiptCandidateV1 {
            occurrence: &wrong_occurrence,
            policy: &fixture.fee_policy,
            pre_state: &fixture.fee_state,
            post_state: &fixture.fee_post_state,
            journal: &fixture.buyback_budget_occurrence,
            effects: &fixture.fee_effects,
            receipt: &receipt,
        },
        &governed,
        &PanickingVerifier,
    );
    assert!(wrong_occurrence_result.is_err());

    let mut wrong_epoch = fixture.buyback_budget_occurrence.clone();
    wrong_epoch.writer_epoch += 1;
    let wrong_epoch_result = verify_zdex_fee_allocation_receipt_v1(
        ZDEXFeeAllocationReceiptCandidateV1 {
            occurrence: &fixture.allocation_occurrence,
            policy: &fixture.fee_policy,
            pre_state: &fixture.fee_state,
            post_state: &fixture.fee_post_state,
            journal: &wrong_epoch,
            effects: &fixture.fee_effects,
            receipt: &receipt,
        },
        &governed,
        &PanickingVerifier,
    );
    assert!(wrong_epoch_result.is_err());
}

#[test]
fn policy_registry_root_matches_python_golden_vector() {
    let fixture = fixture();

    assert_eq!(
        fixture
            .policies
            .registry_root()
            .expect("policy registry root")
            .as_str(),
        "0x91935990f8290fcca1ed76bbd4ea11aaccc85d8067096e10ca3fb908f79cc759"
    );
    assert_eq!(
        canonical_bytes_v1(&fixture.policies).expect("policy registry bytes"),
        br#"{"bindings":[{"command_kind":"protocol_buy_and_burn","policy_kind":"zdex_buyback_execution_v1","policy_root":"0x4603d57180f7be6fc23dd39ffdf1da2eb1b6b19168dca37349875183e4296599"},{"command_kind":"protocol_fee_allocation","policy_kind":"zdex_fee_allocation","policy_root":"0xd810507e5d15fd874a2e75b6f32b71b47174a799b8015301700e4554614032c2"}],"schema":"zenodex/global-settlement-abi/v1"}"#
    );
}

#[test]
fn buyback_execution_policy_root_matches_python_golden_vector() {
    let fixture = fixture();
    assert_eq!(
        fixture
            .buyback_execution_policy
            .policy_root()
            .expect("buyback execution policy root")
            .as_str(),
        "0x4603d57180f7be6fc23dd39ffdf1da2eb1b6b19168dca37349875183e4296599"
    );
}

#[test]
fn buyback_execution_policy_decode_and_resource_aliases_fail_closed() {
    // Arrange.
    let fixture = fixture();
    let mut unknown_field =
        serde_json::to_value(&fixture.buyback_execution_policy).expect("policy must serialize");
    unknown_field
        .as_object_mut()
        .expect("policy JSON must be an object")
        .insert("caller_pool_override".to_owned(), json!("pool:attacker"));
    let mut aliased = fixture.buyback_execution_policy.clone();
    aliased.zdex_asset_id = aliased.quote_asset_id.clone();

    // Act / Assert.
    assert!(
        serde_json::from_value::<ZDEXBuybackExecutionPolicyV1>(unknown_field).is_err(),
        "unknown policy fields must reject"
    );
    assert!(
        aliased.validate().is_err(),
        "buyback direction requires distinct assets"
    );
}

#[test]
fn policy_registry_rejects_duplicate_unsorted_wrong_command_and_unknown_fields() {
    let first = EconomicPolicyBindingV1 {
        policy_kind: "a".to_owned(),
        command_kind: "b".to_owned(),
        policy_root: root(991),
    };
    let second = EconomicPolicyBindingV1 {
        policy_kind: "a".to_owned(),
        command_kind: "c".to_owned(),
        policy_root: root(992),
    };
    let duplicate = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![first.clone(), first.clone()],
    };
    let unsorted = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![second, first],
    };
    let fixture = fixture();

    assert!(duplicate.validate().is_err());
    assert!(unsorted.validate().is_err());
    assert!(fixture
        .policies
        .require_binding(ZDEX_FEE_ALLOCATION_POLICY_KIND_V1, "protocol_wrong_command",)
        .is_err());
    assert!(serde_json::from_value::<EconomicPolicyBindingV1>(json!({
        "policy_kind": ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
        "command_kind": PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        "policy_root": fixture.fee_policy.policy_root().expect("policy root"),
        "unexpected": true,
    }))
    .is_err());

    let bindings: Vec<_> = (0..257)
        .map(|index| EconomicPolicyBindingV1 {
            policy_kind: format!("policy_{index:03}"),
            command_kind: "command".to_owned(),
            policy_root: root(991),
        })
        .collect();
    let at_limit = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: bindings[..256].to_vec(),
    };
    let over_limit = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings,
    };
    assert!(at_limit.validate().is_ok());
    assert!(over_limit.validate().is_err());
}

#[test]
fn fee_allocation_requires_nonempty_succinct_receipt_before_verifier() {
    let fixture = fixture();
    let governed = governed_fee_profile(&fixture);
    let cases = [
        (ReceiptKindV1::COMPOSITE, b"receipt".as_slice()),
        (ReceiptKindV1::CONDITIONAL, b"receipt".as_slice()),
        (ReceiptKindV1::FAKE, b"receipt".as_slice()),
        (ReceiptKindV1::DEVELOPMENT, b"receipt".as_slice()),
        (ReceiptKindV1::SUCCINCT, b"".as_slice()),
    ];

    for (receipt_kind, receipt_bytes) in cases {
        let receipt = ZDEXLaneReceiptEnvelopeV1 {
            receipt_kind,
            receipt_bytes: receipt_bytes.to_vec(),
        };
        let result = verify_zdex_fee_allocation_receipt_v1(
            ZDEXFeeAllocationReceiptCandidateV1 {
                occurrence: &fixture.allocation_occurrence,
                policy: &fixture.fee_policy,
                pre_state: &fixture.fee_state,
                post_state: &fixture.fee_post_state,
                journal: &fixture.buyback_budget_occurrence,
                effects: &fixture.fee_effects,
                receipt: &receipt,
            },
            &governed,
            &PanickingVerifier,
        );

        assert!(result.is_err());
    }
}

#[test]
fn command_must_consume_exact_authenticated_budget_object() {
    let mut fixture = fixture();
    fixture.occurrence.consumed_object_ids = vec![root(991).to_string()];
    reauthenticate_buyback_leaves(&mut fixture);

    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = compose(&fixture) else {
        panic!("wrong consumed object must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn buyback_budget_must_consume_exact_verified_fee_ingress() {
    // Arrange: create a valid generic allocation that consumes only part of ingress.
    let fixture = fixture_with_fee_ingress(626);
    assert_eq!(fixture.buyback_budget_occurrence.fee_charged_atoms, 625);
    assert_eq!(fixture.verified_buyback_budget.fee_ingress_atoms(), 626);

    // Act.
    let result = compose(&fixture);

    // Assert.
    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = result else {
        panic!("partial fee-ingress buyback budget must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn unbound_budget_occurrence_is_typed_no_effect_reject() {
    let mut fixture = fixture();
    fixture
        .buyback_budget_occurrence
        .authorized_buyback_route_release_id = root(992);

    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = compose(&fixture) else {
        panic!("unbound budget occurrence must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn buyback_budget_cannot_be_redirected_to_another_source() {
    let mut fixture = fixture();
    fixture.purchase.quote_source_bucket_id = "account:alice".to_owned();

    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = compose(&fixture) else {
        panic!("redirected budget source must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn quote_budget_substitution_is_typed_no_effect_reject() {
    let mut fixture = fixture();
    fixture.burn.authorized_quote_input_atoms -= 1;
    fixture.burn_effects = burn_effects(&fixture.burn);
    fixture.burn.effect_plan_root = fixture
        .burn_effects
        .effect_plan_root()
        .expect("mutated burn plan root");
    let receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"mutated-burn".to_vec(),
    };
    fixture.verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1 {
            route_release: &fixture.route,
            module_release: &fixture.burn_release,
            occurrence: &fixture.occurrence,
            journal: &fixture.burn,
            effects: &fixture.burn_effects,
            receipt: &receipt,
        },
        &AcceptingVerifier,
    )
    .expect("mutated leaf remains internally valid");

    let ZDEXPurchaseBurnRouteResultV1::Rejected(rejected) = compose(&fixture) else {
        panic!("budget substitution must reject")
    };
    assert_eq!(
        rejected.code,
        ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH
    );
    assert!(rejected.effects.is_empty());
}

#[test]
fn cryptographic_verifier_rejection_returns_no_witness() {
    let fixture = fixture();
    let receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"rejected".to_vec(),
    };
    let error = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1 {
            route_release: &fixture.route,
            module_release: &fixture.spot_release,
            occurrence: &fixture.occurrence,
            journal: &fixture.purchase,
            effects: &fixture.purchase_effects,
            receipt: &receipt,
        },
        &RejectingVerifier,
    )
    .expect_err("verifier rejection must propagate");

    assert_eq!(
        error.to_string(),
        "invalid ABI V1 binding: test receipt rejection"
    );
}

#[test]
fn non_authoritative_receipt_shapes_reject_before_verifier() {
    let fixture = fixture();
    let cases = [
        (ReceiptKindV1::COMPOSITE, b"receipt".as_slice()),
        (ReceiptKindV1::CONDITIONAL, b"receipt".as_slice()),
        (ReceiptKindV1::FAKE, b"receipt".as_slice()),
        (ReceiptKindV1::DEVELOPMENT, b"receipt".as_slice()),
        (ReceiptKindV1::SUCCINCT, b"".as_slice()),
    ];

    for (receipt_kind, receipt_bytes) in cases {
        let receipt = ZDEXLaneReceiptEnvelopeV1 {
            receipt_kind,
            receipt_bytes: receipt_bytes.to_vec(),
        };
        let result = verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1 {
                route_release: &fixture.route,
                module_release: &fixture.spot_release,
                occurrence: &fixture.occurrence,
                journal: &fixture.purchase,
                effects: &fixture.purchase_effects,
                receipt: &receipt,
            },
            &PanickingVerifier,
        );

        assert!(result.is_err());
    }
}

#[test]
fn active_release_cannot_cross_shadow_only_admission() {
    let fixture = fixture();
    let mut active_route = fixture.route.clone();
    active_route.status = ReleaseStatusV1::ACTIVE_NEW;
    active_route.accepts_new_objects = true;
    active_route.evidence_statuses = active_evidence();
    active_route
        .validate()
        .expect("control active route must be structurally valid");
    let receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"active".to_vec(),
    };

    let error = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1 {
            route_release: &active_route,
            module_release: &fixture.spot_release,
            occurrence: &fixture.occurrence,
            journal: &fixture.purchase,
            effects: &fixture.purchase_effects,
            receipt: &receipt,
        },
        &AcceptingVerifier,
    )
    .expect_err("unpromoted verifier must reject active releases");

    assert!(error.to_string().contains("ZDEX route release status"));
}

#[test]
fn wrong_purchase_effect_root_rejects_before_receipt_authority() {
    let fixture = fixture();
    let mut effects = fixture.purchase_effects.clone();
    effects.rows[0].delta_atoms += 1;
    let receipt = ZDEXLaneReceiptEnvelopeV1 {
        receipt_kind: ReceiptKindV1::SUCCINCT,
        receipt_bytes: b"mutated".to_vec(),
    };
    let error = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1 {
            route_release: &fixture.route,
            module_release: &fixture.spot_release,
            occurrence: &fixture.occurrence,
            journal: &fixture.purchase,
            effects: &effects,
            receipt: &receipt,
        },
        &AcceptingVerifier,
    )
    .expect_err("unbound effects must reject");

    assert!(error
        .to_string()
        .contains("ZDEX purchase journal or effects"));
}

#[test]
fn preexisting_transient_burn_inventory_is_invalid() {
    let mut fixture = fixture();
    fixture.purchase.burn_bucket_pre_atoms = 1;

    let error = fixture
        .purchase
        .validate()
        .expect_err("purchase burn bucket must begin empty");

    assert!(error
        .to_string()
        .contains("ZDEX purchase transient burn bucket projection"));
}

#[test]
fn incomplete_transient_burn_drain_is_invalid() {
    let mut fixture = fixture();
    fixture.burn.burn_bucket_post_atoms = 1;

    let error = fixture
        .burn
        .validate()
        .expect_err("burn bucket must drain completely");

    assert!(error
        .to_string()
        .contains("ZDEX burn transient bucket projection"));
}

struct FeeLaneReceiptFixture {
    context: ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    module: zenodex_global_settlement_abi_v1::LaneModuleTransitionJournalV1,
    port: zenodex_global_settlement_abi_v1::ZDEXTokenomicsFeeAllocationPrivatePortV1,
    pre_state: ZDEXTokenomicsLaneStateV1,
    post_state: ZDEXTokenomicsLaneStateV1,
    allocation: zenodex_global_settlement_abi_v1::ZDEXFeeAllocationAcceptedV1,
    policy: ZDEXFeeAllocationPolicyV1,
    receipt: ZDEXLaneReceiptEnvelopeV1,
}

impl FeeLaneReceiptFixture {
    fn lane_candidate(&self) -> ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_> {
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

    fn receipt_candidate<'a>(
        &'a self,
        occurrence: &'a EconomicCommandOccurrenceV1,
        verified_allocation: &'a VerifiedZDEXFeeAllocationV1,
    ) -> ZDEXTokenomicsFeeLaneReceiptCandidateV1<'a> {
        ZDEXTokenomicsFeeLaneReceiptCandidateV1 {
            occurrence,
            lane_candidate: self.lane_candidate(),
            verified_allocation,
            receipt: &self.receipt,
        }
    }
}

fn fee_lane_state(fee_state: ZDEXFeeStateV1) -> ZDEXTokenomicsLaneStateV1 {
    ZDEXTokenomicsLaneStateV1 {
        schema: ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1.to_owned(),
        supply_state: ZDEXSupplyStateV1 {
            asset_id: root(880),
            policy_root: root(881),
            decimals: 8,
            precision_epoch: 0,
            live_supply_atoms: 1_000,
            buckets: vec![ZDEXAmountBucketV1 {
                bucket_id: "wallet:alice".to_owned(),
                amount_atoms: 1_000,
            }],
            burn_budget_epoch: 5,
            remaining_epoch_burn_cap_atoms: 100,
        },
        fee_allocation_states: vec![fee_state],
        staking_state_root: root(882),
        host_claims_state_root: root(883),
        treasury_claims_state_root: root(884),
        proof_rewards_state_root: root(885),
        cover_reserve_state_root: root(886),
        lp_rebates_state_root: root(887),
    }
}

fn fee_lane_receipt_fixture(base: &Fixture) -> FeeLaneReceiptFixture {
    let allocation = zenodex_global_settlement_abi_v1::ZDEXFeeAllocationAcceptedV1 {
        pre_state: base.fee_state.clone(),
        post_state: base.fee_post_state.clone(),
        effects: base.fee_effects.clone(),
        occurrence: base.buyback_budget_occurrence.clone(),
    };
    allocation.validate().expect("fee acceptance must validate");
    let policy = base.fee_policy.clone();
    let port = build_zdex_tokenomics_fee_allocation_private_port_v1(&allocation, &policy)
        .expect("fee private port");
    let module =
        build_zdex_tokenomics_fee_allocation_module_journal_v1(&allocation, &policy, &port)
            .expect("fee module journal");
    let occurrence = &allocation.occurrence;
    let coordinator = base
        .coordinators
        .release_for(LaneIdV1::ZDEX_TOKENOMICS)
        .expect("tokenomics coordinator");
    FeeLaneReceiptFixture {
        context: ZDEXTokenomicsFeeAllocationCoordinatorContextV1 {
            schema: ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1.to_owned(),
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: occurrence.profile_root.clone(),
            writer_epoch: occurrence.writer_epoch,
            coordinator_release_id: coordinator.coordinator_release_id.clone(),
            allocation_route_release_id: occurrence.allocation_route_release_id.clone(),
            authorized_buyback_route_release_id: occurrence
                .authorized_buyback_route_release_id
                .clone(),
            tokenomics_module_release_id: occurrence.tokenomics_module_release_id.clone(),
            command_occurrence_id: occurrence.command_occurrence_id.clone(),
            policy_root: occurrence.policy_root.clone(),
        },
        module,
        port,
        pre_state: fee_lane_state(allocation.pre_state.clone()),
        post_state: fee_lane_state(allocation.post_state.clone()),
        allocation,
        policy,
        receipt: ZDEXLaneReceiptEnvelopeV1 {
            receipt_kind: ReceiptKindV1::SUCCINCT,
            receipt_bytes: b"fee-tokenomics-lane-receipt".to_vec(),
        },
    }
}

struct ExactLaneVerifier {
    receipt: Vec<u8>,
    image: RootV1,
    journal: Vec<u8>,
}

impl ZDEXLaneSuccinctReceiptVerifierV1 for ExactLaneVerifier {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        if receipt_bytes != self.receipt
            || expected_image_id != &self.image
            || expected_journal_bytes != self.journal
        {
            return Err(AbiErrorV1::InvalidBinding("fee lane exact receipt binding"));
        }
        Ok(())
    }
}

#[test]
fn profile_selected_fee_leaf_and_coordinator_receipt_bind_one_complete_lane() {
    // Arrange
    let base = fixture();
    let lane = fee_lane_receipt_fixture(&base);
    let governed = bind_zdex_fee_allocation_shadow_profile_v1(
        &base.profile.profile_id,
        base.profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &base.profile,
            lanes: &base.lanes,
            coordinators: &base.coordinators,
            routes: &base.routes,
            policy_registry: &base.policies,
        },
    )
    .expect("governed fee profile");
    let composed = compose_zdex_tokenomics_fee_allocation_lane_v1(lane.lane_candidate())
        .expect("fee lane composition");
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(composed) = composed else {
        panic!("valid fee lane rejected")
    };
    let coordinator = base
        .coordinators
        .release_for(LaneIdV1::ZDEX_TOKENOMICS)
        .expect("tokenomics coordinator");
    let verifier = ExactLaneVerifier {
        receipt: lane.receipt.receipt_bytes.clone(),
        image: coordinator.guest_image_id.clone(),
        journal: canonical_bytes_v1(&composed.lane_journal).expect("lane journal bytes"),
    };
    assert_ne!(
        base.allocation_occurrence.pre_state_root,
        base.fee_state.state_root().unwrap()
    );

    // Act
    let verified = verify_zdex_tokenomics_fee_lane_receipt_v1(
        lane.receipt_candidate(&base.allocation_occurrence, &base.verified_buyback_budget),
        &governed,
        &verifier,
    )
    .expect("fee lane receipt must verify");

    // Assert
    assert_eq!(verified.profile_root(), &base.profile.profile_id);
    assert_eq!(
        verified.route_release_id(),
        &base.buyback_budget_occurrence.allocation_route_release_id
    );
    assert_eq!(verified.module_release_id(), &base.burn_release.release_id);
    assert_eq!(
        verified.coordinator_release_id(),
        &coordinator.coordinator_release_id
    );
    assert_eq!(
        verified.pre_lane_root(),
        &lane.pre_state.state_root().unwrap()
    );
    assert_eq!(
        verified.post_lane_root(),
        &lane.post_state.state_root().unwrap()
    );
    assert_eq!(
        verified.binding_root().unwrap(),
        RootV1::parse(
            "0x5a0edace975c58c0954cdaa2f73d72594b6d8e256e6ccc796daa75ba38cf6654",
            "fee lane verified binding root",
            false,
        )
        .unwrap()
    );
}

#[test]
fn unrelated_lane_root_substitution_requires_a_new_exact_receipt() {
    // Arrange
    let base = fixture();
    let mut shifted = fee_lane_receipt_fixture(&base);
    let original = compose_zdex_tokenomics_fee_allocation_lane_v1(shifted.lane_candidate())
        .expect("original fee lane composition");
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(original) = original else {
        panic!("valid original fee lane rejected")
    };
    let coordinator = base
        .coordinators
        .release_for(LaneIdV1::ZDEX_TOKENOMICS)
        .expect("tokenomics coordinator");
    let verifier = ExactLaneVerifier {
        receipt: shifted.receipt.receipt_bytes.clone(),
        image: coordinator.guest_image_id.clone(),
        journal: canonical_bytes_v1(&original.lane_journal).expect("original lane journal bytes"),
    };
    shifted.pre_state.staking_state_root = root(999);
    shifted.post_state.staking_state_root = root(999);
    let governed = governed_fee_profile(&base);

    // Act
    let result = verify_zdex_tokenomics_fee_lane_receipt_v1(
        shifted.receipt_candidate(&base.allocation_occurrence, &base.verified_buyback_budget),
        &governed,
        &verifier,
    );

    // Assert
    let error = result.expect_err("shifted lane state requires a new exact receipt");
    assert!(error.to_string().contains("exact receipt binding"));
}

#[test]
fn fee_lane_receipt_rejects_context_and_receipt_shape_before_verifier() {
    // Arrange
    let base = fixture();
    let mut wrong_context = fee_lane_receipt_fixture(&base);
    wrong_context.context.coordinator_release_id = root(999);
    let governed = bind_zdex_fee_allocation_shadow_profile_v1(
        &base.profile.profile_id,
        base.profile.authority_epoch,
        ZDEXFeeAllocationProfileRegistriesV1 {
            profile: &base.profile,
            lanes: &base.lanes,
            coordinators: &base.coordinators,
            routes: &base.routes,
            policy_registry: &base.policies,
        },
    )
    .expect("governed fee profile");
    let mut wrong_receipt = fee_lane_receipt_fixture(&base);
    wrong_receipt.receipt.receipt_kind = ReceiptKindV1::CONDITIONAL;

    // Act
    let context_result = verify_zdex_tokenomics_fee_lane_receipt_v1(
        wrong_context.receipt_candidate(&base.allocation_occurrence, &base.verified_buyback_budget),
        &governed,
        &PanickingVerifier,
    );
    let receipt_result = verify_zdex_tokenomics_fee_lane_receipt_v1(
        wrong_receipt.receipt_candidate(&base.allocation_occurrence, &base.verified_buyback_budget),
        &governed,
        &PanickingVerifier,
    );

    // Assert
    assert!(context_result.is_err());
    assert!(receipt_result.is_err());
}
