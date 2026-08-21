use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    compose_zdex_purchase_burn_route_v1, hash_global_v1, verify_zdex_amm_purchase_receipt_v1,
    verify_zdex_burn_receipt_v1, zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1, AbiErrorV1, AbiResultV1, AssetConservationRowV1,
    EconomicCommandOccurrenceV1, EconomicEffectKindV1, EconomicEffectRowV1, EvidenceStatusV1,
    GlobalEconomicEffectPlanV1, LaneIdV1, LaneModuleReleaseV1, LaneWriteV1, ReceiptKindV1,
    ReleaseStatusV1, RootV1, RouteReleaseV1, VerifiedZDEXAMMPurchaseV1, VerifiedZDEXBurnV1,
    ZDEXAMMPurchaseJournalV1, ZDEXBurnJournalV1, ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1, ZDEXLaneSuccinctReceiptVerifierV1, ZDEXPurchaseBurnRouteCandidateV1,
    ZDEXPurchaseBurnRouteRejectCodeV1, ZDEXPurchaseBurnRouteResultV1,
    ZDEXPurchaseReceiptCandidateV1, AMM_POOL_CUSTODY_DOMAIN_V1, GLOBAL_SETTLEMENT_ABI_V1,
    PROTOCOL_BURN_CUSTODY_DOMAIN_V1, PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
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

fn occurrence(route: &RouteReleaseV1) -> EconomicCommandOccurrenceV1 {
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zenodex-shadow".to_owned(),
        deployment_root: root(1),
        height: 7,
        tx_index: 2,
        op_index: 1,
        command_kind: PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned(),
        route_release_id: route.route_release_id.clone(),
        subject_id: "protocol-buyback-controller".to_owned(),
        grant_root: root(2),
        nonce: 9,
        profile_root: root(3),
        pre_state_root: root(4),
        consumed_object_ids: vec![],
    }
}

fn purchase_effects(journal: &ZDEXAMMPurchaseJournalV1) -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
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
    }
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
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: journal.pre_tokenomics_lane_root.clone(),
            post_root: journal.post_tokenomics_lane_root.clone(),
        }],
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
    spot_release: LaneModuleReleaseV1,
    burn_release: LaneModuleReleaseV1,
    route: RouteReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    purchase: ZDEXAMMPurchaseJournalV1,
    purchase_effects: GlobalEconomicEffectPlanV1,
    verified_purchase: VerifiedZDEXAMMPurchaseV1,
    burn: ZDEXBurnJournalV1,
    burn_effects: GlobalEconomicEffectPlanV1,
    verified_burn: VerifiedZDEXBurnV1,
}

fn fixture() -> Fixture {
    let spot_release = lane_release(LaneIdV1::SPOT_LIQUIDITY, 1);
    let burn_release = lane_release(LaneIdV1::ZDEX_TOKENOMICS, 2);
    let route = route_release(&spot_release, &burn_release);
    let occurrence = occurrence(&route);
    let occurrence_id = occurrence.occurrence_id().expect("occurrence id");
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
        quote_pool_bucket_id: "pool:quote".to_owned(),
        zdex_pool_bucket_id: "pool:zdex".to_owned(),
        burn_bucket_id: "protocol:zdex-burn-transient".to_owned(),
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
        zdex_asset_id: purchase.zdex_asset_id.clone(),
        burn_bucket_id: purchase.burn_bucket_id.clone(),
        burned_zdex_atoms: purchase.purchased_zdex_atoms,
        burn_bucket_pre_atoms: purchase.purchased_zdex_atoms,
        burn_bucket_post_atoms: 0,
        zdex_owned_pre_atoms: purchase.zdex_owned_atoms,
        zdex_owned_post_atoms: purchase.zdex_owned_atoms - purchase.purchased_zdex_atoms,
        zdex_supply_pre_atoms: purchase.zdex_supply_atoms,
        zdex_supply_post_atoms: purchase.zdex_supply_atoms - purchase.purchased_zdex_atoms,
        pre_tokenomics_lane_root: root(620),
        post_tokenomics_lane_root: root(621),
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
        spot_release,
        burn_release,
        route,
        occurrence,
        purchase,
        purchase_effects,
        verified_purchase,
        burn,
        burn_effects,
        verified_burn,
    }
}

fn compose(fixture: &Fixture) -> ZDEXPurchaseBurnRouteResultV1 {
    compose_zdex_purchase_burn_route_v1(ZDEXPurchaseBurnRouteCandidateV1 {
        route_release: &fixture.route,
        occurrence: &fixture.occurrence,
        purchase_journal: &fixture.purchase,
        purchase_effects: &fixture.purchase_effects,
        verified_purchase: &fixture.verified_purchase,
        burn_journal: &fixture.burn,
        burn_effects: &fixture.burn_effects,
        verified_burn: &fixture.verified_burn,
    })
    .expect("route composition must execute")
}

#[test]
fn rust_matches_python_golden_composition_root_and_effects() {
    let fixture = fixture();
    let ZDEXPurchaseBurnRouteResultV1::Accepted(accepted) = compose(&fixture) else {
        panic!("valid fixture must accept")
    };

    assert_eq!(
        accepted
            .composition_root()
            .expect("composition root")
            .as_str(),
        "0x9b78d0e13245ed8fe956680fb1141d1542522c6f73bef459b796a62fc15d00d4"
    );
    assert_eq!(accepted.effects.occurrence_consumptions.len(), 1);
    assert_eq!(accepted.effects.lane_writes.len(), 2);
    assert!(accepted
        .effects
        .rows
        .iter()
        .all(|row| row.principal != fixture.purchase.burn_bucket_id));
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
