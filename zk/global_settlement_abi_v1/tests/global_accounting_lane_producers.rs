//! Rust side of the registered-empty lane producers (wave A) against the shared fixture.
//!
//! The producer applied to the accepted fixture state's lane roots must yield exactly the
//! fragments the accepted certificate carries for EXTERNAL_CUSTODY and PROOF_REWARDS; an
//! enabled lane, a foreign root, and an unregistered lane reject with the closed codes.
//! Authority: NONE.

use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, produce_registered_empty_fragment_v1, registered_empty_lane_root_v1,
    GlobalEconomicStateV1, LaneIdV1, LaneProducerRejectCodeV1, LaneStateRootV1, RootV1,
};

fn fixture() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_accounting_allocation_certificate_v1_golden.json");
    serde_json::from_slice(&fs::read(path).expect("fixture readable")).expect("fixture JSON")
}

fn accepted_state_and_certificate() -> (GlobalEconomicStateV1, Value) {
    let fixture = fixture();
    let vector = &fixture["vectors"]["accepts_registered_empty_certificate_over_empty_state"];
    let state: GlobalEconomicStateV1 =
        serde_json::from_value(vector["state"].clone()).expect("state decodes");
    (state, vector["certificate"].clone())
}

fn lane_root(state: &GlobalEconomicStateV1, lane: LaneIdV1) -> LaneStateRootV1 {
    state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == lane)
        .expect("lane root present")
        .clone()
}

#[test]
fn producer_reproduces_the_accepted_fixture_fragments() {
    let (state, certificate) = accepted_state_and_certificate();
    for lane in [LaneIdV1::EXTERNAL_CUSTODY, LaneIdV1::PROOF_REWARDS] {
        let produced =
            produce_registered_empty_fragment_v1(&lane_root(&state, lane)).expect("produces");
        let bytes = canonical_bytes_v1(&produced).expect("fragment encodes");
        let produced_json: Value = serde_json::from_slice(&bytes).expect("JSON");
        let expected = certificate["ordered_lane_fragments"]
            .as_array()
            .expect("fragments")
            .iter()
            .find(|f| f["lane_id"] == Value::String(format!("{lane:?}")))
            .expect("fixture fragment")
            .clone();
        assert_eq!(produced_json, expected, "{lane:?}");
        let empty_root = registered_empty_lane_root_v1(lane)
            .expect("root")
            .expect("registered");
        assert_eq!(produced.lane_state_root, empty_root);
    }
    assert_eq!(
        registered_empty_lane_root_v1(LaneIdV1::ASSET_TRANSFER).expect("root"),
        None
    );
}

#[test]
fn producer_rejects_enabled_foreign_root_and_unregistered_lanes() {
    let (state, _) = accepted_state_and_certificate();
    let mut enabled = lane_root(&state, LaneIdV1::EXTERNAL_CUSTODY);
    enabled.enabled = true;
    let reject = produce_registered_empty_fragment_v1(&enabled).expect_err("enabled rejects");
    assert_eq!(reject.code, LaneProducerRejectCodeV1::LANE_ENABLED);
    let mut foreign = lane_root(&state, LaneIdV1::PROOF_REWARDS);
    foreign.state_root =
        RootV1::parse(format!("0x{:064x}", 4242u64), "foreign root", false).expect("root");
    let reject = produce_registered_empty_fragment_v1(&foreign).expect_err("foreign root rejects");
    assert_eq!(
        reject.code,
        LaneProducerRejectCodeV1::REGISTERED_EMPTY_ROOT_DRIFT
    );
    assert_eq!(reject.committed_lane_root, foreign.state_root);
    let reject = produce_registered_empty_fragment_v1(&lane_root(&state, LaneIdV1::ASSET_TRANSFER))
        .expect_err("unregistered rejects");
    assert_eq!(
        reject.code,
        LaneProducerRejectCodeV1::LANE_NOT_REGISTERED_EMPTY
    );
    assert_eq!(LaneProducerRejectCodeV1::ALL.len(), 3);
    assert_eq!(
        LaneProducerRejectCodeV1::LANE_ENABLED.message(),
        "registered-empty lane is enabled"
    );
}

// --- wave B: the receipt-backed ASSET_TRANSFER producer ---------------------

use zenodex_global_settlement_abi_v1::{
    produce_asset_transfer_fragment_v1, transition_asset_transfer_lane_module_v1, AssetSupplyV1,
    AssetTransferCommandV1, AssetTransferContextV1, AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1, AssetTransferLaneModuleResultV1, AssetTransferPolicyV1,
    AssetTransferStateV1, ClaimantEntitlementRowV1, EconomicAmountV1, LaneAllocationFragmentV1,
    LaneProducerKindV1, ReceiptBackedProducerRejectCodeV1, ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn wave_b_root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn wave_b_accepted(custody: Vec<EconomicAmountV1>) -> AssetTransferLaneModuleAcceptedV1 {
    let custody_total: u128 = custody.iter().map(|row| row.amount_atoms).sum();
    let input = AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: "zeno-asset-test".to_owned(),
            deployment_root: wave_b_root(1),
            profile_root: wave_b_root(2),
            writer_epoch: 7,
            module_release_id: wave_b_root(3),
            command_occurrence_id: wave_b_root(4),
            subject_id: "alice".to_owned(),
            grant_root: wave_b_root(5),
        },
        pre_state: AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: wave_b_root(3),
            policies: vec![AssetTransferPolicyV1 {
                asset: "USD".to_owned(),
                fee_owner: "treasury".to_owned(),
                transfer_fee_atoms: 2,
                enabled: true,
            }],
            balances: vec![
                EconomicAmountV1 {
                    owner: "alice".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 100,
                },
                EconomicAmountV1 {
                    owner: "bob".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 10,
                },
                EconomicAmountV1 {
                    owner: "treasury".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 5,
                },
            ],
            supplies: vec![AssetSupplyV1 {
                asset: "USD".to_owned(),
                amount_atoms: 115 + custody_total,
            }],
        },
        command: AssetTransferCommandV1 {
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            asset: "USD".to_owned(),
            sender: "alice".to_owned(),
            recipient: "bob".to_owned(),
            amount_atoms: 30,
            max_fee_atoms: 2,
        },
        asset_policy_registry_root: wave_b_root(11),
        fee_policy_registry_root: wave_b_root(12),
        custody,
    };
    let result = transition_asset_transfer_lane_module_v1(&input)
        .expect("typed lane module transition must evaluate");
    let AssetTransferLaneModuleResultV1::Accepted(accepted) = result else {
        panic!("valid lane module transition must accept")
    };
    *accepted
}

fn wave_b_setup() -> (
    AssetTransferLaneModuleAcceptedV1,
    LaneStateRootV1,
    LaneAllocationFragmentV1,
    Vec<ClaimantEntitlementRowV1>,
) {
    let accepted = wave_b_accepted(vec![EconomicAmountV1 {
        owner: "pool-a".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "spot-pool".to_owned(),
        amount_atoms: 5,
    }]);
    let journal = &accepted.module_journal;
    let lane_root = LaneStateRootV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        module_release_id: wave_b_root(3),
        enabled: true,
        state_root: journal.post_lane_root.clone(),
    };
    let prior = LaneAllocationFragmentV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        module_release_id: wave_b_root(3),
        enabled: true,
        lane_state_root: journal.pre_lane_root.clone(),
        producer_kind: LaneProducerKindV1::RECEIPT_BACKED,
        binding_root: journal.pre_lane_root.clone(),
        controlled_locations: Vec::new(),
        claimant_entitlements: Vec::new(),
        unencumbered_reserves: Vec::new(),
        pending_external_obligations: Vec::new(),
        terminal_bindings: Vec::new(),
    };
    let entitlements = vec![ClaimantEntitlementRowV1 {
        asset: "USD".to_owned(),
        claimant: "alice".to_owned(),
        control_domain: "spot-pool".to_owned(),
        amount_atoms: 5,
    }];
    (accepted, lane_root, prior, entitlements)
}

#[test]
fn receipt_backed_producer_accepts_and_binds_the_receipt_root() {
    let (accepted, lane_root, prior, entitlements) = wave_b_setup();
    let fragment = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &entitlements)
        .expect("bound transition must produce");
    assert_eq!(fragment.lane_id, LaneIdV1::ASSET_TRANSFER);
    assert!(fragment.enabled);
    assert_eq!(fragment.producer_kind, LaneProducerKindV1::RECEIPT_BACKED);
    assert_eq!(
        fragment.lane_state_root,
        accepted.module_journal.post_lane_root
    );
    assert_eq!(fragment.binding_root, accepted.module_journal.receipt_root);
    assert_eq!(fragment.controlled_locations.len(), 1);
    assert_eq!(
        fragment.controlled_locations[0].controlling_principal,
        "pool-a"
    );
    assert_eq!(fragment.claimant_entitlements, entitlements);
    assert!(fragment.terminal_bindings.is_empty());
}

#[test]
fn receipt_backed_producer_rejects_binding_drifts_in_precedence_order() {
    let (accepted, lane_root, prior, entitlements) = wave_b_setup();
    let disabled = LaneStateRootV1 {
        enabled: false,
        ..lane_root.clone()
    };
    let reject = produce_asset_transfer_fragment_v1(&accepted, &disabled, &prior, &entitlements)
        .expect_err("disabled lane rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::LANE_DISABLED
    );
    let forged = LaneStateRootV1 {
        state_root: wave_b_root(999),
        ..lane_root.clone()
    };
    let reject = produce_asset_transfer_fragment_v1(&accepted, &forged, &prior, &entitlements)
        .expect_err("forged post root rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::JOURNAL_ROOT_DRIFT
    );
    let stale = LaneAllocationFragmentV1 {
        lane_state_root: wave_b_root(888),
        binding_root: wave_b_root(888),
        ..prior.clone()
    };
    let reject = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &stale, &entitlements)
        .expect_err("stale prior rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL
    );
    let short = vec![ClaimantEntitlementRowV1 {
        asset: "USD".to_owned(),
        claimant: "alice".to_owned(),
        control_domain: "spot-pool".to_owned(),
        amount_atoms: 4,
    }];
    let reject = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &short)
        .expect_err("uncovered atoms reject");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_COVERAGE_DRIFT
    );
    assert_eq!(reject.detail, "coverage");
}

#[test]
fn receipt_backed_producer_rejects_entitlement_fold_overflow() {
    let (accepted, lane_root, prior, _) = wave_b_setup();
    let overflowing = vec![
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "alice".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: u128::MAX,
        },
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "bob".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: u128::MAX,
        },
    ];
    let reject = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &overflowing)
        .expect_err("entitlement fold overflows");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::CONTROLLED_FOLD_OVERFLOW
    );
    assert_eq!(reject.detail, "entitlements");
}

#[test]
fn receipt_backed_producer_rejects_lane_release_prior_and_terminal_drifts() {
    let (accepted, lane_root, prior, entitlements) = wave_b_setup();
    // JOURNAL_LANE_DRIFT: committed root names a foreign lane.
    let foreign = LaneStateRootV1 {
        lane_id: LaneIdV1::SPOT_LIQUIDITY,
        ..lane_root.clone()
    };
    let reject = produce_asset_transfer_fragment_v1(&accepted, &foreign, &prior, &entitlements)
        .expect_err("foreign lane rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::JOURNAL_LANE_DRIFT
    );
    // MODULE_RELEASE_DRIFT.
    let release = LaneStateRootV1 {
        module_release_id: wave_b_root(99),
        ..lane_root.clone()
    };
    let reject = produce_asset_transfer_fragment_v1(&accepted, &release, &prior, &entitlements)
        .expect_err("release drift rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::MODULE_RELEASE_DRIFT
    );
    // STALE_JOURNAL via a foreign-lane prior (Opus P17 P2-1 exploit shape).
    let foreign_prior = LaneAllocationFragmentV1 {
        lane_id: LaneIdV1::EXTERNAL_CUSTODY,
        producer_kind: LaneProducerKindV1::REGISTERED_EMPTY_DISABLED,
        enabled: false,
        ..prior.clone()
    };
    let reject =
        produce_asset_transfer_fragment_v1(&accepted, &lane_root, &foreign_prior, &entitlements)
            .expect_err("foreign prior rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL
    );
    assert_eq!(reject.detail, "prior lane");
    // STALE_JOURNAL via a prior at a different release.
    let stale_release_prior = LaneAllocationFragmentV1 {
        module_release_id: wave_b_root(77),
        ..prior.clone()
    };
    let reject = produce_asset_transfer_fragment_v1(
        &accepted,
        &lane_root,
        &stale_release_prior,
        &entitlements,
    )
    .expect_err("prior release drift rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL
    );
    assert_eq!(reject.detail, "prior release");
    // ACCEPTED_INVALID (Opus P18 P2-C): mutating only the journal breaks accepted.validate();
    // this pins exactly that path, and only that path -- the reachable TERMINAL_ROOT_NOT_EMPTY
    // check is pinned by the unit test in the producers module, which rebinds the port root and
    // recomputes the receipt root so no earlier gate can fire.
    let mut mutated = accepted.clone();
    mutated.module_journal.terminal_obligations_root = wave_b_root(7);
    let reject = produce_asset_transfer_fragment_v1(&mutated, &lane_root, &prior, &entitlements)
        .expect_err("inconsistent accepted rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::ACCEPTED_INVALID
    );
    assert_eq!(reject.detail, "accepted validation");
    // Prior-chain residual (Opus P18 P3-b): kind and enabled flag are now checked.
    let wrong_kind_prior = LaneAllocationFragmentV1 {
        producer_kind: LaneProducerKindV1::NO_PRODUCER,
        ..prior.clone()
    };
    let reject =
        produce_asset_transfer_fragment_v1(&accepted, &lane_root, &wrong_kind_prior, &entitlements)
            .expect_err("non-receipt-backed prior rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL
    );
    assert_eq!(reject.detail, "prior kind");
    let disabled_prior = LaneAllocationFragmentV1 {
        enabled: false,
        ..prior.clone()
    };
    let reject =
        produce_asset_transfer_fragment_v1(&accepted, &lane_root, &disabled_prior, &entitlements)
            .expect_err("disabled prior rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL
    );
    assert_eq!(reject.detail, "prior disabled");
    // Row ceiling (Opus P18 P2-D): a canonical table above the ceiling gets a closed reject.
    let too_many: Vec<ClaimantEntitlementRowV1> = (0..5000)
        .map(|i| ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: format!("c{i:06}"),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: 1,
        })
        .collect();
    let reject = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &too_many)
        .expect_err("over-ceiling entitlements reject");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL
    );
    assert_eq!(reject.detail, "row ceiling");
}

#[test]
fn receipt_backed_producer_rejects_non_canonical_entitlements() {
    let (accepted, lane_root, prior, _) = wave_b_setup();
    let unordered = vec![
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "zed".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: 2,
        },
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "alice".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: 3,
        },
    ];
    let reject = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &unordered)
        .expect_err("unordered entitlements reject");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL
    );
    assert_eq!(reject.detail, "entitlement ordering");
    let zero = vec![
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "alice".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: 5,
        },
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "zzz".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: 0,
        },
    ];
    let reject = produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &zero)
        .expect_err("zero-amount entitlement rejects");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL
    );
    assert_eq!(reject.detail, "zero amount");
    // Precedence pair (Opus P17 P3-3): disabled + overflow -> LANE_DISABLED.
    let disabled = LaneStateRootV1 {
        enabled: false,
        ..lane_root.clone()
    };
    let overflowing = vec![
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "alice".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: u128::MAX,
        },
        ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "bob".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: u128::MAX,
        },
    ];
    let reject = produce_asset_transfer_fragment_v1(&accepted, &disabled, &prior, &overflowing)
        .expect_err("disabled wins over overflow");
    assert_eq!(
        reject.code,
        ReceiptBackedProducerRejectCodeV1::LANE_DISABLED
    );
}
