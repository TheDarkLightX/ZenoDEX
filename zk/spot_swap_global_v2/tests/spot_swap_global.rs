//! Joint Spot/asset/global transition: complete projection, independent
//! accounting, mixed histories, precedence and exact no-op rejections.
//!
//! Carried from `tests/core/test_spot_swap_global_v2.py`,
//! `test_spot_swap_plan_v2.py` and `test_spot_swap_state_v2.py`. Every fixture
//! is built from typed values. No fixture is a receipt, no result grants
//! publication authority, and independent Python/Rust parity is root's lane.
//!
//! Nonclaims: these tests do not establish parity by themselves, do not cover
//! the 4096-row asset balance capacity end to end, and do not exercise the
//! JSON-lines transport.

use std::collections::BTreeMap;

use zenodex_global_settlement_abi_v2::{
    asset_transfer_policy_root_v2, derive_asset_lane_custody_global_post_v2,
    transition_asset_lane_custody_v2, AbiErrorV2, AssetClassV2, AssetConservationRowV2,
    AssetLaneCommandV2, AssetLaneContextV2, AssetLaneCustodyResultV2, AssetLaneCustodyStateV2,
    AssetOriginKindV2, AssetOriginRecordV2, AssetOriginRegistrationPolicyV2,
    AssetOriginRegistryStateV2, AssetSupplyV2, AssetTransferCommandV2, AssetTransferPolicyV2,
    AssetTransferStateV2, EconomicAmountV2, EconomicCommandOccurrenceV2, EconomicEffectKindV2,
    EconomicEffectRowV2, FeeConservationRowV2, GlobalEconomicStateV2, LaneIdV2, LaneStateRootV2,
    RootV2, TerminalObligationStatusV2, TerminalObligationV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ALL_LANE_IDS_V2, ASSET_ATOM_DECIMALS_V2, ASSET_LANE_CUSTODY_STATE_SCHEMA_V2,
    ASSET_ORIGIN_REGISTRY_SCHEMA_V2, ASSET_TRANSFER_COMMAND_KIND_V2,
    ASSET_TRANSFER_MODULE_SCHEMA_V2, GLOBAL_SETTLEMENT_ABI_V2,
};
use zenodex_spot_swap_global_v2::{
    plan_spot_swap_v2, transition_spot_swap_global_v2, PoolStatusV2, SpotIntentNonceV2,
    SpotLPPositionV2, SpotPoolSnapshotV2, SpotSwapContextV2, SpotSwapGlobalAcceptedV2,
    SpotSwapGlobalRejectCodeV2, SpotSwapGlobalRejectKindV2, SpotSwapGlobalResultV2,
    SpotSwapInputErrorV2, SpotSwapIntentPartsV2, SpotSwapIntentV2, SpotSwapKindV2,
    SpotSwapPlanResultV2, SpotSwapRejectCodeV2, SpotSwapStateV2, SwapIntentFieldValueV2,
    SwapIntentIntegerV2, CURVE_TAG_CPMM_V2, LP_LOCK_PUBKEY_V2, MIN_LP_LOCK_V2,
    SPOT_POOL_CUSTODY_DOMAIN_V2, SPOT_SWAP_STATE_SCHEMA_V2, SWAP_INTENT_MODULE_V2,
    SWAP_INTENT_VERSION_V2,
};

const CHAIN_ID: &str = "spot-test";
const ESCROW_OWNER: &str = "other";
const ESCROW_DOMAIN: &str = "escrow";
const TIMESTAMP: u64 = 100;
const RESERVE_MAX: u64 = 3_000_000_000;

fn owner(byte: &str) -> String {
    format!("0x{}", byte.repeat(48))
}

fn alice() -> String {
    owner("aa")
}

fn bob() -> String {
    owner("bb")
}

fn carol() -> String {
    owner("cc")
}

fn mallory() -> String {
    owner("dd")
}

fn root(value: u64) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "test root", false).expect("canonical root")
}

fn origin_root(asset: &str) -> RootV2 {
    root(1_000 + u64::from(asset.as_bytes()[0]))
}

fn amount(owner: &str, asset: &str, domain: &str, atoms: u128) -> EconomicAmountV2 {
    EconomicAmountV2 {
        owner: owner.to_owned(),
        asset: asset.to_owned(),
        custody_domain: domain.to_owned(),
        amount_atoms: atoms,
    }
}

fn sort_amounts(rows: &mut [EconomicAmountV2]) {
    rows.sort_by(|left, right| {
        (
            left.asset.as_str(),
            left.owner.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                right.asset.as_str(),
                right.owner.as_str(),
                right.custody_domain.as_str(),
            ))
    });
}

fn policy(asset: &str) -> AssetTransferPolicyV2 {
    AssetTransferPolicyV2 {
        asset: asset.to_owned(),
        fee_owner: "treasury".to_owned(),
        transfer_fee_atoms: 0,
        enabled: true,
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(origin_root(asset)),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
    }
}

fn registry(
    policies: &[AssetTransferPolicyV2],
    drift_asset: Option<&str>,
) -> AssetOriginRegistryStateV2 {
    let assets = policies
        .iter()
        .map(|policy| {
            let transfer_policy_root = if drift_asset == Some(policy.asset.as_str()) {
                root(999)
            } else {
                asset_transfer_policy_root_v2(policy).expect("policy root")
            };
            AssetOriginRecordV2 {
                asset: policy.asset.clone(),
                origin_kind: AssetOriginKindV2::TAU_ORIGINATED,
                origin_root: policy.asset_origin_root.clone().expect("origin"),
                transfer_policy_root,
                issue_policy_root: RootV2::zero(),
                decimals: u64::from(ASSET_ATOM_DECIMALS_V2),
                asset_class: policy.asset_class,
            }
        })
        .collect();
    AssetOriginRegistryStateV2 {
        schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
        module_release_id: root(10),
        policy: AssetOriginRegistrationPolicyV2 {
            authority_subject: "governance".to_owned(),
            authority_grant_root: root(31),
            allow_native: false,
            allow_tau_originated: true,
        },
        assets,
    }
}

fn pool(fee_bps: u64, reserve0: u64, reserve1: u64) -> SpotPoolSnapshotV2 {
    let mut pool = SpotPoolSnapshotV2 {
        pool_id: String::new(),
        asset0: "A".to_owned(),
        asset1: "B".to_owned(),
        reserve0,
        reserve1,
        fee_bps,
        lp_supply: 14_142,
        status: PoolStatusV2::ACTIVE,
        created_at: 7,
        curve_tag: CURVE_TAG_CPMM_V2.to_owned(),
        curve_params: String::new(),
    };
    pool.pool_id = pool.canonical_pool_id();
    pool
}

fn lp_rows() -> Vec<SpotLPPositionV2> {
    vec![
        SpotLPPositionV2 {
            owner: LP_LOCK_PUBKEY_V2.to_owned(),
            shares: MIN_LP_LOCK_V2,
            last_mint_timestamp: None,
            last_remove_timestamp: None,
            churn_tier: 0,
            last_churn_update_timestamp: None,
        },
        SpotLPPositionV2 {
            owner: bob(),
            shares: 13_142,
            last_mint_timestamp: Some(7),
            last_remove_timestamp: None,
            churn_tier: 2,
            last_churn_update_timestamp: Some(7),
        },
        SpotLPPositionV2 {
            owner: carol(),
            shares: 0,
            last_mint_timestamp: Some(2),
            last_remove_timestamp: Some(6),
            churn_tier: 1,
            last_churn_update_timestamp: Some(6),
        },
    ]
}

fn spot_state(
    pool: SpotPoolSnapshotV2,
    lp_positions: Vec<SpotLPPositionV2>,
    intent_nonces: Vec<SpotIntentNonceV2>,
) -> SpotSwapStateV2 {
    SpotSwapStateV2 {
        schema: SPOT_SWAP_STATE_SCHEMA_V2.to_owned(),
        module_release_id: root(20),
        pool,
        lp_positions,
        intent_nonces,
    }
}

fn asset_frame(
    spot: &SpotSwapStateV2,
    policies: Vec<AssetTransferPolicyV2>,
    registry: AssetOriginRegistryStateV2,
    alice_a: u128,
    alice_b: u128,
) -> AssetLaneCustodyStateV2 {
    let mut balances = Vec::new();
    if alice_a > 0 {
        balances.push(amount(&alice(), "A", ACCOUNT_CUSTODY_DOMAIN_V2, alice_a));
    }
    if alice_b > 0 {
        balances.push(amount(&alice(), "B", ACCOUNT_CUSTODY_DOMAIN_V2, alice_b));
    }
    // An unrelated funded custody row must survive swaps and ordinary transfers.
    let mut custody = vec![amount(ESCROW_OWNER, "A", ESCROW_DOMAIN, 20)];
    custody.extend(spot.pool_holdings());
    sort_amounts(&mut custody);
    let supplies = vec![
        AssetSupplyV2 {
            asset: "A".to_owned(),
            amount_atoms: u128::from(spot.pool.reserve0) + alice_a + 20,
        },
        AssetSupplyV2 {
            asset: "B".to_owned(),
            amount_atoms: u128::from(spot.pool.reserve1) + alice_b,
        },
    ];
    AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state: AssetTransferStateV2 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
            module_release_id: root(10),
            policies,
            balances,
            supplies,
        },
        origin_registry: registry,
        managed_policies: Vec::new(),
        custody,
    }
}

fn global_state(assets: &AssetLaneCustodyStateV2, spot: &SpotSwapStateV2) -> GlobalEconomicStateV2 {
    let asset_root = assets.state_root().expect("asset root");
    let spot_root = spot.state_root().expect("spot root");
    let lane_roots = ALL_LANE_IDS_V2
        .iter()
        .copied()
        .enumerate()
        .map(|(index, lane_id)| match lane_id {
            LaneIdV2::ASSET_TRANSFER => LaneStateRootV2 {
                lane_id,
                module_release_id: root(10),
                enabled: true,
                state_root: asset_root.clone(),
            },
            LaneIdV2::SPOT_LIQUIDITY => LaneStateRootV2 {
                lane_id,
                module_release_id: root(20),
                enabled: true,
                state_root: spot_root.clone(),
            },
            _ => LaneStateRootV2 {
                lane_id,
                module_release_id: root(100 + u64::try_from(index).expect("small index")),
                enabled: false,
                state_root: RootV2::zero(),
            },
        })
        .collect();
    GlobalEconomicStateV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: CHAIN_ID.to_owned(),
        deployment_root: root(40),
        writer_epoch: 1,
        height: 0,
        profile_root: root(41),
        lane_roots,
        balances: assets.balances().to_vec(),
        supplies: assets
            .supplies()
            .iter()
            .filter(|row| row.amount_atoms > 0)
            .cloned()
            .collect(),
        custody: assets.custody.clone(),
        liabilities: Vec::new(),
        reserves: Vec::new(),
        oracle_occurrences: Vec::new(),
        replay_state: Vec::new(),
        terminal_obligations: Vec::new(),
        history_root: RootV2::zero(),
        outbox: Vec::new(),
    }
}

#[derive(Clone)]
struct World {
    assets: AssetLaneCustodyStateV2,
    spot: SpotSwapStateV2,
    state: GlobalEconomicStateV2,
}

impl World {
    fn roots(&self) -> (RootV2, RootV2, RootV2) {
        (
            self.assets.state_root().expect("assets root"),
            self.spot.state_root().expect("spot root"),
            self.state.state_root().expect("state root"),
        )
    }

    fn with_spot(mut self, spot: SpotSwapStateV2) -> Self {
        let spot_root = spot.state_root().expect("spot root");
        set_lane(&mut self.state, LaneIdV2::SPOT_LIQUIDITY, |row| {
            row.state_root = spot_root.clone();
        });
        self.spot = spot;
        self
    }

    fn with_assets(mut self, assets: AssetLaneCustodyStateV2) -> Self {
        let asset_root = assets.state_root().expect("asset root");
        set_lane(&mut self.state, LaneIdV2::ASSET_TRANSFER, |row| {
            row.state_root = asset_root.clone();
        });
        self.assets = assets;
        self
    }
}

fn set_lane(
    state: &mut GlobalEconomicStateV2,
    lane: LaneIdV2,
    change: impl Fn(&mut LaneStateRootV2),
) {
    for row in &mut state.lane_roots {
        if row.lane_id == lane {
            change(row);
        }
    }
}

fn lane_root(state: &GlobalEconomicStateV2, lane: LaneIdV2) -> RootV2 {
    state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == lane)
        .expect("lane row")
        .state_root
        .clone()
}

fn build_world_from(spot: SpotSwapStateV2, alice_a: u128, alice_b: u128) -> World {
    let policies = vec![policy("A"), policy("B")];
    let registry = registry(&policies, None);
    let assets = asset_frame(&spot, policies, registry, alice_a, alice_b);
    let state = global_state(&assets, &spot);
    World {
        assets,
        spot,
        state,
    }
}

fn build_world(fee_bps: u64, reserve0: u64, reserve1: u64, alice_a: u128, alice_b: u128) -> World {
    build_world_from(
        spot_state(pool(fee_bps, reserve0, reserve1), lp_rows(), Vec::new()),
        alice_a,
        alice_b,
    )
}

fn world(fee_bps: u64) -> World {
    build_world(fee_bps, 10_000, 20_000, 1_000, 1_000)
}

fn integer(value: i128) -> SwapIntentFieldValueV2 {
    SwapIntentFieldValueV2::Integer(SwapIntentIntegerV2::from_i128(value))
}

fn text(value: &str) -> SwapIntentFieldValueV2 {
    SwapIntentFieldValueV2::Text(value.to_owned())
}

fn intent_parts_for(
    pool_id: &str,
    exact_out: bool,
    reverse: bool,
    overrides: &[(&str, SwapIntentFieldValueV2)],
) -> SpotSwapIntentPartsV2 {
    let mut fields = BTreeMap::new();
    fields.insert("pool_id".to_owned(), text(pool_id));
    fields.insert("asset_in".to_owned(), text(if reverse { "B" } else { "A" }));
    fields.insert(
        "asset_out".to_owned(),
        text(if reverse { "A" } else { "B" }),
    );
    fields.insert("nonce".to_owned(), integer(1));
    if exact_out {
        fields.insert("amount_out".to_owned(), integer(7));
        fields.insert("max_amount_in".to_owned(), integer(10));
    } else {
        fields.insert("amount_in".to_owned(), integer(10));
        fields.insert("min_amount_out".to_owned(), integer(7));
    }
    for (key, value) in overrides {
        fields.insert((*key).to_owned(), value.clone());
    }
    SpotSwapIntentPartsV2 {
        module: SWAP_INTENT_MODULE_V2.to_owned(),
        version: SWAP_INTENT_VERSION_V2.to_owned(),
        kind: if exact_out {
            SpotSwapKindV2::SWAP_EXACT_OUT
        } else {
            SpotSwapKindV2::SWAP_EXACT_IN
        },
        intent_id: format!("0x{}", "11".repeat(32)),
        sender_pubkey: alice(),
        deadline: TIMESTAMP,
        salt: None,
        fields,
    }
}

fn intent_parts(
    spot: &SpotSwapStateV2,
    exact_out: bool,
    reverse: bool,
    overrides: &[(&str, SwapIntentFieldValueV2)],
) -> SpotSwapIntentPartsV2 {
    intent_parts_for(&spot.pool.pool_id, exact_out, reverse, overrides)
}

fn intent_for(
    pool_id: &str,
    exact_out: bool,
    reverse: bool,
    overrides: &[(&str, SwapIntentFieldValueV2)],
) -> SpotSwapIntentV2 {
    SpotSwapIntentV2::new(intent_parts_for(pool_id, exact_out, reverse, overrides))
        .expect("valid swap intent")
}

fn intent(
    spot: &SpotSwapStateV2,
    exact_out: bool,
    reverse: bool,
    overrides: &[(&str, SwapIntentFieldValueV2)],
) -> SpotSwapIntentV2 {
    intent_for(&spot.pool.pool_id, exact_out, reverse, overrides)
}

fn occurrence(
    state: &GlobalEconomicStateV2,
    intent: &SpotSwapIntentV2,
    outer_nonce: u64,
) -> EconomicCommandOccurrenceV2 {
    EconomicCommandOccurrenceV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        height: state.height.saturating_add(1),
        tx_index: 0,
        op_index: 0,
        command_kind: intent.command_kind().to_owned(),
        command_body_hash: intent.command_body_hash().expect("command body hash"),
        route_release_id: root(50),
        subject_id: intent.sender_pubkey().to_owned(),
        grant_root: root(51),
        nonce: outer_nonce,
        profile_root: state.profile_root.clone(),
        pre_state_root: state.state_root().expect("state root"),
        consumed_object_ids: Vec::new(),
    }
}

fn run(
    world: &World,
    intent: &SpotSwapIntentV2,
    occurrence: &EconomicCommandOccurrenceV2,
    timestamp: u64,
) -> SpotSwapGlobalResultV2 {
    transition_spot_swap_global_v2(
        &world.assets,
        &world.spot,
        &world.state,
        intent,
        occurrence,
        timestamp,
    )
    .expect("typed transition")
}

fn accept(
    world: &World,
    intent: &SpotSwapIntentV2,
    outer_nonce: u64,
) -> (SpotSwapGlobalAcceptedV2, World) {
    let before = world.roots();
    let occurrence = occurrence(&world.state, intent, outer_nonce);
    let result = run(world, intent, &occurrence, TIMESTAMP);
    assert_eq!(world.roots(), before);
    let accepted = match result {
        SpotSwapGlobalResultV2::Accepted(accepted) => *accepted,
        SpotSwapGlobalResultV2::Rejected(rejected) => {
            panic!("expected acceptance, got {:?}", rejected.code)
        }
    };
    assert_eq!(accepted.production_authority(), "NONE");
    assert_eq!(accepted.post_state().supplies, world.state.supplies);
    assert_eq!(accepted.post_spot().lp_positions, world.spot.lp_positions);
    assert_eq!(accepted.post_state().liabilities, world.state.liabilities);
    assert_eq!(
        accepted.post_state().terminal_obligations,
        world.state.terminal_obligations
    );
    assert_eq!(accepted.post_state().outbox, world.state.outbox);
    let escrow = accepted
        .post_state()
        .custody
        .iter()
        .filter(|row| row.custody_domain == ESCROW_DOMAIN)
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(escrow, vec![amount(ESCROW_OWNER, "A", ESCROW_DOMAIN, 20)]);
    let next = World {
        assets: accepted.post_assets().clone(),
        spot: accepted.post_spot().clone(),
        state: accepted.post_state().clone(),
    };
    (accepted, next)
}

fn assert_rejected(
    world: &World,
    intent: &SpotSwapIntentV2,
    occurrence: &EconomicCommandOccurrenceV2,
    timestamp: u64,
    expected: SpotSwapGlobalRejectCodeV2,
) {
    let before = world.roots();
    let state_root = world.state.state_root().expect("state root");
    for _ in 0..2 {
        let result = run(world, intent, occurrence, timestamp);
        let SpotSwapGlobalResultV2::Rejected(rejected) = result else {
            panic!("expected rejection {expected:?}, got acceptance")
        };
        assert_eq!(rejected.code, expected);
        assert_eq!(rejected.pre_state_root, state_root);
        assert_eq!(rejected.post_state_root(), &state_root);
        assert!(rejected.effects().is_empty());
    }
    assert_eq!(world.roots(), before);
}

fn reject_swap(code: SpotSwapRejectCodeV2) -> SpotSwapGlobalRejectCodeV2 {
    SpotSwapGlobalRejectCodeV2::Swap(code)
}

fn reject_global(kind: SpotSwapGlobalRejectKindV2) -> SpotSwapGlobalRejectCodeV2 {
    SpotSwapGlobalRejectCodeV2::Global(kind)
}

fn effect_row(
    kind: EconomicEffectKindV2,
    principal: &str,
    asset: &str,
    domain: &str,
    delta_atoms: i128,
) -> EconomicEffectRowV2 {
    EconomicEffectRowV2 {
        kind,
        principal: principal.to_owned(),
        asset: asset.to_owned(),
        custody_domain: domain.to_owned(),
        delta_atoms,
    }
}

fn conservation(asset: &str, supply: u128) -> AssetConservationRowV2 {
    AssetConservationRowV2 {
        asset: asset.to_owned(),
        owned_and_custodied_pre_atoms: supply,
        owned_and_custodied_post_atoms: supply,
        supply_pre_atoms: supply,
        supply_post_atoms: supply,
        authorized_issue_atoms: 0,
        authorized_burn_atoms: 0,
    }
}

fn transfer(world: &World, outer_nonce: u64) -> World {
    let command = AssetTransferCommandV2 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V2.to_owned(),
        asset: "A".to_owned(),
        sender: alice(),
        recipient: bob(),
        amount_atoms: 3,
        max_fee_atoms: 0,
        asset_origin_root: Some(origin_root("A")),
    };
    let occurrence = EconomicCommandOccurrenceV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: world.state.chain_id.clone(),
        deployment_root: world.state.deployment_root.clone(),
        height: world.state.height.saturating_add(1),
        tx_index: 0,
        op_index: 0,
        command_kind: command.command_kind.clone(),
        command_body_hash: command.command_body_hash().expect("transfer body"),
        route_release_id: root(52),
        subject_id: alice(),
        grant_root: root(51),
        nonce: outer_nonce,
        profile_root: world.state.profile_root.clone(),
        pre_state_root: world.state.state_root().expect("state root"),
        consumed_object_ids: Vec::new(),
    };
    let context = AssetLaneContextV2 {
        writer_epoch: world.state.writer_epoch,
        module_release_id: world.assets.module_release_id().clone(),
        global_pre_state_root: world.state.state_root().expect("state root"),
        occurrence: Some(occurrence.clone()),
    };
    let result = transition_asset_lane_custody_v2(
        &context,
        &world.assets,
        &AssetLaneCommandV2::Transfer(command),
    )
    .expect("typed lane transition");
    let accepted = match result {
        AssetLaneCustodyResultV2::Accepted(accepted) => accepted,
        AssetLaneCustodyResultV2::Rejected(rejected) => {
            panic!("transfer must accept, got {:?}", rejected.code())
        }
    };
    let post_state = derive_asset_lane_custody_global_post_v2(
        &world.assets,
        &accepted,
        &world.state,
        &occurrence,
    )
    .expect("global post state");
    World {
        assets: accepted.post_state().clone(),
        spot: world.spot.clone(),
        state: post_state,
    }
}

// The independent fee oracle keeps the Python `(x * fee + 9999) // 10000` form
// verbatim so it stays a separate formulation from the crate's `ceil_div`.
#[allow(clippy::manual_div_ceil)]
#[test]
fn given_actual_intent_when_swapped_then_wallet_pool_shares_and_global_state_reconcile() {
    for fee_bps in [0_u64, 30] {
        for exact_out in [false, true] {
            for reverse in [false, true] {
                let world = world(fee_bps);
                let bound = if exact_out {
                    ("max_amount_in", integer(20))
                } else {
                    ("min_amount_out", integer(1))
                };
                let command = intent(
                    &world.spot,
                    exact_out,
                    reverse,
                    &[("recipient", text(&bob())), bound],
                );
                let (accepted, _) = accept(&world, &command, 1);
                let post = accepted.post_state();
                let movements = accepted
                    .effects()
                    .rows
                    .iter()
                    .filter(|row| row.kind == EconomicEffectKindV2::ACCOUNT_MOVEMENT)
                    .collect::<Vec<_>>();
                let debit = movements
                    .iter()
                    .find(|row| row.delta_atoms < 0)
                    .map(|row| row.delta_atoms.unsigned_abs())
                    .expect("debit row");
                let credit = movements
                    .iter()
                    .find(|row| row.delta_atoms > 0)
                    .map(|row| u128::try_from(row.delta_atoms).expect("positive"))
                    .expect("credit row");
                let (asset_in, asset_out) = if reverse { ("B", "A") } else { ("A", "B") };
                let balances = post
                    .balances
                    .iter()
                    .map(|row| {
                        (
                            (
                                row.asset.clone(),
                                row.owner.clone(),
                                row.custody_domain.clone(),
                            ),
                            row.amount_atoms,
                        )
                    })
                    .collect::<BTreeMap<_, _>>();
                let mut expected = BTreeMap::new();
                expected.insert(
                    (asset_in.to_owned(), alice(), "accounts".to_owned()),
                    1_000 - debit,
                );
                expected.insert(
                    (asset_out.to_owned(), alice(), "accounts".to_owned()),
                    1_000,
                );
                expected.insert((asset_out.to_owned(), bob(), "accounts".to_owned()), credit);
                assert_eq!(
                    balances, expected,
                    "fee {fee_bps} exact_out {exact_out} reverse {reverse}"
                );
                let before_pool = [
                    ("A", u128::from(world.spot.pool.reserve0)),
                    ("B", u128::from(world.spot.pool.reserve1)),
                ]
                .into_iter()
                .collect::<BTreeMap<_, _>>();
                let after_pool = post
                    .custody
                    .iter()
                    .filter(|row| row.custody_domain == SPOT_POOL_CUSTODY_DOMAIN_V2)
                    .map(|row| (row.asset.as_str(), row.amount_atoms))
                    .collect::<BTreeMap<_, _>>();
                assert_eq!(after_pool[asset_in], before_pool[asset_in] + debit);
                assert_eq!(after_pool[asset_out], before_pool[asset_out] - credit);
                for supply in &world.state.supplies {
                    let total = post
                        .balances
                        .iter()
                        .chain(&post.custody)
                        .filter(|row| row.asset == supply.asset)
                        .map(|row| row.amount_atoms)
                        .sum::<u128>();
                    assert_eq!(total, supply.amount_atoms);
                }
                assert_eq!(accepted.post_spot().intent_nonce(&alice()), 1);
                let lanes = accepted
                    .effects()
                    .lane_writes
                    .iter()
                    .map(|row| row.lane_id)
                    .collect::<Vec<_>>();
                assert_eq!(
                    lanes,
                    vec![LaneIdV2::ASSET_TRANSFER, LaneIdV2::SPOT_LIQUIDITY]
                );
                let fee = (debit * u128::from(fee_bps) + 9_999) / 10_000;
                let allocated = accepted
                    .effects()
                    .rows
                    .iter()
                    .filter(|row| row.kind == EconomicEffectKindV2::FEE_ALLOCATION)
                    .map(|row| row.delta_atoms)
                    .sum::<i128>();
                assert_eq!(allocated, i128::try_from(fee).expect("fee fits"));
                let conserved = accepted
                    .effects()
                    .fee_conservation
                    .iter()
                    .map(|row| row.current_allocations_atoms)
                    .sum::<u128>();
                assert_eq!(conserved, fee);
            }
        }
    }
}

#[test]
fn given_exact_output_seven_with_max_ten_then_debit_is_five_and_whole_fee_stays_in_reserves() {
    // Carried from the Python 1000/1000 fixture (9 in, 7 out, fee 1) onto the
    // 10000/20000 joint fixture: 5 in, 7 out, fee 1, entire fee in reserves.
    let world = world(30);
    let command = intent(&world.spot, true, false, &[("recipient", text(&bob()))]);
    let occurrence_id = occurrence(&world.state, &command, 1)
        .occurrence_id()
        .expect("occurrence id");
    let (accepted, next) = accept(&world, &command, 1);
    let pool_id = world.spot.pool.pool_id.clone();
    assert_eq!(
        (next.spot.pool.reserve0, next.spot.pool.reserve1),
        (10_005, 19_993)
    );
    assert_eq!(next.spot.pool.lp_supply, world.spot.pool.lp_supply);
    assert_eq!(next.spot.pool.created_at, world.spot.pool.created_at);
    assert_eq!(next.spot.pool.status, PoolStatusV2::ACTIVE);
    let mut expected_balances = vec![
        amount(&alice(), "A", "accounts", 995),
        amount(&alice(), "B", "accounts", 1_000),
        amount(&bob(), "B", "accounts", 7),
    ];
    sort_amounts(&mut expected_balances);
    assert_eq!(next.state.balances, expected_balances);
    assert_eq!(next.assets.balances(), expected_balances.as_slice());
    assert_eq!(
        accepted.effects().rows,
        vec![
            effect_row(
                EconomicEffectKindV2::ACCOUNT_MOVEMENT,
                &alice(),
                "A",
                "accounts",
                -5
            ),
            effect_row(
                EconomicEffectKindV2::ACCOUNT_MOVEMENT,
                &bob(),
                "B",
                "accounts",
                7
            ),
            effect_row(EconomicEffectKindV2::CUSTODY, &pool_id, "A", "spot_pool", 5),
            effect_row(
                EconomicEffectKindV2::CUSTODY,
                &pool_id,
                "B",
                "spot_pool",
                -7
            ),
            effect_row(
                EconomicEffectKindV2::FEE_ALLOCATION,
                &pool_id,
                "A",
                "spot_pool",
                1
            ),
        ]
    );
    assert_eq!(
        accepted.effects().fee_conservation,
        vec![FeeConservationRowV2 {
            asset: "A".to_owned(),
            fee_charged_atoms: 1,
            current_allocations_atoms: 1,
            carried_residue_atoms: 0,
        }]
    );
    assert_eq!(
        accepted.effects().asset_conservation,
        vec![conservation("A", 11_020), conservation("B", 21_000)]
    );
    assert_eq!(
        accepted.effects().occurrence_consumptions,
        vec![occurrence_id]
    );
    assert!(accepted.effects().external_outbox_enqueue.is_empty());
    assert_eq!(next.state.height, 1);
    assert_eq!(next.state.replay_state.len(), 1);
}

#[test]
fn given_zero_fee_pool_then_no_fee_rows_and_output_is_floored() {
    let world = world(0);
    let command = intent(&world.spot, false, false, &[("min_amount_out", integer(1))]);
    let (accepted, next) = accept(&world, &command, 1);
    assert!(accepted
        .effects()
        .rows
        .iter()
        .all(|row| row.kind != EconomicEffectKindV2::FEE_ALLOCATION));
    assert!(accepted.effects().fee_conservation.is_empty());
    assert_eq!(
        (next.spot.pool.reserve0, next.spot.pool.reserve1),
        (10_010, 19_981)
    );
    assert_eq!(
        next.state.balances,
        vec![
            amount(&alice(), "A", "accounts", 990),
            amount(&alice(), "B", "accounts", 1_019),
        ]
    );
}

#[test]
fn given_full_fee_pool_then_both_modes_reject_the_quote_without_effects() {
    let world = world(10_000);
    for exact_out in [false, true] {
        let command = intent(&world.spot, exact_out, false, &[]);
        assert_rejected(
            &world,
            &command,
            &occurrence(&world.state, &command, 1),
            TIMESTAMP,
            reject_swap(SpotSwapRejectCodeV2::QUOTE_REJECTED),
        );
    }
}

#[test]
fn given_dust_inputs_then_zero_net_or_zero_output_rejects_and_one_atom_output_accepts() {
    let fee = world(30);
    let dust = intent(
        &fee.spot,
        false,
        false,
        &[("amount_in", integer(1)), ("min_amount_out", integer(0))],
    );
    assert_rejected(
        &fee,
        &dust,
        &occurrence(&fee.state, &dust, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::QUOTE_REJECTED),
    );
    let free = world(0);
    let reverse_dust = intent(
        &free.spot,
        false,
        true,
        &[("amount_in", integer(1)), ("min_amount_out", integer(0))],
    );
    assert_rejected(
        &free,
        &reverse_dust,
        &occurrence(&free.state, &reverse_dust, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::QUOTE_REJECTED),
    );
    let one_atom = intent(
        &free.spot,
        false,
        false,
        &[("amount_in", integer(1)), ("min_amount_out", integer(0))],
    );
    let (accepted, next) = accept(&free, &one_atom, 1);
    let credit = accepted
        .effects()
        .rows
        .iter()
        .find(|row| row.kind == EconomicEffectKindV2::ACCOUNT_MOVEMENT && row.delta_atoms > 0)
        .map(|row| row.delta_atoms);
    assert_eq!(credit, Some(1));
    assert_eq!(next.spot.pool.reserve1, 19_999);
    let drain = intent(
        &free.spot,
        true,
        false,
        &[
            ("amount_out", integer(20_000)),
            ("max_amount_in", integer(i128::from(RESERVE_MAX))),
        ],
    );
    assert_rejected(
        &free,
        &drain,
        &occurrence(&free.state, &drain, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::QUOTE_REJECTED),
    );
}

#[test]
fn given_reserve_domain_maximum_then_exact_neighbor_accepts_and_next_atom_rejects() {
    let world = build_world(0, RESERVE_MAX - 10, RESERVE_MAX, 11, 0);
    let exact = intent(&world.spot, false, false, &[("min_amount_out", integer(0))]);
    let (accepted, next) = accept(&world, &exact, 1);
    assert_eq!(next.spot.pool.reserve0, RESERVE_MAX);
    assert_eq!(next.spot.pool.reserve1, RESERVE_MAX - 10);
    assert!(accepted
        .post_state()
        .balances
        .iter()
        .any(|row| row.owner == alice() && row.asset == "B" && row.amount_atoms == 10));
    let over = intent(
        &world.spot,
        false,
        false,
        &[("amount_in", integer(11)), ("min_amount_out", integer(0))],
    );
    assert_rejected(
        &world,
        &over,
        &occurrence(&world.state, &over, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::QUOTE_REJECTED),
    );
}

#[test]
fn given_insufficient_sender_balance_then_rejects_without_effects() {
    let world = world(30);
    let command = intent(
        &world.spot,
        false,
        false,
        &[
            ("amount_in", integer(1_001)),
            ("min_amount_out", integer(1)),
        ],
    );
    assert_rejected(
        &world,
        &command,
        &occurrence(&world.state, &command, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INSUFFICIENT_BALANCE),
    );
}

#[test]
fn scalar_context_subject_has_python_character_bounds_before_pool_validation() {
    let mut small = pool(30, 1_000, 1_000);
    let command = intent_for(&small.pool_id, true, false, &[]);
    let mut context = SpotSwapContextV2 {
        subject_id: alice(),
        block_timestamp: TIMESTAMP,
        sender_input_atoms: 100,
        recipient_output_atoms: 0,
    };
    assert!(matches!(
        plan_spot_swap_v2(&context, &small, &command),
        Ok(SpotSwapPlanResultV2::Planned(_))
    ));
    for subject in ["x".to_owned(), "é".repeat(512)] {
        context.subject_id = subject;
        assert_eq!(
            plan_spot_swap_v2(&context, &small, &command),
            Ok(SpotSwapPlanResultV2::Rejected(
                SpotSwapRejectCodeV2::SUBJECT_MISMATCH
            ))
        );
    }
    for subject in [String::new(), "x".repeat(513), "é".repeat(513)] {
        context.subject_id = subject;
        assert_eq!(
            plan_spot_swap_v2(&context, &small, &command),
            Err(AbiErrorV2::InvalidBounds("Spot context subject"))
        );
    }
    small.fee_bps = 10_001;
    assert_eq!(
        plan_spot_swap_v2(&context, &small, &command),
        Err(AbiErrorV2::InvalidBounds("Spot context subject"))
    );
}

#[test]
fn given_recipient_balance_at_u128_neighbors_then_plan_overflow_rejects_and_exact_fit_accepts() {
    // Nonclaim: at the joint level a recipient balance within seven atoms of
    // u128::MAX cannot coexist with a pool holding more than seven atoms of
    // the same asset under one u128 supply, so BALANCE_OVERFLOW is
    // invariant-unreachable there. The planner keeps the Python guard.
    let small = pool(30, 1_000, 1_000);
    let command = intent_for(&small.pool_id, true, false, &[]);
    let context = |recipient_output_atoms: u128| SpotSwapContextV2 {
        subject_id: alice(),
        block_timestamp: TIMESTAMP,
        sender_input_atoms: 100,
        recipient_output_atoms,
    };
    assert_eq!(
        plan_spot_swap_v2(&context(u128::MAX - 6), &small, &command).expect("typed plan"),
        SpotSwapPlanResultV2::Rejected(SpotSwapRejectCodeV2::BALANCE_OVERFLOW)
    );
    match plan_spot_swap_v2(&context(u128::MAX - 7), &small, &command).expect("typed plan") {
        SpotSwapPlanResultV2::Planned(plan) => {
            assert_eq!(plan.post_recipient_output_atoms(), u128::MAX);
            assert_eq!(
                (
                    plan.amount_in_atoms(),
                    plan.amount_out_atoms(),
                    plan.fee_atoms()
                ),
                (9, 7, 1)
            );
            assert_eq!(plan.post_sender_input_atoms(), 91);
            assert_eq!(plan.post_pool().reserve0, 1_009);
        }
        SpotSwapPlanResultV2::Rejected(code) => panic!("exact fit must plan, got {code:?}"),
    }
    let full = pool(30, RESERVE_MAX, 1_000);
    let command = intent_for(
        &full.pool_id,
        true,
        false,
        &[
            ("amount_out", integer(1)),
            ("max_amount_in", integer(i128::from(RESERVE_MAX))),
        ],
    );
    let rich = SpotSwapContextV2 {
        subject_id: alice(),
        block_timestamp: TIMESTAMP,
        sender_input_atoms: u128::MAX,
        recipient_output_atoms: 0,
    };
    assert_eq!(
        plan_spot_swap_v2(&rich, &full, &command).expect("typed plan"),
        SpotSwapPlanResultV2::Rejected(SpotSwapRejectCodeV2::QUOTE_REJECTED)
    );
}

// Brute-force oracle carried verbatim from the Python test; its ceil formulas
// are intentionally not the crate's `ceil_div`.
#[allow(clippy::manual_div_ceil)]
#[test]
fn independent_small_domain_exact_out_minimum_and_rounding() {
    let (mut accepted, mut rejected) = (0_u32, 0_u32);
    for reserve_in in [9_u64, 17, 31] {
        for reserve_out in [11_u64, 29, 53] {
            for fee_bps in [0_u64, 30, 1_000] {
                for wanted in 1..6_u64 {
                    let (rin, rout, fee_rate, want) = (
                        u128::from(reserve_in),
                        u128::from(reserve_out),
                        u128::from(fee_bps),
                        u128::from(wanted),
                    );
                    let net = |n: u128| n - (n * fee_rate + 9_999) / 10_000;
                    let gross = (1..100_u128)
                        .find(|&n| rout * net(n) / (rin + net(n)) >= want)
                        .expect("a gross input below 100 exists");
                    let fee = (gross * fee_rate + 9_999) / 10_000;
                    let quote_out = rout * (gross - fee) / (rin + gross - fee);
                    let gap_bps = ((quote_out - want) * 10_000 + want - 1) / want;
                    let small = pool(fee_bps, reserve_in, reserve_out);
                    let command = intent_for(
                        &small.pool_id,
                        true,
                        false,
                        &[
                            ("amount_out", integer(i128::from(wanted))),
                            ("max_amount_in", integer(99)),
                        ],
                    );
                    let context = SpotSwapContextV2 {
                        subject_id: alice(),
                        block_timestamp: TIMESTAMP,
                        sender_input_atoms: 100,
                        recipient_output_atoms: 5,
                    };
                    let result = plan_spot_swap_v2(&context, &small, &command).expect("typed plan");
                    if gap_bps > 200 {
                        assert_eq!(
                            result,
                            SpotSwapPlanResultV2::Rejected(SpotSwapRejectCodeV2::QUOTE_REJECTED)
                        );
                        rejected += 1;
                    } else {
                        match result {
                            SpotSwapPlanResultV2::Planned(plan) => {
                                assert_eq!(
                                    (
                                        plan.amount_in_atoms(),
                                        plan.amount_out_atoms(),
                                        plan.fee_atoms()
                                    ),
                                    (gross, want, fee)
                                );
                                assert_eq!(
                                    plan.pool_deltas(),
                                    (i128::try_from(gross).expect("gross"), -i128::from(wanted))
                                );
                                accepted += 1;
                            }
                            SpotSwapPlanResultV2::Rejected(code) => {
                                panic!("{reserve_in}/{reserve_out} fee {fee_bps} wanted {wanted}: {code:?}")
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(accepted > 0 && rejected > 0);
}

#[test]
fn given_slippage_bounds_then_both_modes_reject_and_beyond_u128_bounds_follow_python_comparisons() {
    let world = world(30);
    let tight_out = intent(&world.spot, true, false, &[("max_amount_in", integer(4))]);
    assert_rejected(
        &world,
        &tight_out,
        &occurrence(&world.state, &tight_out, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::SLIPPAGE_LIMIT),
    );
    let tight_in = intent(
        &world.spot,
        false,
        false,
        &[("min_amount_out", integer(99))],
    );
    assert_rejected(
        &world,
        &tight_in,
        &occurrence(&world.state, &tight_in, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::SLIPPAGE_LIMIT),
    );
    let huge = SwapIntentFieldValueV2::Integer(
        SwapIntentIntegerV2::parse_canonical_text("340282366920938463463374607431768211456")
            .expect("2^128 is admitted by the legacy codec"),
    );
    let beyond_min = intent(
        &world.spot,
        false,
        false,
        &[("min_amount_out", huge.clone())],
    );
    assert_rejected(
        &world,
        &beyond_min,
        &occurrence(&world.state, &beyond_min, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::SLIPPAGE_LIMIT),
    );
    let beyond_max = intent(&world.spot, true, false, &[("max_amount_in", huge)]);
    let (accepted, _) = accept(&world, &beyond_max, 1);
    assert_eq!(accepted.effects().rows.len(), 5);
}

#[test]
fn correct_economics_wrong_context_rejects_without_nonce_or_effects() {
    let world = world(30);
    let command = intent(&world.spot, true, false, &[]);
    let base = occurrence(&world.state, &command, 1);
    let variants = vec![
        EconomicCommandOccurrenceV2 {
            chain_id: "wrong".to_owned(),
            ..base.clone()
        },
        EconomicCommandOccurrenceV2 {
            deployment_root: root(77),
            ..base.clone()
        },
        EconomicCommandOccurrenceV2 {
            profile_root: root(77),
            ..base.clone()
        },
        EconomicCommandOccurrenceV2 {
            pre_state_root: root(77),
            ..base.clone()
        },
        EconomicCommandOccurrenceV2 {
            height: 2,
            ..base.clone()
        },
    ];
    for variant in variants {
        assert_rejected(
            &world,
            &command,
            &variant,
            TIMESTAMP,
            reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH),
        );
    }
}

#[test]
fn maximum_height_rejects_with_context_precedence_over_body_mismatch() {
    let mut world = world(30);
    world.state.height = u64::MAX;
    let pre_root = world
        .state
        .state_root()
        .expect("maximum height remains representable");
    let command = intent(&world.spot, true, false, &[]);
    for height in [0, u64::MAX - 1, u64::MAX] {
        let mut occurrence = occurrence(&world.state, &command, 1);
        occurrence.height = height;
        occurrence.command_body_hash = root(999);
        assert_rejected(
            &world,
            &command,
            &occurrence,
            TIMESTAMP,
            reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH),
        );
    }
    assert_eq!(world.state.state_root().expect("root"), pre_root);
}

#[test]
fn independent_guards_reject_unauthorized_or_unacceptable_commands() {
    let world = world(30);
    let command = intent(&world.spot, true, false, &[]);

    let mut body = occurrence(&world.state, &command, 1);
    body.command_body_hash = root(999);
    assert_rejected(
        &world,
        &command,
        &body,
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH),
    );

    let mut kind = occurrence(&world.state, &command, 1);
    kind.command_kind = "wrong".to_owned();
    assert_rejected(
        &world,
        &command,
        &kind,
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH),
    );

    let mut objects = occurrence(&world.state, &command, 1);
    objects.consumed_object_ids = vec![root(5).as_str().to_owned()];
    assert_rejected(
        &world,
        &command,
        &objects,
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH),
    );

    let mut subject = occurrence(&world.state, &command, 1);
    subject.subject_id = mallory();
    assert_rejected(
        &world,
        &command,
        &subject,
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::SUBJECT_MISMATCH),
    );

    let funds = intent(
        &world.spot,
        false,
        false,
        &[
            ("amount_in", integer(1_001)),
            ("min_amount_out", integer(1)),
        ],
    );
    assert_rejected(
        &world,
        &funds,
        &occurrence(&world.state, &funds, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INSUFFICIENT_BALANCE),
    );

    let slippage = intent(&world.spot, true, false, &[("max_amount_in", integer(1))]);
    assert_rejected(
        &world,
        &slippage,
        &occurrence(&world.state, &slippage, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::SLIPPAGE_LIMIT),
    );

    assert_rejected(
        &world,
        &command,
        &occurrence(&world.state, &command, 1),
        TIMESTAMP + 1,
        reject_swap(SpotSwapRejectCodeV2::EXPIRED),
    );

    let gap = intent(&world.spot, true, false, &[("nonce", integer(2))]);
    assert_rejected(
        &world,
        &gap,
        &occurrence(&world.state, &gap, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INVALID_NONCE),
    );
}

#[test]
fn every_original_intent_field_is_bound_to_the_occurrence() {
    let world = world(30);
    let original = intent(&world.spot, true, false, &[]);
    let bound = occurrence(&world.state, &original, 1);

    let mut id = intent_parts(&world.spot, true, false, &[]);
    id.intent_id = root(77).as_str().to_owned();
    let mut salt = intent_parts(&world.spot, true, false, &[]);
    salt.salt = Some("different".to_owned());
    let mut deadline = intent_parts(&world.spot, true, false, &[]);
    deadline.deadline = TIMESTAMP + 1;
    let recipient = intent_parts(&world.spot, true, false, &[("recipient", text(&mallory()))]);
    for parts in [id, salt, deadline, recipient] {
        let changed = SpotSwapIntentV2::new(parts).expect("valid variant");
        assert_ne!(
            changed.command_body_hash().expect("hash"),
            original.command_body_hash().expect("hash")
        );
        assert_rejected(
            &world,
            &changed,
            &bound,
            TIMESTAMP,
            reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH),
        );
    }
    // The legacy constructor forbids a foreign module or version before hashing.
    let mut module = intent_parts(&world.spot, true, false, &[]);
    module.module = "Other".to_owned();
    assert!(SpotSwapIntentV2::new(module).is_err());
    let mut version = intent_parts(&world.spot, true, false, &[]);
    version.version = "0.2".to_owned();
    assert!(SpotSwapIntentV2::new(version).is_err());
}

#[test]
fn unsupported_fields_reject_before_context_binding() {
    let world = world(30);
    let plain = intent(&world.spot, true, false, &[]);
    let mut wrong_chain = occurrence(&world.state, &plain, 1);
    wrong_chain.chain_id = "wrong".to_owned();
    let foreign = intent(
        &world.spot,
        true,
        false,
        &[("quote_receipt_hash", text("foreign"))],
    );
    assert_rejected(
        &world,
        &foreign,
        &wrong_chain,
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::UNSUPPORTED_FIELDS),
    );
    let mut nested = intent_parts(&world.spot, true, false, &[]);
    nested
        .fields
        .insert("route".to_owned(), SwapIntentFieldValueV2::Nested);
    let nested = SpotSwapIntentV2::new(nested).expect("nested foreign key constructs");
    assert_rejected(
        &world,
        &nested,
        &wrong_chain,
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::UNSUPPORTED_FIELDS),
    );
}

#[test]
fn asset_swap_asset_swap_history_keeps_independent_inner_and_outer_nonces() {
    let world = transfer(&world(30), 1);
    let first = intent(&world.spot, true, false, &[("nonce", integer(1))]);
    let (_, world) = accept(&world, &first, 2);
    let world = transfer(&world, 3);
    let stale = intent(&world.spot, true, false, &[("nonce", integer(1))]);
    assert_rejected(
        &world,
        &stale,
        &occurrence(&world.state, &stale, 4),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INVALID_NONCE),
    );
    let next = intent(&world.spot, true, false, &[("nonce", integer(2))]);
    assert_rejected(
        &world,
        &next,
        &occurrence(&world.state, &next, 3),
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::REPLAY_ALREADY_CONSUMED),
    );
    let (_, world) = accept(&world, &next, 4);
    assert_eq!(world.spot.intent_nonce(&alice()), 2);
    assert_eq!(world.state.replay_state.len(), 4);
    assert_eq!(world.state.height, 4);
}

#[test]
fn incomplete_or_misattributed_projection_cannot_admit_a_swap() {
    for defect in [
        "missing-custody",
        "extra-custody",
        "reserve-mismatch",
        "lp-owner",
        "lp-metadata",
        "module",
        "disabled",
        "asset-root",
        "nominal-claims",
    ] {
        let mut world = world(30);
        match defect {
            "missing-custody" => world
                .state
                .custody
                .retain(|row| row.custody_domain != SPOT_POOL_CUSTODY_DOMAIN_V2),
            "extra-custody" => {
                world
                    .state
                    .custody
                    .push(amount("fake", "A", SPOT_POOL_CUSTODY_DOMAIN_V2, 1));
                sort_amounts(&mut world.state.custody);
            }
            "reserve-mismatch" => {
                let mut spot = world.spot.clone();
                spot.pool.reserve0 += 1;
                world = world.with_spot(spot);
            }
            "lp-owner" => {
                let mut rows = lp_rows();
                rows[1].owner = mallory();
                rows.sort_by(|left, right| left.owner.cmp(&right.owner));
                world.spot.lp_positions = rows;
            }
            "lp-metadata" => world.spot.lp_positions[1].last_remove_timestamp = Some(99),
            "module" => set_lane(&mut world.state, LaneIdV2::SPOT_LIQUIDITY, |row| {
                row.module_release_id = root(66);
            }),
            "disabled" => set_lane(&mut world.state, LaneIdV2::SPOT_LIQUIDITY, |row| {
                row.enabled = false;
            }),
            "asset-root" => set_lane(&mut world.state, LaneIdV2::ASSET_TRANSFER, |row| {
                row.state_root = root(66);
            }),
            _ => {
                world.state.liabilities = vec![amount(&bob(), "A", SPOT_POOL_CUSTODY_DOMAIN_V2, 1)];
            }
        }
        let command = intent(&world.spot, true, false, &[]);
        assert_rejected(
            &world,
            &command,
            &occurrence(&world.state, &command, 1),
            TIMESTAMP,
            reject_global(SpotSwapGlobalRejectKindV2::PROJECTION_MISMATCH),
        );
    }
}

#[test]
fn swap_preserves_unrelated_open_claim_dormant_lp_rows_and_escrow_custody() {
    let mut world = world(30);
    world.state.liabilities = vec![amount(&carol(), "A", ESCROW_DOMAIN, 20)];
    world.state.terminal_obligations = vec![TerminalObligationV2 {
        obligation_id: "carol-claim".to_owned(),
        lane_id: LaneIdV2::STRATEGY_ESCROW,
        claimant: carol(),
        asset: "A".to_owned(),
        liability_domain: ESCROW_DOMAIN.to_owned(),
        amount_atoms: 20,
        status: TerminalObligationStatusV2::OPEN,
    }];
    let command = intent(&world.spot, true, false, &[]);
    let (accepted, next) = accept(&world, &command, 1);
    assert_eq!(next.state.liabilities, world.state.liabilities);
    assert_eq!(
        next.state.terminal_obligations,
        world.state.terminal_obligations
    );
    assert_eq!(next.spot.lp_positions, lp_rows());
    assert_eq!(next.spot.lp_positions[2].shares, 0);
    assert_eq!(next.spot.lp_positions[2].last_remove_timestamp, Some(6));
    assert!(accepted
        .effects()
        .rows
        .iter()
        .all(|row| row.custody_domain != ESCROW_DOMAIN));
}

#[test]
fn nonce_exhaustion_and_full_new_subject_table_are_logical_noops() {
    let base = world(30);
    let exhausted_spot = spot_state(
        base.spot.pool.clone(),
        lp_rows(),
        vec![SpotIntentNonceV2 {
            owner: alice(),
            last_nonce: u64::from(u32::MAX),
        }],
    );
    let exhausted = base.clone().with_spot(exhausted_spot);
    let command = intent(
        &exhausted.spot,
        true,
        false,
        &[("nonce", integer(i128::from(u32::MAX)))],
    );
    assert_rejected(
        &exhausted,
        &command,
        &occurrence(&exhausted.state, &command, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INVALID_NONCE),
    );

    let nonces = (0..4_096_u64)
        .map(|index| SpotIntentNonceV2 {
            owner: format!("0x{index:096x}"),
            last_nonce: 1,
        })
        .collect::<Vec<_>>();
    let full_spot = spot_state(base.spot.pool.clone(), lp_rows(), nonces.clone());
    let full = base.clone().with_spot(full_spot);
    let command = intent(&full.spot, true, false, &[]);
    assert_rejected(
        &full,
        &command,
        &occurrence(&full.state, &command, 1),
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::SUCCESSOR_REJECTED),
    );

    // At capacity an already represented owner can still act; a table limit
    // must not become a ban on every required successor state.
    let mut existing = nonces[1..].to_vec();
    existing.push(SpotIntentNonceV2 {
        owner: alice(),
        last_nonce: 1,
    });
    let existing_spot = spot_state(base.spot.pool.clone(), lp_rows(), existing);
    let represented = base.with_spot(existing_spot);
    let command = intent(&represented.spot, true, false, &[("nonce", integer(2))]);
    let (_, next) = accept(&represented, &command, 1);
    assert_eq!(next.spot.intent_nonces.len(), 4_096);
    assert_eq!(next.spot.intent_nonce(&alice()), 2);
}

#[test]
fn asset_policy_must_be_known_and_admitted_without_inventing_token_fee_semantics() {
    for defect in ["disabled", "transfer-fee", "origin"] {
        let base = world(30);
        let mut policies = vec![policy("A"), policy("B")];
        match defect {
            "disabled" => policies[0].enabled = false,
            "transfer-fee" => policies[0].transfer_fee_atoms = 1,
            _ => {}
        }
        let registry = registry(&policies, (defect == "origin").then_some("A"));
        let mut assets = base.assets.clone();
        assets.transfer_state.policies = policies;
        assets.origin_registry = registry;
        let world = base.with_assets(assets);
        let command = intent(&world.spot, true, false, &[]);
        let expected = if defect == "origin" {
            SpotSwapGlobalRejectKindV2::ASSET_ORIGIN_MISMATCH
        } else {
            SpotSwapGlobalRejectKindV2::UNSUPPORTED_ASSET_POLICY
        };
        assert_rejected(
            &world,
            &command,
            &occurrence(&world.state, &command, 1),
            TIMESTAMP,
            reject_global(expected),
        );
    }
}

#[test]
fn noncanonical_inner_identity_is_a_typed_input_error_after_context_checks() {
    let world = world(30);
    let canonical = alice();
    for alias in [canonical[2..].to_owned(), canonical.to_ascii_uppercase()] {
        let mut sender = intent_parts(&world.spot, true, false, &[]);
        sender.sender_pubkey = alias.clone();
        let sender = SpotSwapIntentV2::new(sender)
            .expect("the legacy constructor accepts any nonempty sender");
        let mut bound = occurrence(&world.state, &sender, 1);
        bound.subject_id = alias.clone();
        let before = world.roots();
        let error = transition_spot_swap_global_v2(
            &world.assets,
            &world.spot,
            &world.state,
            &sender,
            &bound,
            TIMESTAMP,
        )
        .expect_err("alias sender is a typed input error");
        assert!(
            matches!(error, SpotSwapInputErrorV2::SenderIdentity(_)),
            "{error}"
        );
        assert_eq!(error.code(), "INPUT_SENDER_IDENTITY");
        assert_eq!(world.roots(), before);

        let recipient = intent(&world.spot, true, false, &[("recipient", text(&alias))]);
        let bound = occurrence(&world.state, &recipient, 1);
        let error = transition_spot_swap_global_v2(
            &world.assets,
            &world.spot,
            &world.state,
            &recipient,
            &bound,
            TIMESTAMP,
        )
        .expect_err("alias recipient is a typed input error");
        assert!(matches!(error, SpotSwapInputErrorV2::RecipientIdentity(_)));
        assert_eq!(error.code(), "INPUT_RECIPIENT_IDENTITY");

        // Context checks keep precedence: the same alias with a wrong chain is
        // an ordinary no-op rejection, exactly where Python returns first.
        let mut wrong = bound.clone();
        wrong.chain_id = "wrong".to_owned();
        assert_rejected(
            &world,
            &recipient,
            &wrong,
            TIMESTAMP,
            reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH),
        );
    }
}

#[test]
fn timestamp_is_bound_even_when_both_times_admit_the_same_economics() {
    let world = world(30);
    let command = intent(&world.spot, true, false, &[]);
    let bound = occurrence(&world.state, &command, 1);
    let accepted_at = |timestamp: u64| match run(&world, &command, &bound, timestamp) {
        SpotSwapGlobalResultV2::Accepted(accepted) => *accepted,
        SpotSwapGlobalResultV2::Rejected(rejected) => panic!("{:?}", rejected.code),
    };
    let earlier = accepted_at(99);
    let later = accepted_at(100);
    assert_eq!(earlier.post_state(), later.post_state());
    assert_eq!(earlier.post_spot(), later.post_spot());
    assert_eq!(earlier.effects(), later.effects());
    assert_eq!(
        earlier.refinement_root().expect("root"),
        later.refinement_root().expect("root")
    );
    assert_ne!(earlier.statement_root(), later.statement_root());
}

#[test]
fn accepted_roots_bind_pre_state_post_state_effects_and_refinement() {
    let world = world(30);
    let command = intent(&world.spot, true, false, &[]);
    let (accepted, next) = accept(&world, &command, 1);
    assert_eq!(
        accepted.refinement().pre_state_root(),
        &world.state.state_root().expect("pre root")
    );
    assert_eq!(
        accepted.refinement().post_state_root(),
        &next.state.state_root().expect("post root")
    );
    assert_eq!(
        accepted.refinement().effect_plan_root(),
        &accepted.effects().effect_plan_root().expect("effect root")
    );
    assert!(accepted.refinement().terminal_plan_root().is_zero());
    assert!(accepted.refinement().oracle_plan_root().is_zero());
    assert_eq!(
        next.assets.state_root().expect("asset root"),
        lane_root(&next.state, LaneIdV2::ASSET_TRANSFER)
    );
    assert_eq!(
        next.spot.state_root().expect("spot root"),
        lane_root(&next.state, LaneIdV2::SPOT_LIQUIDITY)
    );
    assert_eq!(next.state.height, world.state.height + 1);
    assert_eq!(next.state.replay_state.len(), 1);
    assert_eq!(
        accepted.effects().lane_writes[0].pre_root,
        lane_root(&world.state, LaneIdV2::ASSET_TRANSFER)
    );
    assert_eq!(
        accepted.effects().lane_writes[1].post_root,
        lane_root(&next.state, LaneIdV2::SPOT_LIQUIDITY)
    );
}

#[test]
fn repeated_command_is_deterministic_and_cannot_replay_after_acceptance() {
    let world = world(30);
    let command = intent(&world.spot, true, false, &[]);
    let bound = occurrence(&world.state, &command, 1);
    let first = run(&world, &command, &bound, TIMESTAMP);
    let second = run(&world, &command, &bound, TIMESTAMP);
    assert_eq!(first, second);
    let (_, next) = accept(&world, &command, 1);
    // The same occurrence against the successor: the pre-state root moved on.
    assert_rejected(
        &next,
        &command,
        &bound,
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH),
    );
    // A fresh occurrence with the consumed inner nonce.
    assert_rejected(
        &next,
        &command,
        &occurrence(&next.state, &command, 2),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INVALID_NONCE),
    );
    // A fresh occurrence reusing the outer nonce with the next inner nonce.
    let next_command = intent(&next.spot, true, false, &[("nonce", integer(2))]);
    assert_rejected(
        &next,
        &next_command,
        &occurrence(&next.state, &next_command, 1),
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::REPLAY_ALREADY_CONSUMED),
    );
}

#[test]
fn control_lp_owner_substitution_is_observable_through_the_spot_root_binding() {
    let world = world(30);
    let mut rows = lp_rows();
    rows[1].owner = mallory();
    rows.sort_by(|left, right| left.owner.cmp(&right.owner));
    let mut substituted = world.spot.clone();
    substituted.lp_positions = rows;
    assert_ne!(
        substituted.state_root().expect("root"),
        world.spot.state_root().expect("root")
    );
    let mut tampered = world.clone();
    tampered.spot = substituted.clone();
    let command = intent(&tampered.spot, true, false, &[]);
    assert_rejected(
        &tampered,
        &command,
        &occurrence(&tampered.state, &command, 1),
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::PROJECTION_MISMATCH),
    );
    // Negative control: ownership follows the committed lane root, never the
    // caller's table alone; rebinding the root admits the swap unchanged.
    let rebound = world.with_spot(substituted);
    let command = intent(&rebound.spot, true, false, &[]);
    let (_, next) = accept(&rebound, &command, 1);
    assert!(next
        .spot
        .lp_positions
        .iter()
        .any(|row| row.owner == mallory()));
}

#[test]
fn control_recipient_substitution_changes_body_hash_and_post_state() {
    let world = world(30);
    let to_bob = intent(&world.spot, true, false, &[("recipient", text(&bob()))]);
    let to_mallory = intent(&world.spot, true, false, &[("recipient", text(&mallory()))]);
    assert_ne!(
        to_bob.command_body_hash().expect("hash"),
        to_mallory.command_body_hash().expect("hash")
    );
    let (bob_accepted, _) = accept(&world, &to_bob, 1);
    let (mallory_accepted, _) = accept(&world, &to_mallory, 1);
    assert_ne!(bob_accepted.post_state(), mallory_accepted.post_state());
    assert!(bob_accepted
        .post_state()
        .balances
        .iter()
        .any(|row| row.owner == bob() && row.asset == "B" && row.amount_atoms == 7));
    assert!(mallory_accepted
        .post_state()
        .balances
        .iter()
        .any(|row| row.owner == mallory() && row.asset == "B" && row.amount_atoms == 7));
    // The occurrence bound the original body; a substituted recipient mismatches.
    assert_rejected(
        &world,
        &to_mallory,
        &occurrence(&world.state, &to_bob, 1),
        TIMESTAMP,
        reject_global(SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH),
    );
}

#[test]
fn pool_inactive_and_unsupported_curve_reject_after_identity_checks() {
    let base = world(30);
    let mut frozen_pool = base.spot.pool.clone();
    frozen_pool.status = PoolStatusV2::FROZEN;
    let frozen = base.with_spot(spot_state(frozen_pool, lp_rows(), Vec::new()));
    let command = intent(&frozen.spot, true, false, &[]);
    assert_rejected(
        &frozen,
        &command,
        &occurrence(&frozen.state, &command, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::POOL_INACTIVE),
    );

    let mut cubic_pool = pool(30, 10_000, 20_000);
    cubic_pool.curve_tag = "CUBIC_SUM_V1".to_owned();
    cubic_pool.curve_params = "{\"p\":1,\"q\":1}".to_owned();
    cubic_pool.pool_id = cubic_pool.canonical_pool_id();
    let cubic = build_world_from(spot_state(cubic_pool, lp_rows(), Vec::new()), 1_000, 1_000);
    let command = intent(&cubic.spot, true, false, &[]);
    assert_rejected(
        &cubic,
        &command,
        &occurrence(&cubic.state, &command, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::UNSUPPORTED_CURVE),
    );
}

#[test]
fn pool_and_asset_mismatch_reject_after_subject_deadline_and_nonce_checks() {
    let world = world(30);
    let other_pool = intent(&world.spot, true, false, &[("pool_id", text("other"))]);
    assert_rejected(
        &world,
        &other_pool,
        &occurrence(&world.state, &other_pool, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::POOL_MISMATCH),
    );
    let foreign_asset = intent(&world.spot, true, false, &[("asset_out", text("C"))]);
    assert_rejected(
        &world,
        &foreign_asset,
        &occurrence(&world.state, &foreign_asset, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::ASSET_MISMATCH),
    );
    let same_asset = intent(&world.spot, true, false, &[("asset_out", text("A"))]);
    assert_rejected(
        &world,
        &same_asset,
        &occurrence(&world.state, &same_asset, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::ASSET_MISMATCH),
    );
    // Precedence: an out-of-range nonce beats a pool mismatch.
    let bad_nonce = intent(
        &world.spot,
        true,
        false,
        &[("pool_id", text("other")), ("nonce", integer(0))],
    );
    assert_rejected(
        &world,
        &bad_nonce,
        &occurrence(&world.state, &bad_nonce, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INVALID_NONCE),
    );
    let text_nonce = intent(&world.spot, true, false, &[("nonce", text("1"))]);
    assert_rejected(
        &world,
        &text_nonce,
        &occurrence(&world.state, &text_nonce, 1),
        TIMESTAMP,
        reject_swap(SpotSwapRejectCodeV2::INVALID_NONCE),
    );
}
