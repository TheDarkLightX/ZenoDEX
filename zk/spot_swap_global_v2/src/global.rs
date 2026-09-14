//! Pure joint SPOT_LIQUIDITY and ASSET_TRANSFER successor for GlobalSettlementABI V2.
//!
//! Mirrors `src/core/spot_swap_global_v2.py::transition_spot_swap_global_v2`.
//! The quote module owns arithmetic; this module owns complete state, command
//! and nonce binding. It reconstructs all V2 tables, both lane writes, the
//! replay commitment and the shared refinement input. Authentication, time
//! provenance, proof admission and publication remain shell obligations; no
//! candidate is a receipt and every output has authority `NONE`.

use std::collections::BTreeMap;

use serde::Serialize;
use zenodex_global_settlement_abi_v2::{
    hash_global_v2, refine_global_economic_state_effects_v2, AbiErrorV2, AbiResultV2, AssetClassV2,
    AssetConservationRowV2, AssetLaneCustodyStateV2, EconomicAmountV2, EconomicCommandOccurrenceV2,
    EconomicEffectKindV2, EconomicEffectRowV2, FeeConservationRowV2, GlobalEconomicEffectPlanV2,
    GlobalEconomicStateEffectRefinementCandidateV2, GlobalEconomicStateEffectRefinementV2,
    GlobalEconomicStateV2, GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2, LaneIdV2,
    LaneStateRootV2, LaneWriteV2, ReplayStateV2, RootV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2, ASSET_LANE_CUSTODY_STATE_SCHEMA_V2, GLOBAL_SETTLEMENT_ABI_V2,
};

use crate::intent::{SpotSwapCommandBodyV2, SpotSwapIntentV2, SwapIntentFieldProfileV2};
use crate::plan::{
    plan_spot_swap_v2, SpotSwapContextV2, SpotSwapPlanResultV2, SpotSwapPlanV2,
    SpotSwapRejectCodeV2,
};
use crate::state::{
    validate_spot_owner_v2, SpotIntentNonceV2, SpotSwapStateV2, SPOT_POOL_CUSTODY_DOMAIN_V2,
    SPOT_SWAP_STATE_SCHEMA_V2,
};

pub const SPOT_SWAP_GLOBAL_STATEMENT_DOMAIN_V2: &str = "spot-swap-global-statement-v2";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum SpotSwapGlobalRejectKindV2 {
    OCCURRENCE_CONTEXT_MISMATCH,
    OCCURRENCE_COMMAND_MISMATCH,
    REPLAY_ALREADY_CONSUMED,
    PROJECTION_MISMATCH,
    ASSET_ORIGIN_MISMATCH,
    UNSUPPORTED_ASSET_POLICY,
    SUCCESSOR_REJECTED,
}

impl SpotSwapGlobalRejectKindV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::OCCURRENCE_CONTEXT_MISMATCH => "OCCURRENCE_CONTEXT_MISMATCH",
            Self::OCCURRENCE_COMMAND_MISMATCH => "OCCURRENCE_COMMAND_MISMATCH",
            Self::REPLAY_ALREADY_CONSUMED => "REPLAY_ALREADY_CONSUMED",
            Self::PROJECTION_MISMATCH => "PROJECTION_MISMATCH",
            Self::ASSET_ORIGIN_MISMATCH => "ASSET_ORIGIN_MISMATCH",
            Self::UNSUPPORTED_ASSET_POLICY => "UNSUPPORTED_ASSET_POLICY",
            Self::SUCCESSOR_REJECTED => "SUCCESSOR_REJECTED",
        }
    }
}

pub const ALL_SPOT_SWAP_GLOBAL_REJECT_KINDS_V2: [SpotSwapGlobalRejectKindV2; 7] = [
    SpotSwapGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH,
    SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH,
    SpotSwapGlobalRejectKindV2::REPLAY_ALREADY_CONSUMED,
    SpotSwapGlobalRejectKindV2::PROJECTION_MISMATCH,
    SpotSwapGlobalRejectKindV2::ASSET_ORIGIN_MISMATCH,
    SpotSwapGlobalRejectKindV2::UNSUPPORTED_ASSET_POLICY,
    SpotSwapGlobalRejectKindV2::SUCCESSOR_REJECTED,
];

/// The Python `SpotSwapGlobalRejectedV2.code` union: a global binding code or
/// a planner code. `as_str` yields the exact Python enum value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpotSwapGlobalRejectCodeV2 {
    Global(SpotSwapGlobalRejectKindV2),
    Swap(SpotSwapRejectCodeV2),
}

impl SpotSwapGlobalRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Global(kind) => kind.as_str(),
            Self::Swap(code) => code.as_str(),
        }
    }
}

/// Typed structural failure: the Python `TypeError`/`ValueError` raise family.
/// It carries no economic decision and never produces a successor.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpotSwapInputErrorV2 {
    Assets(AbiErrorV2),
    SpotState(AbiErrorV2),
    GlobalState(AbiErrorV2),
    Occurrence(AbiErrorV2),
    Intent(AbiErrorV2),
    SenderIdentity(AbiErrorV2),
    RecipientIdentity(AbiErrorV2),
    Internal(AbiErrorV2),
}

impl SpotSwapInputErrorV2 {
    /// Stable typed code for the native parity transport.
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Assets(_) => "INPUT_ASSETS",
            Self::SpotState(_) => "INPUT_SPOT_STATE",
            Self::GlobalState(_) => "INPUT_GLOBAL_STATE",
            Self::Occurrence(_) => "INPUT_OCCURRENCE",
            Self::Intent(_) => "INPUT_INTENT",
            Self::SenderIdentity(_) => "INPUT_SENDER_IDENTITY",
            Self::RecipientIdentity(_) => "INPUT_RECIPIENT_IDENTITY",
            Self::Internal(_) => "INPUT_INTERNAL",
        }
    }

    pub const fn detail(&self) -> &AbiErrorV2 {
        match self {
            Self::Assets(error)
            | Self::SpotState(error)
            | Self::GlobalState(error)
            | Self::Occurrence(error)
            | Self::Intent(error)
            | Self::SenderIdentity(error)
            | Self::RecipientIdentity(error)
            | Self::Internal(error) => error,
        }
    }
}

impl core::fmt::Display for SpotSwapInputErrorV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{}: {}", self.code(), self.detail())
    }
}

impl std::error::Error for SpotSwapInputErrorV2 {}

/// Exact no-op rejection bound to the submitted pre-state root.
///
/// The post-state root is derived, so a caller cannot assign it independently:
///
/// ```compile_fail
/// use zenodex_spot_swap_global_v2::SpotSwapGlobalRejectedV2;
/// fn replace_post_root(rejected: &mut SpotSwapGlobalRejectedV2) {
///     rejected.post_state_root = rejected.pre_state_root.clone();
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpotSwapGlobalRejectedV2 {
    pub code: SpotSwapGlobalRejectCodeV2,
    pub pre_state_root: RootV2,
}

impl SpotSwapGlobalRejectedV2 {
    pub fn post_state_root(&self) -> &RootV2 {
        &self.pre_state_root
    }

    pub fn effects(&self) -> GlobalEconomicEffectPlanV2 {
        GlobalEconomicEffectPlanV2::empty()
    }
}

/// Complete accepted candidate. Getters return references to owned values;
/// the value confers no verifier or publication authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpotSwapGlobalAcceptedV2 {
    post_assets: AssetLaneCustodyStateV2,
    post_spot: SpotSwapStateV2,
    post_state: GlobalEconomicStateV2,
    effects: GlobalEconomicEffectPlanV2,
    refinement: GlobalEconomicStateEffectRefinementV2,
    statement_root: RootV2,
}

impl SpotSwapGlobalAcceptedV2 {
    fn new(
        post_assets: AssetLaneCustodyStateV2,
        post_spot: SpotSwapStateV2,
        pre_state: &GlobalEconomicStateV2,
        post_state: GlobalEconomicStateV2,
        effects: GlobalEconomicEffectPlanV2,
        occurrence: &EconomicCommandOccurrenceV2,
        statement_root: RootV2,
    ) -> AbiResultV2<Self> {
        post_assets.validate()?;
        post_spot.validate()?;
        post_state.validate()?;
        effects.validate()?;
        statement_root.validate("Spot input statement root", false)?;
        require_complete_asset_projection_v2(&post_assets, &post_state)?;
        require_spot_swap_projection_v2(&post_spot, &post_state)?;
        let terminal_plan = GlobalTerminalObligationPlanV2::empty();
        let oracle_plan = GlobalOracleOccurrencePlanV2::empty();
        let refinement = refine_global_economic_state_effects_v2(
            &GlobalEconomicStateEffectRefinementCandidateV2 {
                pre_state,
                post_state: &post_state,
                effect_plan: &effects,
                consumed_occurrences: std::slice::from_ref(occurrence),
                terminal_plan: &terminal_plan,
                oracle_plan: &oracle_plan,
            },
        )?;
        Ok(Self {
            post_assets,
            post_spot,
            post_state,
            effects,
            refinement,
            statement_root,
        })
    }

    pub fn post_assets(&self) -> &AssetLaneCustodyStateV2 {
        &self.post_assets
    }

    pub fn post_spot(&self) -> &SpotSwapStateV2 {
        &self.post_spot
    }

    pub fn post_state(&self) -> &GlobalEconomicStateV2 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV2 {
        &self.effects
    }

    pub fn refinement(&self) -> &GlobalEconomicStateEffectRefinementV2 {
        &self.refinement
    }

    pub fn refinement_root(&self) -> AbiResultV2<RootV2> {
        self.refinement.refinement_root()
    }

    pub fn statement_root(&self) -> &RootV2 {
        &self.statement_root
    }

    pub fn production_authority(&self) -> &'static str {
        self.refinement.production_authority()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum SpotSwapGlobalResultV2 {
    Accepted(Box<SpotSwapGlobalAcceptedV2>),
    Rejected(Box<SpotSwapGlobalRejectedV2>),
}

/// `_require_complete_projection`: the custody lane is the global economic frame.
pub fn require_complete_asset_projection_v2(
    assets: &AssetLaneCustodyStateV2,
    state: &GlobalEconomicStateV2,
) -> AbiResultV2<()> {
    let lane = state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == LaneIdV2::ASSET_TRANSFER)
        .ok_or(AbiErrorV2::InvalidBinding(
            "custody lane/global complete projection mismatch",
        ))?;
    let positive_supplies = assets.supplies().iter().filter(|row| row.amount_atoms != 0);
    if state.balances != assets.balances()
        || state.custody != assets.custody
        || !state.supplies.iter().eq(positive_supplies)
        || !state.reserves.is_empty()
        || lane.state_root != assets.state_root()?
        || lane.module_release_id != *assets.module_release_id()
        || !lane.enabled
    {
        return Err(AbiErrorV2::InvalidBinding(
            "custody lane/global complete projection mismatch",
        ));
    }
    Ok(())
}

/// `require_spot_swap_projection_v2`: single-pool custody is exact; share
/// claims live only in the Spot root and never as nominal pool atom claims.
pub fn require_spot_swap_projection_v2(
    spot: &SpotSwapStateV2,
    state: &GlobalEconomicStateV2,
) -> AbiResultV2<()> {
    let lane = state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == LaneIdV2::SPOT_LIQUIDITY)
        .ok_or(AbiErrorV2::InvalidBinding("Spot lane root missing"))?;
    if lane.module_release_id != spot.module_release_id
        || !lane.enabled
        || lane.state_root != spot.state_root()?
    {
        return Err(AbiErrorV2::InvalidBinding(
            "Spot lane root, release or enablement differs",
        ));
    }
    let pool_rows = state
        .custody
        .iter()
        .filter(|row| row.custody_domain == SPOT_POOL_CUSTODY_DOMAIN_V2)
        .map(
            |EconomicAmountV2 {
                 owner,
                 asset,
                 custody_domain: _,
                 amount_atoms,
             }| { (owner.as_str(), asset.as_str(), *amount_atoms) },
        );
    let pool = &spot.pool;
    let expected_rows = [
        (
            pool.pool_id.as_str(),
            pool.asset0.as_str(),
            u128::from(pool.reserve0),
        ),
        (
            pool.pool_id.as_str(),
            pool.asset1.as_str(),
            u128::from(pool.reserve1),
        ),
    ];
    if !pool_rows.eq(expected_rows) {
        return Err(AbiErrorV2::InvalidBinding(
            "Spot pool custody must equal its two reserves exactly",
        ));
    }
    if state
        .liabilities
        .iter()
        .any(|row| row.custody_domain == SPOT_POOL_CUSTODY_DOMAIN_V2)
        || state
            .terminal_obligations
            .iter()
            .any(|row| row.liability_domain == SPOT_POOL_CUSTODY_DOMAIN_V2)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "Spot share rights cannot coexist with nominal pool atom claims",
        ));
    }
    Ok(())
}

fn context_reject(
    state: &GlobalEconomicStateV2,
    state_root: &RootV2,
    intent: &SpotSwapIntentV2,
    occurrence: &EconomicCommandOccurrenceV2,
) -> AbiResultV2<Option<SpotSwapGlobalRejectKindV2>> {
    if occurrence.chain_id != state.chain_id
        || occurrence.deployment_root != state.deployment_root
        || occurrence.profile_root != state.profile_root
        || occurrence.pre_state_root != *state_root
        || Some(occurrence.height) != state.height.checked_add(1)
    {
        return Ok(Some(
            SpotSwapGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH,
        ));
    }
    let replay_id = occurrence.replay_id()?;
    let occurrence_id = occurrence.occurrence_id()?;
    if state
        .replay_state
        .iter()
        .any(|row| row.replay_id == replay_id.as_str() || row.occurrence_id == occurrence_id)
    {
        return Ok(Some(SpotSwapGlobalRejectKindV2::REPLAY_ALREADY_CONSUMED));
    }
    let body_hash = intent.command_body_hash()?;
    if !occurrence.consumed_object_ids.is_empty()
        || occurrence.command_kind != intent.command_kind()
        || occurrence.command_body_hash != body_hash
    {
        return Ok(Some(
            SpotSwapGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH,
        ));
    }
    Ok(None)
}

/// `_policy_reject`: origins must validate and both pool assets must be
/// enabled, non-native, eight-decimal and free of token transfer fees.
fn policy_reject(
    assets: &AssetLaneCustodyStateV2,
    spot: &SpotSwapStateV2,
) -> Option<SpotSwapGlobalRejectKindV2> {
    if !assets.policy_origin_bindings_hold() {
        return Some(SpotSwapGlobalRejectKindV2::ASSET_ORIGIN_MISMATCH);
    }
    for asset in [spot.pool.asset0.as_str(), spot.pool.asset1.as_str()] {
        let Some(policy) = assets
            .transfer_policies()
            .iter()
            .find(|policy| policy.asset == asset)
        else {
            return Some(SpotSwapGlobalRejectKindV2::UNSUPPORTED_ASSET_POLICY);
        };
        if !policy.enabled
            || policy.asset_class == AssetClassV2::TauNativeCoin
            || policy.atom_decimals != ASSET_ATOM_DECIMALS_V2
            || policy.transfer_fee_atoms != 0
        {
            return Some(SpotSwapGlobalRejectKindV2::UNSUPPORTED_ASSET_POLICY);
        }
    }
    None
}

fn account_balance(state: &GlobalEconomicStateV2, asset: &str, owner: &str) -> u128 {
    state
        .balances
        .iter()
        .find(|row| {
            row.asset == asset
                && row.owner == owner
                && row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V2
        })
        .map_or(0, |row| row.amount_atoms)
}

fn amount_key(row: &EconomicAmountV2) -> (&str, &str, &str) {
    (&row.asset, &row.owner, &row.custody_domain)
}

fn effect_kind_label(kind: EconomicEffectKindV2) -> &'static str {
    match kind {
        EconomicEffectKindV2::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV2::ISSUE => "ISSUE",
        EconomicEffectKindV2::BURN => "BURN",
        EconomicEffectKindV2::CUSTODY => "CUSTODY",
        EconomicEffectKindV2::LIABILITY => "LIABILITY",
        EconomicEffectKindV2::RESERVE => "RESERVE",
        EconomicEffectKindV2::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV2::REWARD => "REWARD",
        EconomicEffectKindV2::SLASH => "SLASH",
    }
}

fn effect_row_key(row: &EconomicEffectRowV2) -> (&'static str, &str, &str, &str) {
    (
        effect_kind_label(row.kind),
        &row.asset,
        &row.principal,
        &row.custody_domain,
    )
}

fn signed(value: u128, field: &'static str) -> AbiResultV2<i128> {
    i128::try_from(value).map_err(|_| AbiErrorV2::InvalidBounds(field))
}

fn successor_spot(
    spot: &SpotSwapStateV2,
    intent: &SpotSwapIntentV2,
    plan: &SpotSwapPlanV2,
) -> AbiResultV2<SpotSwapStateV2> {
    let mut nonces = spot
        .intent_nonces
        .iter()
        .map(|row| (row.owner.clone(), row.last_nonce))
        .collect::<BTreeMap<_, _>>();
    nonces.insert(intent.sender_pubkey().to_owned(), u64::from(plan.nonce()));
    let post_spot = SpotSwapStateV2 {
        schema: SPOT_SWAP_STATE_SCHEMA_V2.to_owned(),
        module_release_id: spot.module_release_id.clone(),
        pool: plan.post_pool().clone(),
        lp_positions: spot.lp_positions.clone(),
        intent_nonces: nonces
            .into_iter()
            .map(|(owner, last_nonce)| SpotIntentNonceV2 { owner, last_nonce })
            .collect(),
    };
    post_spot.validate()?;
    Ok(post_spot)
}

fn successor_balances(
    state: &GlobalEconomicStateV2,
    intent: &SpotSwapIntentV2,
    plan: &SpotSwapPlanV2,
) -> Vec<EconomicAmountV2> {
    let mut amounts = state
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
    amounts.insert(
        (
            intent.asset_in().to_owned(),
            intent.sender_pubkey().to_owned(),
            ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
        ),
        plan.post_sender_input_atoms(),
    );
    amounts.insert(
        (
            intent.asset_out().to_owned(),
            intent.recipient().to_owned(),
            ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
        ),
        plan.post_recipient_output_atoms(),
    );
    amounts
        .into_iter()
        .filter(|(_, amount_atoms)| *amount_atoms != 0)
        .map(
            |((asset, owner, custody_domain), amount_atoms)| EconomicAmountV2 {
                owner,
                asset,
                custody_domain,
                amount_atoms,
            },
        )
        .collect()
}

fn successor_custody(
    state: &GlobalEconomicStateV2,
    post_spot: &SpotSwapStateV2,
) -> Vec<EconomicAmountV2> {
    let mut custody = state
        .custody
        .iter()
        .filter(|row| row.custody_domain != SPOT_POOL_CUSTODY_DOMAIN_V2)
        .cloned()
        .collect::<Vec<_>>();
    custody.extend(post_spot.pool_holdings());
    custody.sort_by(|left, right| amount_key(left).cmp(&amount_key(right)));
    custody
}

fn successor_lane_roots(
    state: &GlobalEconomicStateV2,
    assets_root: &RootV2,
    spot_root: &RootV2,
) -> Vec<LaneStateRootV2> {
    state
        .lane_roots
        .iter()
        .map(|row| {
            let mut next = row.clone();
            match row.lane_id {
                LaneIdV2::ASSET_TRANSFER => next.state_root = assets_root.clone(),
                LaneIdV2::SPOT_LIQUIDITY => next.state_root = spot_root.clone(),
                _ => {}
            }
            next
        })
        .collect()
}

fn successor_replay_state(
    state: &GlobalEconomicStateV2,
    occurrence: &EconomicCommandOccurrenceV2,
) -> AbiResultV2<Vec<ReplayStateV2>> {
    let mut rows = state.replay_state.clone();
    rows.push(ReplayStateV2 {
        replay_id: occurrence.replay_id()?.to_string(),
        occurrence_id: occurrence.occurrence_id()?,
    });
    rows.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    Ok(rows)
}

fn effect_rows(
    spot: &SpotSwapStateV2,
    intent: &SpotSwapIntentV2,
    plan: &SpotSwapPlanV2,
) -> AbiResultV2<(Vec<EconomicEffectRowV2>, Vec<FeeConservationRowV2>)> {
    let amount_in = signed(plan.amount_in_atoms(), "Spot effect input delta")?;
    let amount_out = signed(plan.amount_out_atoms(), "Spot effect output delta")?;
    let fee = signed(plan.fee_atoms(), "Spot effect fee delta")?;
    let pool_id = spot.pool.pool_id.as_str();
    let mut rows = vec![
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: intent.sender_pubkey().to_owned(),
            asset: intent.asset_in().to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: -amount_in,
        },
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: intent.recipient().to_owned(),
            asset: intent.asset_out().to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: amount_out,
        },
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::CUSTODY,
            principal: pool_id.to_owned(),
            asset: intent.asset_in().to_owned(),
            custody_domain: SPOT_POOL_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: amount_in,
        },
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::CUSTODY,
            principal: pool_id.to_owned(),
            asset: intent.asset_out().to_owned(),
            custody_domain: SPOT_POOL_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: -amount_out,
        },
    ];
    let mut fees = Vec::new();
    if fee != 0 {
        rows.push(EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::FEE_ALLOCATION,
            principal: pool_id.to_owned(),
            asset: intent.asset_in().to_owned(),
            custody_domain: SPOT_POOL_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: fee,
        });
        fees.push(FeeConservationRowV2 {
            asset: intent.asset_in().to_owned(),
            fee_charged_atoms: plan.fee_atoms(),
            current_allocations_atoms: plan.fee_atoms(),
            carried_residue_atoms: 0,
        });
    }
    rows.sort_by(|left, right| effect_row_key(left).cmp(&effect_row_key(right)));
    Ok((rows, fees))
}

fn asset_conservation(
    state: &GlobalEconomicStateV2,
    intent: &SpotSwapIntentV2,
) -> AbiResultV2<Vec<AssetConservationRowV2>> {
    let supplies = state
        .supplies
        .iter()
        .map(|row| (row.asset.as_str(), row.amount_atoms))
        .collect::<BTreeMap<_, _>>();
    let mut assets = [intent.asset_in(), intent.asset_out()];
    assets.sort_unstable();
    assets
        .iter()
        .map(|asset| {
            let supply = supplies
                .get(asset)
                .copied()
                .ok_or(AbiErrorV2::InvalidBinding("Spot swap asset supply"))?;
            Ok(AssetConservationRowV2 {
                asset: (*asset).to_owned(),
                owned_and_custodied_pre_atoms: supply,
                owned_and_custodied_post_atoms: supply,
                supply_pre_atoms: supply,
                supply_post_atoms: supply,
                authorized_issue_atoms: 0,
                authorized_burn_atoms: 0,
            })
        })
        .collect()
}

fn lane_writes(before: &[LaneStateRootV2], after: &[LaneStateRootV2]) -> Vec<LaneWriteV2> {
    before
        .iter()
        .zip(after)
        .filter(|(left, right)| left.state_root != right.state_root)
        .map(|(left, right)| LaneWriteV2 {
            lane_id: left.lane_id,
            pre_root: left.state_root.clone(),
            post_root: right.state_root.clone(),
        })
        .collect()
}

/// `_project_successor`: the one complete candidate this relation admits.
fn project_successor(
    assets: &AssetLaneCustodyStateV2,
    spot: &SpotSwapStateV2,
    state: &GlobalEconomicStateV2,
    intent: &SpotSwapIntentV2,
    plan: &SpotSwapPlanV2,
    occurrence: &EconomicCommandOccurrenceV2,
    statement_root: RootV2,
) -> AbiResultV2<SpotSwapGlobalAcceptedV2> {
    let post_spot = successor_spot(spot, intent, plan)?;
    let balances = successor_balances(state, intent, plan);
    let custody = successor_custody(state, &post_spot);
    let mut transfer_state = assets.transfer_state.clone();
    transfer_state.balances = balances.clone();
    let post_assets = AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state,
        origin_registry: assets.origin_registry.clone(),
        managed_policies: assets.managed_policies.clone(),
        custody: custody.clone(),
    };
    let post_assets_root = post_assets.state_root()?;
    let post_spot_root = post_spot.state_root()?;
    let next_lane_roots = successor_lane_roots(state, &post_assets_root, &post_spot_root);
    let post_state = GlobalEconomicStateV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        writer_epoch: state.writer_epoch,
        height: state
            .height
            .checked_add(1)
            .ok_or(AbiErrorV2::InvalidBounds("global state height"))?,
        profile_root: state.profile_root.clone(),
        lane_roots: next_lane_roots.clone(),
        balances,
        supplies: state.supplies.clone(),
        custody,
        liabilities: state.liabilities.clone(),
        reserves: state.reserves.clone(),
        oracle_occurrences: state.oracle_occurrences.clone(),
        replay_state: successor_replay_state(state, occurrence)?,
        terminal_obligations: state.terminal_obligations.clone(),
        history_root: state.history_root.clone(),
        outbox: state.outbox.clone(),
    };
    let (rows, fee_conservation) = effect_rows(spot, intent, plan)?;
    let effects = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows,
        asset_conservation: asset_conservation(state, intent)?,
        fee_conservation,
        lane_writes: lane_writes(&state.lane_roots, &next_lane_roots),
        occurrence_consumptions: vec![occurrence.occurrence_id()?],
        external_outbox_enqueue: Vec::new(),
    };
    SpotSwapGlobalAcceptedV2::new(
        post_assets,
        post_spot,
        state,
        post_state,
        effects,
        occurrence,
        statement_root,
    )
}

#[derive(Serialize)]
struct StatementBodyV2<'a> {
    pre_state_root: &'a RootV2,
    command: SpotSwapCommandBodyV2<'a>,
    occurrence: &'a EconomicCommandOccurrenceV2,
    block_timestamp: u64,
}

fn reject(
    state_root: &RootV2,
    code: SpotSwapGlobalRejectCodeV2,
) -> Result<SpotSwapGlobalResultV2, SpotSwapInputErrorV2> {
    Ok(SpotSwapGlobalResultV2::Rejected(Box::new(
        SpotSwapGlobalRejectedV2 {
            code,
            pre_state_root: state_root.clone(),
        },
    )))
}

/// Derive one complete candidate or an exact logical no-op.
///
/// Malformed typed values return `SpotSwapInputErrorV2` at the same point
/// where the Python transition raises. Inner intent nonces require `last + 1`;
/// outer replay nonces remain independent. Neither nonce is consumed on
/// rejection. Timestamp provenance must be checked by the future shell.
pub fn transition_spot_swap_global_v2(
    assets: &AssetLaneCustodyStateV2,
    spot: &SpotSwapStateV2,
    state: &GlobalEconomicStateV2,
    intent: &SpotSwapIntentV2,
    occurrence: &EconomicCommandOccurrenceV2,
    block_timestamp: u64,
) -> Result<SpotSwapGlobalResultV2, SpotSwapInputErrorV2> {
    assets.validate().map_err(SpotSwapInputErrorV2::Assets)?;
    spot.validate().map_err(SpotSwapInputErrorV2::SpotState)?;
    state
        .validate()
        .map_err(SpotSwapInputErrorV2::GlobalState)?;
    occurrence
        .validate()
        .map_err(SpotSwapInputErrorV2::Occurrence)?;
    intent.validate().map_err(SpotSwapInputErrorV2::Intent)?;
    let state_root = state.state_root().map_err(SpotSwapInputErrorV2::Internal)?;

    if intent
        .field_profile()
        .map_err(SpotSwapInputErrorV2::Intent)?
        == SwapIntentFieldProfileV2::Unsupported
    {
        return reject(
            &state_root,
            SpotSwapGlobalRejectCodeV2::Swap(SpotSwapRejectCodeV2::UNSUPPORTED_FIELDS),
        );
    }
    if let Some(kind) = context_reject(state, &state_root, intent, occurrence)
        .map_err(SpotSwapInputErrorV2::Internal)?
    {
        return reject(&state_root, SpotSwapGlobalRejectCodeV2::Global(kind));
    }
    if require_complete_asset_projection_v2(assets, state).is_err()
        || require_spot_swap_projection_v2(spot, state).is_err()
    {
        return reject(
            &state_root,
            SpotSwapGlobalRejectCodeV2::Global(SpotSwapGlobalRejectKindV2::PROJECTION_MISMATCH),
        );
    }
    if let Some(kind) = policy_reject(assets, spot) {
        return reject(&state_root, SpotSwapGlobalRejectCodeV2::Global(kind));
    }
    validate_spot_owner_v2(intent.sender_pubkey(), "Spot swap sender")
        .map_err(SpotSwapInputErrorV2::SenderIdentity)?;
    validate_spot_owner_v2(intent.recipient(), "Spot swap recipient")
        .map_err(SpotSwapInputErrorV2::RecipientIdentity)?;

    let context = SpotSwapContextV2 {
        subject_id: occurrence.subject_id.clone(),
        block_timestamp,
        sender_input_atoms: account_balance(state, intent.asset_in(), intent.sender_pubkey()),
        recipient_output_atoms: account_balance(state, intent.asset_out(), intent.recipient()),
    };
    let plan = match plan_spot_swap_v2(&context, &spot.pool, intent)
        .map_err(SpotSwapInputErrorV2::Internal)?
    {
        SpotSwapPlanResultV2::Rejected(code) => {
            return reject(&state_root, SpotSwapGlobalRejectCodeV2::Swap(code))
        }
        SpotSwapPlanResultV2::Planned(plan) => plan,
    };
    let expected_nonce = spot.intent_nonce(intent.sender_pubkey()).checked_add(1);
    if expected_nonce != Some(u64::from(plan.nonce())) {
        return reject(
            &state_root,
            SpotSwapGlobalRejectCodeV2::Swap(SpotSwapRejectCodeV2::INVALID_NONCE),
        );
    }
    let statement_root = hash_global_v2(
        SPOT_SWAP_GLOBAL_STATEMENT_DOMAIN_V2,
        &StatementBodyV2 {
            pre_state_root: &state_root,
            command: intent.command_body(),
            occurrence,
            block_timestamp,
        },
    )
    .map_err(SpotSwapInputErrorV2::Internal)?;
    match project_successor(
        assets,
        spot,
        state,
        intent,
        &plan,
        occurrence,
        statement_root,
    ) {
        Ok(accepted) => Ok(SpotSwapGlobalResultV2::Accepted(Box::new(accepted))),
        Err(_) => reject(
            &state_root,
            SpotSwapGlobalRejectCodeV2::Global(SpotSwapGlobalRejectKindV2::SUCCESSOR_REJECTED),
        ),
    }
}
