//! Pure joint PERPS_MARGIN and ASSET_TRANSFER successor for GlobalSettlementABI V2.
//!
//! V1 remains the economic decision kernel.  This module reconstructs all V2
//! tables, lane writes, replay commitment, terminal plan, and shared
//! refinement input.  It creates no receipt, authentication witness, or
//! publication authority.

use std::collections::BTreeMap;

use serde::Serialize;
use zenodex_global_settlement_abi_v1::{
    transition_perps_margin_v1, AbiErrorV1, AbiResultV1, PerpsMarginCommandV1,
    PerpsMarginContextV1, PerpsMarginRejectCodeV1, PerpsMarginResultV1, PerpsMarginStateV1, RootV1,
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, ZERO_ROOT_V1,
};
use zenodex_global_settlement_abi_v2::{
    hash_economic_command_body_v2, hash_global_v2, refine_global_economic_state_effects_v2,
    AbiErrorV2, AbiResultV2, AssetClassV2, AssetConservationRowV2, AssetLaneCustodyStateV2,
    AssetTransferStateV2, EconomicAmountV2, EconomicCommandOccurrenceV2, EconomicEffectKindV2,
    EconomicEffectRowV2, GlobalEconomicEffectPlanV2,
    GlobalEconomicStateEffectRefinementCandidateV2, GlobalEconomicStateEffectRefinementV2,
    GlobalEconomicStateV2, GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2, LaneIdV2,
    LaneWriteV2, ReplayStateV2, RootV2, ACCOUNT_CUSTODY_DOMAIN_V2, ASSET_ATOM_DECIMALS_V2,
    ASSET_LANE_CUSTODY_STATE_SCHEMA_V2, GLOBAL_SETTLEMENT_ABI_V2,
};

use crate::claims::{
    advance_margin_claims_v2, derive_terminal_plan_v2, require_margin_claim_projection_v2,
};
use crate::state::PerpsMarginStateV2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum PerpsMarginGlobalRejectKindV2 {
    OCCURRENCE_CONTEXT_MISMATCH,
    REPLAY_ALREADY_CONSUMED,
    OCCURRENCE_COMMAND_MISMATCH,
    PROJECTION_MISMATCH,
    ASSET_ORIGIN_MISMATCH,
    UNKNOWN_COLLATERAL,
    DISABLED_COLLATERAL,
    UNSUPPORTED_COLLATERAL,
    INSUFFICIENT_BALANCE,
    SUCCESSOR_REJECTED,
}

impl PerpsMarginGlobalRejectKindV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::OCCURRENCE_CONTEXT_MISMATCH => "OCCURRENCE_CONTEXT_MISMATCH",
            Self::REPLAY_ALREADY_CONSUMED => "REPLAY_ALREADY_CONSUMED",
            Self::OCCURRENCE_COMMAND_MISMATCH => "OCCURRENCE_COMMAND_MISMATCH",
            Self::PROJECTION_MISMATCH => "PROJECTION_MISMATCH",
            Self::ASSET_ORIGIN_MISMATCH => "ASSET_ORIGIN_MISMATCH",
            Self::UNKNOWN_COLLATERAL => "UNKNOWN_COLLATERAL",
            Self::DISABLED_COLLATERAL => "DISABLED_COLLATERAL",
            Self::UNSUPPORTED_COLLATERAL => "UNSUPPORTED_COLLATERAL",
            Self::INSUFFICIENT_BALANCE => "INSUFFICIENT_BALANCE",
            Self::SUCCESSOR_REJECTED => "SUCCESSOR_REJECTED",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginGlobalRejectCodeV2 {
    Global(PerpsMarginGlobalRejectKindV2),
    Margin(PerpsMarginRejectCodeV1),
}

impl PerpsMarginGlobalRejectCodeV2 {
    pub const fn global(kind: PerpsMarginGlobalRejectKindV2) -> Self {
        Self::Global(kind)
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Global(kind) => kind.as_str(),
            Self::Margin(code) => match code {
                PerpsMarginRejectCodeV1::RELEASE_MISMATCH => "RELEASE_MISMATCH",
                PerpsMarginRejectCodeV1::UNKNOWN_COMMAND => "UNKNOWN_COMMAND",
                PerpsMarginRejectCodeV1::MARKET_DRAIN_ONLY => "MARKET_DRAIN_ONLY",
                PerpsMarginRejectCodeV1::HALTED_MARKET => "HALTED_MARKET",
                PerpsMarginRejectCodeV1::MARKET_MISMATCH => "MARKET_MISMATCH",
                PerpsMarginRejectCodeV1::ASSET_MISMATCH => "ASSET_MISMATCH",
                PerpsMarginRejectCodeV1::UNAUTHORIZED_SUBJECT => "UNAUTHORIZED_SUBJECT",
                PerpsMarginRejectCodeV1::ORACLE_AUTHORITY_MISSING => "ORACLE_AUTHORITY_MISSING",
                PerpsMarginRejectCodeV1::ORACLE_PRICE_MISMATCH => "ORACLE_PRICE_MISMATCH",
                PerpsMarginRejectCodeV1::UNEXPECTED_ORACLE_AUTHORITY => {
                    "UNEXPECTED_ORACLE_AUTHORITY"
                }
                PerpsMarginRejectCodeV1::ACCOUNT_MISSING => "ACCOUNT_MISSING",
                PerpsMarginRejectCodeV1::ACCOUNT_OWNER_MISMATCH => "ACCOUNT_OWNER_MISMATCH",
                PerpsMarginRejectCodeV1::ACCOUNT_CLOSED => "ACCOUNT_CLOSED",
                PerpsMarginRejectCodeV1::ACCOUNT_LIMIT => "ACCOUNT_LIMIT",
                PerpsMarginRejectCodeV1::NONCE_MISMATCH => "NONCE_MISMATCH",
                PerpsMarginRejectCodeV1::NONCE_OVERFLOW => "NONCE_OVERFLOW",
                PerpsMarginRejectCodeV1::ZERO_AMOUNT => "ZERO_AMOUNT",
                PerpsMarginRejectCodeV1::INVALID_CLOSE_AMOUNT => "INVALID_CLOSE_AMOUNT",
                PerpsMarginRejectCodeV1::EFFECT_DELTA_OVERFLOW => "EFFECT_DELTA_OVERFLOW",
                PerpsMarginRejectCodeV1::BALANCE_OVERFLOW => "BALANCE_OVERFLOW",
                PerpsMarginRejectCodeV1::INSUFFICIENT_COLLATERAL => "INSUFFICIENT_COLLATERAL",
                PerpsMarginRejectCodeV1::MAINTENANCE_BREACH => "MAINTENANCE_BREACH",
                PerpsMarginRejectCodeV1::POSITION_OPEN => "POSITION_OPEN",
                PerpsMarginRejectCodeV1::COLLATERAL_REMAINS => "COLLATERAL_REMAINS",
                PerpsMarginRejectCodeV1::ARITHMETIC_OVERFLOW => "ARITHMETIC_OVERFLOW",
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct PerpsMarginOracleV2 {
    pub authority_root: RootV2,
    pub occurrence_root: RootV2,
    pub price_e8: u128,
}

impl PerpsMarginOracleV2 {
    pub fn new(
        authority_root: RootV2,
        occurrence_root: RootV2,
        price_e8: u128,
    ) -> AbiResultV2<Self> {
        let value = Self {
            authority_root,
            occurrence_root,
            price_e8,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        self.authority_root
            .validate("margin oracle authority root", false)?;
        self.occurrence_root
            .validate("margin oracle occurrence root", false)?;
        if self.price_e8 == 0 {
            return Err(AbiErrorV2::InvalidBounds("margin oracle price"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PerpsMarginGlobalRejectedV2 {
    pub code: PerpsMarginGlobalRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
}

impl PerpsMarginGlobalRejectedV2 {
    fn new(
        state: &GlobalEconomicStateV2,
        code: PerpsMarginGlobalRejectCodeV2,
    ) -> AbiResultV2<Self> {
        let root = state.state_root()?;
        Ok(Self {
            code,
            pre_state_root: root.clone(),
            post_state_root: root,
        })
    }

    pub fn effects(&self) -> GlobalEconomicEffectPlanV2 {
        GlobalEconomicEffectPlanV2::empty()
    }

    pub fn terminal_plan(&self) -> GlobalTerminalObligationPlanV2 {
        GlobalTerminalObligationPlanV2::empty()
    }

    pub fn oracle_plan(&self) -> GlobalOracleOccurrencePlanV2 {
        GlobalOracleOccurrencePlanV2::empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PerpsMarginGlobalAcceptedV2 {
    post_assets: AssetLaneCustodyStateV2,
    post_margin: PerpsMarginStateV2,
    post_state: GlobalEconomicStateV2,
    effects: GlobalEconomicEffectPlanV2,
    terminal_plan: GlobalTerminalObligationPlanV2,
    refinement: GlobalEconomicStateEffectRefinementV2,
    statement_root: RootV2,
}

impl PerpsMarginGlobalAcceptedV2 {
    fn new(
        post_assets: AssetLaneCustodyStateV2,
        post_margin: PerpsMarginStateV2,
        post_state: GlobalEconomicStateV2,
        effects: GlobalEconomicEffectPlanV2,
        terminal_plan: GlobalTerminalObligationPlanV2,
        refinement: GlobalEconomicStateEffectRefinementV2,
        statement_root: RootV2,
    ) -> AbiResultV2<Self> {
        post_assets.validate()?;
        post_margin.validate()?;
        post_state.validate()?;
        effects.validate()?;
        terminal_plan.validate()?;
        statement_root.validate("perps margin global statement root", false)?;
        if refinement.post_state_root() != &post_state.state_root()?
            || refinement.effect_plan_root() != &effects.effect_plan_root()?
            || refinement.terminal_plan_root() != &terminal_plan.plan_root()?
        {
            return Err(AbiErrorV2::InvalidBinding(
                "margin global refinement output mismatch",
            ));
        }
        require_complete_asset_projection(&post_assets, &post_state)?;
        require_margin_claim_projection_v2(&post_margin, &post_state)?;
        Ok(Self {
            post_assets,
            post_margin,
            post_state,
            effects,
            terminal_plan,
            refinement,
            statement_root,
        })
    }

    pub fn post_assets(&self) -> &AssetLaneCustodyStateV2 {
        &self.post_assets
    }

    pub fn post_margin(&self) -> &PerpsMarginStateV2 {
        &self.post_margin
    }

    pub fn post_state(&self) -> &GlobalEconomicStateV2 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV2 {
        &self.effects
    }

    pub fn terminal_plan(&self) -> &GlobalTerminalObligationPlanV2 {
        &self.terminal_plan
    }

    pub fn refinement(&self) -> &GlobalEconomicStateEffectRefinementV2 {
        &self.refinement
    }

    pub fn statement_root(&self) -> &RootV2 {
        &self.statement_root
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PerpsMarginGlobalResultV2 {
    Accepted(Box<PerpsMarginGlobalAcceptedV2>),
    Rejected(Box<PerpsMarginGlobalRejectedV2>),
}

fn reject(
    state: &GlobalEconomicStateV2,
    code: PerpsMarginGlobalRejectCodeV2,
) -> AbiResultV2<PerpsMarginGlobalResultV2> {
    Ok(PerpsMarginGlobalResultV2::Rejected(Box::new(
        PerpsMarginGlobalRejectedV2::new(state, code)?,
    )))
}

fn require_complete_asset_projection(
    assets: &AssetLaneCustodyStateV2,
    state: &GlobalEconomicStateV2,
) -> AbiResultV2<()> {
    let lane = state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == LaneIdV2::ASSET_TRANSFER)
        .ok_or(AbiErrorV2::InvalidBinding("asset lane/global root missing"))?;
    let positive_supplies = assets
        .supplies()
        .iter()
        .filter(|row| row.amount_atoms > 0)
        .cloned()
        .collect::<Vec<_>>();
    if state.balances != assets.balances()
        || state.custody != assets.custody
        || state.supplies != positive_supplies
        || !state.reserves.is_empty()
        || lane.state_root != assets.state_root()?
        || lane.module_release_id != *assets.module_release_id()
        || !lane.enabled
    {
        return Err(AbiErrorV2::InvalidBinding(
            "asset lane/global complete projection mismatch",
        ));
    }
    Ok(())
}

fn context_reject(
    state: &GlobalEconomicStateV2,
    state_root: &RootV2,
    command: &PerpsMarginCommandV1,
    occurrence: &EconomicCommandOccurrenceV2,
) -> AbiResultV2<Option<PerpsMarginGlobalRejectKindV2>> {
    if occurrence.chain_id != state.chain_id
        || occurrence.deployment_root != state.deployment_root
        || occurrence.profile_root != state.profile_root
        || occurrence.pre_state_root != *state_root
        || Some(occurrence.height) != state.height.checked_add(1)
    {
        return Ok(Some(
            PerpsMarginGlobalRejectKindV2::OCCURRENCE_CONTEXT_MISMATCH,
        ));
    }
    let replay_id = occurrence.replay_id()?;
    let occurrence_id = occurrence.occurrence_id()?;
    if state
        .replay_state
        .iter()
        .any(|row| row.replay_id == replay_id.to_string() || row.occurrence_id == occurrence_id)
    {
        return Ok(Some(PerpsMarginGlobalRejectKindV2::REPLAY_ALREADY_CONSUMED));
    }
    let body_hash = hash_economic_command_body_v2(&command.command_kind, command)
        .map_err(|_| AbiErrorV2::InvalidBinding("perps margin command body"))?;
    if !occurrence.consumed_object_ids.is_empty()
        || occurrence.command_kind != command.command_kind
        || occurrence.command_body_hash != body_hash
    {
        return Ok(Some(
            PerpsMarginGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH,
        ));
    }
    Ok(None)
}

fn collateral_reject(
    assets: &AssetLaneCustodyStateV2,
    margin: &PerpsMarginStateV2,
) -> Option<PerpsMarginGlobalRejectKindV2> {
    if !assets.policy_origin_bindings_hold() {
        return Some(PerpsMarginGlobalRejectKindV2::ASSET_ORIGIN_MISMATCH);
    }
    let asset = &margin.economic_state.collateral_asset;
    let Some(policy) = assets
        .transfer_policies()
        .iter()
        .find(|policy| policy.asset == *asset)
    else {
        return Some(PerpsMarginGlobalRejectKindV2::UNKNOWN_COLLATERAL);
    };
    if !policy.enabled {
        return Some(PerpsMarginGlobalRejectKindV2::DISABLED_COLLATERAL);
    }
    if policy.asset_class == AssetClassV2::TauNativeCoin
        || policy.atom_decimals != ASSET_ATOM_DECIMALS_V2
    {
        return Some(PerpsMarginGlobalRejectKindV2::UNSUPPORTED_COLLATERAL);
    }
    None
}

fn v1_root(root: &RootV2, field: &'static str, allow_zero: bool) -> AbiResultV1<RootV1> {
    RootV1::parse(root.as_str().to_owned(), field, allow_zero)
}

fn v1_zero_root(field: &'static str) -> AbiResultV1<RootV1> {
    RootV1::parse(ZERO_ROOT_V1.to_owned(), field, true)
}

fn v1_context(
    state: &GlobalEconomicStateV2,
    margin: &PerpsMarginStateV2,
    occurrence: &EconomicCommandOccurrenceV2,
    oracle: Option<&PerpsMarginOracleV2>,
) -> Result<PerpsMarginContextV1, AbiErrorV2> {
    let occurrence_id = occurrence.occurrence_id()?;
    Ok(PerpsMarginContextV1 {
        chain_id: state.chain_id.clone(),
        deployment_root: v1_root(&state.deployment_root, "V1 deployment root", false)
            .map_err(|_| AbiErrorV2::InvalidRoot("V1 deployment root"))?,
        profile_root: v1_root(&state.profile_root, "V1 profile root", false)
            .map_err(|_| AbiErrorV2::InvalidRoot("V1 profile root"))?,
        writer_epoch: state.writer_epoch,
        module_release_id: margin.economic_state.module_release_id.clone(),
        command_occurrence_id: v1_root(&occurrence_id, "V1 occurrence id", false)
            .map_err(|_| AbiErrorV2::InvalidRoot("V1 occurrence id"))?,
        subject_id: occurrence.subject_id.clone(),
        grant_root: v1_root(&occurrence.grant_root, "V1 grant root", false)
            .map_err(|_| AbiErrorV2::InvalidRoot("V1 grant root"))?,
        oracle_authority_root: match oracle {
            Some(value) => v1_root(&value.authority_root, "V1 Oracle authority root", false)
                .map_err(|_| AbiErrorV2::InvalidRoot("V1 Oracle authority root"))?,
            None => v1_zero_root("V1 Oracle authority root")
                .map_err(|_| AbiErrorV2::InvalidRoot("V1 Oracle authority root"))?,
        },
        oracle_occurrence_root: match oracle {
            Some(value) => v1_root(&value.occurrence_root, "V1 Oracle occurrence root", false)
                .map_err(|_| AbiErrorV2::InvalidRoot("V1 Oracle occurrence root"))?,
            None => v1_zero_root("V1 Oracle occurrence root")
                .map_err(|_| AbiErrorV2::InvalidRoot("V1 Oracle occurrence root"))?,
        },
        oracle_price_e8: oracle.map(|value| value.price_e8).unwrap_or(0),
    })
}

fn command_effect_rows(command: &PerpsMarginCommandV1) -> AbiResultV2<Vec<EconomicEffectRowV2>> {
    if command.command_kind == PERPS_MARGIN_CLOSE_COMMAND_KIND_V1 {
        return Ok(Vec::new());
    }
    let magnitude = i128::try_from(command.amount_atoms)
        .map_err(|_| AbiErrorV2::InvalidBounds("margin effect delta"))?;
    let delta = if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 {
        magnitude
    } else {
        -magnitude
    };
    Ok(vec![
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: command.owner.clone(),
            asset: command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: -delta,
        },
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::CUSTODY,
            principal: command.account_id.clone(),
            asset: command.asset.clone(),
            custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: delta,
        },
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::LIABILITY,
            principal: command.owner.clone(),
            asset: command.asset.clone(),
            custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: delta,
        },
    ])
}

fn apply_delta(value: u128, delta: i128) -> AbiResultV2<u128> {
    if delta >= 0 {
        value
            .checked_add(delta as u128)
            .ok_or(AbiErrorV2::InvalidBounds("margin amount overflow"))
    } else {
        value
            .checked_sub(delta.unsigned_abs())
            .ok_or(AbiErrorV2::InvalidBinding("margin amount underflow"))
    }
}

fn apply_amount_rows(
    table: &[EconomicAmountV2],
    rows: &[EconomicEffectRowV2],
    kind: EconomicEffectKindV2,
) -> AbiResultV2<Vec<EconomicAmountV2>> {
    let mut values = table
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
    for row in rows.iter().filter(|row| row.kind == kind) {
        let key = (
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let value = apply_delta(values.get(&key).copied().unwrap_or(0), row.delta_atoms)?;
        values.insert(key, value);
    }
    Ok(values
        .into_iter()
        .filter(|(_, amount)| *amount > 0)
        .map(
            |((asset, owner, custody_domain), amount_atoms)| EconomicAmountV2 {
                owner,
                asset,
                custody_domain,
                amount_atoms,
            },
        )
        .collect())
}

fn totals_by_asset(
    balances: &[EconomicAmountV2],
    custody: &[EconomicAmountV2],
    reserves: &[EconomicAmountV2],
) -> AbiResultV2<BTreeMap<String, u128>> {
    let mut totals = BTreeMap::<String, u128>::new();
    for row in balances.iter().chain(custody).chain(reserves) {
        let total = totals
            .get(&row.asset)
            .copied()
            .unwrap_or(0)
            .checked_add(row.amount_atoms)
            .ok_or(AbiErrorV2::Conservation("margin owned amount overflow"))?;
        totals.insert(row.asset.clone(), total);
    }
    Ok(totals)
}

fn lane_roots(
    pre: &[zenodex_global_settlement_abi_v2::LaneStateRootV2],
    assets_root: &RootV2,
    margin_root: &RootV2,
) -> Vec<zenodex_global_settlement_abi_v2::LaneStateRootV2> {
    pre.iter()
        .map(|row| {
            let mut next = row.clone();
            match row.lane_id {
                LaneIdV2::ASSET_TRANSFER => next.state_root = assets_root.clone(),
                LaneIdV2::PERPS_MARKET => next.state_root = margin_root.clone(),
                _ => {}
            }
            next
        })
        .collect()
}

fn lane_writes(
    before: &[zenodex_global_settlement_abi_v2::LaneStateRootV2],
    after: &[zenodex_global_settlement_abi_v2::LaneStateRootV2],
) -> Vec<LaneWriteV2> {
    let mut writes = before
        .iter()
        .zip(after)
        .filter(|(left, right)| left.state_root != right.state_root)
        .map(|(left, right)| LaneWriteV2 {
            lane_id: left.lane_id,
            pre_root: left.state_root.clone(),
            post_root: right.state_root.clone(),
        })
        .collect::<Vec<_>>();
    writes.sort_by_key(|row| row.lane_id.as_str());
    writes
}

fn replay_state(
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

fn project_successor(
    assets: &AssetLaneCustodyStateV2,
    margin: &PerpsMarginStateV2,
    state: &GlobalEconomicStateV2,
    command: &PerpsMarginCommandV1,
    occurrence: &EconomicCommandOccurrenceV2,
    economic_post: PerpsMarginStateV1,
) -> AbiResultV2<(
    AssetLaneCustodyStateV2,
    PerpsMarginStateV2,
    GlobalEconomicStateV2,
    GlobalEconomicEffectPlanV2,
    GlobalTerminalObligationPlanV2,
    GlobalEconomicStateEffectRefinementV2,
)> {
    let rows = command_effect_rows(command)?;
    let balances = apply_amount_rows(
        &state.balances,
        &rows,
        EconomicEffectKindV2::ACCOUNT_MOVEMENT,
    )?;
    let custody = apply_amount_rows(&state.custody, &rows, EconomicEffectKindV2::CUSTODY)?;
    let liabilities =
        apply_amount_rows(&state.liabilities, &rows, EconomicEffectKindV2::LIABILITY)?;
    let occurrence_id = occurrence.occurrence_id()?;
    let (post_margin, terminals) = advance_margin_claims_v2(
        margin,
        economic_post,
        &state.terminal_obligations,
        &command.account_id,
        &occurrence_id,
    )?;

    let mut transfer_state: AssetTransferStateV2 = assets.transfer_state.clone();
    transfer_state.balances = balances.clone();
    let post_assets = AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state,
        origin_registry: assets.origin_registry.clone(),
        managed_policies: assets.managed_policies.clone(),
        custody: custody.clone(),
    };
    let post_assets_root = post_assets.state_root()?;
    let post_margin_root = post_margin.state_root()?;
    let next_lane_roots = lane_roots(&state.lane_roots, &post_assets_root, &post_margin_root);
    let replay = replay_state(state, occurrence)?;
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
        liabilities,
        reserves: state.reserves.clone(),
        oracle_occurrences: state.oracle_occurrences.clone(),
        replay_state: replay,
        terminal_obligations: terminals.clone(),
        history_root: state.history_root.clone(),
        outbox: state.outbox.clone(),
    };
    post_state.validate()?;

    let writes = lane_writes(&state.lane_roots, &next_lane_roots);
    let conservation = if rows.is_empty() {
        Vec::new()
    } else {
        let pre_totals = totals_by_asset(&state.balances, &state.custody, &state.reserves)?;
        let post_totals = totals_by_asset(
            &post_state.balances,
            &post_state.custody,
            &post_state.reserves,
        )?;
        let supply = state
            .supplies
            .iter()
            .find(|row| row.asset == command.asset)
            .map(|row| row.amount_atoms)
            .unwrap_or(0);
        vec![AssetConservationRowV2 {
            asset: command.asset.clone(),
            owned_and_custodied_pre_atoms: pre_totals.get(&command.asset).copied().unwrap_or(0),
            owned_and_custodied_post_atoms: post_totals.get(&command.asset).copied().unwrap_or(0),
            supply_pre_atoms: supply,
            supply_post_atoms: supply,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        }]
    };
    let effects = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows,
        asset_conservation: conservation,
        fee_conservation: Vec::new(),
        lane_writes: writes,
        occurrence_consumptions: vec![occurrence_id.clone()],
        external_outbox_enqueue: Vec::new(),
    };
    let terminal_deltas = derive_terminal_plan_v2(&state.terminal_obligations, &terminals)?;
    let terminal_plan = GlobalTerminalObligationPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        deltas: terminal_deltas,
    };
    require_complete_asset_projection(&post_assets, &post_state)?;
    require_margin_claim_projection_v2(&post_margin, &post_state)?;
    let oracle_plan = GlobalOracleOccurrencePlanV2::empty();
    let refinement =
        refine_global_economic_state_effects_v2(&GlobalEconomicStateEffectRefinementCandidateV2 {
            pre_state: state,
            post_state: &post_state,
            effect_plan: &effects,
            consumed_occurrences: std::slice::from_ref(occurrence),
            terminal_plan: &terminal_plan,
            oracle_plan: &oracle_plan,
        })?;
    Ok((
        post_assets,
        post_margin,
        post_state,
        effects,
        terminal_plan,
        refinement,
    ))
}

#[derive(Serialize)]
struct StatementBodyV2<'a> {
    schema: &'static str,
    pre_state_root: &'a RootV2,
    command: &'a PerpsMarginCommandV1,
    occurrence: &'a EconomicCommandOccurrenceV2,
    oracle: &'a Option<PerpsMarginOracleV2>,
}

fn map_v1_error(_: AbiErrorV1) -> AbiErrorV2 {
    AbiErrorV2::InvalidBinding("V1 margin kernel input evaluation")
}

/// Recompute one complete joint V2 candidate with ordered no-op rejections.
pub fn transition_perps_margin_global_v2(
    assets: &AssetLaneCustodyStateV2,
    margin: &PerpsMarginStateV2,
    state: &GlobalEconomicStateV2,
    command: &PerpsMarginCommandV1,
    occurrence: &EconomicCommandOccurrenceV2,
    oracle: Option<&PerpsMarginOracleV2>,
) -> AbiResultV2<PerpsMarginGlobalResultV2> {
    assets.validate()?;
    margin.validate()?;
    state.validate()?;
    command
        .command_body_hash()
        .map_err(|_| AbiErrorV2::InvalidBinding("perps margin command"))?;
    occurrence.validate()?;
    if let Some(value) = oracle {
        value.validate()?;
    }

    let state_root = state.state_root()?;
    if let Some(code) = context_reject(state, &state_root, command, occurrence)? {
        return reject(state, PerpsMarginGlobalRejectCodeV2::global(code));
    }
    if require_complete_asset_projection(assets, state).is_err()
        || require_margin_claim_projection_v2(margin, state).is_err()
    {
        return reject(
            state,
            PerpsMarginGlobalRejectCodeV2::global(
                PerpsMarginGlobalRejectKindV2::PROJECTION_MISMATCH,
            ),
        );
    }
    if let Some(code) = collateral_reject(assets, margin) {
        return reject(state, PerpsMarginGlobalRejectCodeV2::global(code));
    }

    let context = v1_context(state, margin, occurrence, oracle)?;
    let economic = transition_perps_margin_v1(&context, &margin.economic_state, command)
        .map_err(map_v1_error)?;
    let economic_post = match economic {
        PerpsMarginResultV1::Rejected(rejected) => {
            return reject(state, PerpsMarginGlobalRejectCodeV2::Margin(rejected.code))
        }
        PerpsMarginResultV1::Accepted(accepted) => accepted.post_state.clone(),
    };
    if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 {
        let balance = state
            .balances
            .iter()
            .find(|row| {
                row.owner == command.owner
                    && row.asset == command.asset
                    && row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V2
            })
            .map(|row| row.amount_atoms)
            .unwrap_or(0);
        if balance < command.amount_atoms {
            return reject(
                state,
                PerpsMarginGlobalRejectCodeV2::global(
                    PerpsMarginGlobalRejectKindV2::INSUFFICIENT_BALANCE,
                ),
            );
        }
    }

    let projected =
        match project_successor(assets, margin, state, command, occurrence, economic_post) {
            Ok(value) => value,
            Err(_) => {
                return reject(
                    state,
                    PerpsMarginGlobalRejectCodeV2::global(
                        PerpsMarginGlobalRejectKindV2::SUCCESSOR_REJECTED,
                    ),
                )
            }
        };
    let statement_oracle = oracle.cloned();
    let statement_root = hash_global_v2(
        "perps-margin-global-statement-v2",
        &StatementBodyV2 {
            schema: "zenodex/perps-margin-global-input/v2",
            pre_state_root: &state_root,
            command,
            occurrence,
            oracle: &statement_oracle,
        },
    )?;
    let (post_assets, post_margin, post_state, effects, terminal_plan, refinement) = projected;
    Ok(PerpsMarginGlobalResultV2::Accepted(Box::new(
        PerpsMarginGlobalAcceptedV2::new(
            post_assets,
            post_margin,
            post_state,
            effects,
            terminal_plan,
            refinement,
            statement_root,
        )?,
    )))
}
