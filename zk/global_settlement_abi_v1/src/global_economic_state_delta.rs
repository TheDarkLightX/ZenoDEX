//! Internal derivation of supported global economic state deltas.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::effects::{EconomicEffectKindV1, GlobalEconomicEffectPlanV1, LaneWriteV1};
use crate::state::{EconomicAmountV1, GlobalEconomicStateV1};
use crate::GLOBAL_SETTLEMENT_ABI_V1;

const I128_MIN_MAGNITUDE_V1: u128 = 1_u128 << 127;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct AmountDeltaRowV1 {
    table: &'static str,
    owner: String,
    asset: String,
    custody_domain: String,
    delta_atoms: i128,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct SupplyDeltaRowV1 {
    asset: String,
    delta_atoms: i128,
}

#[derive(Serialize)]
struct StateDeltaContentV1<'a> {
    schema: &'static str,
    amount_deltas: &'a [AmountDeltaRowV1],
    supply_deltas: &'a [SupplyDeltaRowV1],
    lane_writes: &'a [LaneWriteV1],
}

pub(crate) struct DerivedGlobalEconomicStateDeltaV1 {
    pub(crate) touched_assets: BTreeSet<String>,
    pub(crate) state_delta_root: RootV1,
}

fn checked_signed_delta_v1(post_atoms: u128, pre_atoms: u128) -> AbiResultV1<i128> {
    if post_atoms >= pre_atoms {
        i128::try_from(post_atoms - pre_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("economic refinement signed state delta"))
    } else {
        let magnitude = pre_atoms - post_atoms;
        if magnitude == I128_MIN_MAGNITUDE_V1 {
            Ok(i128::MIN)
        } else {
            i128::try_from(magnitude)
                .map(|value| -value)
                .map_err(|_| AbiErrorV1::InvalidBounds("economic refinement signed state delta"))
        }
    }
}

fn amount_map_v1(rows: &[EconomicAmountV1]) -> BTreeMap<(String, String, String), u128> {
    rows.iter()
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
        .collect()
}

fn amount_delta_rows_v1(
    table: &'static str,
    pre_rows: &[EconomicAmountV1],
    post_rows: &[EconomicAmountV1],
) -> AbiResultV1<Vec<AmountDeltaRowV1>> {
    let pre = amount_map_v1(pre_rows);
    let post = amount_map_v1(post_rows);
    let keys = pre
        .keys()
        .chain(post.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = Vec::new();
    for (asset, owner, custody_domain) in keys {
        let key = (asset.clone(), owner.clone(), custody_domain.clone());
        let delta = checked_signed_delta_v1(
            post.get(&key).copied().unwrap_or(0),
            pre.get(&key).copied().unwrap_or(0),
        )?;
        if delta != 0 {
            rows.push(AmountDeltaRowV1 {
                table,
                owner,
                asset,
                custody_domain,
                delta_atoms: delta,
            });
        }
    }
    Ok(rows)
}

fn effect_amount_delta_rows_v1(
    effect_plan: &GlobalEconomicEffectPlanV1,
    table: &'static str,
    kind: EconomicEffectKindV1,
) -> Vec<AmountDeltaRowV1> {
    let mut rows = effect_plan
        .rows
        .iter()
        .filter(|row| row.kind == kind)
        .map(|row| AmountDeltaRowV1 {
            table,
            owner: row.principal.clone(),
            asset: row.asset.clone(),
            custody_domain: row.custody_domain.clone(),
            delta_atoms: row.delta_atoms,
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

fn require_amount_table_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<AmountDeltaRowV1>> {
    let tables = [
        (
            "balances",
            pre_state.balances.as_slice(),
            post_state.balances.as_slice(),
            EconomicEffectKindV1::ACCOUNT_MOVEMENT,
            "economic refinement balance delta mismatch",
        ),
        (
            "custody",
            pre_state.custody.as_slice(),
            post_state.custody.as_slice(),
            EconomicEffectKindV1::CUSTODY,
            "economic refinement custody delta mismatch",
        ),
        (
            "liabilities",
            pre_state.liabilities.as_slice(),
            post_state.liabilities.as_slice(),
            EconomicEffectKindV1::LIABILITY,
            "economic refinement liability delta mismatch",
        ),
        (
            "reserves",
            pre_state.reserves.as_slice(),
            post_state.reserves.as_slice(),
            EconomicEffectKindV1::RESERVE,
            "economic refinement reserve delta mismatch",
        ),
    ];
    let mut all_rows = Vec::new();
    for (table, pre_rows, post_rows, kind, error) in tables {
        let actual = amount_delta_rows_v1(table, pre_rows, post_rows)?;
        if actual != effect_amount_delta_rows_v1(effect_plan, table, kind) {
            return Err(AbiErrorV1::InvalidBinding(error));
        }
        all_rows.extend(actual);
    }
    all_rows.sort();
    Ok(all_rows)
}

pub(crate) fn supply_map_v1(state: &GlobalEconomicStateV1) -> BTreeMap<String, u128> {
    state
        .supplies
        .iter()
        .map(|row| (row.asset.clone(), row.amount_atoms))
        .collect()
}

fn supply_delta_rows_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
) -> AbiResultV1<Vec<SupplyDeltaRowV1>> {
    let pre = supply_map_v1(pre_state);
    let post = supply_map_v1(post_state);
    let assets = pre
        .keys()
        .chain(post.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = Vec::new();
    for asset in assets {
        let delta = checked_signed_delta_v1(
            post.get(&asset).copied().unwrap_or(0),
            pre.get(&asset).copied().unwrap_or(0),
        )?;
        if delta != 0 {
            rows.push(SupplyDeltaRowV1 {
                asset,
                delta_atoms: delta,
            });
        }
    }
    Ok(rows)
}

fn effect_supply_delta_rows_v1(
    effect_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<SupplyDeltaRowV1>> {
    let mut issued = BTreeMap::<String, u128>::new();
    let mut burned = BTreeMap::<String, u128>::new();
    for row in &effect_plan.rows {
        let target = match row.kind {
            EconomicEffectKindV1::ISSUE => Some((&mut issued, row.delta_atoms.unsigned_abs())),
            EconomicEffectKindV1::BURN => Some((&mut burned, row.delta_atoms.unsigned_abs())),
            _ => None,
        };
        if let Some((totals, amount)) = target {
            let total = totals
                .get(&row.asset)
                .copied()
                .unwrap_or(0)
                .checked_add(amount)
                .ok_or(AbiErrorV1::InvalidBounds(
                    "economic refinement supply effect total",
                ))?;
            totals.insert(row.asset.clone(), total);
        }
    }
    let assets = issued
        .keys()
        .chain(burned.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = Vec::new();
    for asset in assets {
        let delta_atoms = checked_signed_delta_v1(
            issued.get(&asset).copied().unwrap_or(0),
            burned.get(&asset).copied().unwrap_or(0),
        )?;
        if delta_atoms != 0 {
            rows.push(SupplyDeltaRowV1 { asset, delta_atoms });
        }
    }
    Ok(rows)
}

fn require_supply_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<SupplyDeltaRowV1>> {
    let actual = supply_delta_rows_v1(pre_state, post_state)?;
    if actual != effect_supply_delta_rows_v1(effect_plan)? {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement supply delta mismatch",
        ));
    }
    Ok(actual)
}

fn require_lane_writes_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<LaneWriteV1>> {
    let mut rows = Vec::new();
    for (pre_lane, post_lane) in pre_state.lane_roots.iter().zip(&post_state.lane_roots) {
        if pre_lane.lane_id != post_lane.lane_id
            || pre_lane.module_release_id != post_lane.module_release_id
            || pre_lane.enabled != post_lane.enabled
        {
            return Err(AbiErrorV1::InvalidBinding(
                "economic refinement unsupported lane metadata changed",
            ));
        }
        if pre_lane.state_root != post_lane.state_root {
            rows.push(LaneWriteV1 {
                lane_id: pre_lane.lane_id,
                pre_root: pre_lane.state_root.clone(),
                post_root: post_lane.state_root.clone(),
            });
        }
    }
    rows.sort_by_key(|row| row.lane_id.as_str());
    if rows != effect_plan.lane_writes {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement lane write mismatch",
        ));
    }
    Ok(rows)
}

pub(crate) fn derive_global_economic_state_delta_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<DerivedGlobalEconomicStateDeltaV1> {
    let amount_deltas = require_amount_table_v1(pre_state, post_state, effect_plan)?;
    let supply_deltas = require_supply_v1(pre_state, post_state, effect_plan)?;
    let lane_writes = require_lane_writes_v1(pre_state, post_state, effect_plan)?;
    let touched_assets = amount_deltas
        .iter()
        .map(|row| row.asset.clone())
        .chain(supply_deltas.iter().map(|row| row.asset.clone()))
        .collect();
    let state_delta_root = hash_global_v1(
        "global-economic-state-delta-v1",
        &StateDeltaContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            amount_deltas: &amount_deltas,
            supply_deltas: &supply_deltas,
            lane_writes: &lane_writes,
        },
    )?;
    Ok(DerivedGlobalEconomicStateDeltaV1 {
        touched_assets,
        state_delta_root,
    })
}
