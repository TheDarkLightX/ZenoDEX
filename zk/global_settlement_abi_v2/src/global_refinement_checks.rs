use std::collections::{BTreeMap, BTreeSet};

use crate::canonical::{AbiErrorV2, AbiResultV2};
use crate::effects::{EconomicEffectKindV2, GlobalEconomicEffectPlanV2};
use crate::global_refinement_annotations::require_global_annotation_mirrors_v2;
use crate::global_state::GlobalEconomicStateV2;
use crate::lifecycle::TerminalObligationStatusV2;
use crate::signed_atoms::{checked_signed_delta_v2, SignedAtomsDeltaV2};
use crate::state::EconomicAmountV2;

pub(crate) type AmountKeyV2 = (String, String, String);

fn amount_map_v2(rows: &[EconomicAmountV2]) -> BTreeMap<AmountKeyV2, u128> {
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

fn state_table_deltas_v2(
    pre_rows: &[EconomicAmountV2],
    post_rows: &[EconomicAmountV2],
) -> AbiResultV2<BTreeMap<AmountKeyV2, i128>> {
    let pre = amount_map_v2(pre_rows);
    let post = amount_map_v2(post_rows);
    let keys = pre
        .keys()
        .chain(post.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut deltas = BTreeMap::new();
    for key in keys {
        let delta = checked_signed_delta_v2(
            post.get(&key).copied().unwrap_or(0),
            pre.get(&key).copied().unwrap_or(0),
        )?;
        if delta != 0 {
            deltas.insert(key, delta);
        }
    }
    Ok(deltas)
}

pub(crate) fn effect_deltas_v2(
    effect_plan: &GlobalEconomicEffectPlanV2,
    kind: EconomicEffectKindV2,
) -> BTreeMap<AmountKeyV2, i128> {
    effect_plan
        .rows
        .iter()
        .filter(|row| row.kind == kind)
        .map(|row| {
            (
                (
                    row.asset.clone(),
                    row.principal.clone(),
                    row.custody_domain.clone(),
                ),
                row.delta_atoms,
            )
        })
        .collect()
}

fn require_state_effect_rows_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<()> {
    for (pre_rows, post_rows, kind, label) in [
        (
            pre_state.balances.as_slice(),
            post_state.balances.as_slice(),
            EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            "global refinement balances state/effect mismatch",
        ),
        (
            pre_state.custody.as_slice(),
            post_state.custody.as_slice(),
            EconomicEffectKindV2::CUSTODY,
            "global refinement custody state/effect mismatch",
        ),
        (
            pre_state.liabilities.as_slice(),
            post_state.liabilities.as_slice(),
            EconomicEffectKindV2::LIABILITY,
            "global refinement liabilities state/effect mismatch",
        ),
        (
            pre_state.reserves.as_slice(),
            post_state.reserves.as_slice(),
            EconomicEffectKindV2::RESERVE,
            "global refinement reserves state/effect mismatch",
        ),
    ] {
        if state_table_deltas_v2(pre_rows, post_rows)? != effect_deltas_v2(effect_plan, kind) {
            return Err(AbiErrorV2::InvalidBinding(label));
        }
    }
    Ok(())
}

fn supply_effect_deltas_v2(
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<BTreeMap<String, SignedAtomsDeltaV2>> {
    let mut issued = BTreeMap::<String, u128>::new();
    let mut burned = BTreeMap::<String, u128>::new();
    for row in &effect_plan.rows {
        let target = match row.kind {
            EconomicEffectKindV2::ISSUE => Some(&mut issued),
            EconomicEffectKindV2::BURN => Some(&mut burned),
            _ => None,
        };
        if let Some(values) = target {
            let total = values
                .get(&row.asset)
                .copied()
                .unwrap_or(0)
                .checked_add(row.delta_atoms.unsigned_abs())
                .ok_or(AbiErrorV2::InvalidBounds(
                    "global refinement supply effect total",
                ))?;
            values.insert(row.asset.clone(), total);
        }
    }
    let assets = issued
        .keys()
        .chain(burned.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut deltas = BTreeMap::new();
    for asset in assets {
        let delta = SignedAtomsDeltaV2::between(
            issued.get(&asset).copied().unwrap_or(0),
            burned.get(&asset).copied().unwrap_or(0),
        );
        if !delta.is_zero() {
            deltas.insert(asset, delta);
        }
    }
    Ok(deltas)
}

fn supply_state_deltas_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
) -> BTreeMap<String, SignedAtomsDeltaV2> {
    let pre = pre_state.supply_atoms_by_asset();
    let post = post_state.supply_atoms_by_asset();
    let assets = pre
        .keys()
        .chain(post.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut deltas = BTreeMap::new();
    for asset in assets {
        let delta = SignedAtomsDeltaV2::between(
            post.get(&asset).copied().unwrap_or(0),
            pre.get(&asset).copied().unwrap_or(0),
        );
        if !delta.is_zero() {
            deltas.insert(asset, delta);
        }
    }
    deltas
}

fn changed_economic_assets_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<BTreeSet<String>> {
    let mut touched = effect_plan
        .rows
        .iter()
        .map(|row| row.asset.clone())
        .chain(
            effect_plan
                .fee_conservation
                .iter()
                .map(|row| row.asset.clone()),
        )
        .collect::<BTreeSet<_>>();
    for (pre_rows, post_rows) in [
        (
            pre_state.balances.as_slice(),
            post_state.balances.as_slice(),
        ),
        (pre_state.custody.as_slice(), post_state.custody.as_slice()),
        (
            pre_state.liabilities.as_slice(),
            post_state.liabilities.as_slice(),
        ),
        (
            pre_state.reserves.as_slice(),
            post_state.reserves.as_slice(),
        ),
    ] {
        touched.extend(
            state_table_deltas_v2(pre_rows, post_rows)?
                .into_keys()
                .map(|key| key.0),
        );
    }
    touched.extend(supply_state_deltas_v2(pre_state, post_state).into_keys());
    Ok(touched)
}

fn require_asset_conservation_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<()> {
    let pre_owned = pre_state.owned_atoms_by_asset()?;
    let post_owned = post_state.owned_atoms_by_asset()?;
    let pre_supply = pre_state.supply_atoms_by_asset();
    let post_supply = post_state.supply_atoms_by_asset();
    let assets = pre_owned
        .keys()
        .chain(post_owned.keys())
        .chain(pre_supply.keys())
        .chain(post_supply.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    if assets.iter().any(|asset| {
        pre_owned.get(asset).copied().unwrap_or(0) != pre_supply.get(asset).copied().unwrap_or(0)
            || post_owned.get(asset).copied().unwrap_or(0)
                != post_supply.get(asset).copied().unwrap_or(0)
    }) {
        return Err(AbiErrorV2::Conservation(
            "global refinement owned total does not equal supply",
        ));
    }
    let rows = effect_plan
        .asset_conservation
        .iter()
        .map(|row| (row.asset.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let touched = changed_economic_assets_v2(pre_state, post_state, effect_plan)?;
    if rows.keys().copied().ne(touched.iter().map(String::as_str)) {
        return Err(AbiErrorV2::Conservation(
            "global refinement conservation asset coverage mismatch",
        ));
    }
    for asset in touched {
        let row = rows[asset.as_str()];
        if (
            row.owned_and_custodied_pre_atoms,
            row.owned_and_custodied_post_atoms,
            row.supply_pre_atoms,
            row.supply_post_atoms,
        ) != (
            pre_owned.get(&asset).copied().unwrap_or(0),
            post_owned.get(&asset).copied().unwrap_or(0),
            pre_supply.get(&asset).copied().unwrap_or(0),
            post_supply.get(&asset).copied().unwrap_or(0),
        ) {
            return Err(AbiErrorV2::Conservation(
                "global refinement conservation state mismatch",
            ));
        }
    }
    Ok(())
}

fn require_liability_backing_v2(state: &GlobalEconomicStateV2) -> AbiResultV2<()> {
    let mut custody = BTreeMap::<&str, u128>::new();
    for row in &state.custody {
        let total = custody
            .get(row.asset.as_str())
            .copied()
            .unwrap_or(0)
            .checked_add(row.amount_atoms)
            .ok_or(AbiErrorV2::InvalidBounds(
                "global refinement custody backing total",
            ))?;
        custody.insert(row.asset.as_str(), total);
    }
    if state
        .liability_atoms_by_asset()?
        .iter()
        .any(|(asset, amount)| *amount > custody.get(asset.as_str()).copied().unwrap_or(0))
    {
        return Err(AbiErrorV2::Conservation(
            "global refinement liabilities exceed accounting backing",
        ));
    }
    require_open_terminal_liability_coverage_v2(state)
}

fn require_open_terminal_liability_coverage_v2(state: &GlobalEconomicStateV2) -> AbiResultV2<()> {
    let liabilities = amount_map_v2(&state.liabilities);
    let mut open_totals = BTreeMap::<AmountKeyV2, u128>::new();
    for obligation in &state.terminal_obligations {
        if obligation.status != TerminalObligationStatusV2::OPEN {
            continue;
        }
        let key = (
            obligation.asset.clone(),
            obligation.claimant.clone(),
            obligation.liability_domain.clone(),
        );
        let total = open_totals
            .get(&key)
            .copied()
            .unwrap_or(0)
            .checked_add(obligation.amount_atoms)
            .ok_or(AbiErrorV2::InvalidBounds(
                "global refinement open terminal obligation total",
            ))?;
        open_totals.insert(key, total);
    }
    if open_totals
        .iter()
        .any(|(key, total)| *total > liabilities.get(key).copied().unwrap_or(0))
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement open terminal obligations exceed exact liability row",
        ));
    }
    Ok(())
}

pub(crate) fn require_global_economic_tables_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<()> {
    require_state_effect_rows_v2(pre_state, post_state, effect_plan)?;
    if supply_state_deltas_v2(pre_state, post_state) != supply_effect_deltas_v2(effect_plan)? {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement supply issue/burn mismatch",
        ));
    }
    require_asset_conservation_v2(pre_state, post_state, effect_plan)?;
    require_global_annotation_mirrors_v2(effect_plan)?;
    require_liability_backing_v2(pre_state)?;
    require_liability_backing_v2(post_state)
}
