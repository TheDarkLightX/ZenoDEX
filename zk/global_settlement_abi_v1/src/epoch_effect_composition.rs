use std::collections::{btree_map::Entry, BTreeMap};

use crate::canonical::{AbiErrorV1, AbiResultV1, GLOBAL_SETTLEMENT_ABI_V1, MAX_EPOCH_COMMANDS_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, FeeConservationRowV1,
    GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::release::LaneIdV1;

type EffectKeyV1 = (String, String, String, String);

struct EffectTotalV1 {
    kind: EconomicEffectKindV1,
    principal: String,
    asset: String,
    custody_domain: String,
    delta_atoms: i128,
}

struct AssetTotalV1 {
    first_owned_atoms: u128,
    last_owned_atoms: u128,
    first_supply_atoms: u128,
    last_supply_atoms: u128,
    issued_atoms: u128,
    burned_atoms: u128,
}

#[derive(Default)]
struct FeeTotalV1 {
    charged_atoms: u128,
    allocated_atoms: u128,
    residue_atoms: u128,
}

fn effect_kind_name_v1(kind: EconomicEffectKindV1) -> &'static str {
    match kind {
        EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV1::ISSUE => "ISSUE",
        EconomicEffectKindV1::BURN => "BURN",
        EconomicEffectKindV1::CUSTODY => "CUSTODY",
        EconomicEffectKindV1::LIABILITY => "LIABILITY",
        EconomicEffectKindV1::RESERVE => "RESERVE",
        EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV1::REWARD => "REWARD",
        EconomicEffectKindV1::SLASH => "SLASH",
    }
}

fn require_asset_lane_plan_shape_v1(plan: &GlobalEconomicEffectPlanV1) -> AbiResultV1<()> {
    plan.validate()?;
    if plan.lane_writes.len() != 1 || plan.lane_writes[0].lane_id != LaneIdV1::ASSET_TRANSFER {
        return Err(AbiErrorV1::InvalidBinding(
            "asset lane epoch lane write shape",
        ));
    }
    if plan.occurrence_consumptions.len() != 1 {
        return Err(AbiErrorV1::InvalidBinding(
            "asset lane epoch occurrence consumption",
        ));
    }
    if !plan.external_outbox_enqueue.is_empty() {
        return Err(AbiErrorV1::InvalidBinding(
            "asset lane epoch external outbox",
        ));
    }
    Ok(())
}

fn compose_effect_rows_v1(
    plans: &[GlobalEconomicEffectPlanV1],
) -> AbiResultV1<Vec<EconomicEffectRowV1>> {
    let mut totals = BTreeMap::<EffectKeyV1, EffectTotalV1>::new();
    for row in plans.iter().flat_map(|plan| &plan.rows) {
        let key = (
            effect_kind_name_v1(row.kind).to_owned(),
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let total = totals.entry(key).or_insert_with(|| EffectTotalV1 {
            kind: row.kind,
            principal: row.principal.clone(),
            asset: row.asset.clone(),
            custody_domain: row.custody_domain.clone(),
            delta_atoms: 0,
        });
        total.delta_atoms = total
            .delta_atoms
            .checked_add(row.delta_atoms)
            .ok_or(AbiErrorV1::InvalidBounds("asset lane epoch effect total"))?;
    }
    Ok(totals
        .into_values()
        .filter(|total| total.delta_atoms != 0)
        .map(|total| EconomicEffectRowV1 {
            kind: total.kind,
            principal: total.principal,
            asset: total.asset,
            custody_domain: total.custody_domain,
            delta_atoms: total.delta_atoms,
        })
        .collect())
}

fn add_asset_row_v1(
    totals: &mut BTreeMap<String, AssetTotalV1>,
    row: &AssetConservationRowV1,
) -> AbiResultV1<()> {
    match totals.entry(row.asset.clone()) {
        Entry::Vacant(entry) => {
            entry.insert(AssetTotalV1 {
                first_owned_atoms: row.owned_and_custodied_pre_atoms,
                last_owned_atoms: row.owned_and_custodied_post_atoms,
                first_supply_atoms: row.supply_pre_atoms,
                last_supply_atoms: row.supply_post_atoms,
                issued_atoms: row.authorized_issue_atoms,
                burned_atoms: row.authorized_burn_atoms,
            });
        }
        Entry::Occupied(mut entry) => {
            let total = entry.get_mut();
            if total.last_owned_atoms != row.owned_and_custodied_pre_atoms
                || total.last_supply_atoms != row.supply_pre_atoms
            {
                return Err(AbiErrorV1::Conservation(
                    "asset lane epoch conservation history",
                ));
            }
            total.last_owned_atoms = row.owned_and_custodied_post_atoms;
            total.last_supply_atoms = row.supply_post_atoms;
            total.issued_atoms = total
                .issued_atoms
                .checked_add(row.authorized_issue_atoms)
                .ok_or(AbiErrorV1::InvalidBounds("asset lane epoch issue total"))?;
            total.burned_atoms = total
                .burned_atoms
                .checked_add(row.authorized_burn_atoms)
                .ok_or(AbiErrorV1::InvalidBounds("asset lane epoch burn total"))?;
        }
    }
    Ok(())
}

fn compose_asset_conservation_v1(
    plans: &[GlobalEconomicEffectPlanV1],
) -> AbiResultV1<Vec<AssetConservationRowV1>> {
    let mut totals = BTreeMap::<String, AssetTotalV1>::new();
    for row in plans.iter().flat_map(|plan| &plan.asset_conservation) {
        add_asset_row_v1(&mut totals, row)?;
    }
    Ok(totals
        .into_iter()
        .map(|(asset, total)| AssetConservationRowV1 {
            asset,
            owned_and_custodied_pre_atoms: total.first_owned_atoms,
            owned_and_custodied_post_atoms: total.last_owned_atoms,
            supply_pre_atoms: total.first_supply_atoms,
            supply_post_atoms: total.last_supply_atoms,
            authorized_issue_atoms: total.issued_atoms,
            authorized_burn_atoms: total.burned_atoms,
        })
        .collect())
}

fn compose_fee_conservation_v1(
    plans: &[GlobalEconomicEffectPlanV1],
) -> AbiResultV1<Vec<FeeConservationRowV1>> {
    let mut totals = BTreeMap::<String, FeeTotalV1>::new();
    for row in plans.iter().flat_map(|plan| &plan.fee_conservation) {
        let total = totals.entry(row.asset.clone()).or_default();
        total.charged_atoms = total
            .charged_atoms
            .checked_add(row.fee_charged_atoms)
            .ok_or(AbiErrorV1::InvalidBounds("asset lane epoch fee total"))?;
        total.allocated_atoms = total
            .allocated_atoms
            .checked_add(row.current_allocations_atoms)
            .ok_or(AbiErrorV1::InvalidBounds(
                "asset lane epoch fee allocation total",
            ))?;
        total.residue_atoms = total
            .residue_atoms
            .checked_add(row.carried_residue_atoms)
            .ok_or(AbiErrorV1::InvalidBounds(
                "asset lane epoch fee residue total",
            ))?;
    }
    Ok(totals
        .into_iter()
        .map(|(asset, total)| FeeConservationRowV1 {
            asset,
            fee_charged_atoms: total.charged_atoms,
            current_allocations_atoms: total.allocated_atoms,
            carried_residue_atoms: total.residue_atoms,
        })
        .collect())
}

fn compose_lane_write_v1(plans: &[GlobalEconomicEffectPlanV1]) -> AbiResultV1<Vec<LaneWriteV1>> {
    let first = &plans[0].lane_writes[0];
    let mut last_post_root = first.post_root.clone();
    for plan in &plans[1..] {
        let current = &plan.lane_writes[0];
        if current.pre_root != last_post_root {
            return Err(AbiErrorV1::InvalidBinding(
                "asset lane epoch lane write history",
            ));
        }
        last_post_root = current.post_root.clone();
    }
    Ok(vec![LaneWriteV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        pre_root: first.pre_root.clone(),
        post_root: last_post_root,
    }])
}

/// Compose 1..=64 sequential ASSET_TRANSFER route effect plans.
///
/// The function is pure and deterministic. It checks signed and unsigned
/// arithmetic, exact single-occurrence plans, connected conservation and lane
/// histories, and canonical aggregate ordering. It grants no receipt or commit
/// authority.
pub fn compose_asset_lane_epoch_effect_plans_v1(
    route_effect_plans: &[GlobalEconomicEffectPlanV1],
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    if !(1..=MAX_EPOCH_COMMANDS_V1).contains(&route_effect_plans.len()) {
        return Err(AbiErrorV1::InvalidBounds(
            "asset lane epoch route effect plan count",
        ));
    }
    for plan in route_effect_plans {
        require_asset_lane_plan_shape_v1(plan)?;
    }

    let mut occurrence_consumptions = route_effect_plans
        .iter()
        .map(|plan| plan.occurrence_consumptions[0].clone())
        .collect::<Vec<_>>();
    occurrence_consumptions.sort();
    if occurrence_consumptions
        .windows(2)
        .any(|pair| pair[0] == pair[1])
    {
        return Err(AbiErrorV1::InvalidOrder(
            "asset lane epoch occurrence consumptions",
        ));
    }

    let composed = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: compose_effect_rows_v1(route_effect_plans)?,
        asset_conservation: compose_asset_conservation_v1(route_effect_plans)?,
        fee_conservation: compose_fee_conservation_v1(route_effect_plans)?,
        lane_writes: compose_lane_write_v1(route_effect_plans)?,
        occurrence_consumptions,
        external_outbox_enqueue: Vec::new(),
    };
    composed.validate()?;
    Ok(composed)
}
