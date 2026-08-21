use crate::canonical::{AbiErrorV1, AbiResultV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, FeeConservationRowV1,
    GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::release::LaneIdV1;
use crate::zdex_fee_allocation_types::{
    destination_control_domain_v1, destination_principal_v1, ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1, ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1, ZDEXFeeAllocationRejectCodeV1, ZDEXFeeAllocationRejectedV1,
    ZDEXFeeAllocationResultV1, ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1,
    BASIS_POINTS_DENOMINATOR_V1, FEE_INGRESS_CONTROL_DOMAIN_V1, FEE_INGRESS_PRINCIPAL_V1,
    FEE_RESIDUE_CONTROL_DOMAIN_V1, FEE_RESIDUE_PRINCIPAL_V1,
};

struct AllocationProjectionV1 {
    fee_atoms: u128,
    allocations: Vec<ZDEXFeeDestinationAmountV1>,
    residue_atoms: u128,
}

impl AllocationProjectionV1 {
    fn allocated_atoms(&self) -> AbiResultV1<u128> {
        self.allocations
            .iter()
            .try_fold(0_u128, |total, allocation| {
                total
                    .checked_add(allocation.allocation_atoms)
                    .ok_or(AbiErrorV1::Conservation("ZDEX fee allocation sum"))
            })
    }
}

struct EffectInputsV1<'a> {
    context: &'a ZDEXFeeAllocationContextV1,
    pre_state: &'a ZDEXFeeStateV1,
    post_state: &'a ZDEXFeeStateV1,
    projection: &'a AllocationProjectionV1,
}

struct AcceptedInputsV1<'a> {
    transition: EffectInputsV1<'a>,
    effects: &'a GlobalEconomicEffectPlanV1,
}

fn empty_effect_plan_v1() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn reject_v1(
    code: ZDEXFeeAllocationRejectCodeV1,
    pre_state: &ZDEXFeeStateV1,
) -> ZDEXFeeAllocationResultV1 {
    ZDEXFeeAllocationResultV1::Rejected(Box::new(ZDEXFeeAllocationRejectedV1 {
        code,
        pre_state: pre_state.clone(),
        post_state: pre_state.clone(),
        effects: empty_effect_plan_v1(),
    }))
}

fn precheck_v1(
    context: &ZDEXFeeAllocationContextV1,
    pre_state: &ZDEXFeeStateV1,
    policy_root: &crate::RootV1,
    command: &ZDEXFeeAllocationCommandV1,
) -> Option<ZDEXFeeAllocationRejectCodeV1> {
    if context.policy_root != *policy_root || pre_state.policy_root != *policy_root {
        return Some(ZDEXFeeAllocationRejectCodeV1::POLICY_MISMATCH);
    }
    if command.fee_charged_atoms == 0 {
        return Some(ZDEXFeeAllocationRejectCodeV1::ZERO_FEE);
    }
    if command.fee_charged_atoms > i128::MAX.unsigned_abs() {
        return Some(ZDEXFeeAllocationRejectCodeV1::EFFECT_WIDTH_EXCEEDED);
    }
    if command.fee_charged_atoms > pre_state.fee_ingress_atoms {
        return Some(ZDEXFeeAllocationRejectCodeV1::INSUFFICIENT_FEE_INGRESS);
    }
    None
}

fn allocation_floor_v1(fee_atoms: u128, share_bps: u16) -> AbiResultV1<u128> {
    let denominator = u128::from(BASIS_POINTS_DENOMINATOR_V1);
    let share = u128::from(share_bps);
    let quotient_part = (fee_atoms / denominator)
        .checked_mul(share)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX fee allocation quotient"))?;
    let remainder_part = (fee_atoms % denominator)
        .checked_mul(share)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX fee allocation remainder"))?
        / denominator;
    quotient_part
        .checked_add(remainder_part)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX fee allocation"))
}

fn project_v1(
    policy: &ZDEXFeeAllocationPolicyV1,
    fee_atoms: u128,
) -> AbiResultV1<AllocationProjectionV1> {
    let allocations = policy
        .shares
        .iter()
        .map(|share| {
            Ok(ZDEXFeeDestinationAmountV1 {
                destination: share.destination,
                allocation_atoms: allocation_floor_v1(fee_atoms, share.share_bps)?,
            })
        })
        .collect::<AbiResultV1<Vec<_>>>()?;
    let allocated_atoms = allocations.iter().try_fold(0_u128, |total, allocation| {
        total
            .checked_add(allocation.allocation_atoms)
            .ok_or(AbiErrorV1::Conservation("ZDEX fee allocation sum"))
    })?;
    let residue_atoms = fee_atoms
        .checked_sub(allocated_atoms)
        .ok_or(AbiErrorV1::Conservation("ZDEX fee residue"))?;
    Ok(AllocationProjectionV1 {
        fee_atoms,
        allocations,
        residue_atoms,
    })
}

fn next_state_v1(
    pre_state: &ZDEXFeeStateV1,
    projection: &AllocationProjectionV1,
) -> Option<ZDEXFeeStateV1> {
    let destination_balances = pre_state
        .destination_balances
        .iter()
        .zip(&projection.allocations)
        .map(|(previous, allocation)| {
            Some(ZDEXFeeDestinationAmountV1 {
                destination: previous.destination,
                allocation_atoms: previous
                    .allocation_atoms
                    .checked_add(allocation.allocation_atoms)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(ZDEXFeeStateV1 {
        fee_asset_id: pre_state.fee_asset_id.clone(),
        policy_root: pre_state.policy_root.clone(),
        fee_ingress_atoms: pre_state
            .fee_ingress_atoms
            .checked_sub(projection.fee_atoms)?,
        unallocated_reserve_atoms: pre_state
            .unallocated_reserve_atoms
            .checked_add(projection.residue_atoms)?,
        destination_balances,
        owned_and_custodied_atoms: pre_state.owned_and_custodied_atoms,
        supply_atoms: pre_state.supply_atoms,
    })
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

fn effect_rows_v1(
    pre_state: &ZDEXFeeStateV1,
    projection: &AllocationProjectionV1,
) -> AbiResultV1<Vec<EconomicEffectRowV1>> {
    let mut rows = vec![EconomicEffectRowV1 {
        kind: EconomicEffectKindV1::CUSTODY,
        principal: FEE_INGRESS_PRINCIPAL_V1.to_owned(),
        asset: pre_state.fee_asset_id.to_string(),
        custody_domain: FEE_INGRESS_CONTROL_DOMAIN_V1.to_owned(),
        delta_atoms: -i128::try_from(projection.fee_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX charged fee effect"))?,
    }];
    for allocation in projection
        .allocations
        .iter()
        .filter(|allocation| allocation.allocation_atoms > 0)
    {
        rows.push(EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::FEE_ALLOCATION,
            principal: destination_principal_v1(allocation.destination).to_owned(),
            asset: pre_state.fee_asset_id.to_string(),
            custody_domain: destination_control_domain_v1(allocation.destination).to_owned(),
            delta_atoms: i128::try_from(allocation.allocation_atoms)
                .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX fee allocation effect"))?,
        });
    }
    if projection.residue_atoms > 0 {
        rows.push(EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::RESERVE,
            principal: FEE_RESIDUE_PRINCIPAL_V1.to_owned(),
            asset: pre_state.fee_asset_id.to_string(),
            custody_domain: FEE_RESIDUE_CONTROL_DOMAIN_V1.to_owned(),
            delta_atoms: i128::try_from(projection.residue_atoms)
                .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX fee residue effect"))?,
        });
    }
    rows.sort_by(|left, right| {
        (
            effect_kind_name_v1(left.kind),
            left.asset.as_str(),
            left.principal.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                effect_kind_name_v1(right.kind),
                right.asset.as_str(),
                right.principal.as_str(),
                right.custody_domain.as_str(),
            ))
    });
    Ok(rows)
}

fn effect_plan_v1(inputs: &EffectInputsV1<'_>) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: effect_rows_v1(inputs.pre_state, inputs.projection)?,
        asset_conservation: vec![AssetConservationRowV1 {
            asset: inputs.pre_state.fee_asset_id.to_string(),
            owned_and_custodied_pre_atoms: inputs.pre_state.owned_and_custodied_atoms,
            owned_and_custodied_post_atoms: inputs.post_state.owned_and_custodied_atoms,
            supply_pre_atoms: inputs.pre_state.supply_atoms,
            supply_post_atoms: inputs.post_state.supply_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        }],
        fee_conservation: vec![FeeConservationRowV1 {
            asset: inputs.pre_state.fee_asset_id.to_string(),
            fee_charged_atoms: inputs.projection.fee_atoms,
            current_allocations_atoms: inputs.projection.allocated_atoms()?,
            carried_residue_atoms: inputs.projection.residue_atoms,
        }],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: inputs.pre_state.state_root()?,
            post_root: inputs.post_state.state_root()?,
        }],
        occurrence_consumptions: vec![inputs.context.command_occurrence_id.clone()],
        external_outbox_enqueue: vec![],
    };
    effects.validate()?;
    Ok(effects)
}

fn occurrence_v1(inputs: &AcceptedInputsV1<'_>) -> AbiResultV1<ZDEXFeeAllocationOccurrenceV1> {
    let transition = &inputs.transition;
    Ok(ZDEXFeeAllocationOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: transition.context.chain_id.clone(),
        deployment_root: transition.context.deployment_root.clone(),
        profile_root: transition.context.profile_root.clone(),
        writer_epoch: transition.context.writer_epoch,
        allocation_route_release_id: transition.context.allocation_route_release_id.clone(),
        authorized_buyback_route_release_id: transition
            .context
            .authorized_buyback_route_release_id
            .clone(),
        tokenomics_module_release_id: transition.context.tokenomics_module_release_id.clone(),
        command_occurrence_id: transition.context.command_occurrence_id.clone(),
        policy_root: transition.context.policy_root.clone(),
        fee_asset_id: transition.pre_state.fee_asset_id.clone(),
        fee_charged_atoms: transition.projection.fee_atoms,
        allocations: transition.projection.allocations.clone(),
        carried_residue_atoms: transition.projection.residue_atoms,
        pre_lane_root: transition.pre_state.state_root()?,
        post_lane_root: transition.post_state.state_root()?,
        effect_plan_root: inputs.effects.effect_plan_root()?,
    })
}

pub fn transition_zdex_fee_allocation_v1(
    context: &ZDEXFeeAllocationContextV1,
    pre_state: &ZDEXFeeStateV1,
    policy: &ZDEXFeeAllocationPolicyV1,
    command: &ZDEXFeeAllocationCommandV1,
) -> AbiResultV1<ZDEXFeeAllocationResultV1> {
    context.validate()?;
    pre_state.validate()?;
    policy.validate()?;
    if let Some(code) = precheck_v1(context, pre_state, &policy.policy_root()?, command) {
        return Ok(reject_v1(code, pre_state));
    }
    let projection = project_v1(policy, command.fee_charged_atoms)?;
    let Some(post_state) = next_state_v1(pre_state, &projection) else {
        return Ok(reject_v1(
            ZDEXFeeAllocationRejectCodeV1::STATE_OVERFLOW,
            pre_state,
        ));
    };
    let transition = EffectInputsV1 {
        context,
        pre_state,
        post_state: &post_state,
        projection: &projection,
    };
    let effects = effect_plan_v1(&transition)?;
    let inputs = AcceptedInputsV1 {
        transition,
        effects: &effects,
    };
    let occurrence = occurrence_v1(&inputs)?;
    let accepted = ZDEXFeeAllocationAcceptedV1 {
        pre_state: pre_state.clone(),
        post_state,
        occurrence,
        effects,
    };
    accepted.validate()?;
    Ok(ZDEXFeeAllocationResultV1::Accepted(Box::new(accepted)))
}
