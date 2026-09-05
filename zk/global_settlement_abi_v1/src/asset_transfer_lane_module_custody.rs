//! Custody-complete successor execution using unchanged V1 wire values.
//! Unmounted pure data: no receipt witness, release selection or publication.

use crate::asset_transfer_lane_module::{
    receipt_root, transition_asset_transfer_lane_module_v1, AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1, AssetTransferLaneModuleResultV1,
};
use crate::canonical::{AbiErrorV1, AbiResultV1};

/// Preserve the legacy rejection or complete both physical projection totals.
/// Exact input validation and checked projection sums precede returned success.
pub fn transition_asset_transfer_lane_module_custody_v1(
    module_input: &AssetTransferLaneModuleInputV1,
) -> AbiResultV1<AssetTransferLaneModuleResultV1> {
    let legacy = transition_asset_transfer_lane_module_v1(module_input)?;
    let mut accepted = match legacy {
        AssetTransferLaneModuleResultV1::Rejected(rejected) => {
            return Ok(AssetTransferLaneModuleResultV1::Rejected(rejected));
        }
        AssetTransferLaneModuleResultV1::Accepted(accepted) => *accepted,
    };
    for row in &mut accepted.effects.asset_conservation {
        row.owned_and_custodied_pre_atoms = accepted
            .private_port
            .pre_state
            .owned_and_custodied_atoms(&row.asset)?;
        row.owned_and_custodied_post_atoms = accepted
            .private_port
            .post_state
            .owned_and_custodied_atoms(&row.asset)?;
    }
    accepted.effects.validate()?;
    let effect_root = accepted.effects.effect_plan_root()?;
    accepted.private_port.module_effect_plan_root = effect_root.clone();
    accepted.module_journal.effect_plan_root = effect_root;
    accepted.module_journal.private_port_root = accepted.private_port.port_root()?;
    accepted.module_journal.receipt_root = receipt_root(
        &accepted.statement_root,
        &accepted.module_journal,
        &accepted.private_port,
        &accepted.effects,
    )?;
    accepted.validate()?;
    Ok(AssetTransferLaneModuleResultV1::Accepted(Box::new(
        accepted,
    )))
}

/// Return freshly recomputed data after full exact equality, with no authority.
pub fn recompute_asset_transfer_lane_module_custody_v1(
    module_input: &AssetTransferLaneModuleInputV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AbiResultV1<AssetTransferLaneModuleAcceptedV1> {
    let result = transition_asset_transfer_lane_module_custody_v1(module_input)?;
    let AssetTransferLaneModuleResultV1::Accepted(expected) = result else {
        return Err(AbiErrorV1::InvalidBinding(
            "custody-complete supplied acceptance recomputes to rejection",
        ));
    };
    accepted.validate()?;
    if expected.as_ref() != accepted {
        return Err(AbiErrorV1::InvalidBinding(
            "custody-complete supplied acceptance differs from recomputation",
        ));
    }
    Ok(*expected)
}
