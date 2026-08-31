//! Pure Rust mirror of the Python Asset Origin Registry V2 SHADOW core.
//!
//! This module validates structural registry and policy relations and proposes
//! one deterministic registration result. It performs no RISC0 verification,
//! runtime mount, migration, UI action, release, settlement, or production
//! admission.

use serde::Serialize;

use crate::asset_origin_registry_types::*;
use crate::asset_transfer_types::{AssetTransferPolicyV2, ASSET_ATOM_DECIMALS_V2};
use crate::canonical::{hash_global_v2, AbiErrorV2, AbiResultV2, RootV2, GLOBAL_SETTLEMENT_ABI_V2};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::managed_asset_lifecycle_types::ManagedAssetLifecyclePolicyV2;
use crate::proof::LaneModuleTransitionJournalV2;

pub fn asset_transfer_policy_root_v2(policy: &AssetTransferPolicyV2) -> AbiResultV2<RootV2> {
    policy.validate()?;
    hash_global_v2("asset-transfer-policy-v2", policy)
}

pub fn validate_asset_transfer_policy_origin_v2(
    registry: &AssetOriginRegistryStateV2,
    policy: &AssetTransferPolicyV2,
) -> AbiResultV2<AssetOriginRecordV2> {
    registry.validate()?;
    policy.validate()?;
    let record = registry
        .record_for(&policy.asset)?
        .ok_or(AbiErrorV2::InvalidBinding(
            "asset transfer policy has no registered origin",
        ))?;
    let policy_origin = policy
        .asset_origin_root
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "asset transfer policy origin is absent",
        ))?;
    if record.asset_class != policy.asset_class
        || record.origin_root != *policy_origin
        || record.decimals != u64::from(policy.atom_decimals)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "asset transfer policy identity does not match its origin",
        ));
    }
    if record.transfer_policy_root != asset_transfer_policy_root_v2(policy)? {
        return Err(AbiErrorV2::InvalidBinding(
            "asset transfer policy root does not match its origin",
        ));
    }
    Ok(record.clone())
}

pub fn managed_asset_policy_root_v2(policy: &ManagedAssetLifecyclePolicyV2) -> AbiResultV2<RootV2> {
    policy.validate()?;
    hash_global_v2("managed-asset-lifecycle-policy-v2", policy)
}

pub fn validate_managed_asset_policy_origin_v2(
    registry: &AssetOriginRegistryStateV2,
    policy: &ManagedAssetLifecyclePolicyV2,
) -> AbiResultV2<AssetOriginRecordV2> {
    registry.validate()?;
    policy.validate()?;
    let record = registry
        .record_for(&policy.asset)?
        .ok_or(AbiErrorV2::InvalidBinding(
            "managed asset policy has no registered origin",
        ))?;
    let policy_origin = policy
        .asset_origin_root
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "managed asset policy origin is absent",
        ))?;
    if record.asset_class != policy.asset_class
        || record.origin_root != *policy_origin
        || record.decimals != u64::from(policy.atom_decimals)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "managed asset policy identity does not match its origin",
        ));
    }
    if record.issue_policy_root.is_zero() {
        return Err(AbiErrorV2::InvalidBinding(
            "managed asset issue policy is disabled at its origin",
        ));
    }
    if record.issue_policy_root != managed_asset_policy_root_v2(policy)? {
        return Err(AbiErrorV2::InvalidBinding(
            "managed asset issue policy root does not match its origin",
        ));
    }
    Ok(record.clone())
}

fn reject(
    code: AssetOriginRegistrationRejectCodeV2,
    pre_state: &AssetOriginRegistryStateV2,
) -> AbiResultV2<AssetOriginRegistrationResultV2> {
    let root = pre_state.state_root()?;
    let rejected = AssetOriginRegistrationRejectedV2 {
        code,
        pre_state_root: root.clone(),
        post_state_root: root,
        effects: GlobalEconomicEffectPlanV2::empty(),
    };
    rejected.validate()?;
    Ok(AssetOriginRegistrationResultV2::Rejected(Box::new(
        rejected,
    )))
}

fn binding_reject_code(
    context: &AssetOriginRegistrationContextV2,
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
    command_body_hash: &RootV2,
) -> Option<AssetOriginRegistrationRejectCodeV2> {
    let Some(occurrence) = &context.occurrence else {
        return Some(AssetOriginRegistrationRejectCodeV2::MISSING_OCCURRENCE);
    };
    if occurrence.pre_state_root != context.global_pre_state_root
        || !occurrence.consumed_object_ids.is_empty()
    {
        return Some(AssetOriginRegistrationRejectCodeV2::OCCURRENCE_BINDING_MISMATCH);
    }
    if context.module_release_id != pre_state.module_release_id {
        return Some(AssetOriginRegistrationRejectCodeV2::RELEASE_MISMATCH);
    }
    if command.command_kind != ASSET_ORIGIN_REGISTRATION_COMMAND_V2 {
        return Some(AssetOriginRegistrationRejectCodeV2::UNKNOWN_COMMAND);
    }
    if occurrence.command_kind != command.command_kind
        || occurrence.command_body_hash != *command_body_hash
    {
        return Some(AssetOriginRegistrationRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH);
    }
    None
}

fn authority_reject_code(
    context: &AssetOriginRegistrationContextV2,
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
) -> Option<AssetOriginRegistrationRejectCodeV2> {
    let Some(occurrence) = &context.occurrence else {
        return Some(AssetOriginRegistrationRejectCodeV2::MISSING_OCCURRENCE);
    };
    if occurrence.subject_id != pre_state.policy.authority_subject {
        return Some(AssetOriginRegistrationRejectCodeV2::UNAUTHORIZED_SUBJECT);
    }
    if occurrence.grant_root != pre_state.policy.authority_grant_root {
        return Some(AssetOriginRegistrationRejectCodeV2::GRANT_MISMATCH);
    }
    if command.decimals != u64::from(ASSET_ATOM_DECIMALS_V2) {
        return Some(AssetOriginRegistrationRejectCodeV2::DECIMAL_SCALE_MISMATCH);
    }
    let enabled = match command.origin_kind {
        AssetOriginKindV2::NATIVE => pre_state.policy.allow_native,
        AssetOriginKindV2::TAU_ORIGINATED => pre_state.policy.allow_tau_originated,
    };
    if !enabled {
        return Some(AssetOriginRegistrationRejectCodeV2::DISABLED_ORIGIN_KIND);
    }
    if command.origin_kind == AssetOriginKindV2::NATIVE {
        return Some(AssetOriginRegistrationRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED);
    }
    None
}

fn uniqueness_reject_code(
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
) -> AbiResultV2<Option<AssetOriginRegistrationRejectCodeV2>> {
    if pre_state.record_for(&command.asset)?.is_some() {
        return Ok(Some(AssetOriginRegistrationRejectCodeV2::DUPLICATE_ASSET));
    }
    if pre_state
        .assets
        .iter()
        .any(|row| row.origin_root == command.origin_root)
    {
        return Ok(Some(AssetOriginRegistrationRejectCodeV2::DUPLICATE_ORIGIN));
    }
    Ok(None)
}

fn registration_reject_code(
    context: &AssetOriginRegistrationContextV2,
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
    command_body_hash: &RootV2,
) -> AbiResultV2<Option<AssetOriginRegistrationRejectCodeV2>> {
    if let Some(code) = binding_reject_code(context, pre_state, command, command_body_hash) {
        return Ok(Some(code));
    }
    if let Some(code) = authority_reject_code(context, pre_state, command) {
        return Ok(Some(code));
    }
    uniqueness_reject_code(pre_state, command)
}

fn build_post_state(
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
) -> AssetOriginRegistryStateV2 {
    let record = AssetOriginRecordV2 {
        asset: command.asset.clone(),
        origin_kind: command.origin_kind,
        origin_root: command.origin_root.clone(),
        transfer_policy_root: command.transfer_policy_root.clone(),
        issue_policy_root: command.issue_policy_root.clone(),
        decimals: command.decimals,
        asset_class: command.asset_class,
    };
    let mut assets = pre_state.assets.clone();
    assets.push(record);
    assets.sort_by(|left, right| left.asset.cmp(&right.asset));
    AssetOriginRegistryStateV2 {
        schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
        module_release_id: pre_state.module_release_id.clone(),
        policy: pre_state.policy.clone(),
        assets,
    }
}

fn build_effect_plan(
    occurrence_id: RootV2,
    pre_root: RootV2,
    post_root: RootV2,
) -> AbiResultV2<GlobalEconomicEffectPlanV2> {
    let effects = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: vec![LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root,
            post_root,
        }],
        occurrence_consumptions: vec![occurrence_id],
        external_outbox_enqueue: Vec::new(),
    };
    effects.validate()?;
    Ok(effects)
}

#[derive(Serialize)]
struct AssetOriginRegistrationReceiptBodyV2<'a> {
    occurrence_id: &'a RootV2,
    command_body_hash: &'a RootV2,
    pre_state_root: &'a RootV2,
    post_state_root: &'a RootV2,
    effect_plan_root: &'a RootV2,
    private_port_root: &'a RootV2,
    terminal_obligations_root: &'a RootV2,
    oracle_occurrence_plan_root: &'a RootV2,
}

struct AcceptedRootsV2 {
    command_body_hash: RootV2,
    pre_state_root: RootV2,
    post_state_root: RootV2,
    effect_plan_root: RootV2,
}

fn build_module_journal(
    context: &AssetOriginRegistrationContextV2,
    roots: &AcceptedRootsV2,
) -> AbiResultV2<LaneModuleTransitionJournalV2> {
    let occurrence = context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "prepared asset origin occurrence",
        ))?;
    let occurrence_id = occurrence.occurrence_id()?;
    let private_port_root = RootV2::zero();
    let terminal_obligations_root = RootV2::zero();
    let oracle_occurrence_plan_root = RootV2::zero();
    let receipt_root = hash_global_v2(
        "asset-origin-registration-receipt-v2",
        &AssetOriginRegistrationReceiptBodyV2 {
            occurrence_id: &occurrence_id,
            command_body_hash: &roots.command_body_hash,
            pre_state_root: &roots.pre_state_root,
            post_state_root: &roots.post_state_root,
            effect_plan_root: &roots.effect_plan_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &terminal_obligations_root,
            oracle_occurrence_plan_root: &oracle_occurrence_plan_root,
        },
    )?;
    Ok(LaneModuleTransitionJournalV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: context.writer_epoch,
        lane_id: LaneIdV2::ASSET_TRANSFER,
        module_release_id: context.module_release_id.clone(),
        command_occurrence_id: occurrence_id,
        pre_lane_root: roots.pre_state_root.clone(),
        post_lane_root: roots.post_state_root.clone(),
        effect_plan_root: roots.effect_plan_root.clone(),
        private_port_root,
        receipt_root,
        terminal_obligations_root,
        oracle_occurrence_plan_root,
    })
}

fn accept(
    context: &AssetOriginRegistrationContextV2,
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
    command_body_hash: &RootV2,
) -> AbiResultV2<AssetOriginRegistrationResultV2> {
    let occurrence_id = context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "prepared asset origin occurrence",
        ))?
        .occurrence_id()?;
    let post_state = build_post_state(pre_state, command);
    let pre_root = pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = build_effect_plan(occurrence_id, pre_root.clone(), post_root.clone())?;
    let roots = AcceptedRootsV2 {
        command_body_hash: command_body_hash.clone(),
        pre_state_root: pre_root,
        post_state_root: post_root,
        effect_plan_root: effects.effect_plan_root()?,
    };
    let module_journal = build_module_journal(context, &roots)?;
    let accepted = AssetOriginRegistrationAcceptedV2 {
        post_state,
        effects,
        module_journal,
    };
    accepted.validate()?;
    Ok(AssetOriginRegistrationResultV2::Accepted(Box::new(
        accepted,
    )))
}

pub fn transition_asset_origin_registration_v2(
    context: &AssetOriginRegistrationContextV2,
    pre_state: &AssetOriginRegistryStateV2,
    command: &AssetOriginRegistrationCommandV2,
) -> AbiResultV2<AssetOriginRegistrationResultV2> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    let command_body_hash = command.command_body_hash()?;
    if let Some(code) = registration_reject_code(context, pre_state, command, &command_body_hash)? {
        return reject(code, pre_state);
    }
    accept(context, pre_state, command, &command_body_hash)
}
