//! Governed typed policy-registry membership for asset transfer.
//!
//! The transfer lane module carries opaque `asset_policy_registry_root` and
//! `fee_policy_registry_root` values plus one state policy row per asset.
//! Those rows economically control enablement, the fee owner, and the flat
//! fee, so an ungoverned row can redirect or reprice the fee while both
//! opaque roots stay unchanged. This core binds both roots to one exact typed
//! registry that derives two domain-separated roots from the same owned rows:
//! the asset policy root commits the `ASSET_TRANSFER` module release plus
//! ordered `(asset, enabled)` rows, and the fee policy root commits the same
//! release plus ordered `(asset, fee_owner, transfer_fee_atoms)` rows. The
//! active profile's economic policy registry governs both roots for the
//! transfer command kind. Membership then requires the module's release, the
//! command asset, and every carried state policy to match the registry
//! exactly. Direct transfer transitions never consult the registry; it grants
//! no proof, settlement, or publication authority.

use serde::{Deserialize, Serialize};

use crate::asset_transfer_lane_module::AssetTransferLaneModuleInputV1;
use crate::asset_transfer_types::{AssetTransferPolicyV1, ASSET_TRANSFER_COMMAND_KIND_V1};
use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{
    EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, LaneIdV1, LaneRegistryV1,
};

pub const ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1: &str =
    "zenodex/asset-transfer-policy-registry/v1";
pub const ASSET_TRANSFER_ASSET_POLICY_ROOT_SCHEMA_V1: &str =
    "zenodex/asset-transfer-asset-policy-root/v1";
pub const ASSET_TRANSFER_FEE_POLICY_ROOT_SCHEMA_V1: &str =
    "zenodex/asset-transfer-fee-policy-root/v1";
pub const ASSET_TRANSFER_ASSET_POLICY_KIND_V1: &str = "asset_transfer_asset_policy_v1";
pub const ASSET_TRANSFER_FEE_POLICY_KIND_V1: &str = "asset_transfer_fee_policy_v1";
pub const MAX_ASSET_TRANSFER_POLICIES_V1: usize = 256;
const ASSET_POLICY_ROOT_DOMAIN_V1: &str = "asset-transfer-asset-policy-root-v1";
const FEE_POLICY_ROOT_DOMAIN_V1: &str = "asset-transfer-fee-policy-root-v1";

/// Exact governed transfer policy rows bound to one `ASSET_TRANSFER` release.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferPolicyRegistryV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub policies: Vec<AssetTransferPolicyV1>,
}

#[derive(Serialize)]
struct AssetPolicyRowV1<'a> {
    asset: &'a str,
    enabled: bool,
}

#[derive(Serialize)]
struct FeePolicyRowV1<'a> {
    asset: &'a str,
    fee_owner: &'a str,
    transfer_fee_atoms: u128,
}

#[derive(Serialize)]
struct PolicyRootContentV1<'a, Row: Serialize> {
    schema: &'static str,
    module_release_id: &'a RootV1,
    policies: Vec<Row>,
}

impl AssetTransferPolicyRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.module_release_id
            .validate("asset transfer policy registry module release", false)?;
        if self.policies.len() > MAX_ASSET_TRANSFER_POLICIES_V1 {
            return Err(AbiErrorV1::InvalidBounds("asset transfer policy registry"));
        }
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder("asset transfer policy registry"));
        }
        Ok(())
    }

    /// Commit the release plus ordered `(asset, enabled)` rows.
    pub fn asset_policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            ASSET_POLICY_ROOT_DOMAIN_V1,
            &PolicyRootContentV1 {
                schema: ASSET_TRANSFER_ASSET_POLICY_ROOT_SCHEMA_V1,
                module_release_id: &self.module_release_id,
                policies: self
                    .policies
                    .iter()
                    .map(|policy| AssetPolicyRowV1 {
                        asset: &policy.asset,
                        enabled: policy.enabled,
                    })
                    .collect(),
            },
        )
    }

    /// Commit the release plus ordered `(asset, fee_owner, transfer_fee_atoms)` rows.
    pub fn fee_policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            FEE_POLICY_ROOT_DOMAIN_V1,
            &PolicyRootContentV1 {
                schema: ASSET_TRANSFER_FEE_POLICY_ROOT_SCHEMA_V1,
                module_release_id: &self.module_release_id,
                policies: self
                    .policies
                    .iter()
                    .map(|policy| FeePolicyRowV1 {
                        asset: &policy.asset,
                        fee_owner: &policy.fee_owner,
                        transfer_fee_atoms: policy.transfer_fee_atoms,
                    })
                    .collect(),
            },
        )
    }

    pub fn policy_for(&self, asset: &str) -> Option<&AssetTransferPolicyV1> {
        self.policies.iter().find(|policy| policy.asset == asset)
    }
}

/// Require both typed registry roots to be the profile-governed transfer
/// policy roots and the registry release to be the profile-selected
/// `ASSET_TRANSFER` release.
///
/// The asset-policy and fee-policy bindings for `asset_transfer` must each
/// carry the exact domain-separated root of this registry, so swapped roots
/// reject.
pub fn require_governed_asset_transfer_policy_registry_v1(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    policy_registry: &EconomicPolicyRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    asset_policy_registry: &AssetTransferPolicyRegistryV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    occurrence.validate()?;
    let asset_policy_root = asset_policy_registry.asset_policy_root()?;
    let fee_policy_root = asset_policy_registry.fee_policy_root()?;
    if occurrence.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1 {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer policy binding requires an asset transfer command",
        ));
    }
    if policy_registry.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer policy registry outside profile",
        ));
    }
    let asset_binding = policy_registry.require_binding(
        ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
        ASSET_TRANSFER_COMMAND_KIND_V1,
    )?;
    if asset_binding.policy_root != asset_policy_root {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer asset policy root",
        ));
    }
    let fee_binding = policy_registry.require_binding(
        ASSET_TRANSFER_FEE_POLICY_KIND_V1,
        ASSET_TRANSFER_COMMAND_KIND_V1,
    )?;
    if fee_binding.policy_root != fee_policy_root {
        return Err(AbiErrorV1::InvalidBinding("asset transfer fee policy root"));
    }
    if lanes.registry_root()? != profile.lane_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer policy lane registry outside profile",
        ));
    }
    let selected =
        lanes
            .release_for(LaneIdV1::ASSET_TRANSFER)
            .ok_or(AbiErrorV1::InvalidBinding(
                "asset transfer policy lane release",
            ))?;
    if selected.release_id != asset_policy_registry.module_release_id {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer policy registry module release is not profile-selected",
        ));
    }
    Ok(())
}

/// Return the governed member policy the lane module input executes under.
///
/// Both opaque input roots must be the typed registry roots, the registry's
/// module release must be the release the context and pre-state execute
/// under, the command asset must be a member carried by the pre-state, and
/// every carried state policy must equal its member exactly.
pub fn require_asset_transfer_policy_membership_v1<'a>(
    asset_policy_registry: &'a AssetTransferPolicyRegistryV1,
    module_input: &AssetTransferLaneModuleInputV1,
) -> AbiResultV1<&'a AssetTransferPolicyV1> {
    module_input.validate()?;
    if module_input.asset_policy_registry_root != asset_policy_registry.asset_policy_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer lane module asset policy root",
        ));
    }
    if module_input.fee_policy_registry_root != asset_policy_registry.fee_policy_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer lane module fee policy root",
        ));
    }
    if module_input.context.module_release_id != asset_policy_registry.module_release_id
        || module_input.pre_state.module_release_id != asset_policy_registry.module_release_id
    {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer policy registry module release",
        ));
    }
    let member = asset_policy_registry
        .policy_for(&module_input.command.asset)
        .ok_or(AbiErrorV1::InvalidBinding(
            "asset transfer command asset absent from governed registry",
        ))?;
    if !module_input
        .pre_state
        .policies
        .iter()
        .any(|policy| policy.asset == member.asset)
    {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer state omits the governed command policy",
        ));
    }
    for state_policy in &module_input.pre_state.policies {
        if asset_policy_registry.policy_for(&state_policy.asset) != Some(state_policy) {
            return Err(AbiErrorV1::InvalidBinding(
                "asset transfer state policy is not a governed member",
            ));
        }
    }
    Ok(member)
}
