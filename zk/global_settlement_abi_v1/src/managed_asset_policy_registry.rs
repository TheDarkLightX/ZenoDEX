//! Governed typed policy-registry membership for managed-asset issue and burn.
//!
//! The lifecycle lane module carries an opaque `asset_policy_registry_root`
//! and one state policy per asset. This core binds that root to one exact
//! typed registry whose root commits to the exact `ASSET_TRANSFER` module
//! release and the sorted policy rows, and whose root the active profile's
//! economic policy registry governs for the command kind. Membership then
//! requires the module's release, the command asset, and every carried state
//! policy to match the registry exactly. Direct lifecycle transitions never
//! consult the registry; it grants no proof, settlement, or publication
//! authority.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::managed_asset_lifecycle_lane_module::ManagedAssetLifecycleLaneModuleInputV1;
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecyclePolicyV1, MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{
    EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, RouteRegistryV1, RouteReleaseV1,
};

pub const MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1: &str =
    "zenodex/managed-asset-policy-registry/v1";
pub const MANAGED_ASSET_POLICY_KIND_V1: &str = "managed_asset_policy_v1";
pub const MAX_MANAGED_ASSET_POLICIES_V1: usize = 256;

/// Exact governed policy rows bound to one `ASSET_TRANSFER` module release.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetPolicyRegistryV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub policies: Vec<ManagedAssetLifecyclePolicyV1>,
}

impl ManagedAssetPolicyRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.module_release_id
            .validate("managed asset policy registry module release", false)?;
        if self.policies.len() > MAX_MANAGED_ASSET_POLICIES_V1 {
            return Err(AbiErrorV1::InvalidBounds("managed asset policy registry"));
        }
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder("managed asset policy registry"));
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("managed-asset-policy-registry-v1", self)
    }

    pub fn policy_for(&self, asset: &str) -> Option<&ManagedAssetLifecyclePolicyV1> {
        self.policies.iter().find(|policy| policy.asset == asset)
    }
}

/// Require the typed registry root to be the profile-governed managed-asset
/// policy root for the occurrence command kind.
pub fn require_governed_managed_asset_policy_registry_v1(
    profile: &EconomicProfileSnapshotV1,
    policy_registry: &EconomicPolicyRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    asset_policy_registry: &ManagedAssetPolicyRegistryV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    occurrence.validate()?;
    let asset_policy_registry_root = asset_policy_registry.registry_root()?;
    if policy_registry.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset policy registry outside profile",
        ));
    }
    let binding =
        policy_registry.require_binding(MANAGED_ASSET_POLICY_KIND_V1, &occurrence.command_kind)?;
    if binding.policy_root != asset_policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset policy registry root",
        ));
    }
    Ok(())
}

/// Return the governed member policy the lane module input executes under.
///
/// The input's opaque registry root must be the typed registry root, the
/// registry's module release must be the release the context and pre-state
/// execute under, the command asset must be a member, and every carried state
/// policy must equal its member exactly.
pub fn require_managed_asset_policy_membership_v1<'a>(
    asset_policy_registry: &'a ManagedAssetPolicyRegistryV1,
    module_input: &ManagedAssetLifecycleLaneModuleInputV1,
) -> AbiResultV1<&'a ManagedAssetLifecyclePolicyV1> {
    module_input.validate()?;
    if module_input.asset_policy_registry_root != asset_policy_registry.registry_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset lane module policy registry root",
        ));
    }
    if module_input.context.module_release_id != asset_policy_registry.module_release_id
        || module_input.pre_state.module_release_id != asset_policy_registry.module_release_id
    {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset policy registry module release",
        ));
    }
    let member = asset_policy_registry
        .policy_for(&module_input.command.asset)
        .ok_or(AbiErrorV1::InvalidBinding(
            "managed asset command asset absent from governed registry",
        ))?;
    for state_policy in &module_input.pre_state.policies {
        if asset_policy_registry.policy_for(&state_policy.asset) != Some(state_policy) {
            return Err(AbiErrorV1::InvalidBinding(
                "managed asset state policy is not a governed member",
            ));
        }
    }
    Ok(member)
}

/// Return the governed issue or burn route whose policy root is the registry root.
///
/// `RouteReleaseV1::issue_burn_policy_root` is the route-owned issue/burn
/// policy commitment; for managed issue and burn it must equal the exact typed
/// registry root before any route witness or receipt verification.
pub fn require_managed_asset_route_policy_root_v1<'a>(
    routes: &'a RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    asset_policy_registry: &ManagedAssetPolicyRegistryV1,
) -> AbiResultV1<&'a RouteReleaseV1> {
    occurrence.validate()?;
    let registry_root = asset_policy_registry.registry_root()?;
    if occurrence.command_kind != MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
        && occurrence.command_kind != MANAGED_ASSET_BURN_COMMAND_KIND_V1
    {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset route policy binding requires issue or burn",
        ));
    }
    let route =
        routes.route_for_command(&occurrence.command_kind, Some(&occurrence.route_release_id))?;
    if route.issue_burn_policy_root != registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset route issue/burn policy root",
        ));
    }
    Ok(route)
}
