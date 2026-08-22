use std::fs;
use std::path::PathBuf;

use serde_json::{json, Value};
use zenodex_global_settlement_abi_v1::{
    hash_global_v1, validate_m6_capability_profile_binding_v1, EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    M6_CAPABILITY_MANIFEST_ROOT_V1, M6_CAPABILITY_POLICY_KIND_V1,
    M6_CAPABILITY_PROFILE_COMMAND_KIND_V1,
};

fn fixture_profile() -> EconomicProfileSnapshotV1 {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    serde_json::from_value(fixture["vectors"]["economic_profile"]["canonical"].clone()).unwrap()
}

fn registry(policy_root: &str) -> EconomicPolicyRegistryV1 {
    EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![EconomicPolicyBindingV1 {
            policy_kind: M6_CAPABILITY_POLICY_KIND_V1.to_owned(),
            command_kind: M6_CAPABILITY_PROFILE_COMMAND_KIND_V1.to_owned(),
            policy_root: RootV1::parse(policy_root, "M6 capability test root", false).unwrap(),
        }],
    }
}

fn bind_registry(
    mut profile: EconomicProfileSnapshotV1,
    registry: &EconomicPolicyRegistryV1,
) -> EconomicProfileSnapshotV1 {
    profile.policy_registry_root = registry.registry_root().unwrap();
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": profile.authority_epoch,
        "lane_registry_root": profile.lane_registry_root,
        "lane_coordinator_registry_root": profile.lane_coordinator_registry_root,
        "route_registry_root": profile.route_registry_root,
        "proof_shape_root": profile.proof_shape_root,
        "root_image_id": profile.root_image_id,
        "verifier_registry_root": profile.verifier_registry_root,
        "migration_registry_root": profile.migration_registry_root,
        "policy_registry_root": profile.policy_registry_root,
        "terminal_registry_root": profile.terminal_registry_root,
    });
    profile.profile_id = hash_global_v1("global-economic-profile-content-v1", &content).unwrap();
    profile.validate().unwrap();
    profile
}

#[test]
fn exact_capability_manifest_is_bound_through_profile_policy_registry() {
    let registry = registry(M6_CAPABILITY_MANIFEST_ROOT_V1);
    let profile = bind_registry(fixture_profile(), &registry);

    validate_m6_capability_profile_binding_v1(&profile, &registry).unwrap();
}

#[test]
fn altered_or_missing_capability_manifest_rejects() {
    let altered = registry("0x0000000000000000000000000000000000000000000000000000000000000bad");
    let altered_profile = bind_registry(fixture_profile(), &altered);
    assert!(validate_m6_capability_profile_binding_v1(&altered_profile, &altered).is_err());

    let missing = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![],
    };
    let missing_profile = bind_registry(fixture_profile(), &missing);
    assert!(validate_m6_capability_profile_binding_v1(&missing_profile, &missing).is_err());
}
