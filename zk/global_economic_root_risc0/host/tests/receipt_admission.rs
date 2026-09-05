#[path = "../../test_support/mod.rs"]
mod support;

use zenodex_global_economic_root_risc0_host::{
    build_economic_root_executor_env_v1, economic_root_image_root_v1, EconomicRootHostErrorV1,
};
use zenodex_global_economic_root_risc0_methods::ZENODEX_ECONOMIC_ROOT_GUEST_ELF;

#[test]
fn placeholder_method_cannot_construct_a_proving_environment() {
    if !ZENODEX_ECONOMIC_ROOT_GUEST_ELF.is_empty() {
        return;
    }
    let input = support::initial_root_input(support::root(1).as_str());
    assert!(matches!(
        economic_root_image_root_v1(),
        Err(EconomicRootHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        build_economic_root_executor_env_v1(&input, vec![]),
        Err(EconomicRootHostErrorV1::PlaceholderMethod)
    ));
}

#[test]
fn actual_method_binding_rejects_a_foreign_profile_image() {
    if ZENODEX_ECONOMIC_ROOT_GUEST_ELF.is_empty() {
        return;
    }
    let input = support::initial_root_input(support::root(1).as_str());
    assert!(matches!(
        build_economic_root_executor_env_v1(&input, vec![]),
        Err(EconomicRootHostErrorV1::MethodBinding)
    ));
}
