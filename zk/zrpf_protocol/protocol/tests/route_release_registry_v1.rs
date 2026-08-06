use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, RouteModuleReleaseSelectionV1, RouteReleaseRegistryErrorV1,
    RouteReleaseRegistryV1, RouteSelectionKeyV1, MAX_ROUTE_DEPENDENCIES_V1,
    MAX_ROUTE_RELEASES_PER_REGISTRY_V1,
};

#[path = "route_release_registry_v1/binding.rs"]
mod binding;
#[path = "route_release_registry_v1/codec.rs"]
mod codec;
#[path = "route_release_registry_v1/identity.rs"]
mod identity;
#[path = "route_release_registry_v1/support.rs"]
mod support;

use support::{canonical_routes, module_release_selection, registry, route};

#[test]
fn route_count_boundaries_are_zero_one_two_hundred_fifty_six_and_two_hundred_fifty_seven() {
    // Arrange
    let one = vec![route(1, EconomicLaneIdV1::SpotLiquidity, 1)];
    let maximum = canonical_routes(
        (1..=u16::try_from(MAX_ROUTE_RELEASES_PER_REGISTRY_V1).unwrap())
            .map(|seed| route(seed, EconomicLaneIdV1::SpotLiquidity, 1))
            .collect(),
    );
    let above_maximum = canonical_routes(
        (1..=u16::try_from(MAX_ROUTE_RELEASES_PER_REGISTRY_V1 + 1).unwrap())
            .map(|seed| route(seed, EconomicLaneIdV1::SpotLiquidity, 1))
            .collect(),
    );

    // Act
    let empty = RouteReleaseRegistryV1::new(vec![]);
    let one_result = RouteReleaseRegistryV1::new(one);
    let maximum_result = RouteReleaseRegistryV1::new(maximum);
    let above_result = RouteReleaseRegistryV1::new(above_maximum);

    // Assert
    assert_eq!(empty, Err(RouteReleaseRegistryErrorV1::EmptyRegistry));
    assert_eq!(one_result.unwrap().routes().len(), 1);
    assert_eq!(
        maximum_result.unwrap().routes().len(),
        MAX_ROUTE_RELEASES_PER_REGISTRY_V1
    );
    assert_eq!(
        above_result,
        Err(RouteReleaseRegistryErrorV1::TooManyRoutes {
            actual: MAX_ROUTE_RELEASES_PER_REGISTRY_V1 + 1,
            maximum: MAX_ROUTE_RELEASES_PER_REGISTRY_V1,
        })
    );
}

#[test]
fn selection_dependency_boundaries_are_zero_one_eight_and_nine() {
    // Arrange
    let one = vec![module_release_selection(EconomicLaneIdV1::AssetTransfer, 1)];
    let maximum: Vec<_> = EconomicLaneIdV1::ALL[..MAX_ROUTE_DEPENDENCIES_V1]
        .iter()
        .enumerate()
        .map(|(index, lane)| module_release_selection(*lane, index as u16 + 1))
        .collect();
    let above_maximum: Vec<_> = EconomicLaneIdV1::ALL[..=MAX_ROUTE_DEPENDENCIES_V1]
        .iter()
        .enumerate()
        .map(|(index, lane)| module_release_selection(*lane, index as u16 + 1))
        .collect();

    // Act
    let empty = RouteSelectionKeyV1::new(support::root(90), vec![]);
    let one_result = RouteSelectionKeyV1::new(support::root(90), one);
    let maximum_result = RouteSelectionKeyV1::new(support::root(90), maximum);
    let above_result = RouteSelectionKeyV1::new(support::root(90), above_maximum);

    // Assert
    assert_eq!(
        empty,
        Err(RouteReleaseRegistryErrorV1::EmptySelectionDependencies)
    );
    assert_eq!(one_result.unwrap().module_releases().len(), 1);
    assert_eq!(
        maximum_result.unwrap().module_releases().len(),
        MAX_ROUTE_DEPENDENCIES_V1
    );
    assert_eq!(
        above_result,
        Err(RouteReleaseRegistryErrorV1::TooManySelectionDependencies {
            actual: MAX_ROUTE_DEPENDENCIES_V1 + 1,
            maximum: MAX_ROUTE_DEPENDENCIES_V1,
        })
    );
}

#[test]
fn selection_dependencies_are_unique_and_lane_sorted() {
    // Arrange
    let asset = module_release_selection(EconomicLaneIdV1::AssetTransfer, 1);
    let spot = module_release_selection(EconomicLaneIdV1::SpotLiquidity, 2);
    let caller_owned = vec![spot, asset];
    let before = caller_owned.clone();

    // Act
    let duplicate = RouteSelectionKeyV1::new(support::root(90), vec![asset, asset]);
    let reversed = RouteSelectionKeyV1::new(support::root(90), caller_owned.clone());

    // Assert
    assert_eq!(
        duplicate,
        Err(RouteReleaseRegistryErrorV1::DuplicateSelectionLane(
            EconomicLaneIdV1::AssetTransfer
        ))
    );
    assert_eq!(
        reversed,
        Err(RouteReleaseRegistryErrorV1::NonCanonicalSelectionLaneOrder { position: 1 })
    );
    assert_eq!(caller_owned, before);
}

#[test]
fn exact_selector_resolves_and_unknown_command_or_release_rejects_without_fallback() {
    // Arrange
    let expected = route(10, EconomicLaneIdV1::SpotLiquidity, 1);
    let registry = registry(vec![expected.clone()]);
    let before = registry.clone();
    let exact = RouteSelectionKeyV1::from_route(&expected);
    let wrong_command =
        RouteSelectionKeyV1::new(support::root(11), exact.module_releases().to_vec()).unwrap();
    let wrong_release = RouteSelectionKeyV1::new(
        exact.command_variant_root(),
        vec![module_release_selection(EconomicLaneIdV1::SpotLiquidity, 2)],
    )
    .unwrap();

    // Act
    let resolved = registry.resolve(&exact);
    let missing_command = registry.resolve(&wrong_command);
    let missing_release = registry.resolve(&wrong_release);

    // Assert
    assert_eq!(
        resolved.unwrap().route_release_id(),
        expected.route_release_id()
    );
    assert_eq!(
        missing_command,
        Err(RouteReleaseRegistryErrorV1::UnknownRouteSelection)
    );
    assert_eq!(
        missing_release,
        Err(RouteReleaseRegistryErrorV1::UnknownRouteSelection)
    );
    assert_eq!(registry, before);
}

#[test]
fn only_the_selection_key_sorted_permutation_is_accepted() {
    // Arrange
    let routes = [
        route(1, EconomicLaneIdV1::SpotLiquidity, 1),
        route(2, EconomicLaneIdV1::SpotLiquidity, 1),
        route(3, EconomicLaneIdV1::SpotLiquidity, 1),
    ];
    let permutations = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];

    // Act
    let accepted = permutations
        .iter()
        .filter(|order| {
            RouteReleaseRegistryV1::new(order.iter().map(|index| routes[*index].clone()).collect())
                .is_ok()
        })
        .count();

    // Assert
    assert_eq!(accepted, 1);
}

#[test]
fn release_selection_value_is_plain_data_without_authority_constructor() {
    // Arrange / Act
    let value = RouteModuleReleaseSelectionV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        module_release_selection(EconomicLaneIdV1::SpotLiquidity, 1).module_release_id(),
    );

    // Assert
    assert_eq!(value.lane_id(), EconomicLaneIdV1::SpotLiquidity);
}
