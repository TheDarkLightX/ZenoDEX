use zenodex_global_settlement_abi_v1::{
    lane_capability_registry_root_v1, resolve_lane_capability_v1,
    validate_lane_capability_registry_v1, LaneCapabilityDispositionV1, LaneIdV1,
    LANE_CAPABILITY_REGISTRY_V1,
};

#[test]
fn registry_is_exactly_twelve_lanes_and_103_capabilities() {
    // Arrange / Act
    validate_lane_capability_registry_v1().unwrap();
    let capability_count: usize = LANE_CAPABILITY_REGISTRY_V1
        .iter()
        .map(|row| row.capability_ids.len())
        .sum();

    // Assert
    assert_eq!(LANE_CAPABILITY_REGISTRY_V1.len(), 12);
    assert_eq!(capability_count, 103);
    let disabled: Vec<_> = LANE_CAPABILITY_REGISTRY_V1
        .iter()
        .filter(|row| {
            row.disposition == LaneCapabilityDispositionV1::DISABLED_PENDING_COMPLETE_PROFILE
        })
        .collect();
    assert_eq!(disabled.len(), 1);
    assert_eq!(disabled[0].lane_id, LaneIdV1::EXTERNAL_CUSTODY);
    assert_eq!(disabled[0].capability_ids.len(), 9);
}

#[test]
fn every_declared_capability_resolves_and_cross_lane_aliases_reject() {
    // Arrange / Act / Assert
    for row in LANE_CAPABILITY_REGISTRY_V1 {
        for capability_id in row.capability_ids {
            assert_eq!(
                resolve_lane_capability_v1(row.lane_id, capability_id).unwrap(),
                *capability_id
            );
        }
    }
    assert!(resolve_lane_capability_v1(LaneIdV1::ASSET_TRANSFER, "teleport_supply").is_err());
    assert!(resolve_lane_capability_v1(LaneIdV1::FARM_INCENTIVES, "exact_in_swap").is_err());
}

#[test]
fn registry_root_matches_the_python_vector() {
    // Arrange / Act / Assert
    assert_eq!(
        lane_capability_registry_root_v1().unwrap().as_str(),
        "0x9dc72bc86a0e6081ca3fbe6c371803119bc6bf623fd87ceee2deba0d4192e465"
    );
}
