use zenodex_global_settlement_abi_v1::{
    transition_current_profile_lane_v1, CurrentProfileLaneCommandV1, CurrentProfileLaneStateV1,
    LaneIdV1, LaneTransitionRejectCodeV1, RootV1, LANE_CAPABILITY_REGISTRY_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "current profile lane gate test root",
        false,
    )
    .unwrap()
}

#[test]
fn current_profile_is_total_and_fail_closed_for_all_103_capabilities() {
    // Arrange / Act / Assert
    let mut count = 0usize;
    for row in LANE_CAPABILITY_REGISTRY_V1 {
        for capability_id in row.capability_ids {
            let state = CurrentProfileLaneStateV1 {
                lane_id: row.lane_id,
                lane_state_root: root(1),
            };
            let command = CurrentProfileLaneCommandV1 {
                lane_id: row.lane_id,
                capability_id: (*capability_id).to_owned(),
                command_body_hash: root(2),
            };
            let rejected = transition_current_profile_lane_v1(&state, &command).unwrap();
            let expected = if row.lane_id == LaneIdV1::EXTERNAL_CUSTODY {
                LaneTransitionRejectCodeV1::DISABLED_FEATURE
            } else {
                LaneTransitionRejectCodeV1::POLICY_REJECT
            };
            assert_eq!(rejected.code, expected);
            assert_eq!(rejected.pre_state_root, root(1));
            assert_eq!(rejected.post_state_root, root(1));
            assert!(rejected.effects.is_empty());
            count += 1;
        }
    }
    assert_eq!(count, 103);
}

#[test]
fn cross_lane_state_command_pair_rejects_without_effects() {
    // Arrange
    let state = CurrentProfileLaneStateV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        lane_state_root: root(3),
    };
    let command = CurrentProfileLaneCommandV1 {
        lane_id: LaneIdV1::SPOT_LIQUIDITY,
        capability_id: "exact_in_swap".to_owned(),
        command_body_hash: root(4),
    };

    // Act
    let rejected = transition_current_profile_lane_v1(&state, &command).unwrap();

    // Assert
    assert_eq!(rejected.code, LaneTransitionRejectCodeV1::INVALID_CONTEXT);
    assert_eq!(rejected.pre_state_root, root(3));
    assert_eq!(rejected.post_state_root, root(3));
    assert!(rejected.effects.is_empty());
}

#[test]
fn unknown_and_cross_lane_capabilities_fail_validation() {
    // Arrange
    let cross_lane = CurrentProfileLaneCommandV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        capability_id: "exact_in_swap".to_owned(),
        command_body_hash: root(5),
    };
    let unknown = CurrentProfileLaneCommandV1 {
        lane_id: LaneIdV1::FARM_INCENTIVES,
        capability_id: "teleport_supply".to_owned(),
        command_body_hash: root(5),
    };

    // Act / Assert
    assert!(cross_lane.validate().is_err());
    assert!(unknown.validate().is_err());
}

#[test]
fn current_profile_gate_command_root_matches_python_vector() {
    // Arrange
    let command = CurrentProfileLaneCommandV1 {
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        capability_id: "atomic_purchase_and_burn".to_owned(),
        command_body_hash: root(6),
    };

    // Act / Assert
    assert_eq!(
        command.command_root().unwrap().as_str(),
        "0x32e3980f3a32fe0aefcb60bf64b138853d9ace775a7a16ce91976c152f8fbf1a"
    );
}
