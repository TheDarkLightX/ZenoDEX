#[path = "global_economic_state_v1/binding.rs"]
mod binding;
#[path = "global_economic_state_v1/codec.rs"]
mod codec;
#[path = "global_economic_state_v1/identity.rs"]
mod identity;
#[path = "economic_profile_snapshot_v1/support.rs"]
#[allow(dead_code)]
mod profile_support;
#[path = "global_economic_state_v1/route_resolution.rs"]
mod route_resolution;
#[path = "global_economic_state_v1/support.rs"]
mod support;

use support::*;

#[test]
fn lane_state_roots_require_the_closed_twelve_lane_order() {
    // Arrange.
    let valid = lane_state_roots(100);
    let mut duplicate = valid.clone();
    duplicate[1] = duplicate[0];
    let mut reordered = valid.clone();
    reordered.swap(4, 5);

    // Act.
    let too_few = state_content_with_lanes(valid[..11].to_vec());
    let exact = state_content_with_lanes(valid.clone());
    let mut too_many_lanes = valid;
    too_many_lanes.push(GlobalEconomicLaneStateRootV1::new(
        EconomicLaneIdV1::GovernanceMigration,
        root(999),
    ));
    let too_many = state_content_with_lanes(too_many_lanes);
    let duplicate_result = state_content_with_lanes(duplicate);
    let reordered_result = state_content_with_lanes(reordered);

    // Assert.
    assert_eq!(
        too_few,
        Err(GlobalEconomicStateErrorV1::WrongLaneStateRootCount {
            actual: 11,
            expected: 12,
        })
    );
    assert!(exact.is_ok());
    assert_eq!(
        too_many,
        Err(GlobalEconomicStateErrorV1::WrongLaneStateRootCount {
            actual: 13,
            expected: 12,
        })
    );
    assert_eq!(
        duplicate_result,
        Err(GlobalEconomicStateErrorV1::DuplicateLaneStateRoot(
            EconomicLaneIdV1::AssetTransfer,
        ))
    );
    assert_eq!(
        reordered_result,
        Err(GlobalEconomicStateErrorV1::NonCanonicalLaneStateRootOrder {
            position: 4,
            expected: EconomicLaneIdV1::ZusdMonetary,
            actual: EconomicLaneIdV1::PerpsMarket,
        })
    );
}

#[test]
fn height_and_writer_epoch_accept_zero_one_and_integer_maximum() {
    // Arrange / Act.
    let values: Vec<_> = [0, 1, u64::MAX]
        .into_iter()
        .map(|value| {
            GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
                application_id: application_id(1),
                chain_or_domain_id: domain_id(2),
                height: value,
                writer_epoch: value,
                profile_id: profile_id(3),
                lane_state_roots: lane_state_roots(100),
                partition_roots: partition_roots(root(900)),
            })
            .unwrap()
        })
        .collect();

    // Assert.
    assert_eq!(values[0].height(), 0);
    assert_eq!(values[1].writer_epoch(), 1);
    assert_eq!(values[2].height(), u64::MAX);
    assert_eq!(values[2].writer_epoch(), u64::MAX);
}

#[test]
fn object_release_pin_version_and_identity_are_closed() {
    // Arrange.
    let object_id = root(800);
    let release_id = lane_release_id(801);
    let pin =
        EconomicObjectReleasePinV1::new(object_id, EconomicLaneIdV1::AssetTransfer, release_id);

    // Act.
    let same =
        EconomicObjectReleasePinV1::new(object_id, EconomicLaneIdV1::AssetTransfer, release_id);
    let other_lane =
        EconomicObjectReleasePinV1::new(object_id, EconomicLaneIdV1::SpotLiquidity, release_id);
    let other_release = EconomicObjectReleasePinV1::new(
        object_id,
        EconomicLaneIdV1::AssetTransfer,
        lane_release_id(802),
    );

    // Assert.
    assert_eq!(pin.pin_version(), ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1);
    assert_eq!(pin.value_hash().unwrap(), same.value_hash().unwrap());
    assert_ne!(pin.value_hash().unwrap(), other_lane.value_hash().unwrap());
    assert_ne!(
        pin.value_hash().unwrap(),
        other_release.value_hash().unwrap()
    );
}
