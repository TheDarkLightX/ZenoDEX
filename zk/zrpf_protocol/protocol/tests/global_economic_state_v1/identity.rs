use super::support::*;

#[test]
fn state_root_matches_an_independent_manual_reconstruction_and_fixed_vector() {
    // Arrange.
    let state =
        GlobalEconomicStateV1::new(state_content_with_lanes(lane_state_roots(100)).unwrap())
            .unwrap();
    let content = state.content();
    let domain = b"zenodex.global_settlement.global_economic_state_root.v1";

    // Act: reconstruct the normative preimage without the production root helper.
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u16).to_be_bytes());
    hasher.update(domain);
    hasher.update(GLOBAL_ECONOMIC_STATE_VERSION_V1.to_be_bytes());
    hasher.update(content.application_id().as_bytes());
    hasher.update(content.chain_or_domain_id().as_bytes());
    hasher.update(content.height().to_be_bytes());
    hasher.update(content.writer_epoch().to_be_bytes());
    hasher.update(content.profile_id().as_bytes());
    hasher.update([content.lane_state_roots().len() as u8]);
    for lane in content.lane_state_roots() {
        hasher.update([lane.lane_id().code()]);
        hasher.update(lane.state_root().as_bytes());
    }
    let partitions = content.partition_roots();
    for root in [
        partitions.balances_root(),
        partitions.supplies_root(),
        partitions.custody_root(),
        partitions.liabilities_root(),
        partitions.reserves_root(),
        partitions.oracle_occurrences_root(),
        partitions.replay_state_root(),
        partitions.terminal_obligations_root(),
        partitions.release_observations_root(),
        partitions.history_root(),
        partitions.external_outbox_root(),
        partitions.object_release_registry_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    let manual: [u8; 32] = hasher.finalize().into();

    // Assert.
    assert_eq!(state.state_root().as_bytes(), &manual);
    assert_eq!(
        manual,
        [
            244, 178, 72, 247, 178, 230, 45, 189, 155, 64, 111, 142, 86, 238, 21, 72, 111, 41, 119,
            50, 252, 137, 84, 70, 32, 102, 227, 54, 98, 195, 183, 81,
        ]
    );
}

#[test]
fn every_global_state_field_separates_content_derived_identity() {
    // Arrange.
    let baseline =
        GlobalEconomicStateV1::new(state_content_with_lanes(lane_state_roots(100)).unwrap())
            .unwrap();
    let baseline_root = baseline.state_root();
    let mut variants = Vec::new();
    let base = baseline.content();
    variants.push(
        GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
            application_id: application_id(9),
            chain_or_domain_id: base.chain_or_domain_id(),
            height: base.height(),
            writer_epoch: base.writer_epoch(),
            profile_id: base.profile_id(),
            lane_state_roots: base.lane_state_roots().to_vec(),
            partition_roots: base.partition_roots(),
        })
        .unwrap(),
    );
    variants.push(
        GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
            application_id: base.application_id(),
            chain_or_domain_id: domain_id(9),
            height: base.height(),
            writer_epoch: base.writer_epoch(),
            profile_id: base.profile_id(),
            lane_state_roots: base.lane_state_roots().to_vec(),
            partition_roots: base.partition_roots(),
        })
        .unwrap(),
    );
    for (height, writer_epoch, profile_id) in [
        (base.height() + 1, base.writer_epoch(), base.profile_id()),
        (base.height(), base.writer_epoch() + 1, base.profile_id()),
        (base.height(), base.writer_epoch(), profile_id(9)),
    ] {
        variants.push(
            GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
                application_id: base.application_id(),
                chain_or_domain_id: base.chain_or_domain_id(),
                height,
                writer_epoch,
                profile_id,
                lane_state_roots: base.lane_state_roots().to_vec(),
                partition_roots: base.partition_roots(),
            })
            .unwrap(),
        );
    }
    for lane_index in 0..EconomicLaneIdV1::ALL.len() {
        let mut changed_lane_roots = base.lane_state_roots().to_vec();
        changed_lane_roots[lane_index] = GlobalEconomicLaneStateRootV1::new(
            EconomicLaneIdV1::ALL[lane_index],
            root(700 + lane_index as u16),
        );
        variants.push(
            GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
                application_id: base.application_id(),
                chain_or_domain_id: base.chain_or_domain_id(),
                height: base.height(),
                writer_epoch: base.writer_epoch(),
                profile_id: base.profile_id(),
                lane_state_roots: changed_lane_roots,
                partition_roots: base.partition_roots(),
            })
            .unwrap(),
        );
    }
    let baseline_partitions = [
        root(300),
        root(301),
        root(302),
        root(303),
        root(304),
        root(305),
        root(306),
        root(307),
        root(308),
        root(309),
        root(310),
        root(900),
    ];
    for partition_index in 0..baseline_partitions.len() {
        let mut changed = baseline_partitions;
        changed[partition_index] = root(800 + partition_index as u16);
        variants.push(
            GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
                application_id: base.application_id(),
                chain_or_domain_id: base.chain_or_domain_id(),
                height: base.height(),
                writer_epoch: base.writer_epoch(),
                profile_id: base.profile_id(),
                lane_state_roots: base.lane_state_roots().to_vec(),
                partition_roots: GlobalEconomicPartitionRootsV1::new(
                    GlobalEconomicPartitionRootsInputV1 {
                        balances_root: changed[0],
                        supplies_root: changed[1],
                        custody_root: changed[2],
                        liabilities_root: changed[3],
                        reserves_root: changed[4],
                        oracle_occurrences_root: changed[5],
                        replay_state_root: changed[6],
                        terminal_obligations_root: changed[7],
                        release_observations_root: changed[8],
                        history_root: changed[9],
                        external_outbox_root: changed[10],
                        object_release_registry_root: changed[11],
                    },
                ),
            })
            .unwrap(),
        );
    }

    // Act.
    let roots: Vec<_> = variants
        .into_iter()
        .map(|content| GlobalEconomicStateV1::new(content).unwrap().state_root())
        .collect();

    // Assert.
    assert!(roots.into_iter().all(|root| root != baseline_root));
}

#[test]
fn object_release_pin_value_hash_has_an_independent_fixed_preimage() {
    // Arrange.
    let pin = EconomicObjectReleasePinV1::new(
        root(800),
        EconomicLaneIdV1::AssetTransfer,
        lane_release_id(801),
    );
    let domain = b"zenodex.global_settlement.economic_object_release_pin_value.v1";

    // Act.
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u16).to_be_bytes());
    hasher.update(domain);
    hasher.update(ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1.to_be_bytes());
    hasher.update(pin.object_id().as_bytes());
    hasher.update([pin.lane_id().code()]);
    hasher.update(pin.creating_release_id().as_bytes());
    let manual: [u8; 32] = hasher.finalize().into();

    // Assert.
    assert_eq!(pin.value_hash().unwrap().as_bytes(), &manual);
    assert_eq!(
        manual,
        [
            150, 90, 159, 123, 205, 89, 58, 28, 190, 214, 234, 107, 90, 254, 196, 174, 169, 44,
            103, 43, 139, 22, 107, 220, 75, 99, 51, 130, 43, 158, 115, 155,
        ]
    );
}

#[test]
fn partition_root_fields_are_individually_named_and_identity_bound() {
    // Arrange.
    let baseline = partition_roots(root(900));
    let input = GlobalEconomicPartitionRootsInputV1 {
        balances_root: root(300),
        supplies_root: root(301),
        custody_root: root(302),
        liabilities_root: root(303),
        reserves_root: root(304),
        oracle_occurrences_root: root(305),
        replay_state_root: root(306),
        terminal_obligations_root: root(307),
        release_observations_root: root(308),
        history_root: root(309),
        external_outbox_root: root(310),
        object_release_registry_root: root(900),
    };

    // Act.
    let reconstructed = GlobalEconomicPartitionRootsV1::new(input);

    // Assert.
    assert_eq!(reconstructed, baseline);
    assert_eq!(baseline.balances_root(), root(300));
    assert_eq!(baseline.supplies_root(), root(301));
    assert_eq!(baseline.custody_root(), root(302));
    assert_eq!(baseline.liabilities_root(), root(303));
    assert_eq!(baseline.reserves_root(), root(304));
    assert_eq!(baseline.oracle_occurrences_root(), root(305));
    assert_eq!(baseline.replay_state_root(), root(306));
    assert_eq!(baseline.terminal_obligations_root(), root(307));
    assert_eq!(baseline.release_observations_root(), root(308));
    assert_eq!(baseline.history_root(), root(309));
    assert_eq!(baseline.external_outbox_root(), root(310));
    assert_eq!(baseline.object_release_registry_root(), root(900));
}
