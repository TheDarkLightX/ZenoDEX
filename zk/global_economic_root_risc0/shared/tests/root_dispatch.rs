#[path = "../../test_support/mod.rs"]
mod support;

use zenodex_economic_initial_state_risc0_shared::prepare_economic_initial_state_v1;
use zenodex_global_economic_epoch_risc0_shared as epoch;
use zenodex_global_economic_root_risc0_shared::*;

fn prepared(input: RootGuestInputV1) -> PreparedRootV1 {
    prepare_root_input_v1(&canonical_root_input_bytes_v1(&input).unwrap()).unwrap()
}

#[test]
fn genesis_and_epoch_preserve_exact_existing_journals_and_one_profile_image() {
    let image = epoch::image_id_root_v1([1; 8]).unwrap();
    let initial = support::initial_input(image.as_str());
    let expected = prepare_economic_initial_state_v1(initial.clone()).unwrap();
    let genesis = prepared(support::initial_root_input(image.as_str()));
    assert_eq!(genesis.kind(), RootStatementKindV1::Initialization);
    assert_eq!(genesis.journal_bytes(), expected.journal_bytes());
    assert!(genesis.child_claims().is_empty());
    for count in [1, 8] {
        let input = support::epoch_input(&initial, count, [2; 8]);
        let root = prepared(RootGuestInputV1::RecursiveEpochV1(
            epoch::GlobalEconomicRecursiveGuestInputV1::DirectEpoch(input.clone()),
        ));
        assert_eq!(root.kind(), RootStatementKindV1::DirectEpoch);
        assert_eq!(root.root_image_id(), genesis.root_image_id());
        assert_eq!(root.journal_bytes(), input.certificate_journal_bytes);
        assert_eq!(root.child_claims().len(), count);
        for (claim, expected) in root.child_claims().iter().zip(&input.route_receipts) {
            assert_eq!(claim.image_id(), expected.image_id);
            assert_eq!(claim.journal_bytes(), expected.journal_bytes);
        }
    }
}

#[test]
fn aggregate_branches_preserve_order_and_bind_every_child_to_the_root_image() {
    let image = [1; 8];
    let initial = support::initial_input(epoch::image_id_root_v1(image).unwrap().as_str());
    for count in [9, 64] {
        let direct = support::epoch_input(&initial, count, [2; 8]);
        for group in support::aggregation_inputs(&direct) {
            let root = prepared(RootGuestInputV1::RecursiveEpochV1(
                epoch::GlobalEconomicRecursiveGuestInputV1::CommandAggregation(group.clone()),
            ));
            assert_eq!(root.kind(), RootStatementKindV1::CommandAggregation);
            assert_eq!(root.journal_bytes(), group.aggregation_journal_bytes);
            assert_eq!(root.child_claims().len(), group.route_receipts.len());
        }
        let input = support::aggregated_input(&direct, image);
        let root = prepared(RootGuestInputV1::RecursiveEpochV1(
            epoch::GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(input.clone()),
        ));
        assert_eq!(root.kind(), RootStatementKindV1::AggregatedEpoch);
        assert_eq!(root.child_claims().len(), count.div_ceil(8));
        assert_eq!(root.journal_bytes(), direct.certificate_journal_bytes);
        let mut foreign = input.clone();
        foreign.command_aggregation_receipts[0].image_id[0] ^= 1;
        let mut reversed = input.clone();
        reversed.command_aggregation_receipts.reverse();
        let mut missing = input;
        missing.command_aggregation_receipts.pop();
        for invalid in [foreign, reversed, missing] {
            assert!(
                canonical_root_input_bytes_v1(&RootGuestInputV1::RecursiveEpochV1(
                    epoch::GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(invalid),
                ))
                .is_err()
            );
        }
    }
}

#[test]
fn frame_tags_lengths_trailing_bytes_and_noncanonical_payloads_fail_closed() {
    let image = epoch::image_id_root_v1([1; 8]).unwrap();
    let frame =
        canonical_root_input_bytes_v1(&support::initial_root_input(image.as_str())).unwrap();
    for length in 0..ROOT_INPUT_HEADER_BYTES_V1 {
        assert_eq!(
            prepare_root_input_v1(&frame[..length]),
            Err(RootGuestErrorV1::Frame)
        );
    }
    let mut unknown = frame.clone();
    unknown[8] = 2;
    assert_eq!(prepare_root_input_v1(&unknown), Err(RootGuestErrorV1::Tag));
    let mut wrong_tag = frame.clone();
    wrong_tag[8] = 1;
    assert!(prepare_root_input_v1(&wrong_tag).is_err());
    let mut bad_magic = frame.clone();
    bad_magic[0] ^= 1;
    assert_eq!(
        prepare_root_input_v1(&bad_magic),
        Err(RootGuestErrorV1::Frame)
    );
    let mut trailing = frame.clone();
    trailing.push(0);
    assert_eq!(
        prepare_root_input_v1(&trailing),
        Err(RootGuestErrorV1::Frame)
    );
    let mut declared = frame.clone();
    declared[9..13].copy_from_slice(&u32::MAX.to_le_bytes());
    assert_eq!(
        prepare_root_input_v1(&declared),
        Err(RootGuestErrorV1::Bounds)
    );
    declared[9..13].copy_from_slice(&0u32.to_le_bytes());
    assert_eq!(
        prepare_root_input_v1(&declared),
        Err(RootGuestErrorV1::Bounds)
    );
    assert_eq!(
        prepare_root_input_v1(&frame[..frame.len() - 1]),
        Err(RootGuestErrorV1::Frame)
    );
    let mut padded = frame;
    padded.push(b'\n');
    let length = (padded.len() - ROOT_INPUT_HEADER_BYTES_V1) as u32;
    padded[9..13].copy_from_slice(&length.to_le_bytes());
    assert!(matches!(
        prepare_root_input_v1(&padded),
        Err(RootGuestErrorV1::InitialState(_))
    ));
}

#[test]
fn each_private_tag_enforces_its_own_payload_ceiling_before_decode() {
    for (tag, limit) in [(0u8, 8u32 * 1024 * 1024), (1, 2 * 1024 * 1024)] {
        let mut header = ROOT_INPUT_MAGIC_V1.to_vec();
        header.push(tag);
        header.extend_from_slice(&limit.to_le_bytes());
        assert_eq!(prepare_root_input_v1(&header), Err(RootGuestErrorV1::Frame));
        header[9..13].copy_from_slice(&(limit + 1).to_le_bytes());
        assert_eq!(
            prepare_root_input_v1(&header),
            Err(RootGuestErrorV1::Bounds)
        );
    }
}

#[test]
fn wrong_journal_family_context_and_recursive_noncanonical_bytes_reject() {
    let image = epoch::image_id_root_v1([1; 8]).unwrap();
    let initial = support::initial_input(image.as_str());
    let exact = support::epoch_input(&initial, 1, [2; 8]);
    let mut wrong_journal = exact.clone();
    wrong_journal.certificate_journal_bytes = prepare_economic_initial_state_v1(initial)
        .unwrap()
        .journal_bytes()
        .to_vec();
    let mut wrong_context = exact.clone();
    let mut certificate: epoch::GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&wrong_context.certificate_journal_bytes).unwrap();
    certificate.writer_epoch += 1;
    wrong_context.certificate_journal_bytes =
        epoch::canonical_json_bytes_v1(&certificate, "drift").unwrap();
    for invalid in [wrong_journal, wrong_context] {
        assert!(
            canonical_root_input_bytes_v1(&RootGuestInputV1::RecursiveEpochV1(
                epoch::GlobalEconomicRecursiveGuestInputV1::DirectEpoch(invalid),
            ))
            .is_err()
        );
    }
    let mut frame = canonical_root_input_bytes_v1(&RootGuestInputV1::RecursiveEpochV1(
        epoch::GlobalEconomicRecursiveGuestInputV1::DirectEpoch(exact),
    ))
    .unwrap();
    frame.push(0);
    let length = (frame.len() - ROOT_INPUT_HEADER_BYTES_V1) as u32;
    frame[9..13].copy_from_slice(&length.to_le_bytes());
    assert_eq!(
        prepare_root_input_v1(&frame),
        Err(RootGuestErrorV1::NonCanonical)
    );
}
