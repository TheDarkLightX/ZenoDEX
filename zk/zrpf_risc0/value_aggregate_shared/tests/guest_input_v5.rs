use zenodex_zrpf_protocol_v3::MAX_NODE_JOURNAL_BYTES_V4;
use zenodex_zrpf_risc0_value_aggregate_shared::{
    decode_exact_value_aggregate_guest_input_v5, encode_value_aggregate_guest_input_v5,
    ValueAggregateGuestInputErrorV5, ValueAggregateGuestInputV5, ValueAggregateLevelOneInputV5,
    ValueAggregateLevelTwoInputV5, MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5,
};

#[test]
fn one_codec_roundtrips_both_child_wire_kinds() {
    for input in [
        ValueAggregateGuestInputV5::LevelOne(
            ValueAggregateLevelOneInputV5::new(vec![vec![1, 2], vec![3]]).unwrap(),
        ),
        ValueAggregateGuestInputV5::LevelTwo(
            ValueAggregateLevelTwoInputV5::new(vec![vec![4], vec![5, 6]]).unwrap(),
        ),
    ] {
        let bytes = encode_value_aggregate_guest_input_v5(&input).unwrap();
        assert_eq!(
            decode_exact_value_aggregate_guest_input_v5(&bytes).unwrap(),
            input
        );
    }
}

#[test]
fn fixed_wire_contains_only_schema_kind_count_lengths_and_exact_children() {
    let input = ValueAggregateGuestInputV5::LevelOne(
        ValueAggregateLevelOneInputV5::new(vec![vec![0xaa, 0xbb]]).unwrap(),
    );
    assert_eq!(
        encode_value_aggregate_guest_input_v5(&input).unwrap(),
        vec![0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00, 0x02, 0xaa, 0xbb]
    );
}

#[test]
fn declared_count_rejects_before_child_allocation() {
    for (count, expected) in [
        (0, ValueAggregateGuestInputErrorV5::InvalidChildCount(0)),
        (9, ValueAggregateGuestInputErrorV5::InvalidChildCount(9)),
    ] {
        assert_eq!(
            decode_exact_value_aggregate_guest_input_v5(&[0, 1, 1, count]),
            Err(expected)
        );
    }
}

#[test]
fn declared_child_length_rejects_before_copying_payload() {
    let too_large = u32::try_from(MAX_NODE_JOURNAL_BYTES_V4 + 1)
        .unwrap()
        .to_be_bytes();
    let mut bytes = vec![0, 1, 1, 1];
    bytes.extend_from_slice(&too_large);
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&bytes),
        Err(ValueAggregateGuestInputErrorV5::ChildTooLarge {
            child: 0,
            actual: MAX_NODE_JOURNAL_BYTES_V4 + 1,
            maximum: MAX_NODE_JOURNAL_BYTES_V4,
        })
    );

    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&[0, 1, 1, 1, 0, 0, 0, 0]),
        Err(ValueAggregateGuestInputErrorV5::EmptyChild(0))
    );
}

#[test]
fn malformed_schema_kind_truncation_trailing_and_total_size_fail_closed() {
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&[0, 2, 1, 1]),
        Err(ValueAggregateGuestInputErrorV5::InvalidSchema(2))
    );
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&[0, 1, 3, 1]),
        Err(ValueAggregateGuestInputErrorV5::InvalidChildWireKind(3))
    );
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&[0, 1, 1, 1, 0, 0, 0, 2, 9]),
        Err(ValueAggregateGuestInputErrorV5::Truncated)
    );

    let input = ValueAggregateGuestInputV5::LevelTwo(
        ValueAggregateLevelTwoInputV5::new(vec![vec![7]]).unwrap(),
    );
    let mut trailing = encode_value_aggregate_guest_input_v5(&input).unwrap();
    trailing.push(0);
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&trailing),
        Err(ValueAggregateGuestInputErrorV5::TrailingBytes)
    );
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&vec![
            0;
            MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5
                + 1
        ]),
        Err(ValueAggregateGuestInputErrorV5::InputTooLarge {
            actual: MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 + 1,
            maximum: MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5,
        })
    );
}

#[test]
fn every_strict_prefix_of_a_valid_two_child_packet_rejects() {
    let input = ValueAggregateGuestInputV5::LevelOne(
        ValueAggregateLevelOneInputV5::new(vec![vec![1, 2, 3], vec![4, 5]]).unwrap(),
    );
    let bytes = encode_value_aggregate_guest_input_v5(&input).unwrap();
    for end in 0..bytes.len() {
        assert!(
            decode_exact_value_aggregate_guest_input_v5(&bytes[..end]).is_err(),
            "strict prefix {end} unexpectedly decoded"
        );
    }
    assert_eq!(
        decode_exact_value_aggregate_guest_input_v5(&bytes).unwrap(),
        input
    );
}
