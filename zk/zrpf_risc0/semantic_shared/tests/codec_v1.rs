use zenodex_zrpf_protocol_v3::{MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V3};
use zenodex_zrpf_risc0_semantic_shared::{
    decode_exact_semantic_guest_input_v1, encode_semantic_guest_input_v1,
    SemanticGuestInputErrorV1, SemanticGuestInputV1, SemanticGuestLeafDisclosureV1,
    SemanticGuestLevelOneDisclosureV1, MAX_SEMANTIC_GUEST_INPUT_BYTES_V1,
    SEMANTIC_GUEST_INPUT_SCHEMA_VERSION_V1,
};

const SELF_IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
const HEADER_BYTES: usize = 2 + (8 * 4) + 1;

fn leaf(byte: u8, opening: u8) -> SemanticGuestLeafDisclosureV1 {
    SemanticGuestLeafDisclosureV1::new(vec![byte; 3], [opening; 32]).unwrap()
}

fn group(
    byte: u8,
    leaves: Vec<SemanticGuestLeafDisclosureV1>,
) -> SemanticGuestLevelOneDisclosureV1 {
    SemanticGuestLevelOneDisclosureV1::new(vec![byte; 5], leaves).unwrap()
}

fn sample() -> SemanticGuestInputV1 {
    SemanticGuestInputV1::new(
        SELF_IMAGE_ID,
        vec![
            group(11, vec![leaf(21, 31), leaf(22, 32)]),
            group(12, vec![leaf(23, 33)]),
        ],
    )
    .unwrap()
}

fn raw_header(self_image_id: [u32; 8], group_count: u8) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&SEMANTIC_GUEST_INPUT_SCHEMA_VERSION_V1.to_be_bytes());
    for word in self_image_id {
        bytes.extend_from_slice(&word.to_be_bytes());
    }
    bytes.push(group_count);
    bytes
}

#[test]
fn valid_value_roundtrips_with_raw_openings_preserved() {
    let input = sample();
    let encoded = encode_semantic_guest_input_v1(&input).unwrap();
    let decoded = decode_exact_semantic_guest_input_v1(&encoded).unwrap();

    assert_eq!(decoded, input);
    assert_eq!(encode_semantic_guest_input_v1(&decoded).unwrap(), encoded);
    assert_eq!(
        decoded.level_one_disclosures()[0].leaves()[1].semantic_opening(),
        [32; 32]
    );
}

#[test]
fn semantic_opening_is_opaque_and_zero_is_preserved() {
    let input = SemanticGuestInputV1::new(
        SELF_IMAGE_ID,
        vec![group(
            1,
            vec![SemanticGuestLeafDisclosureV1::new(vec![2], [0; 32]).unwrap()],
        )],
    )
    .unwrap();
    let encoded = encode_semantic_guest_input_v1(&input).unwrap();
    let decoded = decode_exact_semantic_guest_input_v1(&encoded).unwrap();
    assert_eq!(
        decoded.level_one_disclosures()[0].leaves()[0].semantic_opening(),
        [0; 32]
    );
}

#[test]
fn every_truncated_prefix_rejects() {
    let encoded = encode_semantic_guest_input_v1(&sample()).unwrap();
    for end in 0..encoded.len() {
        assert!(
            decode_exact_semantic_guest_input_v1(&encoded[..end]).is_err(),
            "truncated prefix {end} unexpectedly decoded"
        );
    }
}

#[test]
fn trailing_bytes_and_stale_schema_reject() {
    let encoded = encode_semantic_guest_input_v1(&sample()).unwrap();
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&trailing),
        Err(SemanticGuestInputErrorV1::TrailingBytes)
    );

    let mut stale_schema = encoded;
    stale_schema[..2].copy_from_slice(&(SEMANTIC_GUEST_INPUT_SCHEMA_VERSION_V1 + 1).to_be_bytes());
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&stale_schema),
        Err(SemanticGuestInputErrorV1::InvalidSchema(2))
    );
}

#[test]
fn zero_and_oversized_level_one_journals_reject_before_payload_allocation() {
    let mut zero = raw_header(SELF_IMAGE_ID, 1);
    zero.extend_from_slice(&0u16.to_be_bytes());
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&zero),
        Err(SemanticGuestInputErrorV1::InvalidLevelOneJournalLength { length: 0 })
    );

    let oversized_length = u16::try_from(MAX_NODE_JOURNAL_BYTES_V3 + 1).unwrap();
    let mut oversized = raw_header(SELF_IMAGE_ID, 1);
    oversized.extend_from_slice(&oversized_length.to_be_bytes());
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&oversized),
        Err(SemanticGuestInputErrorV1::InvalidLevelOneJournalLength {
            length: MAX_NODE_JOURNAL_BYTES_V3 + 1,
        })
    );
}

#[test]
fn zero_and_oversized_leaf_journals_reject_before_payload_allocation() {
    let mut zero = raw_header(SELF_IMAGE_ID, 1);
    zero.extend_from_slice(&1u16.to_be_bytes());
    zero.push(7);
    zero.push(1);
    zero.extend_from_slice(&0u16.to_be_bytes());
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&zero),
        Err(SemanticGuestInputErrorV1::InvalidLeafJournalLength { length: 0 })
    );

    let oversized_length = u16::try_from(MAX_NODE_JOURNAL_BYTES_V3 + 1).unwrap();
    let mut oversized = raw_header(SELF_IMAGE_ID, 1);
    oversized.extend_from_slice(&1u16.to_be_bytes());
    oversized.push(7);
    oversized.push(1);
    oversized.extend_from_slice(&oversized_length.to_be_bytes());
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&oversized),
        Err(SemanticGuestInputErrorV1::InvalidLeafJournalLength {
            length: MAX_NODE_JOURNAL_BYTES_V3 + 1,
        })
    );
}

#[test]
fn ninth_group_and_ninth_leaf_reject() {
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&raw_header(SELF_IMAGE_ID, 9)),
        Err(SemanticGuestInputErrorV1::InvalidLevelOneCount(9))
    );

    let mut nine_leaves = raw_header(SELF_IMAGE_ID, 1);
    nine_leaves.extend_from_slice(&1u16.to_be_bytes());
    nine_leaves.push(7);
    nine_leaves.push(9);
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&nine_leaves),
        Err(SemanticGuestInputErrorV1::InvalidLeafCount(9))
    );
}

#[test]
fn zero_self_image_id_rejects() {
    assert_eq!(
        SemanticGuestInputV1::new([0; 8], vec![group(1, vec![leaf(2, 3)])]),
        Err(SemanticGuestInputErrorV1::ZeroSelfImageId)
    );
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&raw_header([0; 8], 1)),
        Err(SemanticGuestInputErrorV1::ZeroSelfImageId)
    );
}

#[test]
fn exact_maximum_formula_and_maximal_value_match() {
    let per_leaf = 2 + MAX_NODE_JOURNAL_BYTES_V3 + 32;
    let per_group = 2 + MAX_NODE_JOURNAL_BYTES_V3 + 1 + MAX_IMMEDIATE_CHILDREN_V3 * per_leaf;
    assert_eq!(
        MAX_SEMANTIC_GUEST_INPUT_BYTES_V1,
        HEADER_BYTES + MAX_IMMEDIATE_CHILDREN_V3 * per_group
    );
    assert_eq!(MAX_SEMANTIC_GUEST_INPUT_BYTES_V1, 297_147);

    let maximal_leaf =
        || SemanticGuestLeafDisclosureV1::new(vec![1; MAX_NODE_JOURNAL_BYTES_V3], [2; 32]).unwrap();
    let maximal_group = || {
        SemanticGuestLevelOneDisclosureV1::new(
            vec![3; MAX_NODE_JOURNAL_BYTES_V3],
            (0..MAX_IMMEDIATE_CHILDREN_V3)
                .map(|_| maximal_leaf())
                .collect(),
        )
        .unwrap()
    };
    let maximal = SemanticGuestInputV1::new(
        SELF_IMAGE_ID,
        (0..MAX_IMMEDIATE_CHILDREN_V3)
            .map(|_| maximal_group())
            .collect(),
    )
    .unwrap();
    let encoded = encode_semantic_guest_input_v1(&maximal).unwrap();
    assert_eq!(encoded.len(), MAX_SEMANTIC_GUEST_INPUT_BYTES_V1);
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&encoded).unwrap(),
        maximal
    );
}

#[test]
fn one_byte_over_global_maximum_rejects_before_decode() {
    assert_eq!(
        decode_exact_semantic_guest_input_v1(&vec![0; MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 + 1]),
        Err(SemanticGuestInputErrorV1::InputTooLarge {
            actual: MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 + 1,
            maximum: MAX_SEMANTIC_GUEST_INPUT_BYTES_V1,
        })
    );
}
