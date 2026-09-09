use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, hash_bytes_sha256_v2, prepare_asset_lane_custody_global_frame_v2,
    AbiErrorV2, AssetLaneCustodyStatementResultV2, AssetLaneRejectCodeV2, AssetLaneRouteV2,
    AssetTransferRejectCodeV2, ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2,
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2, MAX_CANONICAL_INPUT_BYTES_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/asset_lane_custody_statement_v2_golden.json");

#[derive(Deserialize)]
struct Fixture {
    cases: Vec<Case>,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    name: String,
    route: AssetLaneRouteV2,
    context: Value,
    frame_sha256: String,
    pre_state: Value,
    command: Value,
    global_pre: Value,
    global_post: Value,
    statement: Value,
}

fn fixture() -> Fixture {
    serde_json::from_str(GOLDEN).expect("committed statement fixture must parse")
}

fn case(name: &str) -> Case {
    fixture()
        .cases
        .into_iter()
        .find(|case| case.name == name)
        .unwrap_or_else(|| panic!("golden case {name} must exist"))
}

fn route_byte(route: AssetLaneRouteV2) -> u8 {
    match route {
        AssetLaneRouteV2::TRANSFER => 0,
        AssetLaneRouteV2::MANAGED_LIFECYCLE => 1,
        AssetLaneRouteV2::COORDINATOR => panic!("frame fixtures must select a leaf"),
    }
}

fn components(case: &Case) -> [Vec<u8>; 5] {
    [
        canonical_bytes_v2(&case.context).unwrap(),
        canonical_bytes_v2(&case.pre_state).unwrap(),
        canonical_bytes_v2(&case.command).unwrap(),
        canonical_bytes_v2(&case.global_pre).unwrap(),
        canonical_bytes_v2(&case.global_post).unwrap(),
    ]
}

fn frame_from_parts(route: u8, parts: &[Vec<u8>; 5]) -> Vec<u8> {
    let mut frame = Vec::new();
    frame.extend_from_slice(ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2);
    frame.push(route);
    for part in parts {
        frame.extend_from_slice(&(part.len() as u32).to_le_bytes());
        frame.extend_from_slice(part);
    }
    frame
}

fn frame(case: &Case) -> Vec<u8> {
    frame_from_parts(route_byte(case.route), &components(case))
}

fn length_offsets(parts: &[Vec<u8>; 5]) -> [usize; 5] {
    let mut offsets = [0; 5];
    let mut cursor = ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2.len() + 1;
    for (index, part) in parts.iter().enumerate() {
        offsets[index] = cursor;
        cursor += 4 + part.len();
    }
    offsets
}

#[test]
fn all_five_golden_frames_produce_the_exact_statement_bytes() {
    let fixture = fixture();
    assert_eq!(fixture.cases.len(), 5);
    for case in &fixture.cases {
        let raw = frame(case);
        assert!(raw.len() <= MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2);
        assert_eq!(
            hash_bytes_sha256_v2(&raw),
            case.frame_sha256,
            "{} frame bytes",
            case.name
        );
        let result = prepare_asset_lane_custody_global_frame_v2(&raw)
            .unwrap_or_else(|error| panic!("{} frame failed: {error}", case.name));
        assert_eq!(
            result,
            AssetLaneCustodyStatementResultV2::Statement(
                canonical_bytes_v2(&case.statement).unwrap()
            ),
            "{} frame output",
            case.name
        );
    }
}

#[test]
fn framing_rejects_magic_routes_lengths_trailing_bytes_and_every_truncation() {
    let case = case("transfer_with_claim");
    let parts = components(&case);
    let valid = frame_from_parts(route_byte(case.route), &parts);

    let mut wrong_magic = valid.clone();
    wrong_magic[0] ^= 1;
    assert_eq!(
        prepare_asset_lane_custody_global_frame_v2(&wrong_magic),
        Err(AbiErrorV2::InvalidBinding(
            "asset lane custody global frame magic"
        ))
    );

    for unsupported in 2_u8..=u8::MAX {
        let mut wrong_route = valid.clone();
        wrong_route[ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2.len()] = unsupported;
        assert_eq!(
            prepare_asset_lane_custody_global_frame_v2(&wrong_route),
            Err(AbiErrorV2::InvalidBinding(
                "asset lane custody global frame route"
            )),
            "route {unsupported}"
        );
    }

    for offset in length_offsets(&parts) {
        let mut zero = valid.clone();
        zero[offset..offset + 4].copy_from_slice(&0_u32.to_le_bytes());
        assert_eq!(
            prepare_asset_lane_custody_global_frame_v2(&zero),
            Err(AbiErrorV2::InvalidBounds(
                "asset lane custody global frame component bytes"
            ))
        );

        let mut oversize = valid.clone();
        oversize[offset..offset + 4]
            .copy_from_slice(&((MAX_CANONICAL_INPUT_BYTES_V2 as u32) + 1).to_le_bytes());
        assert_eq!(
            prepare_asset_lane_custody_global_frame_v2(&oversize),
            Err(AbiErrorV2::InvalidBounds(
                "asset lane custody global frame component bytes"
            ))
        );
    }

    let mut trailing = valid.clone();
    trailing.push(0);
    assert_eq!(
        prepare_asset_lane_custody_global_frame_v2(&trailing),
        Err(AbiErrorV2::InvalidBounds(
            "asset lane custody global frame structure"
        ))
    );

    let over_maximum = vec![0; MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 + 1];
    assert_eq!(
        prepare_asset_lane_custody_global_frame_v2(&over_maximum),
        Err(AbiErrorV2::InvalidBounds(
            "asset lane custody global frame bytes"
        ))
    );

    let mut malformed_first_and_truncated_last = valid[..valid.len() - 1].to_vec();
    malformed_first_and_truncated_last[length_offsets(&parts)[0] + 4] = 0xff;
    assert_eq!(
        prepare_asset_lane_custody_global_frame_v2(&malformed_first_and_truncated_last),
        Err(AbiErrorV2::InvalidBounds(
            "asset lane custody global frame structure"
        ))
    );

    for end in 0..valid.len() {
        assert_eq!(
            prepare_asset_lane_custody_global_frame_v2(&valid[..end]),
            Err(AbiErrorV2::InvalidBounds(
                "asset lane custody global frame structure"
            )),
            "truncation at byte {end}"
        );
    }

    assert_eq!(
        MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2,
        8 + 1 + 5 * (4 + MAX_CANONICAL_INPUT_BYTES_V2)
    );
    assert_eq!(MAX_CANONICAL_INPUT_BYTES_V2, 1_048_576);
    assert_eq!(MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2, 5_242_909);
}

#[test]
fn all_components_decode_before_a_typed_leaf_rejection_is_returned() {
    let mut leaf_reject_case = case("transfer_with_claim");
    leaf_reject_case.context["occurrence"] = Value::Null;

    let result = prepare_asset_lane_custody_global_frame_v2(&frame(&leaf_reject_case))
        .expect("validly framed missing occurrence is a typed rejection");
    let AssetLaneCustodyStatementResultV2::Rejected(rejected_output) = result else {
        panic!("missing occurrence must not produce statement bytes")
    };
    assert_eq!(rejected_output.route(), AssetLaneRouteV2::TRANSFER);
    assert_eq!(
        rejected_output.code(),
        AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::MISSING_OCCURRENCE)
    );
    assert_eq!(
        rejected_output.pre_state_root(),
        rejected_output.post_state_root()
    );
    assert!(rejected_output.effects().is_empty());

    let mut parts = components(&leaf_reject_case);
    parts[4] = b"{".to_vec();
    assert!(matches!(
        prepare_asset_lane_custody_global_frame_v2(&frame_from_parts(0, &parts)),
        Err(AbiErrorV2::CanonicalEncoding(_))
    ));
}

#[test]
fn valid_frame_with_a_global_semantic_mismatch_returns_an_abi_error() {
    let mut forged = case("transfer_with_claim");
    forged.global_post["liabilities"][0]["owner"] = Value::String("mallory".to_owned());
    assert_eq!(
        prepare_asset_lane_custody_global_frame_v2(&frame(&forged)),
        Err(AbiErrorV2::InvalidBinding(
            "custody global claimant or custody frame changed"
        ))
    );
}
