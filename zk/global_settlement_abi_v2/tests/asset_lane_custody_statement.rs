use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, prepare_asset_lane_custody_global_statement_v2,
    transition_asset_lane_custody_v2, AssetLaneCommandV2, AssetLaneContextV2,
    AssetLaneCustodyResultV2, AssetLaneCustodyStateV2, AssetLaneCustodyStatementResultV2,
    AssetLaneRouteV2, GlobalEconomicStateV2, ValidateCanonicalV2,
    ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/asset_lane_custody_statement_v2_golden.json");
const GOLDEN_SCHEMA: &str = "zenodex/asset-lane-custody-statement-golden/v2";

#[derive(Deserialize)]
struct StatementFixtureV2 {
    schema: String,
    authority: String,
    cases: Vec<StatementCaseV2>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct StatementCaseV2 {
    name: String,
    route: AssetLaneRouteV2,
    context: Value,
    pre_state: Value,
    command: Value,
    global_pre: Value,
    global_post: Value,
    frame_sha256: String,
    statement: Value,
}

fn fixture() -> StatementFixtureV2 {
    let fixture: StatementFixtureV2 =
        serde_json::from_str(GOLDEN).expect("committed statement fixture must parse");
    assert_eq!(fixture.schema, GOLDEN_SCHEMA);
    assert_eq!(fixture.authority, "NONE");
    fixture
}

fn typed<T>(value: &Value) -> T
where
    T: DeserializeOwned + Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&canonical_bytes_v2(value).expect("fixture value encodes"))
        .expect("fixture value is canonical and valid")
}

fn typed_case(
    case: &StatementCaseV2,
) -> (
    AssetLaneContextV2,
    AssetLaneCustodyStateV2,
    AssetLaneCommandV2,
    GlobalEconomicStateV2,
    GlobalEconomicStateV2,
) {
    let command = match case.route {
        AssetLaneRouteV2::TRANSFER => AssetLaneCommandV2::Transfer(typed(&case.command)),
        AssetLaneRouteV2::MANAGED_LIFECYCLE => {
            AssetLaneCommandV2::ManagedLifecycle(typed(&case.command))
        }
        AssetLaneRouteV2::COORDINATOR => panic!("golden statement route must select a leaf"),
    };
    (
        typed(&case.context),
        typed(&case.pre_state),
        command,
        typed(&case.global_pre),
        typed(&case.global_post),
    )
}

#[test]
fn all_golden_cases_replay_to_the_exact_four_field_canonical_payload() {
    let fixture = fixture();
    assert_eq!(fixture.cases.len(), 5);
    for case in &fixture.cases {
        assert_eq!(case.frame_sha256.len(), 64, "{} frame digest", case.name);
        assert!(
            case.frame_sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f')),
            "{} frame digest",
            case.name
        );
        let (context, pre_state, command, global_pre, global_post) = typed_case(case);
        let direct = transition_asset_lane_custody_v2(&context, &pre_state, &command)
            .unwrap_or_else(|error| panic!("{} coordinator failed: {error}", case.name));
        let AssetLaneCustodyResultV2::Accepted(accepted) = direct else {
            panic!("{} coordinator unexpectedly rejected", case.name)
        };
        assert_eq!(accepted.route(), case.route);

        let first = prepare_asset_lane_custody_global_statement_v2(
            &context,
            &pre_state,
            &command,
            &global_pre,
            &global_post,
        )
        .unwrap_or_else(|error| panic!("{} statement failed: {error}", case.name));
        let second = prepare_asset_lane_custody_global_statement_v2(
            &context,
            &pre_state,
            &command,
            &global_pre,
            &global_post,
        )
        .expect("statement replay prepares");
        assert_eq!(first, second, "{} replay changed", case.name);
        let AssetLaneCustodyStatementResultV2::Statement(bytes) = first else {
            panic!("{} lawful global frame must produce a statement", case.name)
        };
        assert_eq!(
            bytes,
            canonical_bytes_v2(&case.statement).unwrap(),
            "{} statement bytes differ from the independent fixture",
            case.name
        );

        let decoded: Value = serde_json::from_slice(&bytes).unwrap();
        let object = decoded.as_object().expect("statement is an object");
        assert_eq!(object.len(), 4);
        assert_eq!(
            object.get("schema").and_then(Value::as_str),
            Some(ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2)
        );
        assert_eq!(
            canonical_bytes_v2(object.get("module_journal").unwrap()).unwrap(),
            canonical_bytes_v2(accepted.module_journal()).unwrap()
        );
        assert_eq!(
            object.get("global_pre_state_root").unwrap(),
            &serde_json::to_value(global_pre.state_root().unwrap()).unwrap()
        );
        assert_eq!(
            object.get("global_post_state_root").unwrap(),
            &serde_json::to_value(global_post.state_root().unwrap()).unwrap()
        );
    }
}

#[test]
fn global_frame_mutations_return_errors_without_statements() {
    let fixture = fixture();
    let case = fixture
        .cases
        .iter()
        .find(|case| case.name == "transfer_with_claim")
        .expect("claim-bearing transfer case");
    for mutation in 0..4 {
        let (context, pre_state, command, mut global_pre, mut global_post) = typed_case(case);
        match mutation {
            0 => global_post.liabilities[0].owner = "mallory".to_owned(),
            1 => global_post.replay_state.clear(),
            2 => global_post.custody[0].owner = "mallory".to_owned(),
            3 => {
                global_pre.writer_epoch += 1;
                global_post.writer_epoch += 1;
            }
            _ => unreachable!(),
        }
        prepare_asset_lane_custody_global_statement_v2(
            &context,
            &pre_state,
            &command,
            &global_pre,
            &global_post,
        )
        .expect_err("mutated global frame must fail without a statement");
    }
}

#[test]
fn coordinator_rejection_is_returned_before_malformed_global_inputs_are_read() {
    let fixture = fixture();
    let case = fixture
        .cases
        .iter()
        .find(|case| case.name == "transfer_with_claim")
        .expect("transfer case");
    let (mut context, pre_state, command, mut global_pre, mut global_post) = typed_case(case);
    context.occurrence = None;
    global_pre.schema = "broken".to_owned();
    global_post.schema = "also-broken".to_owned();

    let direct = transition_asset_lane_custody_v2(&context, &pre_state, &command)
        .expect("missing occurrence is a typed coordinator result");
    let AssetLaneCustodyResultV2::Rejected(expected) = direct else {
        panic!("missing occurrence must reject")
    };
    let prepared = prepare_asset_lane_custody_global_statement_v2(
        &context,
        &pre_state,
        &command,
        &global_pre,
        &global_post,
    )
    .expect("typed rejection must precede malformed global state");
    assert_eq!(
        prepared,
        AssetLaneCustodyStatementResultV2::Rejected(*expected)
    );
}
