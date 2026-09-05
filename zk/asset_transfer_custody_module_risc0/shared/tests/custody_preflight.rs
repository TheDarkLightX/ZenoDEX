use zenodex_asset_transfer_custody_module_risc0_shared::{
    canonical_asset_transfer_guest_input_bytes_v1,
    prepare_asset_transfer_custody_module_from_canonical_bytes_v1,
    prepare_asset_transfer_custody_module_v1, AssetTransferGuestErrorV1,
    MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_V1,
};
use zenodex_asset_transfer_module_risc0_shared::{
    prepare_asset_transfer_module_from_canonical_bytes_v1, prepare_asset_transfer_module_v1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, transition_asset_transfer_lane_module_custody_v1,
    transition_asset_transfer_lane_module_v1, AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1, AssetTransferLaneModuleResultV1, EconomicAmountV1,
    LaneModuleTransitionJournalV1,
};

const FIXTURE: &str =
    include_str!("../../../../tests/data/asset_transfer_lane_module_custody_v1_golden.json");

fn vectors() -> serde_json::Value {
    let vectors: serde_json::Value =
        serde_json::from_str(FIXTURE).expect("custody fixture must be JSON");
    let cases = vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array");
    assert_eq!(cases.len(), 10);
    assert_eq!(
        cases
            .iter()
            .filter(|case| case.get("accepted").is_some())
            .count(),
        7
    );
    assert_eq!(
        cases
            .iter()
            .filter(|case| case.get("reject_code").is_some())
            .count(),
        3
    );
    vectors
}

fn physical_total(
    balances: &[EconomicAmountV1],
    custody: &[EconomicAmountV1],
    asset: &str,
) -> u128 {
    balances
        .iter()
        .chain(custody)
        .filter(|row| row.asset == asset)
        .map(|row| row.amount_atoms)
        .try_fold(0_u128, |total, amount| total.checked_add(amount))
        .expect("fixture physical total must fit u128")
}

fn input(case: &serde_json::Value) -> AssetTransferLaneModuleInputV1 {
    serde_json::from_value(case["input"].clone()).expect("fixture input must decode")
}

fn assert_accepted_fixture(
    case: &serde_json::Value,
    input: &AssetTransferLaneModuleInputV1,
    prepared: &zenodex_asset_transfer_custody_module_risc0_shared::PreparedAssetTransferModuleV1,
) {
    let expected: AssetTransferLaneModuleAcceptedV1 =
        serde_json::from_value(case["accepted"].clone()).expect("accepted fixture must decode");
    assert_eq!(prepared.accepted, expected, "{}", case["name"]);
    assert_eq!(prepared.input, *input, "{}", case["name"]);

    let expected_total: u128 = case["expected_total"]
        .as_str()
        .expect("expected total must be a decimal string")
        .parse()
        .expect("expected total must fit u128");
    let asset = input.command.asset.as_str();
    assert_eq!(
        physical_total(&input.pre_state.balances, &input.custody, asset),
        expected_total,
        "{} pre total",
        case["name"]
    );
    assert_eq!(
        physical_total(
            &prepared.accepted.private_port.post_state.balances,
            &prepared.accepted.private_port.post_state.custody,
            asset,
        ),
        expected_total,
        "{} post total",
        case["name"]
    );
    let conservation = prepared
        .accepted
        .effects
        .asset_conservation
        .iter()
        .find(|row| row.asset == asset)
        .expect("accepted fixture must contain the command asset conservation row");
    assert_eq!(conservation.owned_and_custodied_pre_atoms, expected_total);
    assert_eq!(conservation.owned_and_custodied_post_atoms, expected_total);
    assert_eq!(
        prepared.accepted.private_port.pre_state.custody, input.custody,
        "{} pre custody frame",
        case["name"]
    );
    assert_eq!(
        prepared.accepted.private_port.post_state.custody, input.custody,
        "{} post custody frame",
        case["name"]
    );
    assert_eq!(
        prepared.journal_bytes,
        canonical_bytes_v1(&expected.module_journal).expect("journal must encode"),
        "{} canonical journal bytes",
        case["name"]
    );
    let journal: LaneModuleTransitionJournalV1 = serde_json::from_slice(&prepared.journal_bytes)
        .expect("prepared journal bytes must decode");
    assert_eq!(journal, expected.module_journal, "{} journal", case["name"]);
    assert_eq!(
        prepared.journal_bytes,
        canonical_bytes_v1(&prepared.accepted.module_journal).expect("journal must re-encode")
    );
}

#[test]
fn accepted_fixture_values_totals_frames_and_journals_are_exact() {
    for case in vectors()["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .filter(|case| case.get("accepted").is_some())
    {
        let input = input(case);
        let input_bytes = canonical_asset_transfer_guest_input_bytes_v1(&input)
            .expect("accepted fixture input must canonicalize");
        let prepared = prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&input_bytes)
            .expect("accepted fixture input must prepare");
        assert_accepted_fixture(case, &input, &prepared);

        let typed = prepare_asset_transfer_custody_module_v1(input.clone())
            .expect("typed accepted fixture input must prepare");
        assert_eq!(typed, prepared, "{} typed/raw result", case["name"]);
    }
}

#[test]
fn zero_custody_matches_legacy_preflight_and_nonzero_custody_differs() {
    for case in vectors()["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .filter(|case| case.get("accepted").is_some())
    {
        let input = input(case);
        let successor = prepare_asset_transfer_custody_module_v1(input.clone())
            .expect("accepted fixture input must prepare");
        let legacy = prepare_asset_transfer_module_v1(input).expect("legacy must prepare");
        if successor.input.custody.is_empty() {
            assert_eq!(successor, legacy, "{} zero custody", case["name"]);
        } else {
            assert_eq!(
                successor.accepted.post_state, legacy.accepted.post_state,
                "{} post state frame",
                case["name"]
            );
            assert_eq!(
                successor.accepted.effects.rows, legacy.accepted.effects.rows,
                "{} movement rows",
                case["name"]
            );
            assert_ne!(
                successor.accepted, legacy.accepted,
                "{} legacy transition must not satisfy custody-complete output",
                case["name"]
            );
            assert_ne!(
                successor.journal_bytes, legacy.journal_bytes,
                "{} custody completion must rebind journal",
                case["name"]
            );
        }
    }
}

#[test]
fn rejected_fixture_states_preserve_exact_code_and_return_no_journal() {
    for case in vectors()["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .filter(|case| case.get("reject_code").is_some())
    {
        let input = input(case);
        let input_bytes = canonical_asset_transfer_guest_input_bytes_v1(&input)
            .expect("rejected fixture input must canonicalize");
        let expected_code = case["reject_code"]
            .as_str()
            .expect("reject code must be text");
        let successor = prepare_asset_transfer_custody_module_v1(input.clone());
        let successor_raw =
            prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&input_bytes);
        let legacy_raw = prepare_asset_transfer_module_from_canonical_bytes_v1(&input_bytes);
        assert_eq!(successor_raw, legacy_raw, "{} raw reject", case["name"]);
        let legacy = prepare_asset_transfer_module_v1(input.clone());
        assert_eq!(successor, legacy, "{} typed reject", case["name"]);
        assert!(matches!(
            successor,
            Err(AssetTransferGuestErrorV1::Rejected(code))
                if format!("{code:?}") == expected_code
        ));
        assert!(matches!(
            successor_raw,
            Err(AssetTransferGuestErrorV1::Rejected(_))
        ));

        let custody_result =
            transition_asset_transfer_lane_module_custody_v1(&input).expect("transition result");
        let legacy_result = transition_asset_transfer_lane_module_v1(&input).expect("transition");
        assert_eq!(
            custody_result, legacy_result,
            "{} transition reject",
            case["name"]
        );
        let AssetTransferLaneModuleResultV1::Rejected(rejected) = custody_result else {
            panic!("{} must reject", case["name"])
        };
        assert_eq!(format!("{:?}", rejected.code), expected_code);
        assert!(
            rejected.effects.is_empty(),
            "{} reject effects",
            case["name"]
        );
        assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    }
}

#[test]
fn canonical_decode_and_predecode_bounds_fail_closed() {
    let vectors = vectors();
    let accepted_case = vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .find(|case| case["name"].as_str() == Some("custody_0"))
        .expect("custody_0 fixture must exist");
    let input = input(accepted_case);
    let canonical = canonical_asset_transfer_guest_input_bytes_v1(&input)
        .expect("fixture input must canonicalize");

    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&[]),
        Err(AssetTransferGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&vec![
            0_u8;
            MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_V1
        ]),
        Err(AssetTransferGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&vec![
            0_u8;
            MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_V1
                + 1
        ]),
        Err(AssetTransferGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(b"{"),
        Err(AssetTransferGuestErrorV1::Decode)
    ));

    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&trailing),
        Err(AssetTransferGuestErrorV1::NonCanonicalInput)
    ));

    let mut unknown: serde_json::Value =
        serde_json::from_slice(&canonical).expect("canonical input must decode");
    unknown
        .as_object_mut()
        .expect("input must be an object")
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).expect("unknown-field input must encode");
    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&unknown),
        Err(AssetTransferGuestErrorV1::Decode)
    ));
}

#[test]
fn canonicality_precedes_typed_abi_rejection() {
    let vectors = vectors();
    let mut input = input(&vectors["cases"][0]);
    input.pre_state.schema = "unsupported-schema".to_owned();
    let mut bytes = canonical_bytes_v1(&input).expect("invalid typed value still encodes");
    assert_eq!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&bytes),
        Err(AssetTransferGuestErrorV1::Abi)
    );
    bytes.push(b'\n');
    assert_eq!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&bytes),
        Err(AssetTransferGuestErrorV1::NonCanonicalInput)
    );
}

#[test]
fn complete_projection_overflow_rejects_before_candidate_output() {
    let overflow: AssetTransferLaneModuleInputV1 =
        serde_json::from_value(vectors()["overflow_input"].clone())
            .expect("overflow fixture input must decode");
    assert!(matches!(
        prepare_asset_transfer_custody_module_v1(overflow.clone()),
        Err(AssetTransferGuestErrorV1::Abi)
    ));
    let bytes = canonical_bytes_v1(&overflow).expect("overflow input must encode");
    assert!(matches!(
        prepare_asset_transfer_custody_module_from_canonical_bytes_v1(&bytes),
        Err(AssetTransferGuestErrorV1::Abi)
    ));
}
