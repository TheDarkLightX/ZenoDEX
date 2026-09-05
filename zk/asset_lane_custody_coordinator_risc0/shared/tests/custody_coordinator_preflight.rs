use zenodex_asset_lane_coordinator_risc0_shared::{
    canonical_asset_lane_coordinator_guest_input_bytes_v1 as legacy_canonical_input,
    prepare_asset_lane_coordinator_from_canonical_bytes_v1 as legacy_prepare_from_canonical,
    AssetLaneCoordinatorGuestErrorV1 as LegacyError,
    AssetLaneCoordinatorGuestInputV1 as LegacyInput,
};
use zenodex_asset_lane_custody_coordinator_risc0_shared::{
    canonical_asset_lane_custody_coordinator_input_bytes_v1,
    prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1,
    prepare_asset_lane_custody_coordinator_v1, AssetLaneCustodyCoordinatorGuestErrorV1,
    AssetLaneCustodyCoordinatorInputV1, MAX_ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_BYTES_V1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, AssetLaneCoordinatorContextV1, AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1, EconomicAmountV1, RootV1,
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

fn module_input(case: &serde_json::Value) -> AssetTransferLaneModuleInputV1 {
    serde_json::from_value(case["input"].clone()).expect("fixture input must decode")
}

fn coordinator_input(
    vectors: &serde_json::Value,
    case: &serde_json::Value,
) -> AssetLaneCustodyCoordinatorInputV1 {
    AssetLaneCustodyCoordinatorInputV1 {
        schema: "zenodex/asset-lane-coordinator-guest-input/v1".to_owned(),
        module_input: module_input(case),
        coordinator_context: serde_json::from_value(vectors["coordinator_context"].clone())
            .expect("fixture coordinator context must decode"),
    }
}

fn legacy_input(input: &AssetLaneCustodyCoordinatorInputV1) -> LegacyInput {
    LegacyInput {
        schema: input.schema.clone(),
        module_input: input.module_input.clone(),
        coordinator_context: input.coordinator_context.clone(),
    }
}

fn root(value: u8) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
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

#[test]
fn accepted_fixture_values_are_custody_complete_and_one_occurrence() {
    let vectors = vectors();
    for case in vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .filter(|case| case.get("accepted").is_some())
    {
        let input = coordinator_input(&vectors, case);
        let typed = prepare_asset_lane_custody_coordinator_v1(input.clone())
            .expect("accepted fixture input must prepare");
        let canonical = canonical_asset_lane_custody_coordinator_input_bytes_v1(&input)
            .expect("accepted fixture input must canonicalize");
        let raw = prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&canonical)
            .expect("accepted fixture input must prepare from canonical bytes");
        assert_eq!(typed, raw, "{} typed/raw result", case["name"]);

        let expected_module: AssetTransferLaneModuleAcceptedV1 =
            serde_json::from_value(case["accepted"].clone())
                .expect("accepted fixture module value must decode");
        assert_eq!(
            typed.module_accepted, expected_module,
            "{} module",
            case["name"]
        );

        let asset = input.module_input.command.asset.as_str();
        let expected_total: u128 = case["expected_total"]
            .as_str()
            .expect("expected total must be decimal text")
            .parse()
            .expect("expected total must fit u128");
        assert_eq!(
            physical_total(
                &input.module_input.pre_state.balances,
                &input.module_input.custody,
                asset,
            ),
            expected_total,
            "{} pre physical total",
            case["name"]
        );
        assert_eq!(
            physical_total(
                &typed.module_accepted.private_port.post_state.balances,
                &typed.module_accepted.private_port.post_state.custody,
                asset,
            ),
            expected_total,
            "{} post physical total",
            case["name"]
        );
        let conservation = typed
            .module_accepted
            .effects
            .asset_conservation
            .iter()
            .find(|row| row.asset == asset)
            .expect("accepted fixture must contain conservation");
        assert_eq!(conservation.owned_and_custodied_pre_atoms, expected_total);
        assert_eq!(conservation.owned_and_custodied_post_atoms, expected_total);
        assert_eq!(
            typed.module_accepted.private_port.pre_state.custody, input.module_input.custody,
            "{} pre custody frame",
            case["name"]
        );
        assert_eq!(
            typed.module_accepted.private_port.post_state.custody, input.module_input.custody,
            "{} post custody frame",
            case["name"]
        );

        assert_eq!(
            typed.module_journal_bytes,
            canonical_bytes_v1(&typed.module_accepted.module_journal)
                .expect("module journal must encode"),
            "{} canonical module journal",
            case["name"]
        );
        assert_eq!(
            typed.lane_journal_bytes,
            canonical_bytes_v1(&typed.lane_accepted.lane_journal)
                .expect("lane journal must encode"),
            "{} canonical lane journal",
            case["name"]
        );
        assert_eq!(
            typed.lane_accepted.post_state, typed.module_accepted.private_port.post_state,
            "{} lane post state",
            case["name"]
        );
        assert_eq!(
            typed
                .lane_accepted
                .lane_journal
                .ordered_module_journal_roots,
            vec![typed
                .module_accepted
                .module_journal
                .journal_root()
                .expect("module journal root must compute")],
            "{} one module journal occurrence",
            case["name"]
        );
        assert_eq!(
            typed.lane_accepted.effects.occurrence_consumptions,
            vec![input.coordinator_context.command_occurrence_id.clone()],
            "{} one occurrence consumption",
            case["name"]
        );
    }
}

#[test]
fn zero_custody_matches_legacy_serialized_values_and_nonzero_is_rejected_by_legacy() {
    let vectors = vectors();
    for case in vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .filter(|case| case.get("accepted").is_some())
    {
        let input = coordinator_input(&vectors, case);
        let successor = prepare_asset_lane_custody_coordinator_v1(input.clone())
            .expect("accepted fixture input must prepare");
        let old_input = legacy_input(&input);
        let old_bytes = legacy_canonical_input(&old_input).expect("legacy input must canonicalize");
        let old = legacy_prepare_from_canonical(&old_bytes);
        if input.module_input.custody.is_empty() {
            let old = old.expect("legacy zero-custody input must prepare");
            assert_eq!(
                serde_json::to_value(&successor.module_accepted).expect("module must serialize"),
                serde_json::to_value(&old.module_accepted).expect("legacy module must serialize"),
                "{} zero-custody module",
                case["name"]
            );
            assert_eq!(
                serde_json::to_value(&successor.lane_accepted).expect("lane must serialize"),
                serde_json::to_value(&old.lane_accepted).expect("legacy lane must serialize"),
                "{} zero-custody lane",
                case["name"]
            );
            assert_eq!(successor.module_journal_bytes, old.module_journal_bytes);
            assert_eq!(successor.lane_journal_bytes, old.lane_journal_bytes);
        } else {
            assert_eq!(
                old,
                Err(LegacyError::CoordinatorRejected(
                    zenodex_global_settlement_abi_v1::AssetLaneCoordinatorRejectCodeV1::CONSERVATION_STATE_MISMATCH,
                )),
                "{} legacy nonzero-custody rejection",
                case["name"]
            );
        }
    }
}

#[test]
fn module_rejections_preserve_codes_and_do_not_create_lane_candidates() {
    let vectors = vectors();
    for case in vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .filter(|case| case.get("reject_code").is_some())
    {
        let input = coordinator_input(&vectors, case);
        let expected = match case["reject_code"].as_str().expect("reject code text") {
            "ZERO_AMOUNT" => {
                zenodex_global_settlement_abi_v1::AssetTransferRejectCodeV1::ZERO_AMOUNT
            }
            "FEE_LIMIT_EXCEEDED" => {
                zenodex_global_settlement_abi_v1::AssetTransferRejectCodeV1::FEE_LIMIT_EXCEEDED
            }
            "INSUFFICIENT_BALANCE" => {
                zenodex_global_settlement_abi_v1::AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE
            }
            other => panic!("unhandled fixture reject code {other}"),
        };
        let expected = Err(AssetLaneCustodyCoordinatorGuestErrorV1::ModuleRejected(
            expected,
        ));
        let typed = prepare_asset_lane_custody_coordinator_v1(input.clone());
        let canonical = canonical_asset_lane_custody_coordinator_input_bytes_v1(&input)
            .expect("rejected fixture input must canonicalize");
        let raw = prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&canonical);
        assert_eq!(typed, expected, "{} typed reject", case["name"]);
        assert_eq!(raw, expected, "{} raw reject", case["name"]);
    }
}

#[test]
fn independent_context_binding_rejections_are_preserved() {
    let vectors = vectors();
    let case = vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .iter()
        .find(|case| case["name"].as_str() == Some("custody_1"))
        .expect("custody_1 fixture must exist");
    let base = coordinator_input(&vectors, case);

    let mut wrong_chain = base.clone();
    wrong_chain.coordinator_context.chain_id = "zeno-other-chain".to_owned();
    assert_eq!(
        prepare_asset_lane_custody_coordinator_v1(wrong_chain),
        Err(
            AssetLaneCustodyCoordinatorGuestErrorV1::CoordinatorRejected(
                zenodex_global_settlement_abi_v1::AssetLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH,
            )
        )
    );

    let mut wrong_occurrence = base.clone();
    wrong_occurrence.coordinator_context.command_occurrence_id = root(99);
    assert_eq!(
        prepare_asset_lane_custody_coordinator_v1(wrong_occurrence),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::CoordinatorRejected(
            zenodex_global_settlement_abi_v1::AssetLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH,
        ))
    );

    let mut unregistered = base;
    unregistered.coordinator_context.compatible_modules[0].module_release_id = root(99);
    assert_eq!(
        prepare_asset_lane_custody_coordinator_v1(unregistered),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::CoordinatorRejected(
            zenodex_global_settlement_abi_v1::AssetLaneCoordinatorRejectCodeV1::MODULE_NOT_REGISTERED,
        ))
    );
}

#[test]
fn raw_preflight_checks_bounds_and_canonicality_before_typed_validation() {
    let vectors = vectors();
    let case = vectors["cases"]
        .as_array()
        .expect("fixture cases must be an array")
        .first()
        .expect("fixture must contain a case");
    let input = coordinator_input(&vectors, case);
    let canonical = canonical_asset_lane_custody_coordinator_input_bytes_v1(&input)
        .expect("fixture input must canonicalize");

    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&[]),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&vec![
            0_u8;
            MAX_ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_BYTES_V1
        ]),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&vec![
            0_u8;
            MAX_ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_BYTES_V1
                + 1
        ]),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(b"{"),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Decode)
    ));

    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&trailing),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::NonCanonicalInput)
    ));

    let mut unknown: serde_json::Value =
        serde_json::from_slice(&canonical).expect("canonical input must decode");
    unknown
        .as_object_mut()
        .expect("input must be an object")
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).expect("unknown input must encode");
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&unknown),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Decode)
    ));

    let mut wrong_schema = input.clone();
    wrong_schema.schema = "unsupported-schema".to_owned();
    assert_eq!(
        prepare_asset_lane_custody_coordinator_v1(wrong_schema.clone()),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Schema)
    );
    let wrong_schema_bytes = canonical_bytes_v1(&wrong_schema).expect("schema value must encode");
    assert_eq!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&wrong_schema_bytes),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Schema)
    );

    let mut invalid_module = input;
    invalid_module.module_input.pre_state.schema = "unsupported-schema".to_owned();
    let invalid_module_bytes = canonical_bytes_v1(&invalid_module)
        .expect("invalid module value must still encode canonically");
    assert_eq!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&invalid_module_bytes),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Abi)
    );
    let mut invalid_module_noncanonical = invalid_module_bytes;
    invalid_module_noncanonical.push(b'\n');
    assert_eq!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(
            &invalid_module_noncanonical
        ),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::NonCanonicalInput)
    );
}

#[test]
fn projection_overflow_rejects_without_a_prepared_candidate() {
    let vectors = vectors();
    let overflow_module: AssetTransferLaneModuleInputV1 =
        serde_json::from_value(vectors["overflow_input"].clone())
            .expect("overflow fixture input must decode");
    let context: AssetLaneCoordinatorContextV1 =
        serde_json::from_value(vectors["coordinator_context"].clone())
            .expect("fixture context must decode");
    let input = AssetLaneCustodyCoordinatorInputV1 {
        schema: "zenodex/asset-lane-coordinator-guest-input/v1".to_owned(),
        module_input: overflow_module,
        coordinator_context: context,
    };
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_v1(input.clone()),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Abi)
    ));
    let bytes = canonical_bytes_v1(&input).expect("overflow input must encode");
    assert!(matches!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&bytes),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::Abi)
    ));
}
