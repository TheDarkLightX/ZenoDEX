use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_asset_lane_epoch_effect_plans_v1,
    derive_route_composition_assumption_root_v1, derive_verified_economic_epoch_commit_id_v1,
    hash_bytes_sha256_v1, AbiErrorV1, AbiResultV1, CommandAggregationJournalV1,
    EconomicCommandOccurrenceV1, EconomicProfileSnapshotV1, GlobalEconomicEffectPlanV1,
    GlobalEconomicEpochCertificateV1, GlobalEconomicStateV1, LaneCompositionJournalV1,
    LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1,
    LaneModuleTransitionJournalV1, LaneRegistryV1, MigrationObjectClassV1, ReceiptKindV1, RootV1,
    RouteCompositionJournalV1, RouteRegistryV1, RouteReleaseV1, StateMigrationCertificateV1,
    ALL_LANE_IDS_V1, ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1,
};

const FIXTURE_SCHEMA: &str = "zenodex/global-settlement-abi-v1-golden/v1";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    fixture_schema: String,
    vectors: BTreeMap<String, GoldenVector>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct GoldenVector {
    canonical: Value,
    canonical_bytes_sha256: String,
    expected_root: String,
    #[serde(default)]
    journal_canonical: Option<Value>,
    #[serde(default)]
    journal_bytes_len: Option<u64>,
    #[serde(default)]
    journal_bytes_sha256: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct VerifiedEconomicEpochCommitVectorV1 {
    certificate_root: RootV1,
    ordered_route_binding_roots: Vec<RootV1>,
    receipt_digest: RootV1,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RouteCompositionAssumptionVectorV1 {
    schema: String,
    profile_id: RootV1,
    route_release_id: RootV1,
    command_occurrence_id: RootV1,
    writer_epoch: u64,
    route_journal_root: RootV1,
    route_journal_digest: RootV1,
    expected_image_id: RootV1,
}

impl RouteCompositionAssumptionVectorV1 {
    fn root(&self) -> AbiResultV1<RootV1> {
        if self.schema != ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        derive_route_composition_assumption_root_v1(
            &self.profile_id,
            &self.route_release_id,
            &self.command_occurrence_id,
            self.writer_epoch,
            &self.route_journal_root,
            &self.route_journal_digest,
            &self.expected_image_id,
        )
    }
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json")
}

fn load_fixture() -> Fixture {
    let bytes = fs::read(fixture_path()).expect("golden fixture must be readable");
    let fixture: Fixture =
        serde_json::from_slice(&bytes).expect("golden fixture must be typed JSON");
    assert_eq!(fixture.fixture_schema, FIXTURE_SCHEMA);
    fixture
}

fn vector<'a>(fixture: &'a Fixture, name: &str) -> &'a GoldenVector {
    fixture
        .vectors
        .get(name)
        .expect("named golden vector must exist")
}

fn parse_vector<T: DeserializeOwned>(vector: &GoldenVector) -> T {
    serde_json::from_value(vector.canonical.clone()).expect("golden canonical value must decode")
}

fn check_vector<T: DeserializeOwned + Serialize>(
    vector: &GoldenVector,
    validate: impl FnOnce(&T) -> AbiResultV1<()>,
    derive_root: impl FnOnce(&T) -> AbiResultV1<RootV1>,
) -> T {
    let typed: T = parse_vector(vector);
    validate(&typed).expect("golden typed value must validate");
    let bytes = canonical_bytes_v1(&typed).expect("golden typed value must encode");
    assert_eq!(hash_bytes_sha256_v1(&bytes), vector.canonical_bytes_sha256);
    let round_trip: Value = serde_json::from_slice(&bytes).expect("canonical bytes must be JSON");
    assert_eq!(round_trip, vector.canonical);
    assert_eq!(
        derive_root(&typed)
            .expect("golden root must derive")
            .as_str(),
        vector.expected_root
    );
    typed
}

#[test]
fn python_and_rust_recompute_identical_typed_roots_and_journal_bytes() {
    let fixture = load_fixture();
    assert_eq!(fixture.vectors.len(), 21);

    check_vector::<LaneModuleReleaseV1>(
        vector(&fixture, "lane_module_release"),
        LaneModuleReleaseV1::validate,
        LaneModuleReleaseV1::derived_release_id,
    );
    let lanes = check_vector::<LaneRegistryV1>(
        vector(&fixture, "lane_registry"),
        LaneRegistryV1::validate,
        LaneRegistryV1::registry_root,
    );
    check_vector::<LaneCoordinatorReleaseV1>(
        vector(&fixture, "lane_coordinator_release"),
        LaneCoordinatorReleaseV1::validate,
        LaneCoordinatorReleaseV1::derived_coordinator_release_id,
    );
    let coordinators = check_vector::<LaneCoordinatorRegistryV1>(
        vector(&fixture, "lane_coordinator_registry"),
        LaneCoordinatorRegistryV1::validate,
        LaneCoordinatorRegistryV1::registry_root,
    );
    check_vector::<RouteReleaseV1>(
        vector(&fixture, "route_release"),
        RouteReleaseV1::validate,
        RouteReleaseV1::derived_release_id,
    );
    let routes = check_vector::<RouteRegistryV1>(
        vector(&fixture, "route_registry"),
        RouteRegistryV1::validate,
        RouteRegistryV1::registry_root,
    );
    let profile = check_vector::<EconomicProfileSnapshotV1>(
        vector(&fixture, "economic_profile"),
        EconomicProfileSnapshotV1::validate,
        EconomicProfileSnapshotV1::derived_profile_id,
    );
    profile
        .validate_registries(&lanes, &coordinators, &routes)
        .expect("golden profile registry bindings must validate");
    let state = check_vector::<GlobalEconomicStateV1>(
        vector(&fixture, "global_state"),
        GlobalEconomicStateV1::validate,
        GlobalEconomicStateV1::state_root,
    );
    state
        .validate_profile_registry(&profile, &lanes)
        .expect("golden state profile bindings must validate");
    check_vector::<GlobalEconomicEffectPlanV1>(
        vector(&fixture, "effect_plan"),
        GlobalEconomicEffectPlanV1::validate,
        GlobalEconomicEffectPlanV1::effect_plan_root,
    );
    let route_effect_plan_1 = check_vector::<GlobalEconomicEffectPlanV1>(
        vector(&fixture, "epoch_route_effect_plan_1"),
        GlobalEconomicEffectPlanV1::validate,
        GlobalEconomicEffectPlanV1::effect_plan_root,
    );
    let route_effect_plan_2 = check_vector::<GlobalEconomicEffectPlanV1>(
        vector(&fixture, "epoch_route_effect_plan_2"),
        GlobalEconomicEffectPlanV1::validate,
        GlobalEconomicEffectPlanV1::effect_plan_root,
    );
    let epoch_composed_effect_plan = check_vector::<GlobalEconomicEffectPlanV1>(
        vector(&fixture, "epoch_composed_effect_plan"),
        GlobalEconomicEffectPlanV1::validate,
        GlobalEconomicEffectPlanV1::effect_plan_root,
    );
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&[route_effect_plan_1, route_effect_plan_2,])
            .expect("golden route effects must compose"),
        epoch_composed_effect_plan
    );
    check_vector::<EconomicCommandOccurrenceV1>(
        vector(&fixture, "command_occurrence"),
        EconomicCommandOccurrenceV1::validate,
        EconomicCommandOccurrenceV1::occurrence_id,
    );
    check_vector::<LaneModuleTransitionJournalV1>(
        vector(&fixture, "module_journal"),
        LaneModuleTransitionJournalV1::validate,
        LaneModuleTransitionJournalV1::journal_root,
    );
    check_vector::<LaneCompositionJournalV1>(
        vector(&fixture, "lane_journal"),
        LaneCompositionJournalV1::validate,
        LaneCompositionJournalV1::journal_root,
    );
    check_vector::<RouteCompositionJournalV1>(
        vector(&fixture, "route_journal"),
        RouteCompositionJournalV1::validate,
        RouteCompositionJournalV1::journal_root,
    );
    check_vector::<RouteCompositionAssumptionVectorV1>(
        vector(&fixture, "route_assumption"),
        |value| value.root().map(|_| ()),
        RouteCompositionAssumptionVectorV1::root,
    );
    check_vector::<CommandAggregationJournalV1>(
        vector(&fixture, "command_aggregation_journal"),
        CommandAggregationJournalV1::validate,
        CommandAggregationJournalV1::journal_root,
    );
    let epoch = check_vector::<GlobalEconomicEpochCertificateV1>(
        vector(&fixture, "epoch_certificate"),
        GlobalEconomicEpochCertificateV1::validate,
        GlobalEconomicEpochCertificateV1::certificate_root,
    );
    let epoch_vector = vector(&fixture, "epoch_certificate");
    let journal_bytes = epoch
        .canonical_journal_bytes()
        .expect("golden journal must encode");
    assert_eq!(
        u64::try_from(journal_bytes.len()).expect("journal length must fit u64"),
        epoch_vector
            .journal_bytes_len
            .expect("journal length must be committed")
    );
    assert_eq!(
        hash_bytes_sha256_v1(&journal_bytes),
        epoch_vector
            .journal_bytes_sha256
            .as_ref()
            .expect("journal digest must be committed")
            .as_str()
    );
    let journal_value: Value =
        serde_json::from_slice(&journal_bytes).expect("golden journal must be JSON");
    assert_eq!(
        Some(&journal_value),
        epoch_vector.journal_canonical.as_ref()
    );
    check_vector::<VerifiedEconomicEpochCommitVectorV1>(
        vector(&fixture, "verified_epoch_commit"),
        |value| {
            derive_verified_economic_epoch_commit_id_v1(
                &value.certificate_root,
                &value.ordered_route_binding_roots,
                &value.receipt_digest,
            )
            .map(|_| ())
        },
        |value| {
            derive_verified_economic_epoch_commit_id_v1(
                &value.certificate_root,
                &value.ordered_route_binding_roots,
                &value.receipt_digest,
            )
        },
    );
    check_vector::<StateMigrationCertificateV1>(
        vector(&fixture, "migration_certificate"),
        StateMigrationCertificateV1::validate,
        StateMigrationCertificateV1::certificate_root,
    );
}

#[test]
fn strict_decode_rejects_unknown_fields_bool_aliases_and_numeric_strings() {
    let fixture = load_fixture();
    let mut release = vector(&fixture, "lane_module_release").canonical.clone();
    release
        .as_object_mut()
        .expect("release vector must be an object")
        .insert("opaque_authority".to_owned(), Value::Bool(true));
    assert!(serde_json::from_value::<LaneModuleReleaseV1>(release).is_err());

    let mut occurrence = vector(&fixture, "command_occurrence").canonical.clone();
    occurrence
        .as_object_mut()
        .expect("occurrence vector must be an object")
        .insert("height".to_owned(), Value::Bool(true));
    assert!(serde_json::from_value::<EconomicCommandOccurrenceV1>(occurrence).is_err());

    let mut occurrence = vector(&fixture, "command_occurrence").canonical.clone();
    occurrence
        .as_object_mut()
        .expect("occurrence vector must be an object")
        .insert("height".to_owned(), Value::String("42".to_owned()));
    assert!(serde_json::from_value::<EconomicCommandOccurrenceV1>(occurrence).is_err());

    let mut effects = vector(&fixture, "effect_plan").canonical.clone();
    effects["rows"][0]
        .as_object_mut()
        .expect("effect row must be an object")
        .insert("host_verdict".to_owned(), Value::Bool(true));
    assert!(serde_json::from_value::<GlobalEconomicEffectPlanV1>(effects).is_err());
}

#[test]
fn content_mutation_conservation_drift_and_migration_skip_fail_closed() {
    let fixture = load_fixture();

    let mut release: LaneModuleReleaseV1 = parse_vector(vector(&fixture, "lane_module_release"));
    release.max_cycles += 1;
    assert!(release.validate().is_err());
    assert!(release.derived_release_id().is_err());

    let mut route: RouteReleaseV1 = parse_vector(vector(&fixture, "route_release"));
    route.guest_image_id = test_root(90_001);
    assert!(route.validate().is_err());
    assert!(route.derived_release_id().is_err());

    let mut effects: GlobalEconomicEffectPlanV1 = parse_vector(vector(&fixture, "effect_plan"));
    effects.asset_conservation[0].supply_post_atoms += 1;
    assert!(effects.validate().is_err());
    assert!(effects.effect_plan_root().is_err());

    let mut migration: StateMigrationCertificateV1 =
        parse_vector(vector(&fixture, "migration_certificate"));
    migration.target_writer_epoch += 1;
    assert!(migration.validate().is_err());
    migration.target_writer_epoch -= 1;
    migration.object_rows[0].classification = MigrationObjectClassV1::MIGRATED;
    migration.object_rows[0].target_object_root = RootV1::parse(
        "0x0000000000000000000000000000000000000000000000000000000000000000",
        "test zero root",
        true,
    )
    .expect("test zero root must parse");
    assert!(migration.validate().is_err());
}

#[test]
fn route_and_epoch_bounds_reject_zero_nine_and_sixty_five() {
    let fixture = load_fixture();
    let route: RouteReleaseV1 = parse_vector(vector(&fixture, "route_release"));

    let mut zero_route = route.clone();
    zero_route.ordered_lanes.clear();
    zero_route.module_release_ids.clear();
    zero_route.dependency_roles.clear();
    zero_route.port_schema_roots.clear();
    assert!(zero_route.validate().is_err());

    let mut wide_route = route;
    wide_route.ordered_lanes = ALL_LANE_IDS_V1[..9].to_vec();
    wide_route.module_release_ids = (1..=9).map(test_root).collect();
    wide_route.dependency_roles = (1..=9).map(|index| format!("ROLE_{index}")).collect();
    wide_route.port_schema_roots = (101..=109).map(test_root).collect();
    assert!(wide_route.validate().is_err());

    let aggregation: CommandAggregationJournalV1 =
        parse_vector(vector(&fixture, "command_aggregation_journal"));
    let mut eight_aggregation = aggregation.clone();
    eight_aggregation.ordered_occurrence_ids = (1..=8).map(test_root).collect();
    eight_aggregation.ordered_route_journal_roots = (101..=108).map(test_root).collect();
    eight_aggregation.ordered_route_assumption_roots = (201..=208).map(test_root).collect();
    eight_aggregation.module_leaf_occurrences = 8;
    eight_aggregation.validate().unwrap();

    let mut zero_aggregation = aggregation;
    zero_aggregation.ordered_occurrence_ids.clear();
    zero_aggregation.ordered_route_journal_roots.clear();
    zero_aggregation.ordered_route_assumption_roots.clear();
    zero_aggregation.module_leaf_occurrences = 0;
    assert!(zero_aggregation.validate().is_err());

    eight_aggregation.ordered_occurrence_ids.push(test_root(9));
    eight_aggregation
        .ordered_route_journal_roots
        .push(test_root(109));
    eight_aggregation
        .ordered_route_assumption_roots
        .push(test_root(209));
    eight_aggregation.module_leaf_occurrences = 9;
    assert!(eight_aggregation.validate().is_err());

    let epoch: GlobalEconomicEpochCertificateV1 =
        parse_vector(vector(&fixture, "epoch_certificate"));
    let mut zero_epoch = epoch.clone();
    zero_epoch.ordered_occurrence_ids.clear();
    zero_epoch.ordered_route_journal_roots.clear();
    zero_epoch.ordered_route_assumption_roots.clear();
    assert!(zero_epoch.validate().is_err());

    let mut wide_epoch = epoch;
    wide_epoch.ordered_occurrence_ids = (1..=65).map(test_root).collect();
    wide_epoch.ordered_route_journal_roots = (101..=165).map(test_root).collect();
    wide_epoch.ordered_route_assumption_roots = (201..=265).map(test_root).collect();
    wide_epoch.module_leaf_occurrences = 65;
    assert!(wide_epoch.validate().is_err());
}

#[test]
fn enum_and_receipt_boundaries_are_closed() {
    assert_eq!(ALL_LANE_IDS_V1[0], LaneIdV1::ASSET_TRANSFER);
    assert_eq!(ALL_LANE_IDS_V1[11], LaneIdV1::GOVERNANCE_MIGRATION);
    assert_eq!(ReceiptKindV1::SUCCINCT, ReceiptKindV1::SUCCINCT);
    assert!(serde_json::from_str::<LaneIdV1>("\"UNKNOWN_LANE\"").is_err());
    assert!(serde_json::from_str::<ReceiptKindV1>("\"PLONK\"").is_err());
}

fn test_root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}
