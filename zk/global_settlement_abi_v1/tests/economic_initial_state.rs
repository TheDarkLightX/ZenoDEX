use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    hash_bytes_sha256_v1, validate_economic_initial_state_bindings_v1,
    EconomicInitialStateCertificateV1, EconomicInitialStateKindV1, EconomicProfileSnapshotV1,
    GlobalEconomicStateV1, ProfileStatusV1, ReceiptKindV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "initial state test root", false).unwrap()
}

fn fixture_vector(name: &str) -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    fixture["vectors"][name]["canonical"].clone()
}

fn profile_and_state() -> (EconomicProfileSnapshotV1, GlobalEconomicStateV1) {
    (
        serde_json::from_value(fixture_vector("economic_profile")).unwrap(),
        serde_json::from_value(fixture_vector("global_state")).unwrap(),
    )
}

fn migration_certificate(
    profile: &EconomicProfileSnapshotV1,
    state: &GlobalEconomicStateV1,
    receipt_bytes: &[u8],
) -> EconomicInitialStateCertificateV1 {
    let mut certificate = EconomicInitialStateCertificateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::MIGRATION,
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        profile_root: profile.profile_id.clone(),
        writer_epoch: state.writer_epoch,
        height: state.height,
        state_root: state.state_root().unwrap(),
        source_profile_root: root(30),
        source_state_root: root(31),
        source_writer_epoch: state.writer_epoch - 1,
        source_height: state.height - 1,
        state_atom_coverage_root: root(32),
        lane_object_coverage_root: root(33),
        replay_continuity_root: root(34),
        terminal_continuity_root: root(35),
        outbox_continuity_root: root(36),
        source_manifest_root: root(37),
        toolchain_manifest_root: root(38),
        root_image_id: profile.root_image_id.clone(),
        receipt_root: RootV1::parse(
            format!("0x{}", hash_bytes_sha256_v1(receipt_bytes)),
            "initial state receipt root",
            false,
        )
        .unwrap(),
        receipt_kind: ReceiptKindV1::SUCCINCT,
        journal_bytes: 1,
        cycle_budget: 1_000_000,
    };
    certificate.journal_bytes =
        u64::try_from(certificate.canonical_journal_bytes().unwrap().len()).unwrap();
    certificate
}

fn genesis_certificate() -> EconomicInitialStateCertificateV1 {
    let receipt_bytes = b"initial-golden";
    let mut certificate = EconomicInitialStateCertificateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::GENESIS,
        chain_id: "tau-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        height: 0,
        state_root: root(3),
        source_profile_root: RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero source profile",
            true,
        )
        .unwrap(),
        source_state_root: RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero source state",
            true,
        )
        .unwrap(),
        source_writer_epoch: 0,
        source_height: 0,
        state_atom_coverage_root: root(4),
        lane_object_coverage_root: root(5),
        replay_continuity_root: root(6),
        terminal_continuity_root: root(7),
        outbox_continuity_root: root(8),
        source_manifest_root: root(9),
        toolchain_manifest_root: root(10),
        root_image_id: root(11),
        receipt_root: RootV1::parse(
            format!("0x{}", hash_bytes_sha256_v1(receipt_bytes)),
            "genesis receipt root",
            false,
        )
        .unwrap(),
        receipt_kind: ReceiptKindV1::SUCCINCT,
        journal_bytes: 1,
        cycle_budget: 1_000_000,
    };
    certificate.journal_bytes =
        u64::try_from(certificate.canonical_journal_bytes().unwrap().len()).unwrap();
    certificate
}

#[test]
fn genesis_certificate_matches_python_golden_roots() {
    let certificate = genesis_certificate();

    assert_eq!(certificate.journal_bytes, 1_336);
    assert_eq!(
        hash_bytes_sha256_v1(&certificate.canonical_journal_bytes().unwrap()),
        "eaa2444864e429f494f61220afecb9610e0d6195aa1d4cb59f34b9193ca5dd88"
    );
    assert_eq!(
        certificate.certificate_root().unwrap().as_str(),
        "0xaad3f289eaa13fc2e96451aa051437c6a91955bd6d026ee3d15517b392c9d809"
    );
}

#[test]
fn migration_certificate_binds_profile_state_lineage_and_receipt() {
    let (profile, state) = profile_and_state();
    let receipt_bytes = b"economic-initial-state-receipt";
    let certificate = migration_certificate(&profile, &state, receipt_bytes);

    validate_economic_initial_state_bindings_v1(&profile, &state, &certificate, receipt_bytes)
        .unwrap();
    assert!(!certificate.certificate_root().unwrap().is_zero());
}

#[test]
fn migration_certificate_rejects_skipped_lineage_and_crossed_state() {
    let (profile, state) = profile_and_state();
    let receipt_bytes = b"economic-initial-state-receipt";
    let certificate = migration_certificate(&profile, &state, receipt_bytes);

    let mut skipped = certificate.clone();
    skipped.source_writer_epoch -= 1;
    assert!(skipped.validate().is_err());

    let mut crossed = certificate;
    crossed.state_root = root(99);
    assert!(
        validate_economic_initial_state_bindings_v1(&profile, &state, &crossed, receipt_bytes,)
            .is_err()
    );

    let mut inactive = profile;
    inactive.status = ProfileStatusV1::SHADOW;
    assert!(validate_economic_initial_state_bindings_v1(
        &inactive,
        &state,
        &migration_certificate(&inactive, &state, receipt_bytes),
        receipt_bytes,
    )
    .is_err());
}
