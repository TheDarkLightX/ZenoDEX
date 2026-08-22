use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_atom_occurrences_v1,
    validate_economic_initial_state_atom_coverage_v1, EconomicInitialStateAtomClassificationV1,
    EconomicInitialStateAtomKindV1, EconomicInitialStateAtomOccurrenceV1,
    EconomicInitialStateAtomSourceV1, EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1, GlobalEconomicStateV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_INITIAL_STATE_ATOM_ROWS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "initial coverage test root",
        false,
    )
    .unwrap()
}

fn fixture_state() -> GlobalEconomicStateV1 {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    serde_json::from_value(fixture["vectors"]["global_state"]["canonical"].clone()).unwrap()
}

fn manifest(
    state: &GlobalEconomicStateV1,
    kind: EconomicInitialStateKindV1,
) -> EconomicInitialStateSourceManifestV1 {
    let classification = match kind {
        EconomicInitialStateKindV1::GENESIS => {
            EconomicInitialStateAtomClassificationV1::GenesisAllocation
        }
        EconomicInitialStateKindV1::MIGRATION => {
            EconomicInitialStateAtomClassificationV1::MigratedTarget
        }
    };
    EconomicInitialStateSourceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind,
        rows: derive_economic_initial_state_atom_occurrences_v1(state)
            .unwrap()
            .into_iter()
            .enumerate()
            .map(|(index, occurrence)| EconomicInitialStateAtomSourceV1 {
                occurrence,
                classification,
                source_authorization_root: root(1_000 + u64::try_from(index).unwrap()),
            })
            .collect(),
    }
}

#[test]
fn explicit_state_atoms_are_classified_exactly_once() {
    let state = fixture_state();
    let manifest = manifest(&state, EconomicInitialStateKindV1::GENESIS);

    let coverage_root =
        validate_economic_initial_state_atom_coverage_v1(&state, &manifest).unwrap();

    assert_eq!(
        manifest
            .rows
            .iter()
            .map(|row| row.occurrence.atom_kind)
            .collect::<Vec<_>>(),
        vec![
            EconomicInitialStateAtomKindV1::Balance,
            EconomicInitialStateAtomKindV1::Supply,
        ]
    );
    assert_eq!(coverage_root, manifest.manifest_root().unwrap());
    assert_eq!(
        manifest.rows[0].occurrence.row_root.as_str(),
        "0x1fc5f26e9f5e3513aa34afc2a5d7d4513002e1479c04d03b45b7a88b47e7c534"
    );
    assert_eq!(
        manifest.rows[1].occurrence.row_root.as_str(),
        "0x35847c7f890093296e3e65a83971465e55ae776d7d2e0cb72152e961ce0f4122"
    );
}

#[test]
fn manifest_root_matches_python_golden_vector() {
    let manifest = EconomicInitialStateSourceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::GENESIS,
        rows: vec![
            EconomicInitialStateAtomSourceV1 {
                occurrence: EconomicInitialStateAtomOccurrenceV1 {
                    atom_kind: EconomicInitialStateAtomKindV1::Balance,
                    state_row_index: 0,
                    row_root: root(1),
                },
                classification: EconomicInitialStateAtomClassificationV1::GenesisAllocation,
                source_authorization_root: root(3),
            },
            EconomicInitialStateAtomSourceV1 {
                occurrence: EconomicInitialStateAtomOccurrenceV1 {
                    atom_kind: EconomicInitialStateAtomKindV1::Supply,
                    state_row_index: 0,
                    row_root: root(2),
                },
                classification: EconomicInitialStateAtomClassificationV1::GenesisAllocation,
                source_authorization_root: root(4),
            },
        ],
    };

    assert_eq!(
        manifest.manifest_root().unwrap().as_str(),
        "0x8fb2073a85c1b563f09860071e0d3ebd2508be80a111c95fcf585eebc90187ba"
    );
}

#[test]
fn omitted_stale_duplicate_and_wrong_classification_rows_reject() {
    let state = fixture_state();
    let manifest = manifest(&state, EconomicInitialStateKindV1::GENESIS);

    let mut omitted = manifest.clone();
    omitted.rows.pop();
    assert!(validate_economic_initial_state_atom_coverage_v1(&state, &omitted).is_err());

    let mut stale = manifest.clone();
    stale.rows[0].occurrence.row_root = root(9_001);
    assert!(validate_economic_initial_state_atom_coverage_v1(&state, &stale).is_err());

    let mut duplicate = manifest.clone();
    duplicate.rows[1] = duplicate.rows[0].clone();
    assert!(duplicate.validate().is_err());

    let mut wrong_classification = manifest;
    wrong_classification.rows[0].classification =
        EconomicInitialStateAtomClassificationV1::MigratedTarget;
    assert!(wrong_classification.validate().is_err());
}

#[test]
fn source_manifest_row_bound_has_exact_neighbors() {
    let source = |index: usize| EconomicInitialStateAtomSourceV1 {
        occurrence: EconomicInitialStateAtomOccurrenceV1 {
            atom_kind: EconomicInitialStateAtomKindV1::Balance,
            state_row_index: u64::try_from(index).unwrap(),
            row_root: root(u64::try_from(index).unwrap() + 1),
        },
        classification: EconomicInitialStateAtomClassificationV1::GenesisAllocation,
        source_authorization_root: root(
            u64::try_from(MAX_INITIAL_STATE_ATOM_ROWS_V1 + index).unwrap() + 2,
        ),
    };
    let at_limit = EconomicInitialStateSourceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::GENESIS,
        rows: (0..MAX_INITIAL_STATE_ATOM_ROWS_V1).map(source).collect(),
    };
    let over_limit = EconomicInitialStateSourceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::GENESIS,
        rows: (0..=MAX_INITIAL_STATE_ATOM_ROWS_V1).map(source).collect(),
    };

    assert!(at_limit.validate().is_ok());
    assert!(over_limit.validate().is_err());
}
