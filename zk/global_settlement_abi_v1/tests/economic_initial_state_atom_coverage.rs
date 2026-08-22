use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_atom_occurrences_v1,
    validate_economic_initial_state_atom_coverage_v1, AbiErrorV1, AssetSupplyV1, EconomicAmountV1,
    EconomicInitialStateAtomClassificationV1, EconomicInitialStateAtomKindV1,
    EconomicInitialStateAtomOccurrenceV1, EconomicInitialStateAtomSourceV1,
    EconomicInitialStateKindV1, EconomicInitialStateSourceManifestV1, GlobalEconomicStateV1,
    RootV1, TerminalObligationStatusV1, TerminalObligationV1, ALL_LANE_IDS_V1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_INITIAL_STATE_ATOM_ROWS_V1,
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
fn all_six_row_kinds_and_terminal_statuses_match_python_golden_vectors() {
    let mut state = fixture_state();
    state.balances = vec![EconomicAmountV1 {
        owner: "alice".to_owned(),
        asset: "ZDEX".to_owned(),
        custody_domain: "accounts".to_owned(),
        amount_atoms: 1,
    }];
    state.supplies = vec![AssetSupplyV1 {
        asset: "ZDEX".to_owned(),
        amount_atoms: 6,
    }];
    state.custody = vec![EconomicAmountV1 {
        owner: "pool-1".to_owned(),
        asset: "ZDEX".to_owned(),
        custody_domain: "pool".to_owned(),
        amount_atoms: 2,
    }];
    state.liabilities = vec![EconomicAmountV1 {
        owner: "claim-1".to_owned(),
        asset: "ZDEX".to_owned(),
        custody_domain: "claim".to_owned(),
        amount_atoms: 3,
    }];
    state.reserves = vec![EconomicAmountV1 {
        owner: "treasury".to_owned(),
        asset: "ZDEX".to_owned(),
        custody_domain: "reserve".to_owned(),
        amount_atoms: 4,
    }];
    state.terminal_obligations = vec![TerminalObligationV1 {
        obligation_id: "terminal-1".to_owned(),
        lane_id: ALL_LANE_IDS_V1[0],
        claimant: "bob".to_owned(),
        asset: "ZDEX".to_owned(),
        amount_atoms: 5,
        status: TerminalObligationStatusV1::OPEN,
    }];

    let roots: Vec<_> = derive_economic_initial_state_atom_occurrences_v1(&state)
        .unwrap()
        .into_iter()
        .map(|occurrence| occurrence.row_root.as_str().to_owned())
        .collect();

    assert_eq!(
        roots,
        vec![
            "0x9cd2992d3a82595674d5901579ff34119bc3c38416516a13563ccbd8c0bb9248",
            "0x89b99532450803b9a8360197d2ae4b3786724369c5f1f384b3a801c059010e45",
            "0xcbc21f2d14fdb62d2c01547ab962eef36de37d04ad09de4ffec54188c9d792ad",
            "0xf083b46ed21f18ace90b8ef7713fbdb58b2a4babb3f66b187be4a0803527a9f9",
            "0xfa7e604762f4317f929d060a2d9c6d245e75402ffe7efcb9679eb0d8fc7389cc",
            "0x816cc31d257fff3434228aeb0a53a50d032fe47e0833541c5ebd063007511c8d",
        ]
    );

    state.balances.clear();
    state.supplies.clear();
    state.custody.clear();
    state.liabilities.clear();
    state.reserves.clear();
    state.terminal_obligations = vec![
        TerminalObligationV1 {
            obligation_id: "a-open".to_owned(),
            lane_id: ALL_LANE_IDS_V1[0],
            claimant: "alice".to_owned(),
            asset: "ZDEX".to_owned(),
            amount_atoms: 0,
            status: TerminalObligationStatusV1::OPEN,
        },
        TerminalObligationV1 {
            obligation_id: "b-drained".to_owned(),
            lane_id: ALL_LANE_IDS_V1[0],
            claimant: "bob".to_owned(),
            asset: "ZDEX".to_owned(),
            amount_atoms: 1,
            status: TerminalObligationStatusV1::DRAINED,
        },
        TerminalObligationV1 {
            obligation_id: "c-tombstoned".to_owned(),
            lane_id: ALL_LANE_IDS_V1[0],
            claimant: "carol".to_owned(),
            asset: "ZDEX".to_owned(),
            amount_atoms: u128::MAX,
            status: TerminalObligationStatusV1::TOMBSTONED,
        },
    ];
    let terminal_roots: Vec<_> = derive_economic_initial_state_atom_occurrences_v1(&state)
        .unwrap()
        .into_iter()
        .map(|occurrence| occurrence.row_root.as_str().to_owned())
        .collect();
    assert_eq!(
        terminal_roots,
        vec![
            "0xb648e4f3759df2305eec420f54a998300dd7a1de7c401ea3dcca786ed1e8b106",
            "0x3ba55fce49c0b0dd2d6a4be268357ccf3ca855277b3daea11599c66ee444326a",
            "0x9cac82bc2b5ffcd8e60ecefe17aa000d1d2308a097f74a24da966b61ca1d82cc",
        ]
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

#[test]
fn explicit_state_row_count_checks_4095_4096_and_rejects_4097_before_row_validation() {
    let balances = |row_count: usize| {
        (0..row_count)
            .map(|index| EconomicAmountV1 {
                owner: format!("owner-{index:04}"),
                asset: "ZDEX".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: u128::try_from(index).unwrap(),
            })
            .collect::<Vec<_>>()
    };

    for row_count in [4_095, 4_096] {
        let mut state = fixture_state();
        state.balances = balances(row_count);
        state.supplies.clear();
        let occurrences = derive_economic_initial_state_atom_occurrences_v1(&state).unwrap();
        assert_eq!(occurrences.len(), row_count);
        assert_eq!(
            occurrences.last().unwrap().state_row_index,
            u64::try_from(row_count - 1).unwrap()
        );
    }

    let mut oversized = fixture_state();
    oversized.balances = balances(4_097);
    oversized.balances[0].owner = "not allowed unicode ☃".to_owned();
    oversized.supplies.clear();
    assert!(matches!(
        derive_economic_initial_state_atom_occurrences_v1(&oversized),
        Err(AbiErrorV1::InvalidBounds(
            "initial state explicit value rows"
        ))
    ));

    let mut invalid_token = fixture_state();
    invalid_token.balances[0].owner = "not allowed unicode ☃".to_owned();
    assert!(derive_economic_initial_state_atom_occurrences_v1(&invalid_token).is_err());
}
