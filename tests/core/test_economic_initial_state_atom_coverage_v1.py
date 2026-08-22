from __future__ import annotations

from dataclasses import replace

import pytest

import src.core.economic_initial_state_atom_coverage_v1 as coverage_module
from src.core.economic_initial_state_atom_coverage_v1 import (
    MAX_INITIAL_STATE_ATOM_ROWS_V1,
    EconomicInitialStateAtomClassificationV1,
    EconomicInitialStateAtomKindV1,
    EconomicInitialStateAtomOccurrenceV1,
    EconomicInitialStateAtomSourceV1,
    EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1,
    derive_economic_initial_state_atom_occurrences_v1,
    economic_initial_state_atom_occurrence_v1,
    validate_economic_initial_state_atom_coverage_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _state() -> GlobalEconomicStateV1:
    lane_roots = tuple(
        LaneStateRootV1(lane_id, _root(100 + index), False, _root(200 + index))
        for index, lane_id in enumerate(ALL_LANE_IDS_V1)
    )
    return GlobalEconomicStateV1(
        chain_id="initial-coverage-test",
        deployment_root=_root(1),
        writer_epoch=3,
        height=0,
        profile_root=_root(2),
        lane_roots=lane_roots,
        balances=(EconomicAmountV1("alice", "ZDEX", "accounts", 1),),
        supplies=(AssetSupplyV1("ZDEX", 6),),
        custody=(EconomicAmountV1("pool-1", "ZDEX", "pool", 2),),
        liabilities=(EconomicAmountV1("claim-1", "ZDEX", "claim", 3),),
        reserves=(EconomicAmountV1("treasury", "ZDEX", "reserve", 4),),
        terminal_obligations=(
            TerminalObligationV1(
                "terminal-1",
                ALL_LANE_IDS_V1[0],
                "bob",
                "ZDEX",
                5,
                TerminalObligationStatusV1.OPEN,
            ),
        ),
    )


def _manifest(
    state: GlobalEconomicStateV1,
    *,
    kind: EconomicInitialStateKindV1 = EconomicInitialStateKindV1.GENESIS,
) -> EconomicInitialStateSourceManifestV1:
    classifications = {
        EconomicInitialStateKindV1.GENESIS: (
            EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION
        ),
        EconomicInitialStateKindV1.MIGRATION: (
            EconomicInitialStateAtomClassificationV1.MIGRATED_TARGET
        ),
    }
    rows = tuple(
        EconomicInitialStateAtomSourceV1(
            occurrence=occurrence,
            classification=classifications[kind],
            source_authorization_root=_root(1_000 + index),
        )
        for index, occurrence in enumerate(
            derive_economic_initial_state_atom_occurrences_v1(state)
        )
    )
    return EconomicInitialStateSourceManifestV1(kind=kind, rows=rows)


def test_given_all_explicit_value_rows_when_derived_then_each_is_classified_once() -> None:
    # Arrange
    state = _state()
    manifest = _manifest(state)

    # Act
    coverage_root = validate_economic_initial_state_atom_coverage_v1(state, manifest)

    # Assert
    assert tuple(row.occurrence.atom_kind for row in manifest.rows) == (
        EconomicInitialStateAtomKindV1.BALANCE,
        EconomicInitialStateAtomKindV1.SUPPLY,
        EconomicInitialStateAtomKindV1.CUSTODY,
        EconomicInitialStateAtomKindV1.LIABILITY,
        EconomicInitialStateAtomKindV1.RESERVE,
        EconomicInitialStateAtomKindV1.TERMINAL_OBLIGATION,
    )
    assert coverage_root == manifest.manifest_root


def test_atom_row_and_manifest_roots_match_rust_golden_vectors() -> None:
    # Arrange
    occurrence = EconomicInitialStateAtomOccurrenceV1(
        EconomicInitialStateAtomKindV1.BALANCE,
        0,
        _root(1),
    )
    derived = economic_initial_state_atom_occurrence_v1(
        EconomicInitialStateAtomKindV1.BALANCE,
        0,
        EconomicAmountV1("alice", "USD", "accounts", 18_446_744_073_709_551_617),
    )
    manifest = EconomicInitialStateSourceManifestV1(
        EconomicInitialStateKindV1.GENESIS,
        (
            EconomicInitialStateAtomSourceV1(
                occurrence,
                EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION,
                _root(3),
            ),
            EconomicInitialStateAtomSourceV1(
                EconomicInitialStateAtomOccurrenceV1(
                    EconomicInitialStateAtomKindV1.SUPPLY,
                    0,
                    _root(2),
                ),
                EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION,
                _root(4),
            ),
        ),
    )

    # Act / Assert
    assert derived.row_root == (
        "0x1fc5f26e9f5e3513aa34afc2a5d7d4513002e1479c04d03b45b7a88b47e7c534"
    )
    assert manifest.manifest_root == (
        "0x8fb2073a85c1b563f09860071e0d3ebd2508be80a111c95fcf585eebc90187ba"
    )

    all_kind_roots = tuple(
        occurrence.row_root
        for occurrence in derive_economic_initial_state_atom_occurrences_v1(_state())
    )
    assert all_kind_roots == (
        "0x9cd2992d3a82595674d5901579ff34119bc3c38416516a13563ccbd8c0bb9248",
        "0x89b99532450803b9a8360197d2ae4b3786724369c5f1f384b3a801c059010e45",
        "0xcbc21f2d14fdb62d2c01547ab962eef36de37d04ad09de4ffec54188c9d792ad",
        "0xf083b46ed21f18ace90b8ef7713fbdb58b2a4babb3f66b187be4a0803527a9f9",
        "0xfa7e604762f4317f929d060a2d9c6d245e75402ffe7efcb9679eb0d8fc7389cc",
        "0x816cc31d257fff3434228aeb0a53a50d032fe47e0833541c5ebd063007511c8d",
    )

    terminal_status_state = replace(
        _state(),
        balances=(),
        supplies=(),
        custody=(),
        liabilities=(),
        reserves=(),
        terminal_obligations=(
            TerminalObligationV1(
                "a-open",
                ALL_LANE_IDS_V1[0],
                "alice",
                "ZDEX",
                0,
                TerminalObligationStatusV1.OPEN,
            ),
            TerminalObligationV1(
                "b-drained",
                ALL_LANE_IDS_V1[0],
                "bob",
                "ZDEX",
                1,
                TerminalObligationStatusV1.DRAINED,
            ),
            TerminalObligationV1(
                "c-tombstoned",
                ALL_LANE_IDS_V1[0],
                "carol",
                "ZDEX",
                (1 << 128) - 1,
                TerminalObligationStatusV1.TOMBSTONED,
            ),
        ),
    )
    assert tuple(
        occurrence.row_root
        for occurrence in derive_economic_initial_state_atom_occurrences_v1(
            terminal_status_state
        )
    ) == (
        "0xb648e4f3759df2305eec420f54a998300dd7a1de7c401ea3dcca786ed1e8b106",
        "0x3ba55fce49c0b0dd2d6a4be268357ccf3ca855277b3daea11599c66ee444326a",
        "0x9cac82bc2b5ffcd8e60ecefe17aa000d1d2308a097f74a24da966b61ca1d82cc",
    )


@pytest.mark.parametrize("mutation", ("omit", "stale", "wrong_classification"))
def test_given_incomplete_or_stale_manifest_when_validated_then_rejects(
    mutation: str,
) -> None:
    # Arrange
    state = _state()
    manifest = _manifest(state)
    if mutation == "omit":
        mutant = replace(manifest, rows=manifest.rows[:-1])
    elif mutation == "stale":
        stale = replace(manifest.rows[0].occurrence, row_root=_root(99_001))
        mutant = replace(
            manifest,
            rows=(replace(manifest.rows[0], occurrence=stale), *manifest.rows[1:]),
        )
    else:
        object.__setattr__(
            manifest.rows[0],
            "classification",
            EconomicInitialStateAtomClassificationV1.MIGRATED_TARGET,
        )
        mutant = manifest

    # Act / Assert
    with pytest.raises(ValueError, match="initial state (atom|source manifest)"):
        validate_economic_initial_state_atom_coverage_v1(state, mutant)


def test_given_duplicate_or_reordered_rows_when_constructed_then_rejects() -> None:
    # Arrange
    manifest = _manifest(_state())

    # Act / Assert
    with pytest.raises(ValueError, match="ordered and unique"):
        replace(manifest, rows=(manifest.rows[0], manifest.rows[0]))
    with pytest.raises(ValueError, match="ordered and unique"):
        replace(manifest, rows=(manifest.rows[1], manifest.rows[0], *manifest.rows[2:]))


def test_given_state_amount_mutation_when_old_manifest_is_replayed_then_rejects() -> None:
    # Arrange
    state = _state()
    manifest = _manifest(state)
    changed_state = replace(
        state,
        balances=(replace(state.balances[0], amount_atoms=2),),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="does not classify the exact target state"):
        validate_economic_initial_state_atom_coverage_v1(changed_state, manifest)


def test_migration_manifest_accepts_only_target_present_classifications() -> None:
    # Arrange
    state = _state()
    migrated = _manifest(state, kind=EconomicInitialStateKindV1.MIGRATION)
    retained = replace(
        migrated,
        rows=tuple(
            replace(
                row,
                classification=(
                    EconomicInitialStateAtomClassificationV1.RETAINED_DRAIN_TARGET
                ),
            )
            for row in migrated.rows
        ),
    )

    # Act / Assert
    assert validate_economic_initial_state_atom_coverage_v1(state, migrated)
    assert validate_economic_initial_state_atom_coverage_v1(state, retained)
    with pytest.raises(ValueError, match="migration target"):
        replace(
            migrated,
            rows=tuple(
                replace(
                    row,
                    classification=(
                        EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION
                    ),
                )
                for row in migrated.rows
            ),
        )


def test_manifest_row_bound_and_exact_integer_index_bva() -> None:
    # Arrange
    def source(index: int) -> EconomicInitialStateAtomSourceV1:
        return EconomicInitialStateAtomSourceV1(
            occurrence=EconomicInitialStateAtomOccurrenceV1(
                EconomicInitialStateAtomKindV1.BALANCE,
                index,
                _root(index + 1),
            ),
            classification=(
                EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION
            ),
            source_authorization_root=_root(MAX_INITIAL_STATE_ATOM_ROWS_V1 + index + 2),
        )

    at_limit = tuple(source(index) for index in range(MAX_INITIAL_STATE_ATOM_ROWS_V1))

    # Act / Assert
    assert len(
        EconomicInitialStateSourceManifestV1(
            EconomicInitialStateKindV1.GENESIS,
            at_limit,
        ).rows
    ) == MAX_INITIAL_STATE_ATOM_ROWS_V1
    with pytest.raises(ValueError, match="row bound"):
        EconomicInitialStateSourceManifestV1(
            EconomicInitialStateKindV1.GENESIS,
            (*at_limit, source(MAX_INITIAL_STATE_ATOM_ROWS_V1)),
        )
    with pytest.raises(TypeError, match="exact integer"):
        EconomicInitialStateAtomOccurrenceV1(
            EconomicInitialStateAtomKindV1.BALANCE,
            True,  # type: ignore[arg-type]
            _root(9),
        )


def _state_with_balance_count(row_count: int) -> GlobalEconomicStateV1:
    state = _state()
    return replace(
        state,
        balances=tuple(
            EconomicAmountV1(f"owner-{index:04}", "ZDEX", "accounts", index)
            for index in range(row_count)
        ),
        supplies=(),
        custody=(),
        liabilities=(),
        reserves=(),
        terminal_obligations=(),
    )


@pytest.mark.parametrize("row_count", (4_095, 4_096))
def test_explicit_state_row_count_accepts_release_boundary_neighbors(
    row_count: int,
) -> None:
    # Arrange
    state = _state_with_balance_count(row_count)

    # Act
    occurrences = derive_economic_initial_state_atom_occurrences_v1(state)

    # Assert
    assert len(occurrences) == row_count
    assert occurrences[-1].state_row_index == row_count - 1


def test_oversize_state_rejects_before_copy_validation_or_row_hashing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    state = _state_with_balance_count(4_097)

    def forbidden_hash(*_args: object, **_kwargs: object) -> str:
        raise AssertionError("oversize rows must reject before hashing")

    monkeypatch.setattr(coverage_module, "hash_global_v1", forbidden_hash)

    # Act / Assert
    with pytest.raises(ValueError, match="coverage bound"):
        derive_economic_initial_state_atom_occurrences_v1(state)


def test_public_checker_revalidates_hostile_frozen_row_mutation() -> None:
    # Arrange
    state = _state()
    object.__setattr__(state.balances[0], "amount_atoms", 1 << 128)

    # Act / Assert
    with pytest.raises(ValueError, match="unsigned 128-bit"):
        derive_economic_initial_state_atom_occurrences_v1(state)
