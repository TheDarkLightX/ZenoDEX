"""Bounded registered-supply complete-row and sparse-support observations.

The V1 cases drive the public global effect projector, whose supply path is
``src/core/global_economic_effect_projector_v1.py:_project_supplies_v1``.
The V2 cases stay on the V2 managed-asset leaf and compare it with an
independent integer-map oracle; V1 objects and the V1 projector are deliberately
absent from that lane.  These tests cover finite row/key correspondence and
reject/no-op behavior.  The V1 projector fixture materializes every positive
non-account remainder as synthetic custody, while remaining unadmitted global
fixture evidence.  They do not establish publisher, finality, crypto, registry
authentication, or whole-runtime refinement.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_effect_projector_v1 import (
    project_single_occurrence_global_effects_v1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    canonical_global_bytes_v1,
)
from src.core.global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    MAX_DELTA_ATOMS_V2,
    MIN_DELTA_ATOMS_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v1 import (
    transition_managed_asset_lifecycle_v1,
)
from src.core.managed_asset_lifecycle_module_v2 import (
    transition_managed_asset_lifecycle_v2,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleStateV2,
)
from tests.core import test_managed_asset_lifecycle_boundaries_v1 as _v1_fixture
from tests.core import test_managed_asset_lifecycle_module_v2 as _v2_fixture


def _root(value: int) -> str:
    return f"0x{value:064x}"


_REGISTERED_ASSETS = ("AAA", "MMM", "UNTOUCHED", "ZZZ")
REGISTERED_ASSETS_V1 = _REGISTERED_ASSETS
REGISTERED_ASSETS_V2 = _REGISTERED_ASSETS
_SUPPLY_GRID = (
    ("first", "AAA", (("AAA", 0), ("MMM", 17), ("UNTOUCHED", 0), ("ZZZ", 23))),
    ("middle", "MMM", (("AAA", 17), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 23))),
    ("last", "ZZZ", (("AAA", 17), ("MMM", 23), ("UNTOUCHED", 0), ("ZZZ", 0))),
)
V1_SUPPLY_GRID = _SUPPLY_GRID
V2_SUPPLY_GRID = _SUPPLY_GRID


def _complete_integer_update(
    rows: tuple[tuple[str, int], ...],
    asset: str,
    delta_atoms: int,
    maximum: int,
) -> tuple[tuple[str, int], ...]:
    """Update complete rows without filtering registered zero rows."""

    values = dict(rows)
    if asset not in values:
        raise AssertionError("integer oracle requires a registered complete row")
    projected = values[asset] + delta_atoms
    if not 0 <= projected <= maximum:
        raise AssertionError("integer oracle received an out-of-range projection")
    values[asset] = projected
    return tuple(sorted(values.items()))


def _sparse_integer_update(
    rows: tuple[tuple[str, int], ...],
    asset: str,
    delta_atoms: int,
    maximum: int,
) -> tuple[tuple[str, int], ...]:
    """Independently update numeric support and omit exactly zero values."""

    values = {row_asset: amount for row_asset, amount in rows if amount != 0}
    projected = values.get(asset, 0) + delta_atoms
    if not 0 <= projected <= maximum:
        raise AssertionError("integer oracle received an out-of-range projection")
    if projected == 0:
        values.pop(asset, None)
    else:
        values[asset] = projected
    return tuple(sorted(values.items()))


def _expected_supply_pairs(
    rows: tuple[tuple[str, int], ...],
    asset: str,
    delta_atoms: int,
    maximum: int,
) -> tuple[tuple[tuple[str, int], ...], tuple[tuple[str, int], ...]]:
    return (
        _complete_integer_update(rows, asset, delta_atoms, maximum),
        _sparse_integer_update(rows, asset, delta_atoms, maximum),
    )


def _pairs_v1(rows: tuple[AssetSupplyV1, ...]) -> tuple[tuple[str, int], ...]:
    return tuple((row.asset, row.amount_atoms) for row in rows)


def _pairs_v2(rows: tuple[AssetSupplyV2, ...]) -> tuple[tuple[str, int], ...]:
    return tuple((row.asset, row.amount_atoms) for row in rows)


def _numeric_pairs_v1(rows: tuple[AssetSupplyV1, ...]) -> tuple[tuple[str, int], ...]:
    return tuple((row.asset, row.amount_atoms) for row in rows if row.amount_atoms != 0)


def _numeric_pairs_v2(rows: tuple[AssetSupplyV2, ...]) -> tuple[tuple[str, int], ...]:
    return tuple((row.asset, row.amount_atoms) for row in rows if row.amount_atoms != 0)


def _assert_supply_pair_observation(
    *,
    initial_rows: tuple[tuple[str, int], ...],
    expected_complete: tuple[tuple[str, int], ...],
    expected_sparse: tuple[tuple[str, int], ...],
    post_complete: tuple[tuple[str, int], ...],
    post_sparse: tuple[tuple[str, int], ...],
    registered_assets: tuple[str, ...],
    target_asset: str,
    target_position: int,
    issue: bool,
) -> None:
    """Check only immutable row-pair observations shared by V1 and V2."""

    assert post_complete == expected_complete
    assert tuple(asset for asset, _ in post_complete) == registered_assets
    assert post_sparse == expected_sparse
    assert tuple(asset for asset, amount in post_complete if amount != 0) == tuple(
        asset for asset, _ in expected_sparse
    )
    assert all(amount > 0 for _, amount in expected_sparse)
    post_values = dict(post_complete)
    assert post_values["UNTOUCHED"] == 0
    for untouched_asset, untouched_amount in initial_rows:
        if untouched_asset != target_asset:
            assert post_values[untouched_asset] == untouched_amount
    if issue:
        assert tuple(asset for asset, _ in expected_sparse).index(target_asset) == target_position
    else:
        assert target_asset not in tuple(asset for asset, _ in expected_sparse)


def _v1_policy(asset: str) -> ManagedAssetLifecyclePolicyV1:
    return replace(_v1_fixture._policy(), asset=asset)


def _v1_state(
    supply_rows: tuple[tuple[str, int], ...],
    *,
    target_asset: str,
    target_balance_atoms: int,
) -> ManagedAssetLifecycleStateV1:
    balances = (
        (
            EconomicAmountV1(
                "alice",
                target_asset,
                ACCOUNT_CUSTODY_DOMAIN_V1,
                target_balance_atoms,
            ),
        )
        if target_balance_atoms
        else ()
    )
    return ManagedAssetLifecycleStateV1(
        module_release_id=_root(3),
        policies=tuple(_v1_policy(asset) for asset in REGISTERED_ASSETS_V1),
        balances=balances,
        supplies=tuple(AssetSupplyV1(asset, amount) for asset, amount in supply_rows),
    )


def _v1_command(*, issue: bool, asset: str, amount_atoms: int) -> ManagedAssetLifecycleCommandV1:
    return replace(
        _v1_fixture._command(issue=issue, amount_atoms=amount_atoms),
        asset=asset,
    )


def _v1_fixture_custody(
    local_state: ManagedAssetLifecycleStateV1,
) -> tuple[EconomicAmountV1, ...]:
    """Account for each positive non-account remainder in the projector fixture."""

    custody_rows: list[EconomicAmountV1] = []
    for supply in local_state.supplies:
        account_atoms = local_state.balance_atoms("alice", supply.asset)
        remainder_atoms = supply.amount_atoms - account_atoms
        if remainder_atoms < 0:
            raise AssertionError("fixture account balance exceeds its supply")
        if remainder_atoms:
            custody_rows.append(
                EconomicAmountV1(
                    "fixture-custody",
                    supply.asset,
                    ACCOUNT_CUSTODY_DOMAIN_V1,
                    remainder_atoms,
                )
            )
    return tuple(custody_rows)


def _v1_global_state(local_state: ManagedAssetLifecycleStateV1) -> GlobalEconomicStateV1:
    """Build a projector-only global state with positive remainders in custody."""

    return GlobalEconomicStateV1(
        chain_id="zeno-registered-supply-v1",
        deployment_root=_root(1),
        writer_epoch=7,
        height=0,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV1(
                lane_id,
                _root(100 + index),
                True,
                local_state.state_root
                if lane_id is LaneIdV1.ASSET_TRANSFER
                else _root(200 + index),
            )
            for index, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        ),
        balances=local_state.balances,
        custody=_v1_fixture_custody(local_state),
        supplies=tuple(row for row in local_state.supplies if row.amount_atoms != 0),
    )


def _v1_occurrence(
    global_state: GlobalEconomicStateV1,
    command: ManagedAssetLifecycleCommandV1,
    *,
    issue: bool,
    nonce: int,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id=global_state.chain_id,
        deployment_root=global_state.deployment_root,
        height=global_state.height + 1,
        tx_index=0,
        op_index=0,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root(8),
        subject_id="issuer" if issue else "alice",
        grant_root=_root(5 if issue else 6),
        nonce=nonce,
        profile_root=global_state.profile_root,
        pre_state_root=global_state.state_root,
        consumed_object_ids=(),
    )


def _v1_context(
    local_state: ManagedAssetLifecycleStateV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> ManagedAssetLifecycleContextV1:
    return replace(
        _v1_fixture._context(issue=occurrence.subject_id == "issuer"),
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        module_release_id=local_state.module_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        subject_id=occurrence.subject_id,
        grant_root=occurrence.grant_root,
    )


def _v1_step(
    local_state: ManagedAssetLifecycleStateV1,
    global_state: GlobalEconomicStateV1,
    *,
    issue: bool,
    asset: str,
    amount_atoms: int,
    nonce: int,
) -> tuple[ManagedAssetLifecycleAcceptedV1, GlobalEconomicStateV1]:
    command = _v1_command(issue=issue, asset=asset, amount_atoms=amount_atoms)
    occurrence = _v1_occurrence(global_state, command, issue=issue, nonce=nonce)
    before_local = canonical_global_bytes_v1(local_state.to_canonical())
    before_global = canonical_global_bytes_v1(global_state.to_canonical())
    result = transition_managed_asset_lifecycle_v1(
        _v1_context(local_state, occurrence),
        local_state,
        command,
    )
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert canonical_global_bytes_v1(local_state.to_canonical()) == before_local
    projected = project_single_occurrence_global_effects_v1(
        global_state,
        result.effects,
        occurrence,
    )
    assert canonical_global_bytes_v1(global_state.to_canonical()) == before_global
    return result, projected


def _v2_origin(asset: str) -> str:
    return _root(40 + REGISTERED_ASSETS_V2.index(asset))


def _v2_policy(
    asset: str,
    *,
    origin: str | None = None,
) -> ManagedAssetLifecyclePolicyV2:
    return replace(
        _v2_fixture._policy(),
        asset=asset,
        asset_origin_root=_v2_origin(asset) if origin is None else origin,
    )


def _v2_state(
    supply_rows: tuple[tuple[str, int], ...],
    *,
    target_asset: str,
    target_balance_atoms: int,
) -> ManagedAssetLifecycleStateV2:
    balances = (
        (
            EconomicAmountV2(
                "alice",
                target_asset,
                ACCOUNT_CUSTODY_DOMAIN_V2,
                target_balance_atoms,
            ),
        )
        if target_balance_atoms
        else ()
    )
    return ManagedAssetLifecycleStateV2(
        module_release_id=_root(3),
        policies=tuple(_v2_policy(asset) for asset in REGISTERED_ASSETS_V2),
        balances=balances,
        supplies=tuple(AssetSupplyV2(asset, amount) for asset, amount in supply_rows),
    )


def _v2_command(
    *,
    issue: bool,
    asset: str,
    amount_atoms: int,
    origin: str | None,
    authorization_root: str | None = None,
) -> ManagedAssetLifecycleCommandV2:
    return replace(
        _v2_fixture._command(
            command_kind=(
                MANAGED_ASSET_ISSUE_COMMAND_KIND_V2 if issue else MANAGED_ASSET_BURN_COMMAND_KIND_V2
            ),
            amount_atoms=amount_atoms,
            authorization_root=(
                _root(5 if issue else 6) if authorization_root is None else authorization_root
            ),
        ),
        asset=asset,
        asset_origin_root=origin,
    )


def _v2_occurrence(
    command: ManagedAssetLifecycleCommandV2,
    *,
    issue: bool,
    nonce: int,
) -> EconomicCommandOccurrenceV2:
    context = _v2_fixture._context(
        command=command,
        subject="issuer" if issue else "alice",
        grant=_root(5 if issue else 6),
        global_pre_root=_root(900 + nonce),
        nonce=nonce,
    )
    occurrence = context.occurrence
    if occurrence is None:
        raise AssertionError("V2 fixture context did not create an occurrence")
    return occurrence


def _v2_context(
    local_state: ManagedAssetLifecycleStateV2,
    occurrence: EconomicCommandOccurrenceV2,
) -> ManagedAssetLifecycleContextV2:
    return _v2_fixture._context(
        occurrence=occurrence,
        global_pre_root=occurrence.pre_state_root,
        module_release_id=local_state.module_release_id,
    )


def _v2_step(
    local_state: ManagedAssetLifecycleStateV2,
    *,
    issue: bool,
    asset: str,
    amount_atoms: int,
    nonce: int,
) -> ManagedAssetLifecycleAcceptedV2:
    command = _v2_command(
        issue=issue,
        asset=asset,
        amount_atoms=amount_atoms,
        origin=_v2_origin(asset),
    )
    occurrence = _v2_occurrence(command, issue=issue, nonce=nonce)
    before = canonical_global_bytes_v2(local_state.to_canonical())
    result = transition_managed_asset_lifecycle_v2(
        _v2_context(local_state, occurrence),
        local_state,
        command,
    )
    assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
    assert canonical_global_bytes_v2(local_state.to_canonical()) == before
    return result


def _assert_v1_rejected_noop(
    state: ManagedAssetLifecycleStateV1,
    command: ManagedAssetLifecycleCommandV1,
    code: ManagedAssetLifecycleRejectCodeV1,
    *,
    issue: bool,
    nonce: int,
) -> None:
    global_state = _v1_global_state(state)
    occurrence = _v1_occurrence(global_state, command, issue=issue, nonce=nonce)
    before_local = canonical_global_bytes_v1(state.to_canonical())
    before_global = canonical_global_bytes_v1(global_state.to_canonical())
    result = transition_managed_asset_lifecycle_v1(
        _v1_context(state, occurrence),
        state,
        command,
    )
    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert result.code is code
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert result.effects.rows == ()
    assert canonical_global_bytes_v1(state.to_canonical()) == before_local
    assert canonical_global_bytes_v1(global_state.to_canonical()) == before_global


def _assert_v2_rejected_noop(
    state: ManagedAssetLifecycleStateV2,
    command: ManagedAssetLifecycleCommandV2,
    code: ManagedAssetLifecycleRejectCodeV2,
    *,
    issue: bool,
    nonce: int,
) -> None:
    occurrence = _v2_occurrence(command, issue=issue, nonce=nonce)
    before = canonical_global_bytes_v2(state.to_canonical())
    result = transition_managed_asset_lifecycle_v2(
        _v2_context(state, occurrence),
        state,
        command,
    )
    assert isinstance(result, ManagedAssetLifecycleRejectedV2)
    assert result.code is code
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert result.effects.rows == ()
    assert canonical_global_bytes_v2(state.to_canonical()) == before


@pytest.mark.parametrize(
    ("case_name", "target_asset", "supply_rows"),
    V1_SUPPLY_GRID,
    ids=("first", "middle", "last"),
)
def test_v1_complete_rows_and_sparse_projector_follow_first_middle_last_cycle(
    case_name: str,
    target_asset: str,
    supply_rows: tuple[tuple[str, int], ...],
) -> None:
    local_state = _v1_state(
        supply_rows,
        target_asset=target_asset,
        target_balance_atoms=0,
    )
    global_state = _v1_global_state(local_state)
    amount_atoms = 7
    expected_position = {"first": 0, "middle": 1, "last": 2}[case_name]

    assert _pairs_v1(local_state.supplies) == supply_rows
    assert _numeric_pairs_v1(local_state.supplies) == _sparse_integer_update(
        supply_rows,
        target_asset,
        0,
        MAX_ATOMS_V1,
    )
    assert _pairs_v1(global_state.supplies) == _numeric_pairs_v1(local_state.supplies)

    for nonce, issue in enumerate((True, False, True), start=1):
        delta_atoms = amount_atoms if issue else -amount_atoms
        pre_complete = _pairs_v1(local_state.supplies)
        pre_custody = global_state.custody
        result, projected_global = _v1_step(
            local_state,
            global_state,
            issue=issue,
            asset=target_asset,
            amount_atoms=amount_atoms,
            nonce=nonce,
        )
        post_state = result.post_state
        expected_complete, expected_sparse = _expected_supply_pairs(
            pre_complete,
            target_asset,
            delta_atoms,
            MAX_ATOMS_V1,
        )
        _assert_supply_pair_observation(
            initial_rows=pre_complete,
            expected_complete=expected_complete,
            expected_sparse=expected_sparse,
            post_complete=_pairs_v1(post_state.supplies),
            post_sparse=_numeric_pairs_v1(post_state.supplies),
            registered_assets=REGISTERED_ASSETS_V1,
            target_asset=target_asset,
            target_position=expected_position,
            issue=issue,
        )
        assert _pairs_v1(projected_global.supplies) == expected_sparse
        assert projected_global.custody == pre_custody
        supply_effects = tuple(
            row
            for row in result.effects.rows
            if row.kind in {EconomicEffectKindV1.ISSUE, EconomicEffectKindV1.BURN}
        )
        assert len(supply_effects) == 1
        assert supply_effects[0].asset == target_asset
        assert supply_effects[0].delta_atoms == delta_atoms
        local_state = post_state
        global_state = projected_global


@pytest.mark.parametrize(
    ("case_name", "target_asset", "supply_rows"),
    V2_SUPPLY_GRID,
    ids=("first", "middle", "last"),
)
def test_v2_complete_rows_and_sparse_integer_support_follow_first_middle_last_cycle(
    case_name: str,
    target_asset: str,
    supply_rows: tuple[tuple[str, int], ...],
) -> None:
    local_state = _v2_state(
        supply_rows,
        target_asset=target_asset,
        target_balance_atoms=0,
    )
    amount_atoms = 7
    expected_position = {"first": 0, "middle": 1, "last": 2}[case_name]

    assert _pairs_v2(local_state.supplies) == supply_rows
    assert _numeric_pairs_v2(local_state.supplies) == _sparse_integer_update(
        supply_rows,
        target_asset,
        0,
        MAX_ATOMS_V2,
    )

    for nonce, issue in enumerate((True, False, True), start=1):
        delta_atoms = amount_atoms if issue else -amount_atoms
        pre_complete = _pairs_v2(local_state.supplies)
        result = _v2_step(
            local_state,
            issue=issue,
            asset=target_asset,
            amount_atoms=amount_atoms,
            nonce=nonce,
        )
        post_state = result.post_state
        expected_complete, expected_sparse = _expected_supply_pairs(
            pre_complete,
            target_asset,
            delta_atoms,
            MAX_ATOMS_V2,
        )
        _assert_supply_pair_observation(
            initial_rows=pre_complete,
            expected_complete=expected_complete,
            expected_sparse=expected_sparse,
            post_complete=_pairs_v2(post_state.supplies),
            post_sparse=_numeric_pairs_v2(post_state.supplies),
            registered_assets=REGISTERED_ASSETS_V2,
            target_asset=target_asset,
            target_position=expected_position,
            issue=issue,
        )
        supply_effects = tuple(
            row
            for row in result.effects.rows
            if row.kind in {EconomicEffectKindV2.ISSUE, EconomicEffectKindV2.BURN}
        )
        assert len(supply_effects) == 1
        assert supply_effects[0].asset == target_asset
        assert supply_effects[0].delta_atoms == delta_atoms
        local_state = post_state


def test_v1_issue_accepts_i128_max_and_projects_u128_value() -> None:
    amount_atoms = MAX_DELTA_ATOMS_V1
    supply_rows = (("AAA", 0), ("MMM", 17), ("UNTOUCHED", 0), ("ZZZ", 23))
    local_state = _v1_state(supply_rows, target_asset="AAA", target_balance_atoms=0)
    result, projected = _v1_step(
        local_state,
        _v1_global_state(local_state),
        issue=True,
        asset="AAA",
        amount_atoms=amount_atoms,
        nonce=101,
    )

    assert result.post_state.supply_atoms("AAA") == MAX_DELTA_ATOMS_V1
    issue_effects = tuple(
        row for row in result.effects.rows if row.kind is EconomicEffectKindV1.ISSUE
    )
    assert len(issue_effects) == 1
    assert issue_effects[0].delta_atoms == MAX_DELTA_ATOMS_V1
    assert projected.supplies[0] == AssetSupplyV1("AAA", MAX_DELTA_ATOMS_V1)
    assert MAX_ATOMS_V1 == (1 << 128) - 1
    assert MAX_DELTA_ATOMS_V1 == (1 << 127) - 1


def test_v1_burn_accepts_i128_min_magnitude_and_removes_zero_support() -> None:
    amount_atoms = -MIN_DELTA_ATOMS_V1
    supply_rows = (("AAA", amount_atoms), ("MMM", 17), ("UNTOUCHED", 0), ("ZZZ", 23))
    local_state = _v1_state(
        supply_rows,
        target_asset="AAA",
        target_balance_atoms=amount_atoms,
    )
    result, projected = _v1_step(
        local_state,
        _v1_global_state(local_state),
        issue=False,
        asset="AAA",
        amount_atoms=amount_atoms,
        nonce=102,
    )

    assert result.post_state.supply_atoms("AAA") == 0
    assert result.post_state.balances == ()
    assert any(
        row.kind is EconomicEffectKindV1.BURN and row.delta_atoms == MIN_DELTA_ATOMS_V1
        for row in result.effects.rows
    )
    assert _pairs_v1(projected.supplies) == (("MMM", 17), ("ZZZ", 23))
    assert MIN_DELTA_ATOMS_V1 == -(1 << 127)


@pytest.mark.parametrize(
    ("issue", "amount_atoms"),
    (
        (True, MAX_DELTA_ATOMS_V1 + 1),
        (False, -MIN_DELTA_ATOMS_V1 + 1),
    ),
    ids=("issue-first-invalid-neighbor", "burn-first-invalid-neighbor"),
)
def test_v1_signed_effect_width_rejects_first_invalid_neighbor_as_noop(
    issue: bool,
    amount_atoms: int,
) -> None:
    supply_rows = (("AAA", 0 if issue else amount_atoms), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 0))
    state = _v1_state(
        supply_rows,
        target_asset="AAA",
        target_balance_atoms=0 if issue else amount_atoms,
    )
    _assert_v1_rejected_noop(
        state,
        _v1_command(issue=issue, asset="AAA", amount_atoms=amount_atoms),
        ManagedAssetLifecycleRejectCodeV1.EFFECT_DELTA_OVERFLOW,
        issue=issue,
        nonce=103 if issue else 104,
    )


def test_v2_issue_accepts_i128_max_and_retains_complete_zero_rows() -> None:
    amount_atoms = MAX_DELTA_ATOMS_V2
    supply_rows = (("AAA", 0), ("MMM", 17), ("UNTOUCHED", 0), ("ZZZ", 23))
    local_state = _v2_state(supply_rows, target_asset="AAA", target_balance_atoms=0)
    result = _v2_step(
        local_state,
        issue=True,
        asset="AAA",
        amount_atoms=amount_atoms,
        nonce=201,
    )

    assert result.post_state.supply_atoms("AAA") == MAX_DELTA_ATOMS_V2
    assert tuple(row.asset for row in result.post_state.supplies) == REGISTERED_ASSETS_V2
    issue_effects = tuple(
        row for row in result.effects.rows if row.kind is EconomicEffectKindV2.ISSUE
    )
    assert len(issue_effects) == 1
    assert issue_effects[0].delta_atoms == MAX_DELTA_ATOMS_V2
    assert _numeric_pairs_v2(result.post_state.supplies) == (
        ("AAA", MAX_DELTA_ATOMS_V2),
        ("MMM", 17),
        ("ZZZ", 23),
    )
    assert MAX_ATOMS_V2 == (1 << 128) - 1
    assert MAX_DELTA_ATOMS_V2 == (1 << 127) - 1


def test_v2_burn_accepts_i128_min_magnitude_and_removes_zero_support() -> None:
    amount_atoms = -MIN_DELTA_ATOMS_V2
    supply_rows = (("AAA", amount_atoms), ("MMM", 17), ("UNTOUCHED", 0), ("ZZZ", 23))
    local_state = _v2_state(
        supply_rows,
        target_asset="AAA",
        target_balance_atoms=amount_atoms,
    )
    result = _v2_step(
        local_state,
        issue=False,
        asset="AAA",
        amount_atoms=amount_atoms,
        nonce=202,
    )

    assert result.post_state.supply_atoms("AAA") == 0
    assert result.post_state.balances == ()
    assert any(
        row.kind is EconomicEffectKindV2.BURN and row.delta_atoms == MIN_DELTA_ATOMS_V2
        for row in result.effects.rows
    )
    assert _numeric_pairs_v2(result.post_state.supplies) == (("MMM", 17), ("ZZZ", 23))
    assert MIN_DELTA_ATOMS_V2 == -(1 << 127)


@pytest.mark.parametrize(
    ("issue", "amount_atoms"),
    (
        (True, MAX_DELTA_ATOMS_V2 + 1),
        (False, -MIN_DELTA_ATOMS_V2 + 1),
    ),
    ids=("issue-first-invalid-neighbor", "burn-first-invalid-neighbor"),
)
def test_v2_signed_effect_width_rejects_first_invalid_neighbor_as_noop(
    issue: bool,
    amount_atoms: int,
) -> None:
    supply_rows = (("AAA", 0 if issue else amount_atoms), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 0))
    state = _v2_state(
        supply_rows,
        target_asset="AAA",
        target_balance_atoms=0 if issue else amount_atoms,
    )
    _assert_v2_rejected_noop(
        state,
        _v2_command(
            issue=issue,
            asset="AAA",
            amount_atoms=amount_atoms,
            origin=_v2_origin("AAA"),
        ),
        ManagedAssetLifecycleRejectCodeV2.EFFECT_DELTA_OVERFLOW,
        issue=issue,
        nonce=203 if issue else 204,
    )


def test_v1_u128_supply_overflow_is_a_byte_preserving_noop() -> None:
    state = _v1_state(
        (("AAA", MAX_ATOMS_V1), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 0)),
        target_asset="AAA",
        target_balance_atoms=0,
    )
    _assert_v1_rejected_noop(
        state,
        _v1_command(issue=True, asset="AAA", amount_atoms=1),
        ManagedAssetLifecycleRejectCodeV1.SUPPLY_OVERFLOW,
        issue=True,
        nonce=105,
    )


def test_v2_u128_supply_overflow_is_a_byte_preserving_noop() -> None:
    state = _v2_state(
        (("AAA", MAX_ATOMS_V2), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 0)),
        target_asset="AAA",
        target_balance_atoms=0,
    )
    _assert_v2_rejected_noop(
        state,
        _v2_command(
            issue=True,
            asset="AAA",
            amount_atoms=1,
            origin=_v2_origin("AAA"),
        ),
        ManagedAssetLifecycleRejectCodeV2.SUPPLY_OVERFLOW,
        issue=True,
        nonce=205,
    )


def test_v1_account_shortage_is_a_byte_preserving_noop() -> None:
    state = _v1_state(
        (("AAA", 10), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 0)),
        target_asset="AAA",
        target_balance_atoms=1,
    )
    _assert_v1_rejected_noop(
        state,
        _v1_command(issue=False, asset="AAA", amount_atoms=2),
        ManagedAssetLifecycleRejectCodeV1.INSUFFICIENT_BALANCE,
        issue=False,
        nonce=106,
    )


def test_v2_account_shortage_is_a_byte_preserving_noop() -> None:
    state = _v2_state(
        (("AAA", 10), ("MMM", 0), ("UNTOUCHED", 0), ("ZZZ", 0)),
        target_asset="AAA",
        target_balance_atoms=1,
    )
    _assert_v2_rejected_noop(
        state,
        _v2_command(
            issue=False,
            asset="AAA",
            amount_atoms=2,
            origin=_v2_origin("AAA"),
        ),
        ManagedAssetLifecycleRejectCodeV2.INSUFFICIENT_BALANCE,
        issue=False,
        nonce=206,
    )


def test_v1_unknown_asset_rejection_is_a_byte_preserving_noop() -> None:
    state = _v1_state(
        (("AAA", 0), ("MMM", 2), ("UNTOUCHED", 0), ("ZZZ", 0)),
        target_asset="AAA",
        target_balance_atoms=0,
    )
    _assert_v1_rejected_noop(
        state,
        _v1_command(issue=True, asset="MISSING", amount_atoms=1),
        ManagedAssetLifecycleRejectCodeV1.UNKNOWN_ASSET,
        issue=True,
        nonce=107,
    )


def test_v2_unknown_asset_rejection_is_a_byte_preserving_noop() -> None:
    state = _v2_state(
        (("AAA", 0), ("MMM", 2), ("UNTOUCHED", 0), ("ZZZ", 0)),
        target_asset="AAA",
        target_balance_atoms=0,
    )
    _assert_v2_rejected_noop(
        state,
        _v2_command(
            issue=True,
            asset="MISSING",
            amount_atoms=1,
            origin=_root(999),
        ),
        ManagedAssetLifecycleRejectCodeV2.UNKNOWN_ASSET,
        issue=True,
        nonce=207,
    )


def test_v2_unknown_registration_is_rejected_before_correspondence() -> None:
    policy = replace(_v2_fixture._policy(), asset="AAA", asset_origin_root=None)
    state = ManagedAssetLifecycleStateV2(
        module_release_id=_root(3),
        policies=(policy,),
        balances=(),
        supplies=(AssetSupplyV2("AAA", 0),),
    )
    command = _v2_command(
        issue=True,
        asset="AAA",
        amount_atoms=1,
        origin=None,
    )

    _assert_v2_rejected_noop(
        state,
        command,
        ManagedAssetLifecycleRejectCodeV2.UNREGISTERED_ASSET,
        issue=True,
        nonce=208,
    )


def test_countermodel_empty_registered_keys_make_decode_equality_vacuous() -> None:
    registered_keys: tuple[str, ...] = ()
    numeric_support = (("UNREGISTERED", 1),)
    decoded_complete = tuple(
        (asset, dict(numeric_support).get(asset, 0)) for asset in registered_keys
    )

    # A decode-only relation over P=[] says nothing because both decoded lists
    # are empty.  Numeric support still exposes the unknown registered key.
    assert decoded_complete == ()
    assert numeric_support != decoded_complete


def test_v1_countermodel_duplicate_supply_keys_are_rejected_before_projection() -> None:
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        ManagedAssetLifecycleStateV1(
            module_release_id=_root(3),
            policies=(_v1_policy("AAA"), _v1_policy("MMM")),
            balances=(),
            supplies=(AssetSupplyV1("AAA", 1), AssetSupplyV1("AAA", 2)),
        )


def test_v2_countermodel_duplicate_supply_keys_are_rejected_before_projection() -> None:
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        ManagedAssetLifecycleStateV2(
            module_release_id=_root(3),
            policies=(_v2_policy("AAA"), _v2_policy("MMM")),
            balances=(),
            supplies=(AssetSupplyV2("AAA", 1), AssetSupplyV2("AAA", 2)),
        )
