"""Real 1 MiB asset-lane boundary controls, with no lowered resource limits.

The independent sizing oracle counts the fixed JSON row skeleton, ASCII quote
and backslash escapes, separators, and decimal digits. Metadata bytes are
obtained from an empty, valid state. These are finite runtime observations,
not a universal serializer or publication proof.
"""

from __future__ import annotations

import pytest

from src.core.asset_lane_coordinator_v2 import (
    AssetLaneAcceptedV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRouteV2,
    transition_asset_lane_v2,
)
from src.core.asset_lane_state_v2 import AssetLaneStateV2
from src.core.global_settlement_resource_limits_v2 import (
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
)
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleAcceptedV2
from tests.core import test_asset_lane_coordinator_v2 as fixture
from tests.core import test_asset_lane_resource_rejection_v2 as resources

_LIMIT = MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
_OWNER = 'ali"ce\\x'
_ROW_SKELETON = b'{"amount_atoms":1,"asset":"EUR","custody_domain":"accounts","owner":""}'


def _escaped_size(text: str) -> int:
    return len(text) + text.count('"') + text.count("\\")


def _boundary_state(*, headroom: int, funded: bool) -> AssetLaneStateV2:
    """Fill the exact requested size with valid rows below the row ceiling."""

    assert _LIMIT == 1_048_576
    usd_rows = ((_OWNER, 9),) if funded else ()
    empty = resources._lane_state(eur_rows=0, usd_rows=usd_rows)
    base_size = len(canonical_global_bytes_v2(empty.to_canonical()))
    target = _LIMIT - headroom
    # A ten-character unique prefix leaves 150 printable-ASCII characters.
    # Each backslash contributes two canonical bytes; an ordinary final
    # character permits either parity without changing a protocol constant.
    min_row_size = len(_ROW_SKELETON) + 10
    max_extra = 300
    count = (target - base_size) // (min_row_size + max_extra + 1) + 1
    first_comma_correction = 0 if funded else 1
    extra = (
        target
        - base_size
        - (len(str(count)) - 1)
        - count * (min_row_size + 1)
        + first_comma_correction
    )
    assert 0 <= extra <= max_extra * count
    assert count + len(usd_rows) < MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
    rows = []
    for index in range(count):
        contribution = min(extra, max_extra)
        extra -= contribution
        owner = f"holder{index:04d}" + "\\" * (contribution // 2) + "x" * (contribution % 2)
        rows.append(EconomicAmountV2(owner, "EUR", "accounts", 1))
    assert extra == 0
    rows.extend(empty.balances)
    state = AssetLaneStateV2(
        empty.module_release_id,
        empty.origin_registry,
        empty.transfer_policies,
        empty.managed_policies,
        tuple(sorted(rows, key=lambda row: row.key)),
        (AssetSupplyV2("EUR", count), AssetSupplyV2("USD", 9 if funded else 0)),
    )
    assert len(canonical_global_bytes_v2(state.to_canonical())) == target
    return state


def _check_issue_boundary(*, funded: bool, added_bytes: int, headroom: int) -> None:
    state = _boundary_state(headroom=headroom, funded=funded)
    command = fixture._managed_command(owner=_OWNER, amount_atoms=1)
    context = fixture._context(command)
    occurrence = context.occurrence
    assert occurrence is not None
    pre_bytes = canonical_global_bytes_v2(state.to_canonical())
    pre_root = state.state_root

    leaf = transition_managed_asset_lifecycle_v2(
        context.managed_context(),
        state.managed_leaf_state(),
        command,
    )
    assert isinstance(leaf, ManagedAssetLifecycleAcceptedV2)
    assert leaf.post_state.balance_atoms(_OWNER, "USD") == (10 if funded else 1)
    # Encode the intended recomposed tables without constructing an oversized
    # state. This observation confirms the independent size prediction.
    proposed = state.to_canonical()
    proposed["balances"] = (
        tuple(row for row in state.balances if row.asset == "EUR") + leaf.post_state.balances
    )
    proposed["supplies"] = (state.supplies[0], *leaf.post_state.supplies)
    assert len(canonical_global_bytes_v2(proposed)) == len(pre_bytes) + added_bytes

    result = transition_asset_lane_v2(context, state, command)
    if headroom == added_bytes:
        assert isinstance(result, AssetLaneAcceptedV2)
        post_bytes = canonical_global_bytes_v2(result.post_state.to_canonical())
        assert post_bytes == canonical_global_bytes_v2(proposed)
        assert len(post_bytes) == _LIMIT
        assert len(result.post_state.balances) == len(state.balances) + (0 if funded else 1)
        assert result.effects.occurrence_consumptions == (occurrence.occurrence_id,)
    else:
        assert headroom == added_bytes - 1
        resources._assert_resource_noop(
            result,
            state,
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
        )
    assert canonical_global_bytes_v2(state.to_canonical()) == pre_bytes
    assert state.state_root == pre_root


@pytest.mark.parametrize("excess", (0, 1))
def test_real_byte_ceiling_counts_escaped_new_owner_and_array_separator(excess: int) -> None:
    # USD and EUR have equal encoded lengths; 0 -> 1 supply adds no digit.
    added_bytes = len(_ROW_SKELETON) + _escaped_size(_OWNER) + 1
    _check_issue_boundary(funded=False, added_bytes=added_bytes, headroom=added_bytes - excess)


@pytest.mark.parametrize("excess", (0, 1))
def test_real_byte_ceiling_counts_balance_and_supply_digit_growth_without_new_rows(
    excess: int,
) -> None:
    # Existing balance and supply both cross 9 -> 10, adding exactly two bytes.
    _check_issue_boundary(funded=True, added_bytes=2, headroom=2 - excess)
