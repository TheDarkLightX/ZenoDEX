"""Real managed-leaf byte boundaries, separate from aggregate admission."""

from __future__ import annotations

import json

import pytest

from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    GlobalEconomicEffectPlanV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleStateV2,
)
from tests.core import test_asset_lane_coordinator_v2 as fixture

_BYTE_CAP = 1_048_576


def _leaf_at_byte_headroom(headroom: int) -> ManagedAssetLifecycleStateV2:
    policies = (fixture._managed_policy(), fixture._managed_policy(asset="ZZZ"))
    supplies = (AssetSupplyV2("USD", 99_998), AssetSupplyV2("ZZZ", 0))
    owners = [f"o{index:04d}" + "a" * 155 for index in range(4095)]

    def state() -> ManagedAssetLifecycleStateV2:
        return ManagedAssetLifecycleStateV2(
            fixture._root("module-release"),
            policies,
            tuple(EconomicAmountV2(owner, "USD", "accounts", 9) for owner in owners),
            supplies,
        )

    extra = _BYTE_CAP - headroom - len(canonical_global_bytes_v2(state()))
    assert extra >= 0
    # A quote replaces one ASCII byte and adds exactly one JSON escape byte.
    # The unique five-byte prefix preserves canonical owner ordering.
    for index, owner in enumerate(owners):
        added = min(extra, 155)
        owners[index] = owner[:5] + '"' * added + "a" * (155 - added)
        extra -= added
    assert extra == 0
    result = state()
    assert len(canonical_global_bytes_v2(result)) == _BYTE_CAP - headroom
    return result


@pytest.mark.parametrize("headroom", (0, 1))
def test_managed_leaf_accepts_exact_byte_cap_and_rejects_one_byte_excess(headroom: int) -> None:
    pre = _leaf_at_byte_headroom(headroom)
    before = canonical_global_bytes_v2(pre)
    before_root = pre.state_root
    owner = pre.balances[0].owner
    command = fixture._managed_command(owner=owner, amount_atoms=1)
    context = fixture._context(command).managed_context()
    # Balance 9 -> 10 adds one digit; supply 99998 -> 99999 adds none.
    proposed = json.loads(before)
    proposed["balances"][0]["amount_atoms"] = 10
    proposed["supplies"][0]["amount_atoms"] = 99_999
    proposed_bytes = json.dumps(proposed, sort_keys=True, separators=(",", ":")).encode("ascii")
    assert len(proposed_bytes) == _BYTE_CAP + 1 - headroom
    assert len(pre.balances) == len(proposed["balances"]) == 4095

    result = transition_managed_asset_lifecycle_v2(context, pre, command)

    if headroom:
        assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
        assert canonical_global_bytes_v2(result.post_state) == proposed_bytes
        assert context.occurrence is not None
        assert result.effects.occurrence_consumptions == (context.occurrence.occurrence_id,)
        assert result.module_journal.pre_lane_root == before_root
        assert result.module_journal.post_lane_root == result.post_state.state_root
    else:
        assert isinstance(result, ManagedAssetLifecycleRejectedV2)
        assert result.code is ManagedAssetLifecycleRejectCodeV2.STATE_RESOURCE_LIMIT
        assert result.pre_state_root == result.post_state_root == before_root
        assert canonical_global_bytes_v2(result.effects) == canonical_global_bytes_v2(
            GlobalEconomicEffectPlanV2.empty()
        )
    assert canonical_global_bytes_v2(pre) == before
    assert pre.state_root == before_root
