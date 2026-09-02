from __future__ import annotations

import re
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
    MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
    MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
    MAX_EFFECT_PLAN_LANE_WRITES_V1,
    MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
    MAX_EFFECT_PLAN_ROWS_V1,
    MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
    MAX_GLOBAL_ORACLE_ROWS_V1,
    MAX_GLOBAL_OUTBOX_ROWS_V1,
    MAX_GLOBAL_REPLAY_ROWS_V1,
    MAX_GLOBAL_SUPPLY_ROWS_V1,
    MAX_GLOBAL_TERMINAL_ROWS_V1,
    ZERO_ROOT_V1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="resource-bound-test",
        deployment_root=_root(1),
        writer_epoch=1,
        height=1,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV1(lane_id, _root(100 + index), False, ZERO_ROOT_V1)
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
    )


def _replace_state_field(
    state: GlobalEconomicStateV1,
    field_name: str,
    value: tuple[object, ...],
) -> GlobalEconomicStateV1:
    return replace(state, **cast(Any, {field_name: value}))


_EFFECT_PLAN_LIMITS = (
    ("rows", MAX_EFFECT_PLAN_ROWS_V1, "effect plan rows"),
    (
        "asset_conservation",
        MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
        "effect plan asset conservation",
    ),
    (
        "fee_conservation",
        MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
        "effect plan fee conservation",
    ),
    ("lane_writes", MAX_EFFECT_PLAN_LANE_WRITES_V1, "effect plan lane writes"),
    (
        "occurrence_consumptions",
        MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
        "effect plan occurrence consumptions",
    ),
    (
        "external_outbox_enqueue",
        MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
        "effect plan external outbox",
    ),
)


@pytest.mark.parametrize(("field_name", "limit", "error_name"), _EFFECT_PLAN_LIMITS)
def test_effect_plan_bounds_accept_limit_and_reject_next_before_traversal(
    field_name: str,
    limit: int,
    error_name: str,
) -> None:
    values: dict[str, Any] = {name: () for name, _, _ in _EFFECT_PLAN_LIMITS}
    values[field_name] = (object(),) * limit

    with pytest.raises(TypeError):
        GlobalEconomicEffectPlanV1(**values)

    values[field_name] = (object(),) * (limit + 1)
    with pytest.raises(
        ValueError,
        match=rf"{re.escape(error_name)} exceeds its {limit}-item ceiling",
    ):
        GlobalEconomicEffectPlanV1(**values)


_GLOBAL_STATE_LIMITS = (
    ("balances", MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, "global state balances"),
    ("supplies", MAX_GLOBAL_SUPPLY_ROWS_V1, "global state supplies"),
    ("custody", MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, "global state custody"),
    (
        "liabilities",
        MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        "global state liabilities",
    ),
    ("reserves", MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, "global state reserves"),
    (
        "oracle_occurrences",
        MAX_GLOBAL_ORACLE_ROWS_V1,
        "global state oracle occurrences",
    ),
    ("replay_state", MAX_GLOBAL_REPLAY_ROWS_V1, "global state replay state"),
    (
        "terminal_obligations",
        MAX_GLOBAL_TERMINAL_ROWS_V1,
        "global state terminal obligations",
    ),
    ("outbox", MAX_GLOBAL_OUTBOX_ROWS_V1, "global state outbox"),
)


@pytest.mark.parametrize(("field_name", "limit", "error_name"), _GLOBAL_STATE_LIMITS)
def test_global_state_bounds_accept_limit_and_reject_next_before_traversal(
    field_name: str,
    limit: int,
    error_name: str,
) -> None:
    baseline = _state()

    with pytest.raises(TypeError):
        _replace_state_field(baseline, field_name, (object(),) * limit)

    with pytest.raises(
        ValueError,
        match=rf"{re.escape(error_name)} exceeds its {limit}-item ceiling",
    ):
        _replace_state_field(baseline, field_name, (object(),) * (limit + 1))


def test_python_and_rust_v1_collection_limits_are_frozen_and_equal() -> None:
    expected = {
        "MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1": 256,
        "MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1": 4_096,
        "MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1": 256,
        "MAX_EFFECT_PLAN_LANE_WRITES_V1": 12,
        "MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1": 4_096,
        "MAX_EFFECT_PLAN_ROWS_V1": 4_096,
        "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1": 4_096,
        "MAX_GLOBAL_ORACLE_ROWS_V1": 4_096,
        "MAX_GLOBAL_OUTBOX_ROWS_V1": 4_096,
        "MAX_GLOBAL_REPLAY_ROWS_V1": 4_096,
        "MAX_GLOBAL_SUPPLY_ROWS_V1": 256,
        "MAX_GLOBAL_TERMINAL_ROWS_V1": 4_096,
    }
    python_limits = {
        "MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1": (MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1),
        "MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1": (MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1),
        "MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1": (MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1),
        "MAX_EFFECT_PLAN_LANE_WRITES_V1": MAX_EFFECT_PLAN_LANE_WRITES_V1,
        "MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1": (MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1),
        "MAX_EFFECT_PLAN_ROWS_V1": MAX_EFFECT_PLAN_ROWS_V1,
        "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1": MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        "MAX_GLOBAL_ORACLE_ROWS_V1": MAX_GLOBAL_ORACLE_ROWS_V1,
        "MAX_GLOBAL_OUTBOX_ROWS_V1": MAX_GLOBAL_OUTBOX_ROWS_V1,
        "MAX_GLOBAL_REPLAY_ROWS_V1": MAX_GLOBAL_REPLAY_ROWS_V1,
        "MAX_GLOBAL_SUPPLY_ROWS_V1": MAX_GLOBAL_SUPPLY_ROWS_V1,
        "MAX_GLOBAL_TERMINAL_ROWS_V1": MAX_GLOBAL_TERMINAL_ROWS_V1,
    }
    assert python_limits == expected

    rust_source = (
        Path(__file__).resolve().parents[2] / "zk/global_settlement_abi_v1/src/canonical.rs"
    ).read_text(encoding="utf-8")
    rust_limits = {
        name: int(value.replace("_", ""))
        for name, value in re.findall(
            r"pub const (MAX_(?:EFFECT_PLAN|GLOBAL_)[A-Z0-9_]+): usize = ([0-9_]+);",
            rust_source,
        )
    }
    assert {name: rust_limits[name] for name in expected} == expected


def test_every_canonical_rust_bound_has_a_python_twin() -> None:
    """Opus P21 NEW-4: total parity over canonical.rs, not a hand-maintained list.

    Every `pub const MAX_...` declaration in canonical.rs, whatever its integer
    type or spacing, must resolve through this single
    mapping with an equal value; a newly added Rust bound with no Python twin
    fails the key-set equality below instead of silently matching no regex."""

    from src.core import global_settlement_types_v1 as types
    from src.core.lane_module_receipt_verification_v1 import (
        MAX_LANE_MODULE_RECEIPT_BYTES_V1,
    )

    rust_source = (
        Path(__file__).resolve().parents[2] / "zk/global_settlement_abi_v1/src/canonical.rs"
    ).read_text(encoding="utf-8")

    def evaluate(expression: str) -> int:
        expression = expression.strip()
        if expression == "u128::MAX":
            return (1 << 128) - 1
        if "<<" in expression:
            left, right = expression.split("<<")
            return int(left.strip().replace("_", "")) << int(right.strip().replace("_", ""))
        if "*" in expression:
            product = 1
            for factor in expression.split("*"):
                product *= int(factor.strip().replace("_", ""))
            return product
        return int(expression.replace("_", ""))

    rust_bounds = {
        name: evaluate(expression)
        for name, expression in re.findall(
            r"pub const (MAX_[A-Z0-9_]+)\s*:\s*[a-z0-9]+\s*=\s*([^;]+);",
            rust_source,
            re.S,
        )
    }
    python_twins = {
        name: getattr(types, name)
        for name in rust_bounds
        if hasattr(types, name)
    }
    python_twins["MAX_LANE_MODULE_RECEIPT_BYTES_V1"] = MAX_LANE_MODULE_RECEIPT_BYTES_V1
    assert set(python_twins) == set(rust_bounds), (
        sorted(set(rust_bounds) - set(python_twins)),
        sorted(set(python_twins) - set(rust_bounds)),
    )
    assert python_twins == rust_bounds
    assert len(rust_bounds) >= 24


def test_transfer_growing_past_the_balance_ceiling_raises_at_construction() -> None:
    """Opus P21 NEW-6: the shared non-total boundary is pinned, not hidden.

    A fully validated pre-state at exactly the balance-row ceiling drives the
    transition into ValueError from the post-state constructor (an ABI decode
    bound, not a typed reject); Rust returns Err(InvalidBounds) for the same
    input. Both transition docstrings state this."""

    from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
    from src.core.asset_transfer_types_v1 import (
        ASSET_TRANSFER_COMMAND_KIND_V1,
        AssetTransferCommandV1,
        AssetTransferContextV1,
        AssetTransferPolicyV1,
        AssetTransferStateV1,
    )
    from src.core.global_settlement_types_v1 import (
        MAX_ASSET_BALANCE_ROWS_V1,
        AssetSupplyV1,
        EconomicAmountV1,
    )

    root = "0x" + "11" * 32
    count = MAX_ASSET_BALANCE_ROWS_V1
    rows = tuple(
        EconomicAmountV1(f"acct-{index:06d}", "USD", "accounts", 10)
        for index in range(count)
    )
    pre_state = AssetTransferStateV1(
        module_release_id=root,
        policies=(AssetTransferPolicyV1("USD", "acct-000000", 0, True),),
        balances=rows,
        supplies=(AssetSupplyV1("USD", 10 * count),),
    )
    context = AssetTransferContextV1("zenodex", root, root, 1, root, root, "acct-000001", root)
    command = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "acct-000001", "brand-new-owner", 1, 0
    )
    with pytest.raises(
        ValueError,
        match=rf"asset transfer balances exceeds its {MAX_ASSET_BALANCE_ROWS_V1}-item ceiling",
    ):
        transition_asset_transfer_v1(context, pre_state, command)


def test_managed_issue_growing_past_the_balance_ceiling_raises_at_construction() -> None:
    """Opus P22 NEW-10: the managed-lifecycle docstring's ceiling claim is bound.

    A fully validated pre-state at exactly the balance-row ceiling drives an
    authorised issue to a new owner into ValueError from the post-state
    constructor (the same ABI decode bound as the transfer boundary; Rust
    returns Err(InvalidBounds) for the same input)."""

    from src.core.global_settlement_types_v1 import (
        MAX_ASSET_BALANCE_ROWS_V1,
        AssetSupplyV1,
        EconomicAmountV1,
    )
    from src.core.managed_asset_lifecycle_module_v1 import (
        transition_managed_asset_lifecycle_v1,
    )
    from src.core.managed_asset_lifecycle_types_v1 import (
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        ManagedAssetClassV1,
        ManagedAssetLifecycleCommandV1,
        ManagedAssetLifecycleContextV1,
        ManagedAssetLifecyclePolicyV1,
        ManagedAssetLifecycleStateV1,
    )

    def root(value: int) -> str:
        return "0x" + f"{value:02x}" * 32

    count = MAX_ASSET_BALANCE_ROWS_V1
    rows = tuple(
        EconomicAmountV1(f"acct-{index:06d}", "USD", "accounts", 1)
        for index in range(count)
    )
    policy = ManagedAssetLifecyclePolicyV1(
        asset="USD",
        asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject="issuer",
        issue_policy_root=root(5),
        burn_policy_root=root(6),
        enabled=True,
    )
    pre_state = ManagedAssetLifecycleStateV1(
        module_release_id=root(3),
        policies=(policy,),
        balances=rows,
        supplies=(AssetSupplyV1("USD", count),),
    )
    context = ManagedAssetLifecycleContextV1(
        chain_id="zenodex",
        deployment_root=root(1),
        profile_root=root(2),
        writer_epoch=7,
        module_release_id=root(3),
        command_occurrence_id=root(4),
        subject_id="issuer",
        grant_root=root(5),
    )
    command = ManagedAssetLifecycleCommandV1(
        command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        asset="USD",
        account_owner="brand-new-owner",
        amount_atoms=1,
    )
    with pytest.raises(
        ValueError,
        match=rf"managed asset lifecycle balances exceeds its {MAX_ASSET_BALANCE_ROWS_V1}-item ceiling",
    ):
        transition_managed_asset_lifecycle_v1(context, pre_state, command)
