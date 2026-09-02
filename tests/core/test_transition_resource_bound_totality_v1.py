from __future__ import annotations

import pytest

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
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
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _asset_transfer_state(row_count: int) -> AssetTransferStateV1:
    return AssetTransferStateV1(
        module_release_id=_root(3),
        policies=(AssetTransferPolicyV1("USD", "acct-000000", 0, True),),
        balances=tuple(
            EconomicAmountV1(f"acct-{index:06d}", "USD", "accounts", 10)
            for index in range(row_count)
        ),
        supplies=(AssetSupplyV1("USD", 10 * row_count),),
    )


def _asset_transfer_context() -> AssetTransferContextV1:
    return AssetTransferContextV1(
        chain_id="resource-bound-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=1,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="acct-000001",
        grant_root=_root(5),
    )


def _asset_transfer_command() -> AssetTransferCommandV1:
    return AssetTransferCommandV1(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        asset="USD",
        sender="acct-000001",
        recipient="brand-new-owner",
        amount_atoms=1,
        max_fee_atoms=0,
    )


def _managed_asset_state(row_count: int) -> ManagedAssetLifecycleStateV1:
    return ManagedAssetLifecycleStateV1(
        module_release_id=_root(3),
        policies=(
            ManagedAssetLifecyclePolicyV1(
                asset="USD",
                asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
                issue_authority_subject="issuer",
                issue_policy_root=_root(5),
                burn_policy_root=_root(6),
                enabled=True,
            ),
        ),
        balances=tuple(
            EconomicAmountV1(f"acct-{index:06d}", "USD", "accounts", 1)
            for index in range(row_count)
        ),
        supplies=(AssetSupplyV1("USD", row_count),),
    )


def _managed_asset_context() -> ManagedAssetLifecycleContextV1:
    return ManagedAssetLifecycleContextV1(
        chain_id="resource-bound-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=1,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="issuer",
        grant_root=_root(5),
    )


def _managed_asset_issue() -> ManagedAssetLifecycleCommandV1:
    return ManagedAssetLifecycleCommandV1(
        command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        asset="USD",
        account_owner="brand-new-owner",
        amount_atoms=1,
    )


def test_asset_transfer_can_grow_to_exact_balance_row_ceiling() -> None:
    pre_state = _asset_transfer_state(MAX_ASSET_BALANCE_ROWS_V1 - 1)
    result = transition_asset_transfer_v1(
        _asset_transfer_context(), pre_state, _asset_transfer_command()
    )

    assert isinstance(result, AssetTransferAcceptedV1)
    assert len(result.post_state.balances) == MAX_ASSET_BALANCE_ROWS_V1


def test_asset_transfer_growth_past_ceiling_is_closed_typed_noop() -> None:
    pre_state = _asset_transfer_state(MAX_ASSET_BALANCE_ROWS_V1)
    result = transition_asset_transfer_v1(
        _asset_transfer_context(), pre_state, _asset_transfer_command()
    )

    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.POST_STATE_RESOURCE_BOUND_EXCEEDED
    assert result.pre_state_root == pre_state.state_root
    assert result.post_state_root == pre_state.state_root
    assert result.effects.is_empty


def test_managed_asset_issue_can_grow_to_exact_balance_row_ceiling() -> None:
    pre_state = _managed_asset_state(MAX_ASSET_BALANCE_ROWS_V1 - 1)
    result = transition_managed_asset_lifecycle_v1(
        _managed_asset_context(), pre_state, _managed_asset_issue()
    )

    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert len(result.post_state.balances) == MAX_ASSET_BALANCE_ROWS_V1


def test_managed_asset_issue_growth_past_ceiling_is_closed_typed_noop() -> None:
    pre_state = _managed_asset_state(MAX_ASSET_BALANCE_ROWS_V1)
    result = transition_managed_asset_lifecycle_v1(
        _managed_asset_context(), pre_state, _managed_asset_issue()
    )

    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert (
        result.code
        is ManagedAssetLifecycleRejectCodeV1.POST_STATE_RESOURCE_BOUND_EXCEEDED
    )
    assert result.pre_state_root == pre_state.state_root
    assert result.post_state_root == pre_state.state_root
    assert result.effects.is_empty


def test_reject_code_families_match_across_languages() -> None:
    """Opus P25 NEW-15: the two extended reject enums carry a family-drift pin.

    The Rust enum declarations are parsed and compared, member for member and in
    order, against the Python enums (the same discipline as the producer-family
    pin), so growing or reordering either family alone fails a gated test."""

    import re
    from pathlib import Path

    from src.core.asset_transfer_types_v1 import AssetTransferRejectCodeV1
    from src.core.managed_asset_lifecycle_types_v1 import ManagedAssetLifecycleRejectCodeV1

    root = Path(__file__).resolve().parents[2]

    def rust_variants(rust_path: str, enum_name: str) -> list[str]:
        source = (root / rust_path).read_text(encoding="utf-8")
        block = source.split(f"pub enum {enum_name} {{", 1)[1].split("}", 1)[0]
        variants: list[str] = []
        for line in block.splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            # Opus P26 NEW-16: every non-blank line must BE a plain variant; a
            # line the scanner cannot parse (CamelCase, tuple variant, missing
            # trailing comma, attribute) fails the pin instead of vanishing.
            match = re.fullmatch(r"([A-Z][A-Z0-9_]*),", stripped)
            assert match, f"{enum_name}: unparsed enum line {stripped!r}"
            variants.append(match.group(1))
        return variants

    for python_enum, rust_path, enum_name, expected_count in (
        (AssetTransferRejectCodeV1, "zk/global_settlement_abi_v1/src/asset_transfer_types.rs", "AssetTransferRejectCodeV1", 12),
        (ManagedAssetLifecycleRejectCodeV1, "zk/global_settlement_abi_v1/src/managed_asset_lifecycle_types.rs", "ManagedAssetLifecycleRejectCodeV1", 15),
    ):
        python_members = [member.name for member in python_enum]
        assert python_members == rust_variants(rust_path, enum_name), enum_name
        assert len(python_members) == expected_count, enum_name
        assert all(member.value == member.name for member in python_enum), enum_name
    assert "POST_STATE_RESOURCE_BOUND_EXCEEDED" in {m.name for m in AssetTransferRejectCodeV1}


def _forged_state(state_type, template, **overrides):
    forged = object.__new__(state_type)
    for field in state_type.__dataclass_fields__:
        object.__setattr__(forged, field, overrides.get(field, getattr(template, field)))
    return forged


def _transfer_totality_fixture():
    from src.core.asset_transfer_types_v1 import (
        ASSET_TRANSFER_COMMAND_KIND_V1,
        AssetTransferCommandV1,
        AssetTransferContextV1,
        AssetTransferPolicyV1,
        AssetTransferStateV1,
    )
    from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1

    root = "0x" + "11" * 32
    template = AssetTransferStateV1(
        module_release_id=root,
        policies=(AssetTransferPolicyV1("USD", "sender", 0, True),),
        balances=(
            EconomicAmountV1("rich", "USD", "accounts", 90),
            EconomicAmountV1("sender", "USD", "accounts", 10),
        ),
        supplies=(AssetSupplyV1("USD", 100),),
    )
    context = AssetTransferContextV1("zenodex", root, root, 1, root, root, "sender", root)
    command = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "sender", "rich", 10, 0
    )
    return template, context, command


def test_transfer_balance_overflow_is_a_defensive_arm_behind_input_re_validation() -> None:
    """Opus P26 NEW-18 / P29 NEW-24: BALANCE_OVERFLOW (transfer side) sits behind
    TWO layers, like the managed arm. In-domain, AssetTransferStateV1 enforces
    balances <= supply <= MAX_ATOMS_V1 at construction, so no valid pre-state
    can drive a balance past the ceiling; and a state forged past __post_init__
    (object.__new__) is refused by the transition's entry re-validation before
    any fold runs. The arm is checked-arithmetic totality whose witness is a
    direct call on the balance fold with an oversized delta, so deleting the
    arm still fails this test."""

    from src.core.asset_transfer_module_v1 import _post_balances, transition_asset_transfer_v1
    from src.core.asset_transfer_types_v1 import AssetTransferRejectCodeV1, AssetTransferStateV1
    from src.core.global_settlement_types_v1 import MAX_ATOMS_V1, EconomicAmountV1

    template, context, command = _transfer_totality_fixture()
    forged = _forged_state(
        AssetTransferStateV1,
        template,
        balances=(
            EconomicAmountV1("rich", "USD", "accounts", MAX_ATOMS_V1 - 5),
            EconomicAmountV1("sender", "USD", "accounts", 10),
        ),
    )
    with pytest.raises(ValueError, match="balances exceed supply"):
        transition_asset_transfer_v1(context, forged, command)
    fold = _post_balances(template, asset="USD", deltas={"rich": MAX_ATOMS_V1})
    assert fold is AssetTransferRejectCodeV1.BALANCE_OVERFLOW


def test_transfer_re_validates_same_type_forged_pre_state() -> None:
    """Opus P29 NEW-24: exact types close subclassing, not __post_init__-skipping.
    A same-type forged pre-state (object.__new__) carrying a custody-domain
    balance row was accepted and the untouched row silently relabelled to
    accounts by the balance fold; non-canonical rows were silently canonicalised
    into a pre_lane_root no constructible state can produce. The entry
    re-validation refuses both before any fold runs, and the valid template
    still transitions."""

    from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
    from src.core.asset_transfer_types_v1 import AssetTransferStateV1
    from src.core.global_settlement_types_v1 import EconomicAmountV1

    template, context, command = _transfer_totality_fixture()
    custody_forged = _forged_state(
        AssetTransferStateV1,
        template,
        balances=(
            EconomicAmountV1("aaa", "USD", "custody", 100),
            EconomicAmountV1("rich", "USD", "accounts", 90),
            EconomicAmountV1("sender", "USD", "accounts", 10),
        ),
    )
    with pytest.raises(ValueError, match="wrong custody domain"):
        transition_asset_transfer_v1(context, custody_forged, command)
    unordered_forged = _forged_state(
        AssetTransferStateV1,
        template,
        balances=(
            EconomicAmountV1("sender", "USD", "accounts", 10),
            EconomicAmountV1("rich", "USD", "accounts", 90),
        ),
    )
    with pytest.raises(ValueError, match="canonically ordered"):
        transition_asset_transfer_v1(context, unordered_forged, command)
    accepted = transition_asset_transfer_v1(context, template, command)
    assert type(accepted).__name__ == "AssetTransferAcceptedV1"


def test_managed_issue_balance_overflow_is_a_defensive_guard_with_a_forgery_witness() -> None:
    """Opus P26 NEW-18: BALANCE_OVERFLOW gains an asserting test (managed side).

    The managed arm sits behind TWO layers: in-domain, an issue moves supply
    no later than any balance, so SUPPLY_OVERFLOW always fires first
    (verified: supply at the ceiling yields SUPPLY_OVERFLOW); and a state
    forged past __post_init__ is refused by the transition's own snapshot
    re-validation before any fold runs (verified here). The arm is
    checked-arithmetic totality, unreachable through every path we could
    construct."""

    from src.core.global_settlement_types_v1 import (
        MAX_ATOMS_V1,
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
        ManagedAssetLifecycleRejectCodeV1,
        ManagedAssetLifecycleStateV1,
    )

    def root(value: int) -> str:
        return "0x" + f"{value:02x}" * 32

    policy = ManagedAssetLifecyclePolicyV1(
        asset="USD",
        asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject="issuer",
        issue_policy_root=root(5),
        burn_policy_root=root(6),
        enabled=True,
    )
    template = ManagedAssetLifecycleStateV1(
        module_release_id=root(3),
        policies=(policy,),
        balances=(EconomicAmountV1("rich", "USD", "accounts", 5),),
        supplies=(AssetSupplyV1("USD", 5),),
    )
    forged = _forged_state(
        ManagedAssetLifecycleStateV1,
        template,
        balances=(EconomicAmountV1("rich", "USD", "accounts", MAX_ATOMS_V1),),
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
        account_owner="rich",
        amount_atoms=1,
    )
    with pytest.raises(ValueError, match="balances exceed supply"):
        transition_managed_asset_lifecycle_v1(context, forged, command)
    assert ManagedAssetLifecycleRejectCodeV1.BALANCE_OVERFLOW.value == "BALANCE_OVERFLOW"


def test_transfer_refuses_state_subclasses() -> None:
    """Opus P27 NEW-21: a subclass that skips __post_init__ and overrides
    state_root is refused by the exact-type gate (the managed sibling already
    refused it; the transfer arm now matches)."""

    from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
    from src.core.asset_transfer_types_v1 import (
        ASSET_TRANSFER_COMMAND_KIND_V1,
        AssetTransferCommandV1,
        AssetTransferContextV1,
        AssetTransferPolicyV1,
        AssetTransferStateV1,
    )
    from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1

    class ForgedState(AssetTransferStateV1):
        def __post_init__(self) -> None:  # skip validation entirely
            pass

        @property
        def state_root(self) -> str:  # type: ignore[override]
            return "0x" + "66" * 32

    root = "0x" + "11" * 32
    forged = ForgedState(
        module_release_id=root,
        policies=(AssetTransferPolicyV1("USD", "treasury", 0, True),),
        balances=(EconomicAmountV1("sender", "USD", "accounts", 100),),
        supplies=(AssetSupplyV1("USD", 100),),
    )
    context = AssetTransferContextV1("zenodex", root, root, 1, root, root, "sender", root)
    command = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "sender", "recv", 10, 0
    )
    with pytest.raises(TypeError, match="exact typed value"):
        transition_asset_transfer_v1(context, forged, command)
