from __future__ import annotations

from enum import Enum

import pytest

import src.core.global_settlement_types_v1 as settlement_types
from src.core.global_settlement_canonical_manifest_v1 import (
    GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPE_SET_V1,
    GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1,
    GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPE_SET_V1,
    GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1,
)
from src.core.global_settlement_types_v1 import (
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)


def test_canonical_admission_manifest_is_frozen_sorted_and_disjoint() -> None:
    # 104 + 35 = 139 exact loaded types after the wave-B producer and certificate
    # registrations (C8); this count was left at 92 + 30 and red from 2026-09-01
    # until C9a'. Exact membership and the source-closure digest are pinned by
    # tools/check_global_settlement_canonical_manifest_v1.py.
    assert len(GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1) == 104
    assert len(GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1) == 35
    assert GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1 == tuple(
        sorted(GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1)
    )
    assert GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1 == tuple(
        sorted(GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1)
    )
    assert GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPE_SET_V1 == frozenset(
        GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1
    )
    assert GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPE_SET_V1 == frozenset(
        GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1
    )
    assert GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPE_SET_V1.isdisjoint(
        GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPE_SET_V1
    )


def test_arbitrary_behavior_bearing_object_rejects_without_hook_execution() -> None:
    calls: list[str] = []

    class RecordingMeta(type):
        def __getattribute__(cls, name: str) -> object:
            calls.append(f"class:{name}")
            return super().__getattribute__(name)

        def __hash__(cls) -> int:
            calls.append("class:__hash__")
            return super().__hash__()

    class BehaviorBearing(metaclass=RecordingMeta):
        __qualname__ = "BehaviorBearing"

        def __getattribute__(self, name: str) -> object:
            calls.append(f"instance:{name}")
            return super().__getattribute__(name)

        def to_canonical(self) -> dict[str, object]:
            calls.append("serializer")
            return {"accepted": True}

    with pytest.raises(TypeError, match="unsupported canonical value type"):
        canonical_global_bytes_v1(BehaviorBearing())

    assert calls == []


def test_registered_type_subclass_rejects_before_overridden_serializer() -> None:
    calls: list[str] = []

    class SubstitutedEconomicAmount(EconomicAmountV1):
        __qualname__ = "SubstitutedEconomicAmount"

        def to_canonical(self) -> dict[str, object]:
            calls.append("serializer")
            return {"accepted": True}

    value = SubstitutedEconomicAmount("alice", "USD", "ledger", 7)
    with pytest.raises(TypeError, match="unsupported canonical value type"):
        canonical_global_bytes_v1(value)

    assert calls == []


def test_forged_registered_fqn_rejects_before_serializer() -> None:
    calls: list[str] = []

    class ForgedEconomicAmount:
        __module__ = EconomicAmountV1.__module__
        __qualname__ = EconomicAmountV1.__qualname__

        def to_canonical(self) -> dict[str, object]:
            calls.append("serializer")
            return {"accepted": True}

    with pytest.raises(TypeError, match="canonical type identity is not current"):
        canonical_global_bytes_v1(ForgedEconomicAmount())

    assert calls == []


def test_registered_module_binding_replacement_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    value = EconomicAmountV1("alice", "USD", "ledger", 7)
    expected = canonical_global_bytes_v1(value)

    monkeypatch.setattr(settlement_types, "EconomicAmountV1", object())
    with pytest.raises(TypeError, match="canonical type identity is not current"):
        canonical_global_bytes_v1(value)

    monkeypatch.undo()
    assert canonical_global_bytes_v1(value) == expected


def test_generic_and_forged_string_enums_reject_without_value_hooks() -> None:
    calls: list[str] = []

    class RogueEnum(str, Enum):
        __qualname__ = "RogueEnum"
        ROGUE = "ROGUE"

        def __getattribute__(self, name: str) -> object:
            if name in {"value", "_value_"}:
                calls.append(name)
            return super().__getattribute__(name)

    rogue_value = RogueEnum.ROGUE
    calls.clear()
    with pytest.raises(TypeError, match="canonical scalar subclasses are unsupported"):
        canonical_global_bytes_v1(rogue_value)
    assert calls == []

    class ForgedLaneId(str, Enum):
        __module__ = LaneIdV1.__module__
        __qualname__ = LaneIdV1.__qualname__
        ROGUE = "ROGUE"

        def __getattribute__(self, name: str) -> object:
            if name in {"value", "_value_"}:
                calls.append(name)
            return super().__getattribute__(name)

    forged_value = ForgedLaneId.ROGUE
    calls.clear()
    with pytest.raises(TypeError, match="canonical type identity is not current"):
        canonical_global_bytes_v1(forged_value)

    assert calls == []


@pytest.mark.parametrize(
    ("value", "expected_bytes", "expected_root"),
    (
        (
            LaneIdV1.ASSET_TRANSFER,
            b'"ASSET_TRANSFER"',
            "0x33c4b5a25bb4c185ea5b7dfaa56a09bdfa6a38361815447697a8dcaf21414927",
        ),
        (
            EconomicAmountV1("alice", "USD", "ledger", 7),
            b'{"amount_atoms":7,"asset":"USD","custody_domain":"ledger","owner":"alice"}',
            "0x90437f97dba1f02e97d967e5c61cad768213a61a6b7b208ec5fc6744569dbab3",
        ),
        (
            GlobalEconomicEffectPlanV1.empty(),
            b'{"asset_conservation":[],"external_outbox_enqueue":[],"fee_conservation":[],'
            b'"lane_writes":[],"occurrence_consumptions":[],"rows":[],'
            b'"schema":"zenodex/global-settlement-abi/v1"}',
            "0xb3e0895c1bf85d7d794417c79732a182520997e813a9b483e1e6dfabf0437510",
        ),
    ),
)
def test_canonical_bytes_and_roots_match_exact_base_goldens(
    value: object,
    expected_bytes: bytes,
    expected_root: str,
) -> None:
    assert canonical_global_bytes_v1(value) == expected_bytes
    assert hash_global_v1("canonical-admission-golden-v1", value) == expected_root


def test_effect_plan_owned_root_matches_exact_base_golden() -> None:
    assert (
        GlobalEconomicEffectPlanV1.empty().effect_plan_root
        == "0x92771a86dce5eab77c388dcd8b6576458b6201a84f93761dd9bfdfb7e64fdbb7"
    )
