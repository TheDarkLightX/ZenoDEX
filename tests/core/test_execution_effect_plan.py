from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.execution_effect_plan import (
    CommittedEffectReferenceV1,
    ExecutionEffectPlanV1,
    NativeBalanceEffectV1,
    NativeBalanceWriteV1,
    execution_effect_plan_hash_v1,
)


def _root(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 32


def _pubkey(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 48


def _plan() -> ExecutionEffectPlanV1:
    return ExecutionEffectPlanV1(
        chain_id="zeno-ledger-test",
        height=7,
        native_balance_effects=(
            NativeBalanceEffectV1(
                tx_index=1,
                tx_hash=_root(1),
                writes=(
                    NativeBalanceWriteV1(
                        pubkey=_pubkey(1), expected_amount=7, amount=3
                    ),
                    NativeBalanceWriteV1(
                        pubkey=_pubkey(2), expected_amount=9, amount=5
                    ),
                ),
            ),
        ),
        committed_effect_references=(
            CommittedEffectReferenceV1(
                effect_kind="cross_shard_ledger_effect",
                effect_id="writer-0",
                artifact_hash=_root(2),
            ),
        ),
    )


def test_effect_plan_roundtrips_and_hash_binds_every_effect() -> None:
    plan = _plan()
    assert ExecutionEffectPlanV1.from_obj(plan.to_obj()) == plan
    baseline = execution_effect_plan_hash_v1(plan)

    changed_write = replace(
        plan.native_balance_effects[0],
        writes=(
            NativeBalanceWriteV1(
                pubkey=_pubkey(1), expected_amount=7, amount=4
            ),
            NativeBalanceWriteV1(
                pubkey=_pubkey(2), expected_amount=9, amount=5
            ),
        ),
    )
    assert execution_effect_plan_hash_v1(
        replace(plan, native_balance_effects=(changed_write,))
    ) != baseline
    assert execution_effect_plan_hash_v1(
        replace(
            plan,
            committed_effect_references=(
                replace(plan.committed_effect_references[0], artifact_hash=_root(3)),
            ),
        )
    ) != baseline


def test_empty_effect_plan_has_a_nonzero_canonical_commitment() -> None:
    plan = ExecutionEffectPlanV1(
        chain_id="zeno-ledger-test",
        height=0,
        native_balance_effects=(),
        committed_effect_references=(),
    )
    assert execution_effect_plan_hash_v1(plan) != _root(0)


def test_effect_plan_rejects_mutable_aliases_and_noncanonical_order() -> None:
    with pytest.raises(TypeError, match="native_balance_effects must be a tuple"):
        replace(_plan(), native_balance_effects=[])  # type: ignore[arg-type]

    reversed_writes = tuple(reversed(_plan().native_balance_effects[0].writes))
    with pytest.raises(ValueError, match="sorted unique by pubkey"):
        replace(_plan().native_balance_effects[0], writes=reversed_writes)

    with pytest.raises(TypeError, match="must be an int"):
        NativeBalanceWriteV1(
            pubkey=_pubkey(1),
            expected_amount=3,
            amount=True,  # type: ignore[arg-type]
        )

    with pytest.raises(ValueError, match="canonical lowercase"):
        NativeBalanceWriteV1(
            pubkey=_pubkey(1)[2:],
            expected_amount=3,
            amount=4,
        )

    with pytest.raises(ValueError, match="must change"):
        NativeBalanceWriteV1(
            pubkey=_pubkey(1),
            expected_amount=3,
            amount=3,
        )


def test_effect_plan_decoder_rejects_unknown_fields_and_numeric_aliases() -> None:
    unknown = _plan().to_obj()
    unknown["caller_epoch"] = 99
    with pytest.raises(ValueError, match="fields mismatch"):
        ExecutionEffectPlanV1.from_obj(unknown)

    boolean_height = _plan().to_obj()
    boolean_height["height"] = True
    with pytest.raises(TypeError, match="height must be an int"):
        ExecutionEffectPlanV1.from_obj(boolean_height)

    leading_zero = _plan().to_obj()
    leading_zero["native_balance_effects"][0]["writes"][0]["amount"] = "03"  # type: ignore[index]
    with pytest.raises(ValueError, match="leading zeroes"):
        ExecutionEffectPlanV1.from_obj(leading_zero)
