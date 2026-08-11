from __future__ import annotations

import json

import pytest

from src.core.global_settlement_abi_v1 import (
    AssetSupplyV1,
    EconomicCommandOccurrenceV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
)
from tools.render_global_settlement_abi_v1_golden import (
    FIXTURE_PATH_V1,
    build_vectors_v1,
    render_vectors_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def test_consensus_integer_widths_reject_cross_language_overflow() -> None:
    with pytest.raises(ValueError, match="unsigned 128-bit"):
        AssetSupplyV1("USD", 1 << 128)
    with pytest.raises(ValueError, match="signed 128-bit"):
        EconomicEffectRowV1(
            EconomicEffectKindV1.ACCOUNT_MOVEMENT,
            "alice",
            "USD",
            "accounts",
            1 << 127,
        )
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        EconomicCommandOccurrenceV1(
            chain_id="zeno-test-chain",
            deployment_root=_root(1),
            height=1 << 64,
            tx_index=0,
            op_index=0,
            command_kind="transfer",
            route_release_id=_root(2),
            subject_id="alice",
            grant_root=_root(3),
            nonce=0,
            profile_root=_root(4),
            pre_state_root=_root(5),
            consumed_object_ids=(),
        )


def test_u128_amount_above_u64_remains_canonical() -> None:
    supply = AssetSupplyV1("USD", (1 << 64) + 1)
    assert supply.amount_atoms == 18_446_744_073_709_551_617


def test_committed_golden_fixture_matches_typed_python_renderer() -> None:
    fixture_text = FIXTURE_PATH_V1.read_text(encoding="utf-8")
    assert fixture_text == render_vectors_v1()
    assert json.loads(fixture_text) == build_vectors_v1()
