from __future__ import annotations

from types import SimpleNamespace

from src.fire.kernel.persisted_bundle_settlement_v1 import _crosscheck_runtime_and_applied_settlement


def test_crosscheck_rejects_string_runtime_holder_delta() -> None:
    receipt = SimpleNamespace(to_dict=lambda: {"receipt": "same"})
    packet = SimpleNamespace(
        receipt=receipt,
        holder_delta=0,
        writer_delta=0,
        payoff_out=0,
    )
    verified_settlement = SimpleNamespace(
        verifier_receipt=receipt,
        holder_delta="0",
        writer_delta=0,
    )

    err = _crosscheck_runtime_and_applied_settlement(
        verified_settlement=verified_settlement,
        apply_result=SimpleNamespace(packet=packet),
    )

    assert err == "crosscheck_runtime_delta_invalid:verified_settlement.holder_delta must be an int"
