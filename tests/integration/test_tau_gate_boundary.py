from __future__ import annotations

import pytest

from src.core.settlement import FillAction, Settlement
from src.integration.tau_gate import TauGateConfig
from src.integration.validation import validate_operations
import src.integration.validation as validation
from src.state.intents import Intent, IntentKind


def _intent_and_rejected_settlement() -> tuple[Intent, Settlement]:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "11" * 32,
        sender_pubkey="pk",
        deadline=1,
        fields={"pool_id": "0x" + "22" * 32, "asset_in": "A", "asset_out": "B"},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.REJECT)],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    return intent, settlement


def test_tau_gate_crash_is_converted_to_rejection(monkeypatch: pytest.MonkeyPatch) -> None:
    intent, settlement = _intent_and_rejected_settlement()

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr("src.integration.tau_gate.validate_settlement_swaps", lambda *args, **kwargs: (_ for _ in ()).throw(RuntimeError("boom")))

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances={},
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )
    assert ok is False
    assert err is not None and err.startswith("Tau gate crashed: RuntimeError: boom")


def test_validation_certificate_errors_are_capped_and_internal_faults_hidden(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    intent, settlement = _intent_and_rejected_settlement()
    detail = "x" * 700

    assert validation._safe_validation_error(ValueError(detail)) == detail[:512]
    assert validation._safe_validation_error(RuntimeError("secret " + detail)) == "internal error: RuntimeError"

    class FaultingUniformBatchCertificate:
        @staticmethod
        def from_obj(_obj: object) -> object:
            raise ValueError(detail)

    monkeypatch.setattr(validation, "UniformBatchCertificateV1", FaultingUniformBatchCertificate)

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances={},
        pools={},
        lp_balances=None,
        block_timestamp=0,
        uniform_batch_certificate={"bad": "certificate"},
    )
    assert ok is False
    assert err == "invalid uniform batch certificate: " + detail[:512]

    def faulting_end_to_end_certificate(**_kwargs: object) -> tuple[bool, str | None, object | None]:
        raise RuntimeError("secret " + detail)

    monkeypatch.setattr(validation, "enforce_settlement_end_to_end_certificate", faulting_end_to_end_certificate)

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances={},
        pools={},
        lp_balances=None,
        block_timestamp=0,
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=object(),  # type: ignore[arg-type]
    )
    assert ok is False
    assert err == "invalid settlement end-to-end certificate inputs: internal error: RuntimeError"
