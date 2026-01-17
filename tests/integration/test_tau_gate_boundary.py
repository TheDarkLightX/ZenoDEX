from __future__ import annotations

import pytest

from src.core.settlement import FillAction, Settlement
from src.integration.tau_gate import TauGateConfig
from src.integration.validation import validate_operations
from src.state.intents import Intent, IntentKind


def test_tau_gate_crash_is_converted_to_rejection(monkeypatch: pytest.MonkeyPatch) -> None:
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

    monkeypatch.setattr("src.integration.validation.validate_settlement", lambda *args, **kwargs: (True, None))
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
