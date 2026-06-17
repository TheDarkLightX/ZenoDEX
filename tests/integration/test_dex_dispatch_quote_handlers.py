from __future__ import annotations

from types import SimpleNamespace

from src.integration.api_server_dex_dispatch import DexRequestContext
from src.integration.dex_dispatch_quote_handlers import _handle_quote


def _pool_dict(*, pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int) -> dict[str, object]:
    return {
        "pool_id": pid,
        "asset0": a0,
        "asset1": a1,
        "reserve0": r0,
        "reserve1": r1,
        "fee_bps": fee_bps,
        "lp_supply": 0,
        "status": "ACTIVE",
        "created_at": 0,
    }


def test_quote_exact_out_rejects_string_two_hop_gate() -> None:
    ctx = DexRequestContext(server=SimpleNamespace(), cors_origin=None, raw_body=None)
    status, body = _handle_quote(
        {
            "kind": "exact_out",
            "asset_in": "A",
            "asset_out": "B",
            "amount_out": 600,
            "apply_two_hop_gate": "yes",
            "pools": [
                _pool_dict(pid="p1", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
                _pool_dict(pid="p2", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
            ],
        },
        ctx,
    )

    assert status == 400
    assert body["ok"] is False
    assert body["error"] == "quote_error"
