# [TESTER] v1

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.cpmm import swap_exact_in


def _import_kernel(module_name: str, rel_path: str) -> Any:
    try:
        return __import__(module_name, fromlist=["*"])
    except ModuleNotFoundError:
        root = Path(__file__).resolve().parents[2]
        abs_path = root / rel_path
        if not abs_path.exists():
            pytest.skip(f"Reference kernel not found at {abs_path}")
        spec = importlib.util.spec_from_file_location(module_name, abs_path)
        assert spec and spec.loader, f"Could not load spec for {module_name} from {abs_path}"
        module = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = module
        spec.loader.exec_module(module)
        return module


cpmm_v8 = _import_kernel("generated.dex_v8_python.cpmm_swap_v8_ref", "generated/dex_v8_python/cpmm_swap_v8_ref.py")


def test_cpmm_swap_v8_matches_python_core_for_protocol_share_0() -> None:
    reserves = [1, 2, 10, 25, 100, 1000, 1_000_000]
    fee_bps_cases = [0, 1, 30, 100, 1000]

    for reserve_in in reserves:
        for reserve_out in reserves:
            for fee_bps in fee_bps_cases:
                state = cpmm_v8.State(
                    fee_bps=fee_bps,
                    protocol_fee_share_bps=0,
                    reserve_in_before=reserve_in,
                    reserve_in=reserve_in,
                    reserve_out_before=reserve_out,
                    reserve_out=reserve_out,
                )

                for amount_in in [1, max(1, reserve_in // 2), reserve_in]:
                    res = cpmm_v8.step(
                        state,
                        cpmm_v8.Command(tag="swap", args={"amount_in": amount_in, "min_amount_out": 1}),
                    )
                    if not res.ok:
                        continue
                    assert res.state is not None
                    assert res.effects is not None

                    amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
                        reserve_in=reserve_in,
                        reserve_out=reserve_out,
                        amount_in=amount_in,
                        fee_bps=fee_bps,
                    )
                    assert int(res.effects["protocol_fee"]) == 0
                    assert int(res.effects["fee_total"]) == int(res.effects["lp_fee"])
                    assert int(res.effects["net_in"]) == amount_in - int(res.effects["fee_total"])

                    assert int(res.effects["amount_out"]) == amount_out
                    assert res.state.reserve_in == new_reserve_in
                    assert res.state.reserve_out == new_reserve_out


def test_cpmm_swap_v8_protocol_fee_reduces_reserve_in_growth() -> None:
    # This doesn't have a Python-core equivalent yet; just assert internal consistency.
    reserve_in, reserve_out = 1_000_000, 1_000_000
    fee_bps = 100  # 1%
    protocol_share = 5000  # 50% of fee removed
    amount_in = 10_000

    state = cpmm_v8.State(
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_share,
        reserve_in_before=reserve_in,
        reserve_in=reserve_in,
        reserve_out_before=reserve_out,
        reserve_out=reserve_out,
    )
    res = cpmm_v8.step(state, cpmm_v8.Command(tag="swap", args={"amount_in": amount_in, "min_amount_out": 1}))
    assert res.ok, res.error
    assert res.state is not None
    assert res.effects is not None

    fee_total = int(res.effects["fee_total"])
    protocol_fee = int(res.effects["protocol_fee"])
    lp_fee = int(res.effects["lp_fee"])
    net_in = int(res.effects["net_in"])

    assert fee_total >= 0
    assert 0 <= protocol_fee <= fee_total
    assert lp_fee == fee_total - protocol_fee
    assert net_in == amount_in - fee_total
    assert bool(res.effects["fee_split_ok"]) is True
    assert bool(res.effects["net_ok"]) is True
    assert res.state.reserve_in == reserve_in + amount_in - protocol_fee
