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


cpmm = _import_kernel("generated.cpmm_python.cpmm_swap_ref", "generated/cpmm_python/cpmm_swap_ref.py")


def _mk_state(reserve_x: int, reserve_y: int) -> Any:
    return cpmm.State(
        fee_bps=0,
        reserve_x=reserve_x,
        reserve_x_before=reserve_x,
        reserve_y=reserve_y,
        reserve_y_before=reserve_y,
    )


def test_swap_exact_in_matches_esso_kernel_no_fee_small_domain() -> None:
    # Reference kernel is bounded (<=50) and uses deterministic integer rounding.
    # Compare on a small representative grid, including fee edge cases.
    reserves = [1, 2, 5, 10, 25, 50]
    amounts = [1, 2, 5, 10, 25, 50]
    fees = [0, 1, 30, 1000, 5000, 9000, 9999, 10000]

    for fee_bps in fees:
        for reserve_x in reserves:
            for reserve_y in reserves:
                state = cpmm.State(
                    fee_bps=fee_bps,
                    reserve_x=reserve_x,
                    reserve_x_before=reserve_x,
                    reserve_y=reserve_y,
                    reserve_y_before=reserve_y,
                )

                # X -> Y
                for amount_in_x in amounts:
                    res = cpmm.step(
                        state,
                        cpmm.Command(
                            tag="swap_x_for_y",
                            args={"amount_in_x": amount_in_x, "min_amount_out": 0},
                        ),
                    )
                    if not res.ok:
                        # The reference kernel is finite-domain and may reject cases that are valid in the
                        # unbounded Python core (e.g. reserve_x + amount_in_x > 50).
                        if reserve_x + amount_in_x > 50:
                            continue
                        with pytest.raises(ValueError):
                            swap_exact_in(
                                reserve_in=reserve_x,
                                reserve_out=reserve_y,
                                amount_in=amount_in_x,
                                fee_bps=fee_bps,
                            )
                        continue

                    amount_out, (new_reserve_x, new_reserve_y) = swap_exact_in(
                        reserve_in=reserve_x,
                        reserve_out=reserve_y,
                        amount_in=amount_in_x,
                        fee_bps=fee_bps,
                    )
                    assert res.state is not None
                    assert res.effects is not None
                    assert int(res.effects["amount_out"]) == amount_out
                    assert res.state.reserve_x == new_reserve_x
                    assert res.state.reserve_y == new_reserve_y

                # Y -> X
                for amount_in_y in amounts:
                    res = cpmm.step(
                        state,
                        cpmm.Command(
                            tag="swap_y_for_x",
                            args={"amount_in_y": amount_in_y, "min_amount_out": 0},
                        ),
                    )
                    if not res.ok:
                        if reserve_y + amount_in_y > 50:
                            continue
                        with pytest.raises(ValueError):
                            swap_exact_in(
                                reserve_in=reserve_y,
                                reserve_out=reserve_x,
                                amount_in=amount_in_y,
                                fee_bps=fee_bps,
                            )
                        continue

                    amount_out, (new_reserve_y, new_reserve_x) = swap_exact_in(
                        reserve_in=reserve_y,
                        reserve_out=reserve_x,
                        amount_in=amount_in_y,
                        fee_bps=fee_bps,
                    )
                    assert res.state is not None
                    assert res.effects is not None
                    assert int(res.effects["amount_out"]) == amount_out
                    assert res.state.reserve_x == new_reserve_x
                    assert res.state.reserve_y == new_reserve_y
