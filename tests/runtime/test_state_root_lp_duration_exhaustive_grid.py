"""Exhaustive LP duration-risk field-separation checks for state-root v5."""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from tools.runtime import state_root_lib as lib


def _pk(byte: int) -> str:
    return "0x" + bytes([byte] * 48).hex()


def _id32(byte: int) -> str:
    return "0x" + bytes([byte] * 32).hex()


PK = _pk(0x11)
POOL = _id32(0x44)


def _base_state() -> dict:
    return {"lp_balances": [{"pubkey": PK, "pool_id": POOL, "amount": 1}]}


def _metadata(
    last_mint_timestamp: int | None,
    last_remove_timestamp: int | None,
    churn_tier: int,
    last_churn_update_timestamp: int | None,
) -> dict:
    return {
        "pubkey": PK,
        "pool_id": POOL,
        "last_mint_timestamp": last_mint_timestamp,
        "last_remove_timestamp": last_remove_timestamp,
        "churn_tier": churn_tier,
        "last_churn_update_timestamp": last_churn_update_timestamp,
    }


def _is_present(metadata: dict) -> bool:
    return (
        metadata["last_mint_timestamp"] is not None
        or metadata["last_remove_timestamp"] is not None
        or metadata["churn_tier"] > 0
        or metadata["last_churn_update_timestamp"] is not None
    )


def _state_with(metadata: dict) -> dict:
    return {**_base_state(), "lp_duration_risk": [metadata]}


def _grid() -> list[tuple[tuple[int | None, int | None, int, int | None], dict]]:
    timestamp_values = [None, 0, 1]
    out = []
    for mint, remove, churn, churn_update in itertools.product(
        timestamp_values, timestamp_values, [0, 1, 2], timestamp_values
    ):
        key = (mint, remove, churn, churn_update)
        out.append((key, _metadata(mint, remove, churn, churn_update)))
    return out


def test_lp_duration_sparse_empty_metadata_is_noop() -> None:
    empty = _metadata(None, None, 0, None)

    assert not _is_present(empty)
    assert lib.state_root_from_json(_state_with(empty)) == lib.state_root_from_json(
        _base_state()
    )
    assert lib.to_rust_json(_state_with(empty))["lp_duration_risk"] == []


def test_lp_duration_present_field_grid_is_injective() -> None:
    roots: dict[str, tuple[int | None, int | None, int, int | None]] = {}

    for key, metadata in _grid():
        if not _is_present(metadata):
            continue
        root = lib.state_root_from_json(_state_with(metadata))
        previous = roots.get(root)
        assert previous is None, f"LP duration metadata collision: {previous} vs {key}"
        roots[root] = key

    assert len(roots) == 80


def test_lp_duration_semantic_field_tuple_is_z3_injective() -> None:
    z3 = pytest.importorskip("z3")

    def opt_slot(has_value, value):
        return z3.If(has_value, value, z3.IntVal(-1))

    a_mint_set, b_mint_set = z3.Bools("a_mint_set b_mint_set")
    a_remove_set, b_remove_set = z3.Bools("a_remove_set b_remove_set")
    a_churn_update_set, b_churn_update_set = z3.Bools(
        "a_churn_update_set b_churn_update_set"
    )
    a_mint, b_mint = z3.Ints("a_mint b_mint")
    a_remove, b_remove = z3.Ints("a_remove b_remove")
    a_churn, b_churn = z3.Ints("a_churn b_churn")
    a_churn_update, b_churn_update = z3.Ints("a_churn_update b_churn_update")

    nonnegative_values = [
        a_mint >= 0,
        b_mint >= 0,
        a_remove >= 0,
        b_remove >= 0,
        a_churn >= 0,
        b_churn >= 0,
        a_churn_update >= 0,
        b_churn_update >= 0,
    ]
    a_present = a_mint_set | a_remove_set | (a_churn > 0) | a_churn_update_set
    b_present = b_mint_set | b_remove_set | (b_churn > 0) | b_churn_update_set
    encoded_equal = [
        opt_slot(a_mint_set, a_mint) == opt_slot(b_mint_set, b_mint),
        opt_slot(a_remove_set, a_remove) == opt_slot(b_remove_set, b_remove),
        a_churn == b_churn,
        opt_slot(a_churn_update_set, a_churn_update)
        == opt_slot(b_churn_update_set, b_churn_update),
    ]
    semantic_differs = z3.Or(
        a_mint_set != b_mint_set,
        z3.And(a_mint_set, b_mint_set, a_mint != b_mint),
        a_remove_set != b_remove_set,
        z3.And(a_remove_set, b_remove_set, a_remove != b_remove),
        a_churn != b_churn,
        a_churn_update_set != b_churn_update_set,
        z3.And(
            a_churn_update_set,
            b_churn_update_set,
            a_churn_update != b_churn_update,
        ),
    )

    solver = z3.Solver()
    solver.add(*nonnegative_values)
    solver.add(a_present, b_present)
    solver.add(*encoded_equal)
    solver.add(semantic_differs)

    assert solver.check() == z3.unsat


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def test_lp_duration_present_field_grid_matches_rust(rust_bin: Path) -> None:
    states = [
        _state_with(metadata)
        for _, metadata in _grid()
        if _is_present(metadata)
    ]

    py = lib.py_eval_all(states)
    assert all(result["ok"] for result in py), [r for r in py if not r["ok"]]
    rust_inputs = [lib.to_rust_json(state) for state in states]
    rs = lib.run_rust(rust_bin, rust_inputs)

    problems = lib.diff_results(py, rs)
    assert not problems, "LP duration grid mismatch:\n" + "\n".join(problems[:20])
