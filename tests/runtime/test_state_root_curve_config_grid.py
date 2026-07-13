"""State-root curve-config boundary grid.

Python `PoolState` normalizes curve configuration before the state root is
computed. The Rust state-root shadow is intentionally stricter at its raw JSON
boundary: it accepts only already-normalized curve fields. This test pins both
contracts so the boundary is explicit and replayable.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.state.canonical import canonical_json_bytes  # noqa: E402
from src.state.pools import compute_pool_id, normalize_curve_config  # noqa: E402
from tools.runtime import state_root_lib as lib  # noqa: E402

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _params(obj: dict[str, int]) -> str:
    return canonical_json_bytes(obj).decode("utf-8")


def _pool(index: int, curve_tag: str, curve_params: str) -> dict:
    try:
        normalized_tag, normalized_params = normalize_curve_config(
            curve_tag=curve_tag,
            curve_params=curve_params,
        )
    except ValueError:
        # Raw Rust-rejection vectors still need a well-formed pool ID; curve
        # validation rejects them before the identity comparison.
        normalized_tag, normalized_params = "CPMM", ""
    return {
        "pool_id": compute_pool_id(
            ASSET0,
            ASSET1,
            index,
            curve_tag=normalized_tag,
            curve_params=normalized_params,
        ),
        "asset0": ASSET0,
        "asset1": ASSET1,
        "reserve0": 100 + index,
        "reserve1": 200 + index,
        "fee_bps": index,
        "lp_supply": 300 + index,
        "status": "active",
        "created_at": 10 + index,
        "curve_tag": curve_tag,
        "curve_params": curve_params,
    }


def _canonical_curve_cases() -> list[tuple[str, str]]:
    huge_a = 2**128 + 51
    huge_b = 2**130 + 79
    return [
        ("CPMM", ""),
        ("CUBIC_SUM_V1", _params({"p": 1, "q": 1})),
        ("CUBIC_SUM_V1", _params({"p": huge_a, "q": huge_b})),
        ("SUM_BOOST_V1", _params({"mu_den": 10_000, "mu_num": 0})),
        ("SUM_BOOST_V1", _params({"mu_den": huge_b, "mu_num": huge_a})),
        ("QUARTIC_BLEND_V1", _params({"c_den": 1, "c_num": 0})),
        ("QUARTIC_BLEND_V1", _params({"c_den": 3, "c_num": 2})),
        ("QUINTIC_BLEND_V1", _params({"c_den": 1, "c_num": 0})),
        ("QUINTIC_BLEND_V1", _params({"c_den": 5, "c_num": 3})),
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def test_canonical_curve_config_grid_matches_rust(rust_bin):
    states = [
        {"pools": [_pool(i, curve_tag, curve_params)]}
        for i, (curve_tag, curve_params) in enumerate(_canonical_curve_cases(), start=1)
    ]
    py = lib.py_eval_all(states)
    rust = lib.run_rust(rust_bin, states)
    assert all(item["ok"] for item in py), py
    assert all(item["ok"] for item in rust), rust
    assert not lib.diff_results(py, rust)
    assert len({item["state_root"] for item in py}) == len(states)


def test_python_normalizes_equivalent_raw_curve_configs():
    raw_to_canonical = [
        ({"curve_tag": "cpmm", "curve_params": {}}, ("CPMM", "")),
        (
            {"curve_tag": "quartic_blend_v1", "curve_params": '{"c_num":2,"c_den":4}'},
            ("QUARTIC_BLEND_V1", _params({"c_den": 2, "c_num": 1})),
        ),
        (
            {"curve_tag": "QUINTIC_BLEND_V1", "curve_params": {"c_num": 6, "c_den": 10}},
            ("QUINTIC_BLEND_V1", _params({"c_den": 5, "c_num": 3})),
        ),
    ]

    for raw, expected in raw_to_canonical:
        assert normalize_curve_config(
            curve_tag=raw["curve_tag"],
            curve_params=raw["curve_params"],
        ) == expected

        raw_state = {"pools": [_pool(1, raw["curve_tag"], raw["curve_params"])]}
        canonical_state = {"pools": [_pool(1, expected[0], expected[1])]}
        assert lib.state_root_from_json(raw_state) == lib.state_root_from_json(canonical_state)


def test_rust_rejects_raw_noncanonical_curve_boundary(rust_bin):
    raw_states = [
        {"pools": [_pool(1, "cpmm", "")]},
        {"pools": [_pool(1, "CPMM", "{}")]},
        {"pools": [_pool(1, "QUARTIC_BLEND_V1", '{"c_num":2,"c_den":4}')]},
        {"pools": [_pool(1, "QUINTIC_BLEND_V1", '{"c_den":10,"c_num":6}')]},
    ]
    rust = lib.run_rust(rust_bin, raw_states)
    assert all(not item["ok"] for item in rust), rust
    assert {item["code"] for item in rust} == {"invalid_curve_config"}
