"""Python/Rust differential for the apply_funding_auto settlement shadow.

Drives the real Python authority (`apply_perp_ops` → `apply_funding_auto` on a
bootstrapped gate-passing isolated-v2 market) and asserts the Rust shadow
(`zenodex-runtime funding-auto`) produces the identical settlement: per-account
collateral / cumulative deltas, the post fee_pool / fee_income / insurance, and
the accept/reject. Skipped (not failed) when neither a prebuilt binary nor cargo
is available.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
for _p in (str(_REPO), str(_REPO / "tools" / "runtime")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from tools.runtime import perp_funding_auto_lib as lib  # noqa: E402

AA, BB, CC = "aa" * 48, "bb" * 48, "cc" * 48


def static_cases() -> list[dict]:
    return [
        # balanced book → net 0, sink unchanged
        {"positions": [(AA, 1_000_000), (BB, -1_000_000)], "clearing_price_e8": 102_000_000},
        # net-long → positive net to sink (old design rejected this)
        {"positions": [(AA, 2_000), (BB, -1_000)], "clearing_price_e8": 102_000_000},
        # net-short, empty sink → reject (negative net underflows sink)
        {"positions": [(AA, 1_000), (BB, -2_000)], "clearing_price_e8": 102_000_000},
        # net-short, prefunded sink → succeeds
        {"positions": [(AA, 1_000), (BB, -2_000)], "clearing_price_e8": 102_000_000, "sink_k": 50},
        # three accounts, zero-net OI but per-account rounding net
        {"positions": [(AA, 2_000), (BB, -1_000), (CC, -1_000)], "clearing_price_e8": 100_090_000},
        # net-long three accounts
        {"positions": [(AA, 5_000), (BB, -2_000), (CC, -1_000)], "clearing_price_e8": 101_500_000},
    ]


def random_cases(seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    pks = [AA, BB, CC]
    cases: list[dict] = []
    for _ in range(n):
        k = rng.randint(2, 3)
        positions = []
        for pk in pks[:k]:
            pos = rng.choice([-1, 1]) * rng.randint(1, 5_000)
            positions.append((pk, pos))
        clearing = rng.choice([100_500_000, 101_000_000, 102_000_000, 98_500_000, 99_000_000])
        sink_k = rng.choice([0, 0, 50, 500, 5_000])
        cases.append({"positions": positions, "clearing_price_e8": clearing, "sink_k": sink_k})
    return cases


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.FundingAutoShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust funding-auto mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    # Sanity: the static corpus exercises both accept and reject.
    assert any(p["ok"] for p in py) and any(not p["ok"] for p in py)


@pytest.mark.parametrize("seed", [1, 7, 20260529])
def test_rust_matches_python_randomized(rust_bin, seed):
    _assert_agrees(random_cases(seed=seed, n=40), rust_bin)


def test_rust_matches_golden_trace(rust_bin):
    # Pin the Rust settlement against drift (no Python needed): replay the
    # committed golden cases and assert the output equals the pinned expected.
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "funding_auto_smoke.json").read_text()
    )
    request = {"cases": golden["cases"]}
    import subprocess

    proc = subprocess.run(
        [str(rust_bin), "funding-auto", "-"],
        input=json.dumps(request),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"], "Rust output drifted from pinned golden trace"
    # The golden corpus exercises both accept and reject.
    assert any(r["ok"] for r in got) and any(not r["ok"] for r in got)
