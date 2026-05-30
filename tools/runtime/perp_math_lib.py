"""Perp stateless-math cross-language differential harness (Phase E1).

Authority: the pure functions in `src/core/perp_v2/math.py`. The Rust shadow is
`zenodex-runtime-core::perp_math`, exposed via the `perp-math` CLI subcommand.

Each case is `{"op": <fn>, <args...>}`. Predicate ops return a `flag` (bool);
the rest return a decimal-string `value` (signed, fits i128). Only `ok`, `flag`,
and `value` are compared. All randomized inputs are kept inside the Rust bridge
domain (magnitudes ≤ 1e18, bps ≤ 1e7); the Python authority is unbounded, so
out-of-domain inputs are exercised in a Rust-only rejection test, not the
differential.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from pathlib import Path

from src.core.perp_v2 import math as m

KERNEL = "perp_math"

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"

_BOOL_OPS = {"is_oracle_fresh", "oracle_move_violated", "is_liquidatable"}

# op -> (callable, ordered arg names)
_OPS = {
    "is_oracle_fresh": (
        m._is_oracle_fresh_python,
        ["now_epoch", "oracle_last_update_epoch", "max_oracle_staleness_epochs", "oracle_seen"],
    ),
    "oracle_move_violated": (
        m._oracle_move_violated_python,
        ["clearing_price_e8", "index_price_e8", "max_oracle_move_bps", "oracle_seen"],
    ),
    "settle_price": (
        m._settle_price_python,
        ["clearing_price_e8", "index_price_e8", "max_oracle_move_bps", "oracle_seen"],
    ),
    "notional_quote": (m._notional_quote_python, ["position_base", "price_e8"]),
    "maint_margin_req": (m._maint_margin_req_python, ["position_base", "price_e8", "maint_bps", "depeg_bps"]),
    "init_margin_req": (m._init_margin_req_python, ["position_base", "price_e8", "init_bps"]),
    "pnl_quote": (m._pnl_quote_python, ["position_base", "settle_price_e8", "index_price_e8"]),
    "is_liquidatable": (
        m._is_liquidatable_python,
        ["position_base", "collateral_after_pnl", "settle_price_e8",
         "maintenance_margin_bps", "depeg_buffer_bps"],
    ),
    "funding_payment": (m._funding_payment_python, ["position_base", "index_price_e8", "rate_bps"]),
}


def py_eval(index: int, case: dict) -> dict:
    op = case.get("op")
    spec = _OPS.get(op)
    if spec is None:
        return {"index": index, "ok": False}
    fn, arg_names = spec
    try:
        args = [case[a] for a in arg_names]
    except KeyError:
        return {"index": index, "ok": False}
    result = fn(*args)
    if op in _BOOL_OPS:
        return {"index": index, "ok": True, "flag": bool(result)}
    return {"index": index, "ok": True, "value": str(int(result))}


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


# --- corpora ------------------------------------------------------------------

P = m.PRICE_SCALE


def static_cases() -> list[dict]:
    return [
        {"op": "is_oracle_fresh", "now_epoch": 5, "oracle_last_update_epoch": 0,
         "max_oracle_staleness_epochs": 10, "oracle_seen": True},
        {"op": "is_oracle_fresh", "now_epoch": 3, "oracle_last_update_epoch": 5,
         "max_oracle_staleness_epochs": 10, "oracle_seen": True},  # future -> stale
        {"op": "oracle_move_violated", "clearing_price_e8": 110, "index_price_e8": 100,
         "max_oracle_move_bps": 500, "oracle_seen": True},
        {"op": "settle_price", "clearing_price_e8": 1_000_000, "index_price_e8": 100,
         "max_oracle_move_bps": 1, "oracle_seen": True},  # ceil-clamp, band != 0
        {"op": "settle_price", "clearing_price_e8": 100, "index_price_e8": 100,
         "max_oracle_move_bps": 50, "oracle_seen": True},  # no violation
        {"op": "notional_quote", "position_base": -5000, "price_e8": 100 * P},
        {"op": "maint_margin_req", "position_base": -5000, "price_e8": 100 * P,
         "maint_bps": 500, "depeg_bps": 100},
        {"op": "init_margin_req", "position_base": 5000, "price_e8": 100 * P, "init_bps": 1000},
        {"op": "pnl_quote", "position_base": 1000, "settle_price_e8": 110 * P, "index_price_e8": 100 * P},
        {"op": "pnl_quote", "position_base": -1000, "settle_price_e8": 110 * P, "index_price_e8": 100 * P},
        {"op": "is_liquidatable", "position_base": 1_000_000, "collateral_after_pnl": 0,
         "settle_price_e8": 100 * P, "maintenance_margin_bps": 500, "depeg_buffer_bps": 0},
        {"op": "is_liquidatable", "position_base": 0, "collateral_after_pnl": -100,
         "settle_price_e8": 100 * P, "maintenance_margin_bps": 500, "depeg_buffer_bps": 0},
        {"op": "funding_payment", "position_base": 1000, "index_price_e8": 100 * P, "rate_bps": 50},
        {"op": "funding_payment", "position_base": 1000, "index_price_e8": 100 * P, "rate_bps": -50},
        {"op": "funding_payment", "position_base": -1000, "index_price_e8": 100 * P, "rate_bps": 50},
    ]


def _spos(rng):
    return rng.randint(-1_000_000_000, 1_000_000_000)


def _price(rng):
    return rng.randint(1, 1_000_000_000_000)  # e8 prices


def _bps(rng):
    return rng.randint(0, 5000)


def _signed_bps(rng):
    return rng.randint(-5000, 5000)


def random_cases(seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    out: list[dict] = []
    for _ in range(n):
        op = rng.choice(list(_OPS))
        if op == "is_oracle_fresh":
            c = {"op": op, "now_epoch": rng.randint(0, 1_000_000),
                 "oracle_last_update_epoch": rng.randint(0, 1_000_000),
                 "max_oracle_staleness_epochs": rng.randint(0, 100),
                 "oracle_seen": rng.random() < 0.8}
        elif op in ("oracle_move_violated", "settle_price"):
            c = {"op": op, "clearing_price_e8": _price(rng), "index_price_e8": _price(rng),
                 "max_oracle_move_bps": _bps(rng), "oracle_seen": rng.random() < 0.85}
        elif op == "notional_quote":
            c = {"op": op, "position_base": _spos(rng), "price_e8": _price(rng)}
        elif op == "maint_margin_req":
            c = {"op": op, "position_base": _spos(rng), "price_e8": _price(rng),
                 "maint_bps": _bps(rng), "depeg_bps": _bps(rng)}
        elif op == "init_margin_req":
            c = {"op": op, "position_base": _spos(rng), "price_e8": _price(rng), "init_bps": _bps(rng)}
        elif op == "pnl_quote":
            c = {"op": op, "position_base": _spos(rng), "settle_price_e8": _price(rng),
                 "index_price_e8": _price(rng)}
        elif op == "is_liquidatable":
            c = {"op": op, "position_base": _spos(rng),
                 "collateral_after_pnl": rng.randint(-10**12, 10**12),
                 "settle_price_e8": _price(rng), "maintenance_margin_bps": _bps(rng),
                 "depeg_buffer_bps": _bps(rng)}
        else:  # funding_payment
            c = {"op": op, "position_base": _spos(rng), "index_price_e8": _price(rng),
                 "rate_bps": _signed_bps(rng)}
        out.append(c)
    return out


# --- Rust bridge --------------------------------------------------------------


class PerpMathShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise PerpMathShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise PerpMathShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise PerpMathShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR),
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        raise PerpMathShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise PerpMathShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, cases: list[dict]) -> list[dict]:
    request = json.dumps({"cases": cases})
    proc = subprocess.run(
        [str(bin_path), "perp-math", "-"],
        input=request,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise PerpMathShadowError(f"rust perp-math exited {proc.returncode}:\n{proc.stderr}")
    return json.loads(proc.stdout)["results"]


def diff_results(py: list[dict], rs: list[dict]) -> list[str]:
    problems: list[str] = []
    if len(py) != len(rs):
        return [f"length mismatch: {len(py)} vs {len(rs)}"]
    for i, (p, r) in enumerate(zip(py, rs)):
        if bool(p["ok"]) != bool(r["ok"]):
            problems.append(f"case {i}: ok python={p['ok']} rust={r['ok']} (code={r.get('code')})")
            continue
        if not p["ok"]:
            continue
        if "flag" in p and p["flag"] != r.get("flag"):
            problems.append(f"case {i}: flag python={p['flag']} rust={r.get('flag')}")
        if "value" in p and p["value"] != r.get("value"):
            problems.append(f"case {i}: value python={p['value']} rust={r.get('value')}")
    return problems
