"""set_market_params differential harness (Python authority <-> Rust shadow).

Operator-only control-parameter governance. The real authority is driven via
`apply_perp_ops`; the op requires an oracle-settled epoch (oracle_last == now),
so states are built with `build_market` then `settle_epoch` (Settled).
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path

from src.core.dex import DexState  # noqa: F401

from tools.runtime import perp_funding_auto_lib as fa

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"

OPERATOR = fa.OPERATOR

_CONTROL_PARAMS = (
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "funding_cap_bps",
    "min_notional_for_bounty",
)


def _min_collectible() -> int:
    from src.integration.perp_engine import PerpEngineConfig

    return int(PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True).min_collectible_liquidation_penalty_quote)


def _reason_category(error: str) -> str:
    e = error or ""
    if "while positions are open" in e:
        return "set_market_params_anti_farming"
    if "out of range" in e or "must be non-negative" in e or "unknown params key" in e or "must be an object" in e:
        return "set_market_params_param_domain"
    if "require min_notional_for_bounty" in e:
        return "set_market_params_min_notional"
    if "require depeg" in e or "require max_oracle_move" in e or "require maintenance_margin" in e or "require liquidation_penalty" in e:
        return "set_market_params_ordering"
    if "position exceeds" in e or "under maintenance margin" in e:
        return "set_market_params_account_unsafe"
    return f"unmapped:{e}"


def _g(gs, key, default=0):
    return gs.get(key, default)


def build_settled_market(*, market_id: str, positions, deposit: int) -> DexState:
    quote_asset = "0x" + ("%02x" % (0x40 + (len(positions) % 100))) * 32
    state = fa.build_market(market_id=market_id, quote_asset=quote_asset, positions=positions, clearing_price_e8=100_000_000, deposit=int(deposit))
    return fa._apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "settle_epoch")])


def with_global_overrides(state: DexState, *, market_id: str, overrides: dict[str, int]) -> DexState:
    if not overrides:
        return state
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    for key, value in overrides.items():
        gs[key] = int(value)
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset,
        global_state=gs,
        accounts=dict(market.accounts),
    )
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def py_eval(index: int, case: dict) -> dict:
    market_id = case.get("market_id", f"perp:smp{index}")
    positions = [(pk, int(p)) for pk, p in case.get("positions", [])]
    state = build_settled_market(market_id=market_id, positions=positions, deposit=int(case.get("deposit", 200_000)))
    state = with_global_overrides(
        state,
        market_id=market_id,
        overrides={
            key: int(case[key])
            for key in ("funding_rate_bps",)
            if key in case
        },
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = market.global_state
    params = dict(case.get("params", {}))

    rust_input: dict = {f"cur_{k}": int(gs[k]) for k in _CONTROL_PARAMS}
    rust_input["cur_funding_rate_bps"] = int(_g(gs, "funding_rate_bps"))
    rust_input["index_price_e8"] = int(gs["index_price_e8"])
    rust_input["min_collectible_liquidation_penalty_quote"] = _min_collectible()
    for k, v in params.items():
        rust_input[f"upd_{k}"] = int(v)
    rust_input["accounts"] = [
        {"position_base": int(a.position_base), "collateral_quote": int(a.collateral_quote)}
        for _, a in sorted(market.accounts.items())
    ]

    res = fa._apply_result(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "set_market_params", params=params)])
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or ""), "_rust_input": rust_input}
    pg = res.state.perps.markets[market_id].global_state
    out = {k: int(pg[k]) for k in _CONTROL_PARAMS}
    out["funding_rate_bps"] = int(pg["funding_rate_bps"])
    out.update({"index": index, "ok": True, "_rust_input": rust_input})
    return out


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        n_keys = rng.randint(0, 3)
        params: dict[str, int] = {}
        for _ in range(n_keys):
            key = rng.choice(_CONTROL_PARAMS)
            params[key] = rng.choice([
                0, 1, 50, 100, 200, 500, 600, 1000, 5000, 9000, 10_000, 10_001,
                1_000_000, 100_000_000, 1_000_000_000_000, -1,
            ])
        positions = []
        if rng.random() < 0.5:
            positions = [("aa" * 48, rng.choice([300_000, 500_000, 1_000_000]))]
        cases.append({"params": params, "positions": positions, "deposit": rng.choice([200_000, 1_000_000]), "market_id": f"perp:smpr{seed}_{k}"})
    return cases


class SetMarketParamsShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise SetMarketParamsShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise SetMarketParamsShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise SetMarketParamsShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise SetMarketParamsShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise SetMarketParamsShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run([str(bin_path), "set-market-params", "-"], input=request, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SetMarketParamsShadowError(f"rust set-market-params exited {proc.returncode}:\n{proc.stderr}")
    return json.loads(proc.stdout)["results"]


def diff_results(py: list[dict], rs: list[dict]) -> list[str]:
    problems: list[str] = []
    if len(py) != len(rs):
        return [f"length mismatch: python {len(py)} vs rust {len(rs)}"]
    fields = list(_CONTROL_PARAMS) + ["funding_rate_bps"]
    for i, (p, r) in enumerate(zip(py, rs)):
        if bool(p["ok"]) != bool(r["ok"]):
            problems.append(f"case {i}: ok python={p['ok']} rust={r['ok']} (rust code={r.get('code')})")
            continue
        if not p["ok"]:
            if p.get("reason") != r.get("code"):
                problems.append(f"case {i}: reject reason python={p.get('reason')} rust={r.get('code')}")
            continue
        for field in fields:
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
    return problems
