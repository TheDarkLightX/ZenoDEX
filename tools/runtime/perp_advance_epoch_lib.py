"""advance_epoch differential harness (Python authority <-> Rust shadow).

The Python authority is the real isolated perps integration path
(`apply_perp_ops`). The Rust shadow models the global-only E2 transition:

* integration gate: current epoch must be settled
  (`oracle_last_update_epoch == now_epoch`);
* kernel delta/domain guard;
* update: `now_epoch += delta`, `epoch_phase = Open`;
* all account state remains outside this transition.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path

from src.core.dex import DexState
from src.state.balances import BalanceTable
from src.state.lp import LPTable

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"

OPERATOR = "00" * 48


def _reason_category(error: str) -> str:
    e = error or ""
    if "cannot advance epoch before settling current epoch" in e:
        return "epoch_not_settled"
    if "param_domain:delta" in e or "delta must be" in e:
        return "param_domain_delta"
    if e == "guard":
        return "advance_epoch_guard"
    return f"unmapped:{e}"


def _op(market_id: str, action: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {"module": "TauPerp", "version": "0.1", "market_id": market_id, "action": action}
    op.update(kwargs)
    return op


def _apply_result(*, state: DexState, tx_sender_pubkey: str, ops: list):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True)
    return apply_perp_ops(config=cfg, state=state, operations={"5": ops}, tx_sender_pubkey=tx_sender_pubkey, block_timestamp=0)


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, ops=ops)
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _with_oracle_snapshot(state: DexState, *, market_id: str, price_e8: int) -> DexState:
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    now = int(gs.get("now_epoch", 0))
    gs["oracle_seen"] = True
    gs["oracle_last_update_epoch"] = max(0, now - 1)
    gs["index_price_e8"] = int(price_e8)
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=dict(market.accounts))
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def _settle_current_epoch(state: DexState, *, market_id: str) -> DexState:
    """Drive the current Open epoch through publish -> settle, ending Settled."""
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    return _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "settle_epoch")])


def build_state(*, market_id: str, setup: str, cycles: int = 0) -> DexState:
    quote_asset = "0x" + "41" * 32
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "init_market", quote_asset=quote_asset)])
    if setup == "init":
        return state
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "advance_epoch", delta=1)])
    if setup == "unsettled_open":
        return state
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    if setup == "price_published":
        return state
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "settle_epoch")])
    if setup == "settled":
        # Optionally advance through `cycles` more full epochs to vary now_epoch.
        for _ in range(max(0, int(cycles))):
            state = _apply(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "advance_epoch", delta=1)])
            state = _settle_current_epoch(state, market_id=market_id)
        return state
    raise ValueError(f"unknown setup: {setup!r}")


def py_eval(index: int, case: dict) -> dict:
    market_id = case.get("market_id", f"perp:adv{index}")
    state = build_state(
        market_id=market_id,
        setup=str(case.get("setup", "init")),
        cycles=int(case.get("cycles", 0)),
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = market.global_state
    rust_input = {
        "now_epoch": int(gs["now_epoch"]),
        "epoch_phase": int(gs["epoch_phase"]),
        "oracle_last_update_epoch": int(gs["oracle_last_update_epoch"]),
        "delta": int(case["delta"]),
    }

    res = _apply_result(state=state, tx_sender_pubkey=OPERATOR, ops=[_op(market_id, "advance_epoch", delta=int(case["delta"]))])
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or ""), "_rust_input": rust_input}
    assert res.state is not None and res.state.perps is not None
    post = res.state.perps.markets[market_id]
    pg = post.global_state
    return {
        "index": index,
        "ok": True,
        "now_epoch": int(pg["now_epoch"]),
        "epoch_phase": int(pg["epoch_phase"]),
        "oracle_last_update_epoch": int(pg["oracle_last_update_epoch"]),
        "_rust_input": rust_input,
    }


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


_SETUPS = ("init", "unsettled_open", "price_published", "settled")


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    """Deterministic randomized differential cases.

    Each case picks one of the four reachable setups and a delta drawn from a
    distribution that straddles the kernel param-domain `[1, 10_000]` (including
    `0` and `> MAX_DELTA`, which must reject as `param_domain_delta`). Settled
    cases additionally vary `now_epoch` via extra epoch cycles so the
    `now += delta` update is exercised at several base epochs.
    """
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        setup = rng.choice(_SETUPS)
        delta = rng.choice([0, 1, 1, 2, 5, 9_999, 10_000, 10_001, 25_000])
        case: dict[str, object] = {"setup": setup, "delta": delta, "market_id": f"perp:rnd{seed}_{k}"}
        if setup == "settled":
            case["cycles"] = rng.randint(0, 3)
        cases.append(case)
    return cases


class AdvanceEpochShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise AdvanceEpochShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise AdvanceEpochShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise AdvanceEpochShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise AdvanceEpochShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise AdvanceEpochShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run([str(bin_path), "advance-epoch", "-"], input=request, capture_output=True, text=True)
    if proc.returncode != 0:
        raise AdvanceEpochShadowError(f"rust advance-epoch exited {proc.returncode}:\n{proc.stderr}")
    return json.loads(proc.stdout)["results"]


def diff_results(py: list[dict], rs: list[dict]) -> list[str]:
    problems: list[str] = []
    if len(py) != len(rs):
        return [f"length mismatch: python {len(py)} vs rust {len(rs)}"]
    for i, (p, r) in enumerate(zip(py, rs)):
        if bool(p["ok"]) != bool(r["ok"]):
            problems.append(f"case {i}: ok python={p['ok']} rust={r['ok']} (rust code={r.get('code')})")
            continue
        if not p["ok"]:
            if p.get("reason") != r.get("code"):
                problems.append(f"case {i}: reject reason python={p.get('reason')} rust={r.get('code')}")
            continue
        for field in ("now_epoch", "epoch_phase", "oracle_last_update_epoch"):
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
    return problems
