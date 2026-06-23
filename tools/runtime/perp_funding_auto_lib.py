"""apply_funding_auto settlement differential harness (Python authority ↔ Rust).

The Python authority is the real engine: a gate-passing isolated-v2 market is
bootstrapped via ``apply_perp_ops`` and the actual ``apply_funding_auto`` op is
applied. The Rust shadow (``zenodex-runtime funding-auto``) is given the SAME
pre-funding inputs (open accounts, gate-derived rate, index price, margin
params, pre-sink values) and must produce the identical settlement: per-account
collateral / cumulative deltas and the post fee_pool / fee_income / insurance,
or the identical accept/reject.

Scope: the bounded-sink SETTLEMENT only (E2 funding-auto slice). The
funding-rate derivation and the oracle/clearing gate are Python-side here; the
rate is read from the authority gate and handed to Rust.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path
from typing import Any

from src.core.dex import DexState
from src.core.perp_apply_funding_auto_gate import evaluate_perp_apply_funding_auto_gate
from src.state.balances import BalanceTable
from src.state.lp import LPTable

KERNEL = "perp_funding_auto"
_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"

OPERATOR = "00" * 48


def _reason_category(error: str) -> str:
    """Map a Python authority reject message to the stable Rust reject code, so
    rejected cases compare reason (not just the accept/reject boolean)."""
    e = error or ""
    if "drive a protocol sink out of bounds" in e:
        return "sink_out_of_domain"
    if "funding already applied this epoch" in e:
        return "funding_already_applied"
    if "would violate collateral bounds" in e:
        return "collateral_bounds"
    if "would violate maintenance margin" in e:
        return "maintenance_margin"
    if "would violate cumulative funding bounds" in e:
        return "cumulative_funding_bounds"
    return f"unmapped:{e}"


def _op(market_id: str, action: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {"module": "TauPerp", "version": "0.1", "market_id": market_id, "action": action}
    op.update(kwargs)
    return op


def _apply_result(*, state: DexState, tx_sender_pubkey: str, ops: list, operator_pubkey: str):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(operator_pubkey=operator_pubkey, allow_isolated_markets=True)
    return apply_perp_ops(config=cfg, state=state, operations={"5": ops}, tx_sender_pubkey=tx_sender_pubkey, block_timestamp=0)


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list, operator_pubkey: str) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, operator_pubkey=operator_pubkey, ops=ops)
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


def build_market(*, market_id: str, quote_asset: str, positions, clearing_price_e8: int, deposit: int = 200_000, sink_k: int = 0) -> DexState:
    """Bootstrap a gate-passing market to epoch 3 with `positions` open and a
    clearing price published. `positions` = list of (pubkey, position_base)."""
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "init_market", quote_asset=quote_asset)])
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "advance_epoch", delta=1)])

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    for pk, _pos in positions:
        funded.set(pk, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    for pk, pos in positions:
        state = _apply(
            state=state, tx_sender_pubkey=pk, operator_pubkey=OPERATOR,
            ops=[
                _op(market_id, "deposit_collateral", account_pubkey=pk, amount=deposit),
                _op(market_id, "set_position", account_pubkey=pk, new_position_base=pos),
            ],
        )

    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "publish_clearing_price", price_e8=int(clearing_price_e8))])

    if sink_k:
        assert state.perps is not None
        market = state.perps.markets[market_id]
        gs = dict(market.global_state)
        init_ins = int(gs.get("initial_insurance", 0))
        claims = int(gs.get("claims_paid", 0))
        gs["fee_income"] = int(sink_k)
        gs["fee_pool_quote"] = int(sink_k)
        gs["insurance_balance"] = init_ins + int(sink_k) - claims
        markets = dict(state.perps.markets)
        markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=dict(market.accounts))
        state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))
    return state


def _gate_rate(market) -> int:
    gs = market.global_state
    outcome = evaluate_perp_apply_funding_auto_gate(
        now_epoch=int(gs.get("now_epoch", 0)),
        clearing_price_seen=bool(gs.get("clearing_price_seen", False)),
        clearing_price_epoch=int(gs.get("clearing_price_epoch", 0)),
        oracle_last_update_epoch=int(gs.get("oracle_last_update_epoch", 0)),
        oracle_seen=bool(gs.get("oracle_seen", False)),
        index_price_e8=int(gs.get("index_price_e8", 0)),
        max_oracle_staleness_epochs=int(gs.get("max_oracle_staleness_epochs", 0)),
        clearing_price_e8=int(gs.get("clearing_price_e8", 0)),
        max_oracle_move_bps=int(gs.get("max_oracle_move_bps", 0)),
        funding_cap_bps=int(gs.get("funding_cap_bps", 0)),
        projected_net_funding_quote=0,
        any_funding_applied_this_epoch=False,
    )
    return int(outcome.funding_rate_bps)


def py_eval(index: int, case: dict) -> dict:
    """Drive the real authority for one case; return (Python result, rust_input)."""
    market_id = case.get("market_id", f"perp:fa{index}")
    quote_asset = "0x" + ("%02x" % (0x40 + (index % 100))) * 32
    state = build_market(
        market_id=market_id, quote_asset=quote_asset,
        positions=[(pk, int(p)) for pk, p in case["positions"]],
        clearing_price_e8=int(case["clearing_price_e8"]),
        deposit=int(case.get("deposit", 200_000)),
        sink_k=int(case.get("sink_k", 0)),
    )
    if case.get("double_apply"):
        # Apply funding once (must succeed) so the measured apply below is a
        # same-epoch replay → exercises the funding_already_applied reject.
        first = _apply_result(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "apply_funding_auto")])
        assert first.ok, first.error
        state = first.state
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = market.global_state
    rate = _gate_rate(market)

    pre_accounts = [
        {
            "key": pk,
            "position_base": int(a.position_base),
            "collateral_quote": int(a.collateral_quote),
            "funding_paid_cumulative": int(a.funding_paid_cumulative),
            "funding_last_applied_epoch": int(a.funding_last_applied_epoch),
        }
        for pk, a in sorted(market.accounts.items())
    ]
    rust_input = {
        "now_epoch": int(gs["now_epoch"]),
        "rate_bps": rate,
        "index_price_e8": int(gs["index_price_e8"]),
        "maintenance_margin_bps": int(gs.get("maintenance_margin_bps", 0)),
        "depeg_buffer_bps": int(gs.get("depeg_buffer_bps", 0)),
        "fee_pool_quote": int(gs["fee_pool_quote"]),
        "fee_income": int(gs["fee_income"]),
        "insurance_balance": int(gs["insurance_balance"]),
        "accounts": pre_accounts,
    }

    res = _apply_result(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[_op(market_id, "apply_funding_auto")])
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or ""), "_rust_input": rust_input}
    post = res.state.perps.markets[market_id]
    pg = post.global_state
    return {
        "index": index,
        "ok": True,
        "funding_rate_bps": int(pg["funding_rate_bps"]),
        "accounts": {
            pk: (int(a.collateral_quote), int(a.funding_paid_cumulative), int(a.funding_last_applied_epoch))
            for pk, a in post.accounts.items()
        },
        "fee_pool_quote": int(pg["fee_pool_quote"]),
        "fee_income": int(pg["fee_income"]),
        "insurance_balance": int(pg["insurance_balance"]),
        "_rust_input": rust_input,
    }


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    """Uniform fuzz interface (matches the other perp op libs).

    2-3 accounts with long/short positions within PERP_POSITION_MAX, clearing
    prices straddling the index, and a varied pre-existing fee/insurance sink.
    """
    import random

    pks = ["aa" * 48, "bb" * 48, "cc" * 48]
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        kk = rng.randint(2, 3)
        positions = [(pk, rng.choice([-1, 1]) * rng.randint(1, 1_000_000)) for pk in pks[:kk]]
        clearing = rng.choice([100_500_000, 101_000_000, 102_000_000, 98_500_000, 99_000_000, 150_000_000, 50_000_000])
        sink_k = rng.choice([0, 0, 50, 500, 5_000])
        cases.append({"positions": positions, "clearing_price_e8": clearing, "sink_k": sink_k, "market_id": f"perp:fafz{seed}_{k}"})
    return cases


# --- Rust bridge --------------------------------------------------------------


class FundingAutoShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise FundingAutoShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise FundingAutoShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise FundingAutoShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise FundingAutoShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise FundingAutoShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run([str(bin_path), "funding-auto", "-"], input=request, capture_output=True, text=True)
    if proc.returncode != 0:
        raise FundingAutoShadowError(f"rust funding-auto exited {proc.returncode}:\n{proc.stderr}")
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
            # reject-reason parity (catches validation-order / fail-closed drift)
            if p.get("reason") != r.get("code"):
                problems.append(f"case {i}: reject reason python={p.get('reason')} rust={r.get('code')}")
            continue
        # global funding_rate_bps parity
        if int(p["funding_rate_bps"]) != int(r["funding_rate_bps"]):
            problems.append(f"case {i}: funding_rate_bps python={p['funding_rate_bps']} rust={r['funding_rate_bps']}")
        # post sink parity
        for field in ("fee_pool_quote", "fee_income", "insurance_balance"):
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
        # per-account collateral + cumulative + funding_last_applied_epoch parity
        rust_accts = {
            a["key"]: (
                int(a["collateral_quote"]),
                int(a["funding_paid_cumulative"]),
                int(a["funding_last_applied_epoch"]),
            )
            for a in r["accounts"]
        }
        if set(rust_accts) != set(p["accounts"]):
            problems.append(f"case {i}: account keys python={sorted(p['accounts'])} rust={sorted(rust_accts)}")
            continue
        for pk, tup in p["accounts"].items():
            if rust_accts[pk] != tup:
                problems.append(f"case {i}: account {pk} python={tup} rust={rust_accts[pk]}")
    return problems
