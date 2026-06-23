"""Account-management ops differential harness (Python authority <-> Rust shadow).

Covers the OPEN-phase isolated ops `deposit_collateral`, `withdraw_collateral`,
`set_position` (single-account, sender-bound) and `clear_breaker` (global,
operator-gated). The real authority is driven via `apply_perp_ops`; OPEN states
are built with the funding-auto harness's `build_market` then settled+advanced.
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
_SINGLE_ACCOUNT_OPS = {"deposit_collateral", "withdraw_collateral", "set_position"}


def _reason_category(error: str, op: str) -> str:
    e = error or ""
    if "param_domain:amount" in e or "amount must be non-negative" in e:
        return "param_domain_amount"
    if "param_domain:new_position_base" in e or "new_position_base must be" in e:
        return "param_domain_new_position_base"
    if "cannot clear breaker while positions are open" in e:
        return "clear_breaker_positions_open"
    if "invariant:inv_maint_margin_ok" in e:
        return "invariant_maint_margin"
    if e == "guard":
        return f"{op}_guard"
    return f"unmapped:{e}"


def _g(gs, key, default=0):
    return gs.get(key, default)


def build_open_state(*, market_id: str, pk: str, position: int, collateral: int, deposit: int, breaker_active: bool) -> DexState:
    """OPEN epoch-4 state with one account holding `position` and `collateral`."""
    quote_asset = "0x" + ("%02x" % (0x40 + (abs(position) % 100))) * 32
    state = fa.build_market(market_id=market_id, quote_asset=quote_asset, positions=[(pk, int(position))], clearing_price_e8=100_000_000, deposit=int(deposit))
    state = fa._apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "settle_epoch")])
    state = fa._apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "advance_epoch", delta=1)])
    m = state.perps.markets[market_id]
    acct = m.accounts[pk]
    new_acct = replace(acct, collateral_quote=int(collateral))
    gs = dict(m.global_state)
    if breaker_active:
        gs["breaker_active"] = True
        gs["breaker_last_trigger_epoch"] = int(gs.get("now_epoch", 0))
    accts = dict(m.accounts)
    accts[pk] = new_acct
    markets = dict(state.perps.markets)
    markets[market_id] = type(m)(quote_asset=m.quote_asset, global_state=gs, accounts=accts)
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def py_eval(index: int, case: dict) -> dict:
    op = str(case["op"])
    market_id = case.get("market_id", f"perp:ao{index}")
    pk = case.get("pk", "aa" * 48)
    state = build_open_state(
        market_id=market_id, pk=pk,
        position=int(case.get("position", 0)),
        collateral=int(case.get("collateral", 200_000)),
        deposit=int(case.get("deposit", 200_000)),
        breaker_active=bool(case.get("breaker_active", False)),
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = market.global_state
    acct = market.accounts[pk]
    amount = int(case.get("amount", 0))
    new_position_base = int(case.get("new_position_base", 0))
    all_flat = all(int(a.position_base) == 0 for a in market.accounts.values())
    rust_input = {
        "op": op,
        "now_epoch": int(gs["now_epoch"]),
        "epoch_phase": int(gs["epoch_phase"]),
        "oracle_last_update_epoch": int(gs["oracle_last_update_epoch"]),
        "max_oracle_staleness_epochs": int(_g(gs, "max_oracle_staleness_epochs")),
        "oracle_seen": bool(gs["oracle_seen"]),
        "index_price_e8": int(gs["index_price_e8"]),
        "position_base": int(acct.position_base),
        "collateral_quote": int(acct.collateral_quote),
        "entry_price_e8": int(acct.entry_price_e8),
        "maintenance_margin_bps": int(_g(gs, "maintenance_margin_bps")),
        "depeg_buffer_bps": int(_g(gs, "depeg_buffer_bps")),
        "initial_margin_bps": int(_g(gs, "initial_margin_bps")),
        "max_position_abs": int(_g(gs, "max_position_abs")),
        "breaker_active": bool(_g(gs, "breaker_active", False)),
        "breaker_last_trigger_epoch": int(_g(gs, "breaker_last_trigger_epoch")),
        "amount": amount,
        "new_position_base": new_position_base,
        "all_positions_flat": bool(all_flat),
    }

    if op in _SINGLE_ACCOUNT_OPS:
        sender = pk
        kwargs = {"account_pubkey": pk}
        if op in ("deposit_collateral", "withdraw_collateral"):
            kwargs["amount"] = amount
        else:
            kwargs["new_position_base"] = new_position_base
    else:  # clear_breaker (operator-gated, no account)
        sender = OPERATOR
        kwargs = {}
    res = fa._apply_result(state=state, tx_sender_pubkey=sender, operator_pubkey=OPERATOR, ops=[fa._op(market_id, op, **kwargs)])
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or "", op), "_rust_input": rust_input}
    post = res.state.perps.markets[market_id]
    pg = post.global_state
    pa = post.accounts.get(pk) or acct
    return {
        "index": index,
        "ok": True,
        "position_base": int(pa.position_base),
        "entry_price_e8": int(pa.entry_price_e8),
        "collateral_quote": int(pa.collateral_quote),
        "breaker_active": bool(_g(pg, "breaker_active", False)),
        "breaker_last_trigger_epoch": int(_g(pg, "breaker_last_trigger_epoch")),
        "_rust_input": rust_input,
    }


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        op = rng.choice(["deposit_collateral", "withdraw_collateral", "set_position", "clear_breaker"])
        pk = ("%02x" % (0xA0 + (k % 80))) * 48
        market_id = f"perp:aor{seed}_{k}"
        if op == "clear_breaker":
            cases.append({"op": op, "position": 0, "collateral": 200_000, "breaker_active": rng.choice([True, False]), "pk": pk, "market_id": market_id})
        elif op == "set_position":
            position = rng.choice([0, 300_000, 500_000])
            cases.append({"op": op, "position": position, "collateral": rng.choice([10_000, 200_000, 1_000_000]),
                          "new_position_base": rng.choice([0, 200_000, 800_000, 1_000_000, 1_000_001, -500_000]),
                          "breaker_active": rng.choice([True, False]), "pk": pk, "market_id": market_id})
        else:  # deposit / withdraw
            position = rng.choice([0, 500_000])
            if op == "deposit_collateral":
                # Deposit also passes an integration wallet-balance check (out of the
                # shadow's perp-only scope); keep amounts within the funded balance (1e9).
                amount = rng.choice([0, 1, 10_000, 150_000, 100_000_000])
            else:
                # Withdraw is bounded by collateral (guard) + the [1, 1e12] kernel domain.
                amount = rng.choice([0, 1, 10_000, 150_000, 300_000, 1_000_000_000_001])
            cases.append({"op": op, "position": position, "collateral": rng.choice([100_000, 200_000]),
                          "amount": amount, "pk": pk, "market_id": market_id})
    return cases


class AccountOpShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise AccountOpShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise AccountOpShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise AccountOpShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise AccountOpShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise AccountOpShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run([str(bin_path), "account-op", "-"], input=request, capture_output=True, text=True)
    if proc.returncode != 0:
        raise AccountOpShadowError(f"rust account-op exited {proc.returncode}:\n{proc.stderr}")
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
        if bool(p["breaker_active"]) != bool(r.get("breaker_active")):
            problems.append(f"case {i}: breaker_active python={p['breaker_active']} rust={r.get('breaker_active')}")
        for field in ("position_base", "entry_price_e8", "collateral_quote", "breaker_last_trigger_epoch"):
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
    return problems
