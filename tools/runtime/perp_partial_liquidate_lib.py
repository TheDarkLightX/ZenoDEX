"""partial_liquidate differential harness (Python authority <-> Rust shadow).

The Python authority is the real isolated perps integration path
(`apply_perp_ops`). The Rust shadow models the single-account mid-`Open`
liquidation. A liquidatable OPEN state is built by opening a position via the
funding-auto harness's `build_market`, settling+advancing to an OPEN epoch, then
lowering the account's collateral below maintenance margin (the account
validator enforces `entry == index` but no collateral floor, so this is a valid
reachable-via-funding state). The liquidation must be sent by the account itself
(`account_pubkey must match tx sender`).
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

_GLOBAL_OVERRIDE_FIELDS = {
    "min_notional_for_bounty",
    "liquidation_penalty_bps",
    "fee_pool_quote",
    "fee_income",
    "initial_insurance",
    "claims_paid",
    "insurance_balance",
}


def _reason_category(error: str) -> str:
    e = error or ""
    if "param_domain:fraction_bps" in e:
        return "param_domain_fraction_bps"
    if e == "guard" or "partial_liquidate rejected" in e:
        return "partial_liquidate_guard"
    return f"unmapped:{e}"


def _g(gs, key, default=0):
    return gs.get(key, default)


def build_liquidatable_open(*, market_id: str, pk: str, position: int, deposit: int, collateral: int, case: dict) -> DexState:
    """Open `position` at index 1e8, settle+advance to an OPEN epoch, then set the
    account's collateral to `collateral` (entry stays == index == 1e8)."""
    quote_asset = "0x" + ("%02x" % (0x40 + (abs(position) % 100))) * 32
    state = fa.build_market(market_id=market_id, quote_asset=quote_asset, positions=[(pk, int(position))], clearing_price_e8=100_000_000, deposit=int(deposit))
    state = fa._apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "settle_epoch")])
    state = fa._apply(state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "advance_epoch", delta=1)])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    acct = m.accounts[pk]
    new_acct = replace(acct, collateral_quote=int(collateral))
    gs = dict(m.global_state)
    for field in _GLOBAL_OVERRIDE_FIELDS:
        if field in case:
            gs[field] = int(case[field])
    accts = dict(m.accounts)
    accts[pk] = new_acct
    markets = dict(state.perps.markets)
    markets[market_id] = type(m)(quote_asset=m.quote_asset, global_state=gs, accounts=accts)
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def py_eval(index: int, case: dict) -> dict:
    market_id = case.get("market_id", f"perp:pl{index}")
    pk = case.get("pk", "aa" * 48)
    state = build_liquidatable_open(
        market_id=market_id, pk=pk,
        position=int(case["position"]), deposit=int(case.get("deposit", 200_000)),
        collateral=int(case["collateral"]), case=case,
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = market.global_state
    acct = market.accounts[pk]
    fraction_bps = int(case.get("fraction_bps", 0))
    rust_input = {
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
        "liquidation_penalty_bps": int(_g(gs, "liquidation_penalty_bps")),
        "min_notional_for_bounty": int(_g(gs, "min_notional_for_bounty")),
        "fee_pool_quote": int(_g(gs, "fee_pool_quote")),
        "fee_income": int(_g(gs, "fee_income")),
        "initial_insurance": int(_g(gs, "initial_insurance")),
        "claims_paid": int(_g(gs, "claims_paid")),
        "fraction_bps": fraction_bps,
    }

    res = fa._apply_result(
        state=state, tx_sender_pubkey=pk, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "partial_liquidate", account_pubkey=pk, fraction_bps=fraction_bps)],
    )
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or ""), "_rust_input": rust_input}
    post = res.state.perps.markets[market_id]
    pg = post.global_state
    pa = post.accounts[pk]
    return {
        "index": index,
        "ok": True,
        "position_base": int(pa.position_base),
        "entry_price_e8": int(pa.entry_price_e8),
        "collateral_quote": int(pa.collateral_quote),
        "fee_pool_quote": int(pg["fee_pool_quote"]),
        "fee_income": int(pg["fee_income"]),
        "insurance_balance": int(pg["insurance_balance"]),
        "liquidated_this_step": bool(pa.liquidated_this_step),
        "_rust_input": rust_input,
    }


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        mag = rng.choice([200_000, 500_000, 1_000_000])
        position = mag if rng.random() < 0.5 else -mag
        # maint @ index 1e8 = |pos|*1e8/1e8 * 6% = |pos|*0.06. Collateral straddles it.
        maint = abs(position) * 600 // 10_000
        collateral = rng.choice([
            maint // 4, maint // 2, maint - 1,        # liquidatable
            maint, maint + 1, maint * 2,              # healthy -> guard
        ])
        fraction = rng.choice([0, 0, 1, 2500, 5000, 10_000, 10_001, 50_000])
        case = {
            "position": position,
            "deposit": max(200_000, abs(position)),  # >= initial margin (10%) at 1e8
            "collateral": int(collateral),
            "fraction_bps": fraction,
            "min_notional_for_bounty": rng.choice([0, 100_000_000]),
            "pk": ("%02x" % (0xA0 + (k % 80))) * 48,
            "market_id": f"perp:plr{seed}_{k}",
        }
        cases.append(case)
    return cases


class PartialLiquidateShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise PartialLiquidateShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise PartialLiquidateShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise PartialLiquidateShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise PartialLiquidateShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise PartialLiquidateShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run(
        [str(bin_path), "partial-liquidate", "-"], input=request, capture_output=True, text=True
    )
    if proc.returncode != 0:
        raise PartialLiquidateShadowError(f"rust partial-liquidate exited {proc.returncode}:\n{proc.stderr}")
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
        if bool(p["liquidated_this_step"]) != bool(r.get("liquidated_this_step")):
            problems.append(f"case {i}: liquidated python={p['liquidated_this_step']} rust={r.get('liquidated_this_step')}")
        for field in ("position_base", "entry_price_e8", "collateral_quote", "fee_pool_quote", "fee_income", "insurance_balance"):
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
    return problems
