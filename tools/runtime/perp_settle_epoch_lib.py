"""settle_epoch differential harness (Python authority <-> Rust shadow).

The Python authority is the real isolated perps integration path
(`apply_perp_ops`). The Rust shadow models the multi-account settlement
transition (PnL realization + optional liquidation + global epoch/breaker/fee
accounting). Multi-account PricePublished pre-states are built with the
funding-auto harness's `build_market`.
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
    "fee_pool_quote",
    "fee_income",
    "initial_insurance",
    "claims_paid",
    "insurance_balance",
    "liquidation_penalty_bps",
    "min_notional_for_bounty",
}


def _reason_category(error: str) -> str:
    e = error or ""
    if "fee/insurance overflow (post-settle)" in e:
        return "settle_epoch_fee_overflow"
    if "insurance negative (post-settle)" in e:
        return "settle_epoch_insurance_negative"
    # The global (dummy) guard surfaces the bare kernel reason "guard"; a
    # per-account guard surfaces "settle_epoch rejected for account X: guard".
    if e == "guard" or "settle_epoch rejected" in e:
        return "settle_epoch_guard"
    return f"unmapped:{e}"


def _g(gs, key, default=0):
    return gs.get(key, default)


def _with_global_overrides(state, *, market_id: str, case: dict):
    overrides = {field: int(case[field]) for field in _GLOBAL_OVERRIDE_FIELDS if field in case}
    if not overrides:
        return state
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    gs.update(overrides)
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=dict(market.accounts))
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def py_eval(index: int, case: dict) -> dict:
    market_id = case.get("market_id", f"perp:se{index}")
    quote_asset = "0x" + ("%02x" % (0x40 + (index % 100))) * 32
    state = fa.build_market(
        market_id=market_id,
        quote_asset=quote_asset,
        positions=[(pk, int(p)) for pk, p in case.get("positions", [])],
        clearing_price_e8=int(case["clearing_price_e8"]),
        deposit=int(case.get("deposit", 200_000)),
        sink_k=int(case.get("sink_k", 0)),
    )
    state = _with_global_overrides(state, market_id=market_id, case=case)
    assert state.perps is not None
    if case.get("double_settle"):
        # Settle once (-> Settled); the measured settle below then runs on a
        # non-PricePublished state and must reject with the guard reason.
        first = fa._apply_result(
            state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
            ops=[fa._op(market_id, "settle_epoch")],
        )
        assert first.ok, first.error
        state = first.state
        assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = market.global_state

    pre_accounts = [
        {
            "key": pk,
            "position_base": int(a.position_base),
            "collateral_quote": int(a.collateral_quote),
            "entry_price_e8": int(a.entry_price_e8),
            "liquidated_this_step": bool(a.liquidated_this_step),
        }
        for pk, a in sorted(market.accounts.items())
    ]
    rust_input = {
        "now_epoch": int(gs["now_epoch"]),
        "epoch_phase": int(gs["epoch_phase"]),
        "clearing_price_seen": bool(gs["clearing_price_seen"]),
        "clearing_price_epoch": int(gs["clearing_price_epoch"]),
        "clearing_price_e8": int(gs["clearing_price_e8"]),
        "oracle_last_update_epoch": int(gs["oracle_last_update_epoch"]),
        "oracle_seen": bool(gs["oracle_seen"]),
        "index_price_e8": int(gs["index_price_e8"]),
        "max_oracle_move_bps": int(_g(gs, "max_oracle_move_bps")),
        "maintenance_margin_bps": int(_g(gs, "maintenance_margin_bps")),
        "depeg_buffer_bps": int(_g(gs, "depeg_buffer_bps")),
        "liquidation_penalty_bps": int(_g(gs, "liquidation_penalty_bps")),
        "min_notional_for_bounty": int(_g(gs, "min_notional_for_bounty")),
        "fee_pool_quote": int(_g(gs, "fee_pool_quote")),
        "fee_income": int(_g(gs, "fee_income")),
        "initial_insurance": int(_g(gs, "initial_insurance")),
        "claims_paid": int(_g(gs, "claims_paid")),
        "breaker_active": bool(_g(gs, "breaker_active", False)),
        "breaker_last_trigger_epoch": int(_g(gs, "breaker_last_trigger_epoch")),
        "accounts": pre_accounts,
    }

    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or ""), "_rust_input": rust_input}
    post = res.state.perps.markets[market_id]
    pg = post.global_state
    return {
        "index": index,
        "ok": True,
        "epoch_phase": int(pg["epoch_phase"]),
        "oracle_last_update_epoch": int(pg["oracle_last_update_epoch"]),
        "oracle_seen": bool(pg["oracle_seen"]),
        "index_price_e8": int(pg["index_price_e8"]),
        "breaker_active": bool(_g(pg, "breaker_active", False)),
        "breaker_last_trigger_epoch": int(_g(pg, "breaker_last_trigger_epoch")),
        "fee_pool_quote": int(pg["fee_pool_quote"]),
        "fee_income": int(pg["fee_income"]),
        "insurance_balance": int(pg["insurance_balance"]),
        "accounts": {
            pk: (
                int(a.collateral_quote),
                int(a.position_base),
                int(a.entry_price_e8),
                bool(a.liquidated_this_step),
            )
            for pk, a in post.accounts.items()
        },
        "_rust_input": rust_input,
    }


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


def _accounts(n: int, mag: int) -> list[tuple[str, int]]:
    # Distinct 48-byte pubkeys; alternating long/short within PERP_POSITION_MAX (1e6).
    out = []
    for k in range(n):
        pk = ("%02x" % (0xA0 + k)) * 48
        sign = 1 if k % 2 == 0 else -1
        out.append((pk, sign * mag))
    return out


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        n_acc = rng.choice([0, 1, 1, 2, 3])
        # |position| <= PERP_POSITION_MAX = 1e6; deposit always >= initial margin.
        mag = rng.choice([0, 200_000, 500_000, 1_000_000])
        positions = _accounts(n_acc, mag)
        # Clearing prices straddle index (1e8): in-band moves (PnL) and
        # out-of-band moves (clamp + breaker).
        clearing = rng.choice([
            100_000_000, 99_000_000, 101_000_000, 96_000_000, 104_000_000,
            150_000_000, 50_000_000,
        ])
        deposit = rng.choice([200_000, 1_000_000, 50_000_000])
        cases.append({
            "positions": positions,
            "clearing_price_e8": clearing,
            "deposit": deposit,
            "market_id": f"perp:ser{seed}_{k}",
        })
    return cases


class SettleEpochShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise SettleEpochShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise SettleEpochShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise SettleEpochShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise SettleEpochShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise SettleEpochShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run(
        [str(bin_path), "settle-epoch", "-"], input=request, capture_output=True, text=True
    )
    if proc.returncode != 0:
        raise SettleEpochShadowError(f"rust settle-epoch exited {proc.returncode}:\n{proc.stderr}")
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
        for field in ("oracle_seen", "breaker_active"):
            if bool(p[field]) != bool(r.get(field)):
                problems.append(f"case {i}: {field} python={p[field]} rust={r.get(field)}")
        for field in (
            "epoch_phase", "oracle_last_update_epoch", "index_price_e8",
            "breaker_last_trigger_epoch", "fee_pool_quote", "fee_income", "insurance_balance",
        ):
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
        # Per-account comparison, keyed by account pubkey.
        rs_accts = {a["key"]: a for a in (r.get("accounts") or [])}
        if set(p["accounts"].keys()) != set(rs_accts.keys()):
            problems.append(f"case {i}: account keys python={sorted(p['accounts'])} rust={sorted(rs_accts)}")
            continue
        for pk, (coll, pos, entry, liq) in p["accounts"].items():
            ra = rs_accts[pk]
            if (
                int(ra["collateral_quote"]) != coll
                or int(ra["position_base"]) != pos
                or int(ra["entry_price_e8"]) != entry
                or bool(ra["liquidated_this_step"]) != liq
            ):
                problems.append(
                    f"case {i} acct {pk}: python=({coll},{pos},{entry},{liq}) "
                    f"rust=({ra['collateral_quote']},{ra['position_base']},{ra['entry_price_e8']},{ra['liquidated_this_step']})"
                )
    return problems
