"""publish_clearing_price differential harness (Python authority <-> Rust shadow).

The Python authority is the real isolated perps integration path
(`apply_perp_ops`). The Rust shadow models the global-only E2 transition:

* integration price checks: `price_e8 >= 0` then `price_e8 > 0`;
* kernel param-domain: `price_e8 <= PERP_PARAM_AMOUNT_MAX`;
* kernel guard: `epoch_phase == Open` and `clearing_price_epoch < now_epoch`;
* update: `clearing_price_{seen,epoch,e8}` set, `epoch_phase = PricePublished`.

State construction is reused from the advance_epoch harness so both surfaces
drive the identical authority bootstrap.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from pathlib import Path

from src.core.dex import DexState  # noqa: F401  (re-exported for parity)

from tools.runtime import perp_advance_epoch_lib as adv

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"

OPERATOR = adv.OPERATOR


def _reason_category(error: str) -> str:
    e = error or ""
    if "price_e8 must be non-negative" in e:
        return "price_e8_negative"
    if "requires price_e8 > 0" in e:
        return "price_e8_not_positive"
    if "param_domain:price_e8" in e:
        return "param_domain_price_e8"
    if e == "guard":
        return "publish_clearing_price_guard"
    return f"unmapped:{e}"


def build_publish_state(*, market_id: str, setup: str, cycles: int = 0) -> DexState:
    """Reachable pre-states for publish_clearing_price.

    `open_deep` advances one epoch past a settled state: a valid Open state at a
    deeper epoch whose clearing-price fields are still seen from the prior epoch
    (clearing_price_epoch < now), which is the cps=true Open accept case.
    """
    if setup == "open_deep":
        st = adv.build_state(market_id=market_id, setup="settled", cycles=cycles)
        st = adv._apply(
            state=st,
            tx_sender_pubkey=OPERATOR,
            ops=[adv._op(market_id, "advance_epoch", delta=1)],
        )
        return st
    return adv.build_state(market_id=market_id, setup=setup, cycles=cycles)


def _apply_result(*, state: DexState, ops: list):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True)
    return apply_perp_ops(
        config=cfg, state=state, operations={"5": ops}, tx_sender_pubkey=OPERATOR, block_timestamp=0
    )


def py_eval(index: int, case: dict) -> dict:
    market_id = case.get("market_id", f"perp:pub{index}")
    state = build_publish_state(
        market_id=market_id,
        setup=str(case.get("setup", "unsettled_open")),
        cycles=int(case.get("cycles", 0)),
    )
    assert state.perps is not None
    gs = state.perps.markets[market_id].global_state
    rust_input = {
        "now_epoch": int(gs["now_epoch"]),
        "epoch_phase": int(gs["epoch_phase"]),
        "clearing_price_seen": bool(gs["clearing_price_seen"]),
        "clearing_price_epoch": int(gs["clearing_price_epoch"]),
        "clearing_price_e8": int(gs["clearing_price_e8"]),
        "oracle_last_update_epoch": int(gs["oracle_last_update_epoch"]),
        "price_e8": int(case["price_e8"]),
    }

    res = _apply_result(
        state=state, ops=[adv._op(market_id, "publish_clearing_price", price_e8=int(case["price_e8"]))]
    )
    if not res.ok:
        return {"index": index, "ok": False, "reason": _reason_category(res.error or ""), "_rust_input": rust_input}
    assert res.state is not None and res.state.perps is not None
    pg = res.state.perps.markets[market_id].global_state
    return {
        "index": index,
        "ok": True,
        "now_epoch": int(pg["now_epoch"]),
        "epoch_phase": int(pg["epoch_phase"]),
        "clearing_price_seen": bool(pg["clearing_price_seen"]),
        "clearing_price_epoch": int(pg["clearing_price_epoch"]),
        "clearing_price_e8": int(pg["clearing_price_e8"]),
        "_rust_input": rust_input,
    }


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


_SETUPS = ("init", "unsettled_open", "price_published", "settled", "open_deep")
# Prices straddle the kernel param-domain [1, PERP_PARAM_AMOUNT_MAX=1e12] and stay
# within the CLI magnitude bound (MAX_ABS=1e18) so arg_mag never short-circuits.
_PRICES = [-1, 0, 1, 100_000_000, 1_000_000_000_000, 1_000_000_000_001, 1_000_000_000_000_000]


def randomized_cases(*, seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    cases: list[dict] = []
    for k in range(n):
        setup = rng.choice(_SETUPS)
        price = rng.choice(_PRICES)
        case: dict[str, object] = {"setup": setup, "price_e8": price, "market_id": f"perp:pubr{seed}_{k}"}
        if setup in ("settled", "open_deep"):
            case["cycles"] = rng.randint(0, 3)
        cases.append(case)
    return cases


class PublishClearingPriceShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise PublishClearingPriceShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise PublishClearingPriceShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise PublishClearingPriceShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR), capture_output=True, text=True,
    )
    if build.returncode != 0:
        raise PublishClearingPriceShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise PublishClearingPriceShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, py_results: list[dict]) -> list[dict]:
    cases = [r["_rust_input"] for r in py_results]
    request = json.dumps({"cases": cases})
    proc = subprocess.run(
        [str(bin_path), "publish-clearing-price", "-"], input=request, capture_output=True, text=True
    )
    if proc.returncode != 0:
        raise PublishClearingPriceShadowError(f"rust publish-clearing-price exited {proc.returncode}:\n{proc.stderr}")
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
        if bool(p["clearing_price_seen"]) != bool(r.get("clearing_price_seen")):
            problems.append(f"case {i}: clearing_price_seen python={p['clearing_price_seen']} rust={r.get('clearing_price_seen')}")
        for field in ("now_epoch", "epoch_phase", "clearing_price_epoch", "clearing_price_e8"):
            if int(p[field]) != int(r[field]):
                problems.append(f"case {i}: {field} python={p[field]} rust={r[field]}")
    return problems
