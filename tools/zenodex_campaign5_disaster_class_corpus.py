#!/usr/bin/env python3
"""Replay the public Campaign 5 ZenoDEX disaster-class corpus.

This corpus binds three Campaign 5 witness families to deterministic local
checks:

* ADL-before-treasury blocks the two-leg sybil bankruptcy siphon in the scoped
  integer model promoted to Lean.
* TWAL exposure accounting sharply reduces the epoch-boundary yield-vampire
  witness in the scoped integer model promoted to Lean.
* Exact-out routing remains bounded and acyclic on a wrapped-asset ring witness.

The corpus is model and implementation evidence for these bounded classes. It
does not claim runtime TWAL reward accounting, runtime ADL queue integration,
UPBA settlement, or exhaustive ZenoDEX disaster coverage.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.routing import RouteQuote, best_route_exact_out_2hop  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402

CORPUS_SCHEMA = "zenodex.campaign5.disaster_class_corpus.v1"
REPLAY_COMMAND = "python3 tools/zenodex_campaign5_disaster_class_corpus.py --format text"
NOT_CLAIMED = [
    "does_not_claim_runtime_twal_accounting",
    "does_not_claim_runtime_adl_queue_integration",
    "does_not_claim_sybil_identity_linkage",
    "does_not_claim_uniform_batch_clearing_closed",
    "does_not_claim_exhaustive_zenodex_disaster_coverage",
    "does_not_claim_production_liveness",
]


def _case_receipt(
    class_id: str,
    *,
    manifest_axes: list[str],
    guard_families: list[str],
    obligations: list[str],
    ok: bool,
    expected: str,
    observed: Mapping[str, Any],
    replay_command: str = REPLAY_COMMAND,
) -> dict[str, Any]:
    return {
        "class_id": class_id,
        "manifest_axes": list(manifest_axes),
        "guard_families": list(guard_families),
        "obligations": list(obligations),
        "ok": bool(ok),
        "status": "closed" if ok else "failed",
        "expected": expected,
        "observed": dict(observed),
        "replay_command": replay_command,
    }


def _bankruptcy_deficit(margin: int, shock_pnl: int) -> int:
    return max(0, int(shock_pnl) - int(margin))


def _adl_sybil_bankruptcy_case() -> dict[str, Any]:
    margin = 1_000
    shock_pnl = 2_000
    initial_capital = 2 * margin
    deficit = _bankruptcy_deficit(margin, shock_pnl)
    standard_final_capital = margin + shock_pnl
    standard_profit = standard_final_capital - initial_capital
    standard_insurance_draw = deficit
    adl_final_capital = margin + shock_pnl - deficit
    adl_profit = adl_final_capital - initial_capital
    adl_treasury_draw = max(0, deficit - shock_pnl)

    ok = (
        standard_profit == standard_insurance_draw == 1_000
        and adl_final_capital == initial_capital
        and adl_profit == 0
        and adl_treasury_draw == 0
    )
    return _case_receipt(
        "adl_sybil_bankruptcy_closure",
        manifest_axes=[
            "perp_sybil_bankruptcy_insurance_drain",
            "perp_offsetting_leg_profit_after_bankruptcy",
            "perp_treasury_draw_before_adl_haircut",
        ],
        guard_families=["adl_deficit_haircut_gate", "settlement_budget_gate"],
        obligations=["adl_deficit_haircut", "budget_conservation", "economic_margin", "schema_total"],
        ok=ok,
        expected="ADL-before-treasury removes the two-leg sybil bankruptcy profit in the Campaign 5 witness",
        observed={
            "model": "PerpADLSybilBankruptcyClosure",
            "margin": margin,
            "shock_pnl": shock_pnl,
            "initial_capital": initial_capital,
            "bankruptcy_deficit": deficit,
            "standard_final_capital": standard_final_capital,
            "standard_profit": standard_profit,
            "standard_insurance_draw": standard_insurance_draw,
            "adl_final_capital": adl_final_capital,
            "adl_profit": adl_profit,
            "adl_treasury_draw": adl_treasury_draw,
        },
    )


def _floor_reward(epoch_reward: int, numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("reward denominator must be positive")
    return int(epoch_reward) * int(numerator) // int(denominator)


def _twal_yield_vampire_case() -> dict[str, Any]:
    epoch_reward = 10_000
    attacker_liquidity = 9_900_000
    attacker_duration = 1
    honest_liquidity = 100_000
    honest_duration = 1_000
    snapshot_weight = attacker_liquidity
    snapshot_total = attacker_liquidity + honest_liquidity
    twal_weight = attacker_liquidity * attacker_duration
    twal_total = twal_weight + honest_liquidity * honest_duration
    snapshot_reward = _floor_reward(epoch_reward, snapshot_weight, snapshot_total)
    twal_reward = _floor_reward(epoch_reward, twal_weight, twal_total)
    reduction_bps = (snapshot_reward - twal_reward) * 10_000 // snapshot_reward

    ok = snapshot_reward == 9_900 and twal_reward == 900 and reduction_bps == 9_090
    return _case_receipt(
        "twal_yield_vampire_closure",
        manifest_axes=[
            "jit_yield_vampire_snapshot_rewards",
            "lp_flash_stake_epoch_boundary_rewards",
        ],
        guard_families=["twal_exposure_gate"],
        obligations=["duration_exposure_accounting", "reward_budget_cap", "schema_total"],
        ok=ok,
        expected="TWAL exposure accounting reduces the Campaign 5 snapshot reward witness from 9900 to 900",
        observed={
            "model": "TWALYieldVampireDefense",
            "epoch_reward": epoch_reward,
            "attacker_liquidity": attacker_liquidity,
            "attacker_duration": attacker_duration,
            "honest_liquidity": honest_liquidity,
            "honest_duration": honest_duration,
            "snapshot_reward": snapshot_reward,
            "twal_reward": twal_reward,
            "reward_reduction_bps": reduction_bps,
        },
    )


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=int(r0) if a0 < a1 else int(r1),
        reserve1=int(r1) if a0 < a1 else int(r0),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _route_asset_paths(route: RouteQuote) -> list[list[str]]:
    paths: list[list[str]] = []
    for leg in route.legs:
        if not leg.hops:
            paths.append([])
            continue
        assets = [leg.hops[0].asset_in]
        assets.extend(hop.asset_out for hop in leg.hops)
        paths.append(assets)
    return paths


def _exact_out_ring_topology_case() -> dict[str, Any]:
    pools = {
        "p_cb_wst": _pool("p_cb_wst", "cbZENO", "wstZENO", 10_000, 10_000, 0),
        "p_st_cb": _pool("p_st_cb", "stZENO", "cbZENO", 10_000, 10_000, 0),
        "p_wst_st": _pool("p_wst_st", "wstZENO", "stZENO", 10_000, 10_000, 0),
    }
    same_asset_route = best_route_exact_out_2hop(
        pools_by_id=pools,
        asset_in="wstZENO",
        asset_out="wstZENO",
        amount_out=100,
    )

    from src.core import routing as routing_mod

    orig = routing_mod._pool_quote_exact_out
    calls = {"n": 0}

    def counting(pool: PoolState, *, asset_in: str, asset_out: str, amount_out: int):
        calls["n"] = int(calls["n"]) + 1
        return orig(pool, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)

    routing_mod._pool_quote_exact_out = counting  # type: ignore[assignment]
    try:
        cross_asset_route = best_route_exact_out_2hop(
            pools_by_id=pools,
            asset_in="wstZENO",
            asset_out="cbZENO",
            amount_out=100,
        )
    finally:
        routing_mod._pool_quote_exact_out = orig  # type: ignore[assignment]

    paths = _route_asset_paths(cross_asset_route) if cross_asset_route is not None else []
    acyclic_paths = all(path and len(path) == len(set(path)) for path in paths)
    bounded_hops = all(1 <= len(leg.hops) <= 2 for leg in cross_asset_route.legs) if cross_asset_route else False
    ok = same_asset_route is None and cross_asset_route is not None and int(calls["n"]) <= 8 and bounded_hops and acyclic_paths
    return _case_receipt(
        "exact_out_ring_topology_closure",
        manifest_axes=[
            "exact_out_negative_cost_routing_cycle",
            "cyclic_wrapped_asset_exact_out_dos",
        ],
        guard_families=["acyclic_routing_gate", "kernel_invariant_gate"],
        obligations=["hop_cap", "kernel_invariant_step", "resource_budget", "route_acyclicity", "schema_total"],
        ok=ok,
        expected="exact-out routing rejects same-asset cycles and returns bounded acyclic paths on a wrapped-asset ring",
        observed={
            "verifier": "src.core.routing.best_route_exact_out_2hop",
            "same_asset_route_rejected": same_asset_route is None,
            "cross_asset_route_found": cross_asset_route is not None,
            "quote_call_count": int(calls["n"]),
            "quote_call_bound": 8,
            "asset_paths": paths,
            "acyclic_paths": acyclic_paths,
            "bounded_hops": bounded_hops,
            "amount_in": None if cross_asset_route is None else int(cross_asset_route.amount_in),
            "amount_out": None if cross_asset_route is None else int(cross_asset_route.amount_out),
        },
    )


def build_corpus() -> dict[str, Any]:
    cases = [
        _adl_sybil_bankruptcy_case(),
        _twal_yield_vampire_case(),
        _exact_out_ring_topology_case(),
    ]
    failed = [case for case in cases if not case["ok"]]
    return {
        "schema": CORPUS_SCHEMA,
        "ok": not failed,
        "status": "accepted" if not failed else "rejected",
        "named_disaster_class_count": len(cases),
        "closed_class_count": len(cases) - len(failed),
        "failed_class_count": len(failed),
        "cases": cases,
        "not_claimed": NOT_CLAIMED,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=None, help="optional output path for the corpus receipt")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_corpus()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    if args.format == "json":
        sys.stdout.write(text)
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"named_disaster_class_count = {receipt['named_disaster_class_count']}",
                    f"closed_class_count = {receipt['closed_class_count']}",
                    f"failed_class_count = {receipt['failed_class_count']}",
                    f"status = {receipt['status']}",
                ]
            )
            + "\n"
        )
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
