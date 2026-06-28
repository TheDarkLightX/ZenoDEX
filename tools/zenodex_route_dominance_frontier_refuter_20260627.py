#!/usr/bin/env python3
"""Bounded refuter for the route dominance Tau frontier envelope."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.amm_dispatch import swap_exact_out_for_pool  # noqa: E402
from src.core.routing_common import pool_connects  # noqa: E402
from src.core.routing_types import RouteHop, RouteLeg, RouteQuote, quote_key  # noqa: E402
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_route_dominance_frontier_refuter_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_ROUTE_DOMINANCE_FRONTIER_REFUTER_20260627.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "route_dominance_frontier_envelope_v1.tau"

ASSET_A = "A"
ASSET_B = "B"
ASSET_C = "C"
MAX_ROUTE_LABELS = 256


@dataclass(frozen=True)
class RouteLabel:
    route_id: str
    route: RouteQuote

    @property
    def objective_key(self) -> tuple[Any, ...]:
        return (int(self.route.amount_in), quote_key(self.route), self.route_id)


@dataclass(frozen=True)
class HostPacket:
    case_id: str
    pools: tuple[PoolState, ...]
    asset_in: str
    asset_out: str
    amount_out: int
    kept_route_ids: tuple[str, ...]
    pruned_route_ids: tuple[str, ...]
    selected_route_id: str
    declared_flags: Mapping[str, int]
    note: str


def _pool(pool_id: str, asset0: str, asset1: str, reserve0: int, reserve1: int, fee_bps: int = 30) -> PoolState:
    left = min(asset0, asset1)
    right = max(asset0, asset1)
    return PoolState(
        pool_id=pool_id,
        asset0=left,
        asset1=right,
        reserve0=int(reserve0 if asset0 == left else reserve1),
        reserve1=int(reserve1 if asset1 == right else reserve0),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _route_pools() -> tuple[PoolState, ...]:
    return tuple(
        sorted(
            (
                _pool("p_ab_direct_expensive", ASSET_A, ASSET_B, 800, 120, 30),
                _pool("p_ab_direct_deep", ASSET_A, ASSET_B, 5_000, 1_900, 30),
                _pool("p_ac", ASSET_A, ASSET_C, 3_000, 2_800, 30),
                _pool("p_cb", ASSET_C, ASSET_B, 3_400, 2_500, 30),
                _pool("p_ac_fee_heavy", ASSET_A, ASSET_C, 2_800, 2_000, 90),
            ),
            key=lambda pool: pool.pool_id,
        )
    )


def _quote_exact_out(pool: PoolState, *, asset_in: str, asset_out: str, amount_out: int) -> int | None:
    if int(amount_out) <= 0:
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        reserve_in, reserve_out = int(pool.reserve0), int(pool.reserve1)
    elif asset_in == pool.asset1 and asset_out == pool.asset0:
        reserve_in, reserve_out = int(pool.reserve1), int(pool.reserve0)
    else:
        return None
    try:
        amount_in, _next_reserves = swap_exact_out_for_pool(
            pool,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=int(amount_out),
        )
    except ValueError:
        return None
    return int(amount_in)


def _direct_label(pool: PoolState, *, asset_in: str, asset_out: str, amount_out: int) -> RouteLabel | None:
    amount_in = _quote_exact_out(pool, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)
    if amount_in is None:
        return None
    hop = RouteHop(pool.pool_id, asset_in, asset_out, int(amount_in), int(amount_out))
    route = RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(amount_in),
        amount_out=int(amount_out),
        legs=(RouteLeg(hops=(hop,), amount_in=int(amount_in), amount_out=int(amount_out)),),
    )
    return RouteLabel(route_id=f"direct:{pool.pool_id}", route=route)


def _two_hop_label(
    pool1: PoolState,
    pool2: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    amount_out: int,
) -> RouteLabel | None:
    if asset_in == pool1.asset0:
        mid = pool1.asset1
    elif asset_in == pool1.asset1:
        mid = pool1.asset0
    else:
        return None
    if mid in {asset_in, asset_out}:
        return None
    if not pool_connects(pool2, mid, asset_out):
        return None
    mid_in = _quote_exact_out(pool2, asset_in=mid, asset_out=asset_out, amount_out=amount_out)
    if mid_in is None:
        return None
    amount_in = _quote_exact_out(pool1, asset_in=asset_in, asset_out=mid, amount_out=mid_in)
    if amount_in is None:
        return None
    hop1 = RouteHop(pool1.pool_id, asset_in, mid, int(amount_in), int(mid_in))
    hop2 = RouteHop(pool2.pool_id, mid, asset_out, int(mid_in), int(amount_out))
    route = RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(amount_in),
        amount_out=int(amount_out),
        legs=(RouteLeg(hops=(hop1, hop2), amount_in=int(amount_in), amount_out=int(amount_out)),),
    )
    return RouteLabel(route_id=f"twohop:{pool1.pool_id}>{pool2.pool_id}", route=route)


def _split_label(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    amount_out: int,
    amount_out_0: int,
) -> RouteLabel | None:
    amount_out_1 = int(amount_out) - int(amount_out_0)
    if amount_out_0 <= 0 or amount_out_1 <= 0:
        return None
    in0 = _quote_exact_out(pool0, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out_0)
    in1 = _quote_exact_out(pool1, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out_1)
    if in0 is None or in1 is None:
        return None
    leg0 = RouteLeg(
        hops=(RouteHop(pool0.pool_id, asset_in, asset_out, int(in0), int(amount_out_0)),),
        amount_in=int(in0),
        amount_out=int(amount_out_0),
    )
    leg1 = RouteLeg(
        hops=(RouteHop(pool1.pool_id, asset_in, asset_out, int(in1), int(amount_out_1)),),
        amount_in=int(in1),
        amount_out=int(amount_out_1),
    )
    route = RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(in0) + int(in1),
        amount_out=int(amount_out),
        legs=(leg0, leg1),
    )
    return RouteLabel(
        route_id=f"split2:{pool0.pool_id}+{pool1.pool_id}:out0={int(amount_out_0)}",
        route=route,
    )


def enumerate_route_labels(
    pools: tuple[PoolState, ...],
    *,
    asset_in: str,
    asset_out: str,
    amount_out: int,
) -> tuple[RouteLabel, ...]:
    labels: dict[str, RouteLabel] = {}
    direct_pools = [pool for pool in pools if pool_connects(pool, asset_in, asset_out)]
    for pool in direct_pools:
        label = _direct_label(pool, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)
        if label is not None:
            labels[label.route_id] = label
    for pool1 in pools:
        for pool2 in pools:
            label = _two_hop_label(pool1, pool2, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)
            if label is not None:
                labels[label.route_id] = label
    for pool0, pool1 in combinations(direct_pools, 2):
        for amount_out_0 in range(1, int(amount_out)):
            label = _split_label(
                pool0,
                pool1,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out=amount_out,
                amount_out_0=amount_out_0,
            )
            if label is not None:
                labels[label.route_id] = label
    return tuple(sorted(labels.values(), key=lambda label: label.objective_key))


def _dominates(kept: RouteLabel, pruned: RouteLabel) -> bool:
    return kept.objective_key <= pruned.objective_key


def _sbf(value: bool) -> int:
    return 1 if value else 0


def _tau_step_from_flags(flags: Mapping[str, int]) -> dict[str, int]:
    return {f"i{idx}": int(flags.get(f"i{idx}", 0)) for idx in range(1, 12)}


def _all_true_flags() -> dict[str, int]:
    return {f"i{idx}": 1 for idx in range(1, 12)}


def verify_host_packet(packet: HostPacket) -> dict[str, Any]:
    labels = enumerate_route_labels(
        packet.pools,
        asset_in=packet.asset_in,
        asset_out=packet.asset_out,
        amount_out=packet.amount_out,
    )
    labels_by_id = {label.route_id: label for label in labels}
    full_ids = set(labels_by_id)
    kept_ids = set(packet.kept_route_ids)
    pruned_ids = set(packet.pruned_route_ids)
    selected_label = labels_by_id.get(packet.selected_route_id)
    kept_labels = [labels_by_id[route_id] for route_id in packet.kept_route_ids if route_id in labels_by_id]
    pruned_labels = [labels_by_id[route_id] for route_id in packet.pruned_route_ids if route_id in labels_by_id]

    selected_domain_nonempty = bool(kept_labels)
    every_pruned_has_dominator = all(
        any(_dominates(kept, pruned) for kept in kept_labels)
        for pruned in pruned_labels
    ) and pruned_ids.issubset(full_ids)
    argmin_ok = (
        selected_label is not None
        and bool(kept_labels)
        and selected_label.route_id == min(kept_labels, key=lambda label: label.objective_key).route_id
    )
    projection_cover_ok = kept_ids.isdisjoint(pruned_ids) and kept_ids | pruned_ids == full_ids
    exact_quote_replay_ok = kept_ids.issubset(full_ids) and pruned_ids.issubset(full_ids) and selected_label is not None
    rounding_model_ok = all(isinstance(label.route.amount_in, int) and label.route.amount_in > 0 for label in labels)
    resource_budget_ok = len(labels) <= MAX_ROUTE_LABELS
    fallback_ok = bool(packet.declared_flags.get("i10", 0))
    no_authority = bool(packet.declared_flags.get("i11", 0))

    computed_flags = {
        "i1": 1,
        "i2": _sbf(selected_domain_nonempty),
        "i3": _sbf(exact_quote_replay_ok),
        "i4": _sbf(every_pruned_has_dominator),
        "i5": _sbf(argmin_ok),
        "i6": _sbf(projection_cover_ok),
        "i7": _sbf(exact_quote_replay_ok),
        "i8": _sbf(rounding_model_ok),
        "i9": _sbf(resource_budget_ok),
        "i10": _sbf(fallback_ok),
        "i11": _sbf(no_authority),
    }
    failed_flags = [name for name, value in computed_flags.items() if int(value) != 1]
    best_full = labels[0] if labels else None
    return {
        "host_ok": not failed_flags,
        "computed_flags": computed_flags,
        "failed_flags": failed_flags,
        "route_label_count": len(labels),
        "best_full_route_id": best_full.route_id if best_full else None,
        "best_full_amount_in": int(best_full.route.amount_in) if best_full else None,
        "selected_route_id": packet.selected_route_id,
        "selected_amount_in": int(selected_label.route.amount_in) if selected_label else None,
        "kept_route_ids": list(packet.kept_route_ids),
        "pruned_route_ids": list(packet.pruned_route_ids),
        "missing_route_ids": sorted(full_ids - kept_ids - pruned_ids),
        "unknown_route_ids": sorted((kept_ids | pruned_ids | {packet.selected_route_id}) - full_ids),
        "labels": [_label_to_json(label) for label in labels],
    }


def _label_to_json(label: RouteLabel) -> dict[str, Any]:
    return {
        "route_id": label.route_id,
        "amount_in": int(label.route.amount_in),
        "amount_out": int(label.route.amount_out),
        "quote_key": list(quote_key(label.route)),
        "legs": [
            [
                {
                    "pool_id": hop.pool_id,
                    "asset_in": hop.asset_in,
                    "asset_out": hop.asset_out,
                    "amount_in": int(hop.amount_in),
                    "amount_out": int(hop.amount_out),
                }
                for hop in leg.hops
            ]
            for leg in label.route.legs
        ],
    }


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_steps(steps: list[dict[str, int]]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "case_outputs": []}
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=steps, timeout_s=10.0)
    return {
        "ok": True,
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "case_outputs": [outputs.get(idx, {}) for idx in range(len(steps))],
    }


def _packets() -> tuple[HostPacket, ...]:
    pools = _route_pools()
    amount_out = 42
    labels = enumerate_route_labels(pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=amount_out)
    best = labels[0]
    second = labels[1]
    third = labels[2]
    return (
        HostPacket(
            case_id="valid_best_only_dominates",
            pools=pools,
            asset_in=ASSET_A,
            asset_out=ASSET_B,
            amount_out=amount_out,
            kept_route_ids=(best.route_id,),
            pruned_route_ids=tuple(label.route_id for label in labels[1:]),
            selected_route_id=best.route_id,
            declared_flags=_all_true_flags(),
            note="The best full-domain route is kept; every pruned label has a kept dominator.",
        ),
        HostPacket(
            case_id="forged_pruned_winner_without_dominator",
            pools=pools,
            asset_in=ASSET_A,
            asset_out=ASSET_B,
            amount_out=amount_out,
            kept_route_ids=(second.route_id,),
            pruned_route_ids=tuple(label.route_id for label in labels if label.route_id != second.route_id),
            selected_route_id=second.route_id,
            declared_flags=_all_true_flags(),
            note="A forged packet prunes the true winner while declaring every proof-surface flag true.",
        ),
        HostPacket(
            case_id="forged_projection_cover_gap",
            pools=pools,
            asset_in=ASSET_A,
            asset_out=ASSET_B,
            amount_out=amount_out,
            kept_route_ids=(best.route_id,),
            pruned_route_ids=tuple(label.route_id for label in labels[1:] if label.route_id != third.route_id),
            selected_route_id=best.route_id,
            declared_flags=_all_true_flags(),
            note="A forged packet omits one non-winner route from both kept and pruned sets.",
        ),
    )


def run_refuter() -> dict[str, Any]:
    packets = _packets()
    declared_steps = [_tau_step_from_flags(packet.declared_flags) for packet in packets]
    host_rows = [verify_host_packet(packet) for packet in packets]
    computed_steps = [_tau_step_from_flags(row["computed_flags"]) for row in host_rows]
    tau_declared = _run_tau_steps(declared_steps)
    tau_computed = _run_tau_steps(computed_steps)
    cases: list[dict[str, Any]] = []
    false_declared_admits = 0
    computed_false_admits = 0
    for idx, packet in enumerate(packets):
        declared_output = tau_declared.get("case_outputs", [{}])[idx] if tau_declared.get("case_outputs") else {}
        computed_output = tau_computed.get("case_outputs", [{}])[idx] if tau_computed.get("case_outputs") else {}
        declared_tau_accepts = declared_output.get("o4") == 1
        computed_tau_accepts = computed_output.get("o4") == 1
        host_ok = bool(host_rows[idx]["host_ok"])
        false_declared_admits += int(declared_tau_accepts and not host_ok)
        computed_false_admits += int(computed_tau_accepts and not host_ok)
        cases.append(
            {
                "case_id": packet.case_id,
                "note": packet.note,
                "host_ok": host_ok,
                "declared_tau_accepts": declared_tau_accepts,
                "computed_tau_accepts": computed_tau_accepts,
                "declared_tau_output": declared_output,
                "computed_tau_output": computed_output,
                "host": host_rows[idx],
            }
        )
    return {
        "schema": "zenodex.route_dominance_frontier_refuter_report.v1",
        "ok": tau_declared.get("ok") is True and tau_computed.get("ok") is True and false_declared_admits == 2 and computed_false_admits == 0,
        "case_count": len(cases),
        "false_declared_admit_count": false_declared_admits,
        "computed_false_admit_count": computed_false_admits,
        "tau_declared": {key: value for key, value in tau_declared.items() if key != "case_outputs"},
        "tau_computed": {key: value for key, value in tau_computed.items() if key != "case_outputs"},
        "cases": cases,
        "non_claims": [
            "This is a bounded direct/two-hop/parallel-split route-label refuter, not an exhaustive all-route theorem.",
            "Tau checks declared proof-surface flags; host verification must compute those flags from route labels.",
            "The artifact does not authorize settlement and does not replace route quote replay.",
        ],
        "replay_command": "python3 tools/zenodex_route_dominance_frontier_refuter_20260627.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Route Dominance Frontier Refuter - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "This artifact checks the route-dominance Tau envelope against host-computed direct, two-hop, and parallel-split exact-out route labels."
    )
    lines.append(
        f"Cases: `{report['case_count']}`. Forged declared Tau admits: `{report['false_declared_admit_count']}`. Computed-flag false admits: `{report['computed_false_admit_count']}`. Overall: `ok={report['ok']}`."
    )
    lines.append("")
    lines.append("Result: Tau is a useful compact envelope only when its flags are produced by a host route-label verifier. Forged all-true flags can admit bad route packets.")
    lines.append("")
    lines.append("## Cases")
    lines.append("")
    lines.append("| case | host ok | Tau with declared flags | Tau with computed flags | failed host flags |")
    lines.append("| --- | --- | --- | --- | --- |")
    for row in report["cases"]:
        failed = ", ".join(f"`{flag}`" for flag in row["host"]["failed_flags"]) or "none"
        lines.append(
            f"| `{row['case_id']}` | `{row['host_ok']}` | `{row['declared_tau_accepts']}` | `{row['computed_tau_accepts']}` | {failed} |"
        )
    lines.append("")
    lines.append("## Best Route Evidence")
    lines.append("")
    for row in report["cases"]:
        host = row["host"]
        lines.append(
            f"- `{row['case_id']}`: selected `{host['selected_route_id']}` amount_in `{host['selected_amount_in']}`, full best `{host['best_full_route_id']}` amount_in `{host['best_full_amount_in']}`."
        )
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(str(report["replay_command"]))
    lines.append("```")
    lines.append("")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path, output_md: Path) -> dict[str, Any]:
    report = run_refuter()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(OUT_DIR / "report.json"))
    parser.add_argument("--output-md", default=str(REPORT_PATH))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "case_count": report["case_count"],
                "false_declared_admit_count": report["false_declared_admit_count"],
                "computed_false_admit_count": report["computed_false_admit_count"],
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
