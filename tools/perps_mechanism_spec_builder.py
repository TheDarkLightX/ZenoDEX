#!/usr/bin/env python3
"""Build a perps mechanism-design spec from Morph scientist artifacts.

The output is two files:
1) JSON spec (machine-readable, includes artifact links + lift metrics)
2) Markdown spec (human-readable policy/checklist)
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
from typing import Any


DEFAULT_ARTIFACTS: dict[str, str] = {
    "perp_oracle_manipulation_reward_subsidy": "runs/mech_sci_iter/loop_ab_r13_reward/perp_oracle_manipulation_reward_subsidy/ab_sweep.json",
    "perp_oracle_manipulation_lp": "runs/mech_sci_iter/loop_ab_r17_lp_reward/perp_oracle_manipulation_lp/ab_sweep.json",
    "perp_settlement_bounty_farming": "runs/mech_sci_iter/loop_ab_r18_exotic/perp_settlement_bounty_farming/ab_sweep.json",
    "perp_funding_rate_gaming": "runs/mech_sci_iter/loop_ab_r18_exotic/perp_funding_rate_gaming/ab_sweep.json",
    "perp_oracle_manipulation": "runs/mech_sci_iter/loop_ab_r8/perp_oracle_manipulation/ab_sweep.json",
    "perp_collateral_depeg": "runs/mech_sci_iter/spec_design_probe/perp_collateral_depeg/ab_sweep.json",
}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _infer_seed_count(payload: dict[str, Any]) -> int:
    seeds = payload.get("seeds")
    if isinstance(seeds, int):
        return seeds
    runs = payload.get("runs")
    if isinstance(runs, list):
        return len(runs)
    agg = payload.get("aggregate")
    if isinstance(agg, dict):
        seeds = agg.get("seeds")
        if isinstance(seeds, int):
            return seeds
    return 0


def _extract_metrics(payload: dict[str, Any]) -> dict[str, float | int]:
    agg = payload.get("aggregate")
    if not isinstance(agg, dict):
        agg = {}
    lift = agg.get("lift")
    if not isinstance(lift, dict):
        lift = {}
    with_portals = agg.get("with_portals")
    if not isinstance(with_portals, dict):
        with_portals = {}
    without_portals = agg.get("without_portals")
    if not isinstance(without_portals, dict):
        without_portals = {}
    return {
        "seeds": _infer_seed_count(payload),
        "has_lift_rate": float(lift.get("has_lift_rate", 0.0)),
        "solved_rate_delta": float(lift.get("solved_rate_delta", 0.0)),
        "avg_seconds_reduction": float(lift.get("avg_seconds_reduction", 0.0)),
        "with_avg_seconds": float(with_portals.get("avg_seconds", 0.0)),
        "without_avg_seconds": float(without_portals.get("avg_seconds", 0.0)),
    }


def _tier(
    *,
    has_lift_rate: float,
    solved_rate_delta: float,
    avg_seconds_reduction: float,
    promote_min: float,
    min_avg_seconds_reduction: float,
) -> str:
    if solved_rate_delta < 0.0:
        return "reject"
    if avg_seconds_reduction < min_avg_seconds_reduction:
        return "hold"
    if has_lift_rate >= promote_min:
        return "promote"
    if has_lift_rate > 0.0:
        return "explore"
    return "hold"


def _build_domain_rows(
    *,
    repo_root: Path,
    promote_min: float,
    min_avg_seconds_reduction: float,
    artifact_map: dict[str, str],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for domain, rel_path in artifact_map.items():
        abs_path = (repo_root / rel_path).resolve()
        if not abs_path.exists():
            rows.append(
                {
                    "domain": domain,
                    "artifact_path": rel_path,
                    "status": "missing",
                    "notes": "artifact_not_found",
                }
            )
            continue
        payload = _load_json(abs_path)
        m = _extract_metrics(payload)
        status = _tier(
            has_lift_rate=float(m["has_lift_rate"]),
            solved_rate_delta=float(m["solved_rate_delta"]),
            avg_seconds_reduction=float(m["avg_seconds_reduction"]),
            promote_min=promote_min,
            min_avg_seconds_reduction=min_avg_seconds_reduction,
        )
        rows.append(
            {
                "domain": domain,
                "artifact_path": rel_path,
                "status": status,
                "metrics": m,
            }
        )
    return rows


def _has_status(rows: list[dict[str, Any]], domain: str, statuses: set[str]) -> bool:
    for row in rows:
        if row.get("domain") == domain and row.get("status") in statuses:
            return True
    return False


def _build_spec(*, rows: list[dict[str, Any]], promote_min: float, min_avg_seconds_reduction: float) -> dict[str, Any]:
    reward_ok = _has_status(rows, "perp_oracle_manipulation_reward_subsidy", {"promote", "explore"})
    lp_ok = _has_status(rows, "perp_oracle_manipulation_lp", {"promote", "explore"})
    funding_ok = _has_status(rows, "perp_funding_rate_gaming", {"promote", "explore"})
    bounty_ok = _has_status(rows, "perp_settlement_bounty_farming", {"promote", "explore"})
    depeg_ok = _has_status(rows, "perp_collateral_depeg", {"promote", "explore"})

    clauses: list[dict[str, Any]] = [
        {
            "id": "C-USD-1",
            "title": "Collateral Value Floor",
            "required": True,
            "rule": (
                "Perp collateral is valued with deterministic haircut bands; opening/increasing positions must use "
                "haircut-adjusted collateral, not nominal quote balances."
            ),
        },
        {
            "id": "C-ORACLE-1",
            "title": "Signed + Fresh Oracle Inputs",
            "required": True,
            "rule": (
                "Clearing-price publication requires authorized signature + nonce + positive price; "
                "all position/funding state transitions fail closed on stale or non-positive index price."
            ),
        },
        {
            "id": "C-RWD-1",
            "title": "Reward Source Non-Recapturable",
            "required": bool(reward_ok),
            "rule": (
                "Any subsidy/rebate must be bounded by extracted protocol fees and never by recapturable LP fees "
                "or raw reported volume."
            ),
        },
        {
            "id": "C-LP-1",
            "title": "Attacker-As-LP Cost Model",
            "required": bool(lp_ok),
            "rule": (
                "Manipulation deterrence uses non-recapturable cost floor; risk checks assume attacker may own LP share "
                "and recapture pool fees."
            ),
        },
        {
            "id": "C-FUND-1",
            "title": "Funding Budget Balance",
            "required": bool(funding_ok),
            "rule": (
                "Funding application must preserve net funding budget balance across open accounts or fail closed."
            ),
        },
        {
            "id": "C-KEEPER-1",
            "title": "Keeper Bounty Anti-Farming",
            "required": bool(bounty_ok),
            "rule": (
                "Keeper bounty must satisfy `bounty <= collected_penalty` with notional/penalty floors and per-epoch caps."
            ),
        },
        {
            "id": "C-DEPEG-1",
            "title": "Depeg Stress Guardrails",
            "required": bool(depeg_ok),
            "rule": (
                "Maintain dynamic leverage and maintenance requirements under collateral depeg stress; "
                "trigger deterministic breaker/deleveraging when haircut-adjusted margin fails."
            ),
        },
    ]

    return {
        "spec_id": "perp_mechanism_scientist_v1",
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "promotion_gate": {
            "has_lift_rate_min": float(promote_min),
            "solved_rate_delta_min": 0.0,
            "avg_seconds_reduction_min": float(min_avg_seconds_reduction),
        },
        "domain_evidence": rows,
        "mechanism_clauses": clauses,
        "rollout_policy": {
            "promote": "Only enable production knobs for domains with status=promote.",
            "explore": "Allow shadow-mode measurements; do not make safety-critical policy relaxations.",
            "hold_or_reject": "No policy expansion; keep strict fail-closed defaults.",
        },
    }


def _fmt_pct(x: float) -> str:
    return f"{(100.0 * x):.1f}%"


def _render_markdown(spec: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Perps Mechanism Spec (Morph Mechanical Scientist)")
    lines.append("")
    lines.append("This spec is generated from Morph A/B evidence and defines which incentive/game-theory clauses are eligible for promotion.")
    lines.append("")
    lines.append("## Evidence Tiers")
    lines.append("")
    lines.append("| Domain | Status | has_lift_rate | solved_rate_delta | avg_seconds_reduction | Artifact |")
    lines.append("|---|---:|---:|---:|---:|---|")
    for row in spec.get("domain_evidence", []):
        domain = str(row.get("domain", ""))
        status = str(row.get("status", ""))
        artifact_path = str(row.get("artifact_path", ""))
        metrics = row.get("metrics")
        if isinstance(metrics, dict):
            has_lift_rate = _fmt_pct(float(metrics.get("has_lift_rate", 0.0)))
            solved_rate_delta = f"{float(metrics.get('solved_rate_delta', 0.0)):.3f}"
            avg_seconds_reduction = f"{float(metrics.get('avg_seconds_reduction', 0.0)):.6f}"
        else:
            has_lift_rate = "-"
            solved_rate_delta = "-"
            avg_seconds_reduction = "-"
        lines.append(
            f"| `{domain}` | `{status}` | {has_lift_rate} | {solved_rate_delta} | {avg_seconds_reduction} | `{artifact_path}` |"
        )
    lines.append("")
    lines.append("## Required Protocol Guarantees")
    lines.append("")
    for clause in spec.get("mechanism_clauses", []):
        if not isinstance(clause, dict):
            continue
        flag = "required" if bool(clause.get("required", False)) else "standby"
        lines.append(
            f"- `{clause.get('id')}` ({flag}): **{clause.get('title')}**. {clause.get('rule')}"
        )
    lines.append("")
    lines.append("## Stable Settlement + Price Feed Baseline")
    lines.append("")
    lines.append("- Settlement asset must have deterministic valuation policy (haircuts/depeg bands) applied in margin checks.")
    lines.append("- Oracle publication must be signed, replay-protected, and stale-price fail-closed.")
    lines.append("- Funding/liquidation incentives must remain revenue-bounded and non-farmable under attacker-as-LP assumptions.")
    lines.append("")
    lines.append("## Promotion Gate")
    lines.append("")
    gate = spec.get("promotion_gate", {})
    lines.append(
        f"- `has_lift_rate >= {float(gate.get('has_lift_rate_min', 0.8)):.2f}`, "
        f"`solved_rate_delta >= {float(gate.get('solved_rate_delta_min', 0.0)):.2f}`, "
        f"and `avg_seconds_reduction >= {float(gate.get('avg_seconds_reduction_min', 0.0)):.6f}`."
    )
    lines.append("- Promote only `status=promote`; others remain shadow-mode or blocked.")
    lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description="Build perps mechanism-design spec from Morph A/B artifacts.")
    ap.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--promote-min-lift-rate", type=float, default=0.8)
    ap.add_argument("--min-avg-seconds-reduction", type=float, default=0.0)
    ap.add_argument(
        "--out-json",
        type=Path,
        default=Path("runs/mech_sci_iter/spec_design/perp_mechanism_scientist_spec_v1.json"),
    )
    ap.add_argument(
        "--out-md",
        type=Path,
        default=Path("docs/derivatives/PERP_MECHANISM_SCIENTIST_SPEC_V1.md"),
    )
    args = ap.parse_args()

    repo_root = args.repo_root.resolve()
    rows = _build_domain_rows(
        repo_root=repo_root,
        promote_min=float(args.promote_min_lift_rate),
        min_avg_seconds_reduction=float(args.min_avg_seconds_reduction),
        artifact_map=DEFAULT_ARTIFACTS,
    )
    spec = _build_spec(
        rows=rows,
        promote_min=float(args.promote_min_lift_rate),
        min_avg_seconds_reduction=float(args.min_avg_seconds_reduction),
    )

    out_json = (repo_root / args.out_json).resolve()
    out_md = (repo_root / args.out_md).resolve()
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_md.parent.mkdir(parents=True, exist_ok=True)

    out_json.write_text(json.dumps(spec, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out_md.write_text(_render_markdown(spec), encoding="utf-8")
    print(json.dumps({"ok": True, "out_json": str(out_json), "out_md": str(out_md)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
