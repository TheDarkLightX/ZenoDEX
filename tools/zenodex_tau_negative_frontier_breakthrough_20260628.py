#!/usr/bin/env python3
"""Replay a Tau-gated negative-frontier campaign breakthrough."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.zenodex_negative_frontier_entropy_scheduler_20260628 import (  # noqa: E402
    REPORT_JSON as SCHEDULER_JSON,
)
from tools.zenodex_negative_frontier_entropy_scheduler_20260628 import (
    REPORT_MD as SCHEDULER_MD,
)
from tools.zenodex_negative_frontier_entropy_scheduler_20260628 import (
    run as run_scheduler_report,
)
from tools.zenodex_tau_solver_portfolio_breakthrough_20260628 import (  # noqa: E402
    _build_report as build_solver_portfolio_report,
)
from tools.zenodex_tauspec_ebrm_baseline_breakthrough_20260628 import (  # noqa: E402
    _build_report as build_tauspec_ebrm_report,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_negative_frontier_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_NEGATIVE_FRONTIER_BREAKTHROUGH_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "negative_frontier_entropy_campaign_certificate_v1.tau"


FACT_ORDER = (
    "certificate_active",
    "bounded_corpus_ok",
    "entropy_beats_recency_ok",
    "entropy_not_worse_than_random_ok",
    "deterministic_replay_ok",
    "severity_floor_ok",
    "work_item_1_ab_covered",
    "work_item_2_cow_covered",
    "tau_runtime_subset_ok",
    "negative_controls_pass",
    "evidence_artifacts_bound",
    "advisory_model_only",
    "no_authority_effect",
)


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_json_command(args: Sequence[str], *, timeout_s: float) -> dict[str, Any]:
    proc = subprocess.run(
        list(args),
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=float(timeout_s),
        check=False,
    )
    if proc.returncode != 0:
        return {
            "ok": False,
            "returncode": int(proc.returncode),
            "stdout": proc.stdout[-4000:],
            "stderr": proc.stderr[-4000:],
        }
    try:
        parsed = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {
            "ok": False,
            "returncode": int(proc.returncode),
            "error": f"non-json output: {exc}",
            "stdout": proc.stdout[-4000:],
            "stderr": proc.stderr[-4000:],
        }
    parsed["returncode"] = int(proc.returncode)
    return parsed


def _control_ok(scheduler: Mapping[str, Any], case_id: str) -> bool:
    for control in scheduler["negative_controls"]:
        if control["case_id"] == case_id:
            return bool(control["ok"])
    return False


def _facts(
    *,
    scheduler: Mapping[str, Any],
    solver_portfolio: Mapping[str, Any],
    tauspec_ebrm: Mapping[str, Any],
    tau_compat: Mapping[str, Any],
) -> dict[str, int]:
    authority = scheduler["authority_boundary"]
    work_items = solver_portfolio["work_items"]
    ebrm_work = tauspec_ebrm["breakthrough"]["work_items_covered"]
    ab_covered = (
        work_items["1_ab_ordering"]["status"] == "covered"
        and bool(ebrm_work["AB"])
        and solver_portfolio["tau"]["invalid_accepts"] == 0
    )
    cow_covered = (
        work_items["2_cow_matching"]["status"] == "covered"
        and bool(ebrm_work["CoW"])
        and solver_portfolio["tau"]["invalid_accepts"] == 0
    )
    all_negative_controls = all(bool(control["ok"]) for control in scheduler["negative_controls"])
    return {
        "certificate_active": 1,
        "bounded_corpus_ok": int(
            scheduler["policy"]["bounded_corpus_axis_count"] == 125
            and scheduler["policy"]["budget"] == 10
            and scheduler["schedules"]["entropy"]["axis_count"] == 10
        ),
        "entropy_beats_recency_ok": int(_control_ok(scheduler, "entropy_beats_recency_unique_families")),
        "entropy_not_worse_than_random_ok": int(_control_ok(scheduler, "entropy_beats_random_unique_families")),
        "deterministic_replay_ok": int(
            _control_ok(scheduler, "deterministic_replay")
            and int(solver_portfolio["tau"]["invalid_accepts"]) == 0
            and int(tauspec_ebrm["selection_tau"]["invalid_accepts"]) == 0
        ),
        "severity_floor_ok": int(_control_ok(scheduler, "severity_floor_preserved")),
        "work_item_1_ab_covered": int(ab_covered),
        "work_item_2_cow_covered": int(cow_covered),
        "tau_runtime_subset_ok": int(bool(tau_compat.get("ok"))),
        "negative_controls_pass": int(
            all_negative_controls
            and bool(solver_portfolio["tau"]["ok"])
            and bool(tauspec_ebrm["selection_tau"]["ok"])
        ),
        "evidence_artifacts_bound": int(TAU_SPEC.exists() and SCHEDULER_JSON.exists() and SCHEDULER_MD.exists()),
        "advisory_model_only": int(bool(authority["advisory_only"])),
        "no_authority_effect": int(
            bool(authority["no_runtime_authority"])
            and bool(authority["no_settlement_authority"])
            and bool(authority["no_governance_authority"])
            and int(solver_portfolio["portfolio_facts"]["no_authority_effect"]) == 1
        ),
    }


def _step_from_facts(facts: Mapping[str, int]) -> dict[str, int]:
    return {f"i{idx}": int(facts[name]) for idx, name in enumerate(FACT_ORDER, start=1)}


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = _step_from_facts(facts)
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "campaign_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All scheduler, work-item, runtime, artifact, advisory, and no-authority facts hold.",
        ),
        TauCase(
            "recency_baseline_reject",
            {**pass_step, "i3": 0},
            {"o1": 0, "o4": 0},
            "A campaign that does not beat the collapsed recency baseline is rejected.",
        ),
        TauCase(
            "random_baseline_reject",
            {**pass_step, "i4": 0},
            {"o1": 0, "o4": 0},
            "A campaign that loses the stable-random diversity control is rejected.",
        ),
        TauCase(
            "determinism_reject",
            {**pass_step, "i5": 0},
            {"o1": 0, "o4": 0},
            "A campaign without deterministic replay cannot admit.",
        ),
        TauCase(
            "severity_floor_reject",
            {**pass_step, "i6": 0},
            {"o1": 0, "o4": 0},
            "Entropy cannot pass by selecting below the declared severity floor.",
        ),
        TauCase(
            "ab_work_item_reject",
            {**pass_step, "i7": 0},
            {"o2": 0, "o4": 0},
            "The campaign certificate remains tied to work item 1 AB ordering coverage.",
        ),
        TauCase(
            "cow_work_item_reject",
            {**pass_step, "i8": 0},
            {"o2": 0, "o4": 0},
            "The campaign certificate remains tied to work item 2 CoW matching coverage.",
        ),
        TauCase(
            "tau_runtime_subset_reject",
            {**pass_step, "i9": 0},
            {"o3": 0, "o4": 0},
            "The latest Tau-supported runtime subset must be explicitly acknowledged.",
        ),
        TauCase(
            "negative_controls_reject",
            {**pass_step, "i10": 0},
            {"o1": 0, "o4": 0},
            "Negative controls are part of the admission surface, not a side note.",
        ),
        TauCase(
            "authority_reject",
            {**pass_step, "i13": 0},
            {"o3": 0, "o4": 0, "o5": 0},
            "A Tau research certificate cannot carry settlement, governance, oracle, or runtime authority.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o4": 0, "o5": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        ),
    )


def _run_tau(facts: Mapping[str, int], tau_bin: str | None) -> dict[str, Any]:
    cases = _tau_cases(facts)
    if not tau_bin:
        return {
            "ok": False,
            "error": "latest Tau binary not found",
            "case_results": [],
            "invalid_accepts": 0,
        }
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=15.0,
    )
    invalid_accepts = 0
    case_results: list[dict[str, Any]] = []
    ok = True
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        expected_primary = int(case.expected.get("o4", 0))
        if expected_primary == 0 and got.get("o4") == 1:
            invalid_accepts += 1
        if mismatches:
            ok = False
        case_results.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    return {
        "ok": ok and invalid_accepts == 0,
        "case_results": case_results,
        "invalid_accepts": invalid_accepts,
    }


def build_report() -> dict[str, Any]:
    scheduler = run_scheduler_report(SCHEDULER_JSON, SCHEDULER_MD)
    solver_portfolio = build_solver_portfolio_report()
    tauspec_ebrm = build_tauspec_ebrm_report()
    tau_compat = _run_json_command([sys.executable, "tools/check_tau_latest_stream_compat.py"], timeout_s=30.0)
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    facts = _facts(
        scheduler=scheduler,
        solver_portfolio=solver_portfolio,
        tauspec_ebrm=tauspec_ebrm,
        tau_compat=tau_compat,
    )
    tau = _run_tau(facts, tau_bin)
    ok = bool(
        all(value == 1 for value in facts.values())
        and scheduler["ok"]
        and solver_portfolio["ok"]
        and tauspec_ebrm["selection_tau"]["ok"]
        and tau_compat.get("ok") is True
        and tau["ok"]
    )
    entropy = scheduler["schedules"]["entropy"]
    recency = scheduler["schedules"]["recency"]
    stable_random = scheduler["schedules"]["stable_random"]
    return {
        "schema": "zenodex.tau_negative_frontier_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Tau-gated negative-frontier entropy campaign certificate",
            "spec_id": "negative_frontier_entropy_campaign_certificate_v1",
            "summary": (
                "Tau now gates an advisory falsifier-campaign scheduler that selects high-severity "
                "negative-frontier axes by entropy gain while preserving deterministic replay, "
                "AB/CoW work-item coverage, runtime-subset compatibility, and no-authority rails."
            ),
            "authority_boundary": "Tau admits the research campaign certificate only. Host/kernel verifiers remain authoritative for settlement, oracle updates, governance, balances, and state roots.",
        },
        "tau": {
            "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
            "tau_bin": tau_bin,
            "tau_version": _tau_version(tau_bin),
            **tau,
        },
        "certificate_facts": facts,
        "scheduler": {
            "report_json": str(SCHEDULER_JSON.relative_to(REPO_ROOT)),
            "report_md": str(SCHEDULER_MD.relative_to(REPO_ROOT)),
            "bounded_corpus_axis_count": scheduler["policy"]["bounded_corpus_axis_count"],
            "budget": scheduler["policy"]["budget"],
            "entropy_unique_family_count": entropy["unique_family_count"],
            "recency_unique_family_count": recency["unique_family_count"],
            "stable_random_unique_family_count": stable_random["unique_family_count"],
            "entropy_post_schedule_nats": entropy["post_schedule_entropy_nats"],
            "recency_post_schedule_nats": recency["post_schedule_entropy_nats"],
            "priority_min": entropy["priority_min"],
            "selected_axis_ids": entropy["axis_ids"],
            "negative_controls": scheduler["negative_controls"],
        },
        "work_items": {
            "1_ab_ordering": solver_portfolio["work_items"]["1_ab_ordering"],
            "2_cow_matching": solver_portfolio["work_items"]["2_cow_matching"],
            "solver_portfolio_tau_invalid_accepts": solver_portfolio["tau"]["invalid_accepts"],
            "tauspec_ebrm_work_items": tauspec_ebrm["breakthrough"]["work_items_covered"],
            "ab_n12_proxy_ratio": solver_portfolio["supporting_reports"]["ab_n12_proxy_ratio"],
            "cow_n20_proxy_ratio": solver_portfolio["supporting_reports"]["cow_n20_proxy_ratio"],
        },
        "tau_runtime_frontier": {
            "latest_stream_compat_ok": tau_compat.get("ok") is True,
            "runtime_rule": tau_compat.get("runtime_rule"),
            "rows": tau_compat.get("rows", []),
        },
        "new_tau_specifications": [
            {
                "spec": "src/tau_specs/recommended/negative_frontier_entropy_campaign_certificate_v1.tau",
                "benefit": "Turns negative-frontier campaign selection into an executable, fail-closed Tau certificate.",
            },
            {
                "spec": "src/tau_specs/recommended/solver_portfolio_upgrade_certificate_v1.tau",
                "benefit": "Keeps AB ordering and CoW matching upgrades behind parity, scope, performance, fallback, rollback, and no-authority facts.",
            },
            {
                "spec": "src/tau_specs/recommended/tauspec_ebrm_frontier_selection_certificate_v1.tau",
                "benefit": "Ranks high-value Tau specs while requiring AB/CoW coverage, zero invalid accepts, deterministic replay, and profile-budget compliance.",
            },
        ],
        "non_claims": [
            "The entropy scheduler is advisory and does not prove that selected tasks will find bugs.",
            "Tau does not compute entropy, matching, DP, CPMM arithmetic, hashes, or timing budgets in this artifact.",
            "The latest Tau runtime still rejects stream add/sub shapes, so arithmetic-heavy obligations stay host-side as named facts.",
            "The AB and CoW statements remain within their declared scoped solver surfaces.",
        ],
        "replay_commands": [
            "python3 tools/zenodex_tau_negative_frontier_breakthrough_20260628.py",
            "python3 tools/zenodex_negative_frontier_entropy_scheduler_20260628.py",
            "python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py",
            "python3 tools/zenodex_tauspec_ebrm_baseline_breakthrough_20260628.py",
            "python3 tools/check_tau_latest_stream_compat.py",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Negative-Frontier Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append("## Tau Certificate")
    lines.append("")
    tau = report["tau"]
    lines.append(f"- Spec: `{tau['spec_path']}`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau cases: `{len(tau['case_results'])}`")
    lines.append(f"- Invalid accepts: `{tau['invalid_accepts']}`")
    lines.append("")
    lines.append("Certificate facts:")
    for key, value in report["certificate_facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.append("")
    lines.append("## Scheduler Evidence")
    lines.append("")
    scheduler = report["scheduler"]
    lines.append(f"- Bounded corpus axes: `{scheduler['bounded_corpus_axis_count']}`")
    lines.append(f"- Budget: `{scheduler['budget']}`")
    lines.append(f"- Entropy unique families: `{scheduler['entropy_unique_family_count']}`")
    lines.append(f"- Recency unique families: `{scheduler['recency_unique_family_count']}`")
    lines.append(f"- Stable-random unique families: `{scheduler['stable_random_unique_family_count']}`")
    lines.append(f"- Entropy post-schedule nats: `{scheduler['entropy_post_schedule_nats']:.6f}`")
    lines.append(f"- Recency post-schedule nats: `{scheduler['recency_post_schedule_nats']:.6f}`")
    lines.append(f"- Priority floor observed: `{scheduler['priority_min']}`")
    lines.append("")
    lines.append("Selected axes:")
    for axis_id in scheduler["selected_axis_ids"]:
        lines.append(f"- `{axis_id}`")
    lines.append("")
    lines.append("## Work Items 1 And 2")
    lines.append("")
    work = report["work_items"]
    lines.append("### 1. AB Ordering")
    lines.append("")
    lines.append(work["1_ab_ordering"]["evidence"])
    lines.append(work["1_ab_ordering"]["non_claim"])
    lines.append(f"AB n=12 permutation-vs-state-reduction proxy ratio: `{work['ab_n12_proxy_ratio']}`.")
    lines.append("")
    lines.append("### 2. CoW Matching")
    lines.append("")
    lines.append(work["2_cow_matching"]["evidence"])
    lines.append(work["2_cow_matching"]["non_claim"])
    lines.append(f"CoW n=20 perfect-matching-vs-Hungarian proxy ratio: `{work['cow_n20_proxy_ratio']}`.")
    lines.append("")
    lines.append("## What Tau Can Do For ZenoDEX")
    lines.append("")
    for item in report["new_tau_specifications"]:
        lines.append(f"- `{item['spec']}`: {item['benefit']}")
    lines.append("")
    lines.append("The current Tau runtime profile supports the safe boolean guard surface used here. Arithmetic-heavy checks remain host-computed facts.")
    lines.append("")
    lines.append("## Tau Runtime Frontier")
    lines.append("")
    runtime = report["tau_runtime_frontier"]
    lines.append(f"- Latest stream compatibility ok: `{runtime['latest_stream_compat_ok']}`")
    lines.append(f"- Runtime rule: {runtime['runtime_rule']}")
    lines.append("")
    lines.append("## Tau Negative Cases")
    lines.append("")
    lines.append("| case | ok | primary output |")
    lines.append("| --- | --- | ---: |")
    for case in tau["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o4')}` |")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    for command in report["replay_commands"]:
        lines.append(command)
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON, output_md: Path = REPORT_MD) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def main() -> int:
    report = run()
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "spec": report["tau"]["spec_path"],
                "tau_cases": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
                "entropy_unique_families": report["scheduler"]["entropy_unique_family_count"],
                "recency_unique_families": report["scheduler"]["recency_unique_family_count"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
