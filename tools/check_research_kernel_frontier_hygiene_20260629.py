#!/usr/bin/env python3
"""Build a local receipt for Research Kernel frontier closure after the n8 chain."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = REPO_ROOT / "generated" / "zenodex_research_kernel_frontier_hygiene_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_RESEARCH_KERNEL_FRONTIER_HYGIENE_20260629.md"
)

CHAIN_REPORT = (
    "generated/zenodex_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629/report.json"
)
EXPECTED_CHAIN_REPORT_HASH = (
    "229620cd20b3c08561bc0d4766199c3687041be3bf6a15cf3ee79a050199a64c"
)
EXPECTED_CHAIN_INDEX_HASH = (
    "7f6d4c6e21fe5118485de7094b27994a5fee96bc6f2db3c4273374d64ef159bb"
)
EXPECTED_GENERATION_DIGEST = (
    "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
)
EXPECTED_MEMBERSHIP_DIGEST = (
    "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2"
)
EXPECTED_WITNESS_DIGEST = (
    "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
)
EXPECTED_TRANSITION_DIGEST = (
    "0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09"
)
EXPECTED_MANIFEST_HASH = (
    "db94660eb8c859821de08b629371e3c056b2469d707b94df56854a5f41f17394"
)


class ReceiptError(ValueError):
    """Raised when the local hygiene receipt cannot be trusted."""


@dataclass(frozen=True)
class ClosureSpec:
    closure_id: str
    frontier_atom_id: str
    frontier_status: str
    closure_kind: str
    summary: str
    resolver_artifacts: tuple[str, ...]
    report_path: str
    replay_command: tuple[str, ...]
    validator: Callable[[Mapping[str, Any]], dict[str, Any]]


@dataclass(frozen=True)
class OpenFrontierSpec:
    frontier_atom_id: str
    frontier_status: str
    reason_open: str
    unblock_plan: str


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _repo_path(path: str) -> Path:
    full = (REPO_ROOT / path).resolve()
    if full != REPO_ROOT and REPO_ROOT not in full.parents:
        raise ReceiptError(f"path escapes repo: {path}")
    return full


def _require_tracked(path: str) -> dict[str, str]:
    full = _repo_path(path)
    if not full.exists():
        raise ReceiptError(f"missing artifact: {path}")
    proc = subprocess.run(
        ["git", "ls-files", "--error-unmatch", path],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise ReceiptError(f"artifact is not tracked by git: {path}")
    return {"path": path, "sha256": _sha256(full)}


def _load_report(path: str) -> dict[str, Any]:
    full = _repo_path(path)
    if not full.exists():
        raise ReceiptError(f"missing generated report: {path}")
    data = json.loads(full.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ReceiptError(f"generated report is not an object: {path}")
    return data


def _require(condition: bool, reason: str, checks: dict[str, Any]) -> None:
    checks[reason] = bool(condition)
    if not condition:
        raise ReceiptError(reason)


def _all_flags_true(flags: Mapping[str, Any]) -> bool:
    return bool(flags) and all(value == 1 or value is True for value in flags.values())


def _non_claims_text(report: Mapping[str, Any]) -> str:
    return "\n".join(str(item) for item in report.get("non_claims", [])).lower()


def _validate_chain_base(report: Mapping[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    _require(
        report.get("schema")
        == "zenodex.ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_report.v1",
        "schema_ok",
        checks,
    )
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(report.get("tau", {}).get("invalid_accepts") == 0, "invalid_accepts_zero", checks)
    _require(_all_flags_true(report.get("facts", {})), "facts_all_true", checks)
    _require(report.get("chain_index_sha256") == EXPECTED_CHAIN_INDEX_HASH, "chain_index_pinned", checks)
    _require(_sha256(_repo_path(CHAIN_REPORT)) == EXPECTED_CHAIN_REPORT_HASH, "chain_report_hash_pinned", checks)
    counts = report.get("chain_counts", {})
    _require(counts.get("stage_tau_report_count") == 5, "stage_count_ok", checks)
    _require(counts.get("sampled_child_mask_count") == 51, "sampled_mask_count_ok", checks)
    _require(counts.get("sampled_child_state_count") == 88, "sampled_state_count_ok", checks)
    _require(counts.get("predecessor_transition_count") == 268, "transition_count_ok", checks)
    non_claims = _non_claims_text(report)
    _require("does not prove exhaustive n=8 coverage" in non_claims, "exhaustive_nonclaim_present", checks)
    _require("does not prove python-to-lean refinement" in non_claims, "lean_refinement_nonclaim_present", checks)
    _require("does not authorize settlement" in non_claims, "authority_nonclaim_present", checks)
    return checks


def _validate_canonical_merkle_risk(report: Mapping[str, Any]) -> dict[str, Any]:
    checks = _validate_chain_base(report)
    stages = report.get("stage_summary", {})
    digests = report.get("chain_digests", {})
    _require(stages.get("canonical_merkle", {}).get("tau_ok") is True, "canonical_tau_ok", checks)
    _require(stages.get("canonical_merkle", {}).get("invalid_accepts") == 0, "canonical_invalid_zero", checks)
    _require(digests.get("generation_frontier_rows_digest") == EXPECTED_GENERATION_DIGEST, "generation_digest_ok", checks)
    _require(digests.get("canonical_membership_rows_digest") == EXPECTED_MEMBERSHIP_DIGEST, "membership_digest_ok", checks)
    return checks


def _validate_bidirectional_transition_risk(report: Mapping[str, Any]) -> dict[str, Any]:
    checks = _validate_chain_base(report)
    stages = report.get("stage_summary", {})
    digests = report.get("chain_digests", {})
    _require(
        stages.get("bidirectional_transition", {}).get("tau_ok") is True,
        "transition_tau_ok",
        checks,
    )
    _require(
        stages.get("bidirectional_transition", {}).get("invalid_accepts") == 0,
        "transition_invalid_zero",
        checks,
    )
    _require(digests.get("transition_rows_digest") == EXPECTED_TRANSITION_DIGEST, "transition_digest_ok", checks)
    _require(digests.get("witness_rows_digest") == EXPECTED_WITNESS_DIGEST, "witness_digest_ok", checks)
    _require(digests.get("canonical_membership_rows_digest") == EXPECTED_MEMBERSHIP_DIGEST, "membership_digest_ok", checks)
    return checks


def _validate_tau_specification_candidate(report: Mapping[str, Any]) -> dict[str, Any]:
    checks = _validate_chain_base(report)
    stages = report.get("stage_summary", {})
    _require(stages.get("generation", {}).get("tau_ok") is True, "generation_tau_ok", checks)
    _require(stages.get("canonical_merkle", {}).get("tau_ok") is True, "canonical_tau_ok", checks)
    _require(stages.get("witness_compression", {}).get("tau_ok") is True, "witness_tau_ok", checks)
    _require(stages.get("bidirectional_transition", {}).get("tau_ok") is True, "transition_tau_ok", checks)
    _require(stages.get("producer", {}).get("tau_ok") is True, "producer_tau_ok", checks)
    _require(report.get("chain_digests", {}).get("producer_manifest_hash") == EXPECTED_MANIFEST_HASH, "manifest_hash_ok", checks)
    return checks


def _validate_proof_object_candidate(report: Mapping[str, Any]) -> dict[str, Any]:
    checks = _validate_chain_base(report)
    breakthrough = report.get("breakthrough", {})
    claims = "\n".join(str(item) for item in breakthrough.get("scoped_claims", [])).lower()
    _require("five sampled n=8 stage tau reports" in claims, "five_stage_claim_present", checks)
    _require("chain index" in claims, "chain_index_claim_present", checks)
    _require("zero invalid accepts" in claims, "invalid_accepts_claim_present", checks)
    _require(report.get("chain_digests", {}).get("producer_manifest_hash") == EXPECTED_MANIFEST_HASH, "producer_manifest_ok", checks)
    return checks


def closure_specs() -> tuple[ClosureSpec, ...]:
    resolver_artifacts = (
        "tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py",
        "tests/tau/test_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py",
        "src/tau_specs/recommended/ab_child_frontier_proof_object_chain_n8_sample_scope_certificate_v1.tau",
        "docs/research/ZENODEX_AB_CHILD_FRONTIER_PROOF_OBJECT_CHAIN_N8_SAMPLE_TAU_CERTIFICATE_20260629.md",
    )
    replay_command = (
        "python3",
        "tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py",
    )
    return (
        ClosureSpec(
            closure_id="n8_chain_resolves_canonical_merkle_refutation_risk",
            frontier_atom_id="atom_ef1f5b6ebed246eb",
            frontier_status="UNDER_TEST",
            closure_kind="resolves",
            summary=(
                "The n8 proof-object chain certificate resolves the sampled canonical-Merkle risk by requiring "
                "the canonical stage Tau report, frontier and membership digests, linked generation digest, "
                "negative cases, and no-authority facts."
            ),
            resolver_artifacts=resolver_artifacts,
            report_path=CHAIN_REPORT,
            replay_command=replay_command,
            validator=_validate_canonical_merkle_risk,
        ),
        ClosureSpec(
            closure_id="n8_chain_resolves_bidirectional_transition_refutation_risk",
            frontier_atom_id="atom_d64b2781e6604d77",
            frontier_status="UNDER_TEST",
            closure_kind="resolves",
            summary=(
                "The n8 proof-object chain certificate resolves the sampled bidirectional-transition risk by requiring "
                "the transition Tau report, transition digest, linked witness digest, linked Merkle membership digest, "
                "negative cases, and no-authority facts."
            ),
            resolver_artifacts=resolver_artifacts,
            report_path=CHAIN_REPORT,
            replay_command=replay_command,
            validator=_validate_bidirectional_transition_risk,
        ),
        ClosureSpec(
            closure_id="n8_chain_specializes_tau_specification_reformulation",
            frontier_atom_id="atom_e4b9b11387894204",
            frontier_status="CANDIDATE",
            closure_kind="specializes",
            summary=(
                "The n8 proof-object chain specializes the Tau-specification reformulation into a concrete "
                "five-stage Tau envelope over generation, canonical Merkle, witness compression, transition, "
                "and producer reports."
            ),
            resolver_artifacts=resolver_artifacts,
            report_path=CHAIN_REPORT,
            replay_command=replay_command,
            validator=_validate_tau_specification_candidate,
        ),
        ClosureSpec(
            closure_id="n8_chain_specializes_proof_object_compression_reformulation",
            frontier_atom_id="atom_41092f7feb7f4df8",
            frontier_status="CANDIDATE",
            closure_kind="specializes",
            summary=(
                "The n8 proof-object chain specializes the proof-object-compression reformulation into a "
                "hash-pinned chain index with five stage reports, shared counts, cross-stage digests, and "
                "producer manifest links."
            ),
            resolver_artifacts=resolver_artifacts,
            report_path=CHAIN_REPORT,
            replay_command=replay_command,
            validator=_validate_proof_object_candidate,
        ),
    )


def open_frontier_specs() -> tuple[OpenFrontierSpec, ...]:
    return (
        OpenFrontierSpec(
            frontier_atom_id="atom_f16f64e92cd14d74",
            frontier_status="UNDER_TEST",
            reason_open="n7 Tau scope refutation risk is separate from the sampled n8 proof-object chain.",
            unblock_plan="Replay the n7 Tau certificate risk against its own source report and add an explicit RK edge if it closes.",
        ),
        OpenFrontierSpec(
            frontier_atom_id="atom_e867f667225442a4",
            frontier_status="UNDER_TEST",
            reason_open="n7 bidirectional transition mutation risk is separate from the sampled n8 transition chain.",
            unblock_plan="Build or replay a n7-specific chain/transition closure receipt with mutation controls.",
        ),
        OpenFrontierSpec(
            frontier_atom_id="atom_c0f2558fe81046cf",
            frontier_status="UNDER_TEST",
            reason_open="record-set monotone-reserve dominance is a Lean/record-set claim, not covered by the n8 child-frontier chain.",
            unblock_plan="Run a dedicated refutation pass over the record-set certificate and register the outcome.",
        ),
        OpenFrontierSpec(
            frontier_atom_id="atom_5e7aa160e5604f79",
            frontier_status="UNDER_TEST",
            reason_open="observed-summary bridge scope is not implied by the n8 child-frontier proof-object chain.",
            unblock_plan="Replay the observed-summary bridge and check stale overclaims separately.",
        ),
        OpenFrontierSpec(
            frontier_atom_id="atom_0641a88159d6456b",
            frontier_status="UNDER_TEST",
            reason_open="reserve-state observed-summary bridge scope is not implied by the n8 child-frontier proof-object chain.",
            unblock_plan="Replay the reserve-state observed-summary bridge and add a closure row only if its own checks pass.",
        ),
    )


def _rk_edge_type_for(spec: ClosureSpec) -> str:
    if spec.frontier_status == "UNDER_TEST":
        return "SUPERSEDES"
    if spec.frontier_status == "CANDIDATE":
        return "SPECIALIZES"
    return "SUPPORTS"


def _refresh_reports(specs: Sequence[ClosureSpec]) -> None:
    seen: set[tuple[str, ...]] = set()
    for spec in specs:
        if spec.replay_command in seen:
            continue
        seen.add(spec.replay_command)
        proc = subprocess.run(
            list(spec.replay_command),
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
            timeout=180,
        )
        if proc.returncode != 0:
            raise ReceiptError(
                f"refresh failed for {' '.join(spec.replay_command)}\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
            )


def build_report(*, refresh: bool = False) -> dict[str, Any]:
    specs = closure_specs()
    if refresh:
        _refresh_reports(specs)

    closures: list[dict[str, Any]] = []
    for spec in specs:
        artifacts = [_require_tracked(path) for path in spec.resolver_artifacts]
        report = _load_report(spec.report_path)
        checks = spec.validator(report)
        closures.append(
            {
                "closure_id": spec.closure_id,
                "frontier_atom_id": spec.frontier_atom_id,
                "frontier_status": spec.frontier_status,
                "closure_kind": spec.closure_kind,
                "summary": spec.summary,
                "resolver_artifacts": artifacts,
                "report_path": spec.report_path,
                "report_sha256": _sha256(_repo_path(spec.report_path)),
                "replay_command": " ".join(spec.replay_command),
                "checks": checks,
                "closed": all(checks.values()),
            }
        )

    open_items = [
        {
            "frontier_atom_id": item.frontier_atom_id,
            "frontier_status": item.frontier_status,
            "reason_open": item.reason_open,
            "unblock_plan": item.unblock_plan,
        }
        for item in open_frontier_specs()
    ]
    report = {
        "schema": "zenodex.research_kernel_frontier_hygiene_20260629.v1",
        "date": "2026-06-29",
        "ok": bool(closures) and all(row["closed"] for row in closures),
        "closure_count": len(closures),
        "open_frontier_count": len(open_items),
        "resolved_count": sum(1 for row in closures if row["closure_kind"] == "resolves"),
        "specialized_count": sum(1 for row in closures if row["closure_kind"] == "specializes"),
        "closures": closures,
        "open_frontier": open_items,
        "research_kernel_edges_to_add": [
            {
                "source_atom_id": "atom_zenodex_research_kernel_frontier_hygiene_20260629",
                "target_atom_id": row["frontier_atom_id"],
                "edge_type": _rk_edge_type_for(
                    next(spec for spec in specs if spec.frontier_atom_id == row["frontier_atom_id"])
                ),
                "closure_kind": row["closure_kind"],
                "rationale": row["summary"],
            }
            for row in closures
        ],
        "non_claims": [
            "This receipt does not mutate Research Kernel frontier ranking by itself; explicit RK edges are required.",
            "This receipt closes only the listed n8 sampled child-frontier items.",
            "This receipt intentionally leaves unrelated n7, observed-summary, and record-set risks open.",
            "This receipt records research-evidence closure only and grants no settlement, governance, state-root, or production authority.",
            "Generated report JSON files are replay outputs; tracked source artifacts and replay commands are the durable evidence handles.",
        ],
        "replay_command": "python3 tools/check_research_kernel_frontier_hygiene_20260629.py",
        "refresh_command": "python3 tools/check_research_kernel_frontier_hygiene_20260629.py --refresh",
    }
    if not report["ok"]:
        raise ReceiptError("one or more closure rows failed")
    return report


def write_json_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown_report(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX Research Kernel Frontier Hygiene - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "A local closure map now connects the sampled n=8 child-frontier proof-object chain certificate to the Research Kernel frontier items it actually covers.",
        "The receipt also lists frontier items that remain open, so the map improves discovery without broadening the supported claim.",
        "",
        f"- Closure rows: `{report['closure_count']}`",
        f"- Resolved rows: `{report['resolved_count']}`",
        f"- Specialized rows: `{report['specialized_count']}`",
        f"- Open frontier rows retained: `{report['open_frontier_count']}`",
        "",
        "## Closure Map",
        "",
        "| frontier atom | closure kind | resolver |",
        "| --- | --- | --- |",
    ]
    for row in report["closures"]:
        lines.append(
            f"| `{row['frontier_atom_id']}` | `{row['closure_kind']}` | `{row['closure_id']}` |"
        )
    lines.extend(
        [
            "",
            "## Open Frontier",
            "",
            "| frontier atom | reason open | next action |",
            "| --- | --- | --- |",
        ]
    )
    for row in report["open_frontier"]:
        lines.append(
            f"| `{row['frontier_atom_id']}` | {row['reason_open']} | {row['unblock_plan']} |"
        )
    lines.extend(
        [
            "",
            "## Research Kernel Edges To Add",
            "",
            "| target atom | edge type | closure kind |",
            "| --- | --- | --- |",
        ]
    )
    for edge in report["research_kernel_edges_to_add"]:
        lines.append(
            f"| `{edge['target_atom_id']}` | `{edge['edge_type']}` | `{edge['closure_kind']}` |"
        )
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(
        [
            "",
            "## Replay",
            "",
            "```bash",
            str(report["replay_command"]),
            "```",
            "",
            "Refresh prerequisite report first:",
            "",
            "```bash",
            str(report["refresh_command"]),
            "```",
            "",
        ]
    )
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true", help="rebuild prerequisite generated reports before checking")
    parser.add_argument("--json-only", action="store_true", help="suppress markdown and human summary output")
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        report = build_report(refresh=args.refresh)
        write_json_report(report)
        if not args.json_only:
            write_markdown_report(report)
    except ReceiptError as exc:
        print(f"research-kernel frontier hygiene check failed: {exc}", file=sys.stderr)
        return 1

    if not args.json_only:
        print(
            json.dumps(
                {
                    "ok": report["ok"],
                    "closure_count": report["closure_count"],
                    "open_frontier_count": report["open_frontier_count"],
                    "report": str(REPORT_JSON.relative_to(REPO_ROOT)),
                },
                indent=2,
                sort_keys=True,
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
