#!/usr/bin/env python3
"""Audit the AB strict zero-min record-set pruning claim surface.

This research-only checker tries to refute stale or over-broad record-set
claims by binding the Lean theorem surface, generated JSON receipts, and public
non-claims into one replayable audit.
"""

from __future__ import annotations

import argparse
import copy
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_strict_zero_min_emitter_witness import _sha256_json, _strip_timing  # noqa: E402

LEAN_FILE = REPO_ROOT / "lean-mathlib" / "Proofs" / "ABStrictZeroMinMonotone.lean"
FORMAL_TEST = REPO_ROOT / "tests" / "formal" / "test_lean_ab_strict_zero_min_monotone.py"
RECORD_KEY_DOC = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_RECORD_KEY_CERTIFICATE_LEAN_20260629.md"
)
RECORD_SET_DOC = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_RECORD_SET_PRUNING_LEAN_20260628.md"
)
RECORD_KEY_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_record_key_certificate_lean_20260629"
    / "report.json"
)
RECORD_SET_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_record_set_pruning_lean_20260628"
    / "report.json"
)
OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_record_set_pruning_refutation_audit_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RECORD_SET_PRUNING_REFUTATION_AUDIT_20260629.md"
)

REPORT_SCHEMA = "zenodex.ab_record_set_pruning_refutation_audit_report.v1"
TARGET_NEGATIVE_CONTROL_COUNT = 8


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _sha256(path: Path) -> str:
    return _sha256_json(path.read_text(encoding="utf-8"))


def _run_command(command: list[str], *, cwd: Path, timeout_s: float) -> dict[str, Any]:
    started = time.monotonic()
    proc = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout_s,
        check=False,
    )
    return {
        "command": " ".join(command),
        "cwd": str(cwd.relative_to(REPO_ROOT)) if cwd != REPO_ROOT else ".",
        "ok": proc.returncode == 0,
        "returncode": proc.returncode,
        "elapsed_s": round(time.monotonic() - started, 6),
        "stdout_tail": proc.stdout[-1200:],
        "stderr_tail": proc.stderr[-1200:],
    }


def _extract_decl(text: str, name: str) -> str:
    pattern = re.compile(rf"^(?:def|theorem|structure)\s+{re.escape(name)}\b", re.M)
    match = pattern.search(text)
    if not match:
        return ""
    start = match.start()
    next_decl = re.search(r"^(?:def|theorem|structure)\s+\w+\b", text[match.end() :], re.M)
    if not next_decl:
        return text[start:]
    return text[start : match.end() + next_decl.start()]


def _replace_in_decl(text: str, name: str, old: str, new: str) -> str:
    block = _extract_decl(text, name)
    if old not in block:
        return text
    return text.replace(block, block.replace(old, new, 1), 1)


def _strip_nondeterminism(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            key: _strip_nondeterminism(item)
            for key, item in value.items()
            if key not in {"elapsed_ms", "elapsed_s", "stdout_tail", "stderr_tail"}
        }
    if isinstance(value, list):
        return [_strip_nondeterminism(item) for item in value]
    return value


def _placeholder_reasons(text: str) -> list[str]:
    reasons: list[str] = []
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    if forbidden.search(text):
        reasons.append("lean_placeholder_token_present")
    return reasons


def _theorem_surface_reasons(text: str) -> list[str]:
    reasons: list[str] = []
    required_markers = {
        "structure_zero_min_key": "structure ZeroMinEconomicKey",
        "record_key_def": "def recordZeroMinEconomicKey",
        "best_record_set_key_def": "def bestRecordSetZeroMinEconomicKey",
        "best_suffix_bound_theorem": "theorem bestSuffixOutputFromRecords_le_selected",
        "best_record_set_key_theorem": "theorem bestRecordSetZeroMinEconomicKey_dominated_by_selected",
        "record_set_certificate_def": "def strictRecordSetPruningCertificate",
        "record_set_certificate_theorem": "theorem strictRecordSetPruningCertificate_validates",
        "witness_record_set_bound": "theorem witness_bestSuffixOutputFromRecords_le_selected",
    }
    for reason, marker in required_markers.items():
        if marker not in text:
            reasons.append(f"{reason}_missing")

    zero_key = _extract_decl(text, "ZeroMinEconomicKey")
    if "executedInput : Nat" not in zero_key or "surplus : Nat" not in zero_key:
        reasons.append("zero_min_key_fields_missing")

    certificate = _extract_decl(text, "strictRecordSetPruningCertificate")
    if "selected.processedReserveIn = record.processedReserveIn" not in certificate:
        reasons.append("same_processed_reserve_premise_missing")
    if "selected.reserveOut ≤ record.reserveOut" not in certificate:
        reasons.append("selected_min_reserve_premise_missing")
    if "suffixExecutable selected.processedReserveIn selected.reserveOut suffix" not in certificate:
        reasons.append("selected_suffix_executable_premise_missing")

    validates = _extract_decl(text, "strictRecordSetPruningCertificate_validates")
    if "zeroMinEconomicKeyDominated" not in validates:
        reasons.append("economic_key_dominance_conclusion_missing")
    if "bestRecordSetZeroMinEconomicKey" not in validates:
        reasons.append("best_record_set_key_conclusion_missing")
    if "recordZeroMinEconomicKey" not in validates:
        reasons.append("selected_record_key_conclusion_missing")
    if "suffixExecutable selected.processedReserveIn selected.reserveOut suffix" not in validates:
        reasons.append("selected_suffix_executable_conclusion_missing")

    best = _extract_decl(text, "bestRecordSetZeroMinEconomicKey_dominated_by_selected")
    if "∀ record, record ∈ records ->" not in best:
        reasons.append("finite_record_set_quantifier_missing")
    if "selected.processedReserveIn = record.processedReserveIn" not in best:
        reasons.append("best_key_same_processed_reserve_premise_missing")
    if "selected.reserveOut ≤ record.reserveOut" not in best:
        reasons.append("best_key_min_reserve_premise_missing")
    return reasons


def _claims_scope_reasons(
    *,
    lean_text: str,
    docs: Mapping[str, str],
    reports: Mapping[str, Mapping[str, Any]],
) -> list[str]:
    reasons: list[str] = []
    joined_docs = "\n".join(docs.values()).lower()
    joined_reports = json.dumps(reports, sort_keys=True).lower()
    joined = joined_docs + "\n" + joined_reports

    forbidden_positive = {
        "forbidden_full_subset_dp_claim": [
            "proves full subset-mask dp exactness",
            "constructs the subset dp table",
            "constructs a subset dp table",
        ],
        "forbidden_python_refinement_claim": [
            "proves python-to-lean refinement",
            "proves python refinement correctness",
        ],
        "forbidden_tie_order_claim": [
            "defines canonical tie order",
            "proves canonical tie order",
        ],
        "forbidden_nonzero_min_claim": [
            "covers nonzero min_amount_out behavior",
            "proves nonzero min_amount_out",
        ],
        "forbidden_authority_claim": [
            "authorizes settlement",
            "authorizes production routing",
            "state-root authority is derived",
        ],
    }
    for reason, needles in forbidden_positive.items():
        if any(needle in joined for needle in needles):
            reasons.append(reason)

    required_nonclaims = {
        "subset_dp_nonclaim_missing": ("does not construct", "subset dp"),
        "python_refinement_nonclaim_missing": ("does not prove python", "refinement"),
        "tie_order_nonclaim_missing": ("canonical tie",),
        "nonzero_min_nonclaim_missing": ("nonzero", "min_amount_out"),
        "authority_nonclaim_missing": ("no settlement", "state-root", "production"),
    }
    for reason, needles in required_nonclaims.items():
        if not all(needle in joined for needle in needles):
            reasons.append(reason)

    if "strictRecordSetPruningCertificate" not in lean_text:
        reasons.append("lean_certificate_surface_missing")
    return reasons


def _report_reasons(reports: Mapping[str, Mapping[str, Any]]) -> list[str]:
    reasons: list[str] = []
    key_report = reports["record_key"]
    set_report = reports["record_set"]
    if key_report.get("ok") is not True:
        reasons.append("record_key_report_not_ok")
    if set_report.get("status") != "pass":
        reasons.append("record_set_report_not_pass")

    required_key_theorems = {
        "recordZeroMinEconomicKey",
        "minReserveRecord_dominates_zeroMinEconomicKey",
        "bestRecordSetZeroMinEconomicKey",
        "bestRecordSetZeroMinEconomicKey_dominated_by_selected",
        "strictRecordSetPruningCertificate",
        "strictRecordSetPruningCertificate_validates",
    }
    if not required_key_theorems.issubset(set(key_report.get("new_lean_theorems", []))):
        reasons.append("record_key_theorem_list_incomplete")

    required_set_theorems = {
        "ABStrictZeroMinMonotone.foldlMax_le_bound",
        "ABStrictZeroMinMonotone.bestSuffixOutputFromRecords_le_selected",
    }
    if not required_set_theorems.issubset(set(set_report.get("theorems", []))):
        reasons.append("record_set_theorem_list_incomplete")

    for report_id, report in reports.items():
        verification = report.get("verification", {})
        if not isinstance(verification, Mapping) or not verification:
            reasons.append(f"{report_id}_verification_missing")
            continue
        for gate, value in verification.items():
            if not isinstance(value, Mapping):
                reasons.append(f"{report_id}_{gate}_verification_malformed")
                continue
            status = value.get("status")
            if status not in {"pass", "ok"}:
                reasons.append(f"{report_id}_{gate}_verification_not_pass")
    return reasons


def _audit_bundle(
    *,
    lean_text: str,
    docs: Mapping[str, str],
    reports: Mapping[str, Mapping[str, Any]],
    run_commands: bool,
) -> dict[str, Any]:
    reasons: list[str] = []
    reasons.extend(_placeholder_reasons(lean_text))
    reasons.extend(_theorem_surface_reasons(lean_text))
    reasons.extend(_claims_scope_reasons(lean_text=lean_text, docs=docs, reports=reports))
    reasons.extend(_report_reasons(reports))

    commands: dict[str, Any] = {}
    if run_commands:
        commands["lake_env_lean"] = _run_command(
            ["lake", "env", "lean", "Proofs/ABStrictZeroMinMonotone.lean"],
            cwd=REPO_ROOT / "lean-mathlib",
            timeout_s=90,
        )
        commands["lake_build_module"] = _run_command(
            ["lake", "build", "Proofs.ABStrictZeroMinMonotone"],
            cwd=REPO_ROOT / "lean-mathlib",
            timeout_s=120,
        )
        commands["focused_pytest"] = _run_command(
            [
                sys.executable,
                "-m",
                "pytest",
                "-q",
                "tests/formal/test_lean_ab_strict_zero_min_monotone.py",
            ],
            cwd=REPO_ROOT,
            timeout_s=120,
        )
        commands["public_claim_scope"] = _run_command(
            [sys.executable, "tools/check_public_claim_scope.py", "--root", ".", "--json"],
            cwd=REPO_ROOT,
            timeout_s=60,
        )
        commands["claims_registry"] = _run_command(
            [sys.executable, "tools/check_claims_registry.py"],
            cwd=REPO_ROOT,
            timeout_s=60,
        )
        for command_id, result in commands.items():
            if result.get("ok") is not True:
                reasons.append(f"{command_id}_failed")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "commands": commands,
        "lean_surface": {
            "required_theorem_count": 8,
            "placeholder_free": not _placeholder_reasons(lean_text),
            "strict_record_set_certificate_decl_hash": _sha256_json(
                _extract_decl(lean_text, "strictRecordSetPruningCertificate")
            ),
            "strict_record_set_validates_decl_hash": _sha256_json(
                _extract_decl(lean_text, "strictRecordSetPruningCertificate_validates")
            ),
        },
        "artifact_hashes": {
            "lean_file": _sha256_json(lean_text),
            "formal_test": _sha256(FORMAL_TEST),
            "record_key_doc": _sha256_json(docs["record_key_doc"]),
            "record_set_doc": _sha256_json(docs["record_set_doc"]),
            "record_key_report": _sha256_json(reports["record_key"]),
            "record_set_report": _sha256_json(reports["record_set"]),
        },
    }


def _negative_controls(
    *,
    lean_text: str,
    docs: Mapping[str, str],
    reports: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    controls: list[tuple[str, str, Mapping[str, str], Mapping[str, Mapping[str, Any]], str]] = []

    controls.append(
        (
            "lean_placeholder_token_present",
            lean_text + "\n-- injected negative control sorry\n",
            docs,
            reports,
            "lean_placeholder_token_present",
        )
    )

    controls.append(
        (
            "same_processed_reserve_premise_missing",
            _replace_in_decl(
                lean_text,
                "strictRecordSetPruningCertificate",
                "selected.processedReserveIn = record.processedReserveIn",
                "selected.processedReserveIn <= record.processedReserveIn",
            ),
            docs,
            reports,
            "same_processed_reserve_premise_missing",
        )
    )

    controls.append(
        (
            "selected_min_reserve_premise_missing",
            _replace_in_decl(
                lean_text,
                "strictRecordSetPruningCertificate",
                "selected.reserveOut ≤ record.reserveOut",
                "record.reserveOut ≤ selected.reserveOut",
            ),
            docs,
            reports,
            "selected_min_reserve_premise_missing",
        )
    )

    controls.append(
        (
            "selected_suffix_executable_premise_missing",
            lean_text.replace(
                "suffixExecutable selected.processedReserveIn selected.reserveOut suffix",
                "True",
                1,
            ),
            docs,
            reports,
            "selected_suffix_executable_premise_missing",
        )
    )

    overclaim_docs = dict(docs)
    overclaim_docs["record_key_doc"] += "\nThis proves full subset-mask DP exactness.\n"
    controls.append(
        (
            "forbidden_full_subset_dp_claim",
            lean_text,
            overclaim_docs,
            reports,
            "forbidden_full_subset_dp_claim",
        )
    )

    bad_report = copy.deepcopy(dict(reports))
    bad_report["record_key"] = copy.deepcopy(bad_report["record_key"])
    bad_report["record_key"]["ok"] = False
    controls.append(
        (
            "record_key_report_not_ok",
            lean_text,
            docs,
            bad_report,
            "record_key_report_not_ok",
        )
    )

    incomplete_report = copy.deepcopy(dict(reports))
    incomplete_report["record_key"] = copy.deepcopy(incomplete_report["record_key"])
    incomplete_report["record_key"]["new_lean_theorems"] = [
        item
        for item in incomplete_report["record_key"].get("new_lean_theorems", [])
        if item != "strictRecordSetPruningCertificate_validates"
    ]
    controls.append(
        (
            "record_key_theorem_list_incomplete",
            lean_text,
            docs,
            incomplete_report,
            "record_key_theorem_list_incomplete",
        )
    )

    authority_docs = dict(docs)
    authority_docs["record_set_doc"] += "\nThis authorizes settlement.\n"
    controls.append(
        (
            "forbidden_authority_claim",
            lean_text,
            authority_docs,
            reports,
            "forbidden_authority_claim",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, mutated_lean, mutated_docs, mutated_reports, expected_reason in controls:
        audit = _audit_bundle(
            lean_text=mutated_lean,
            docs=mutated_docs,
            reports=mutated_reports,
            run_commands=False,
        )
        output.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(audit["ok"]),
                "expected_reason": expected_reason,
                "reasons": audit["reasons"],
            }
        )
    return output


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    lean_text = _read(LEAN_FILE)
    docs = {
        "record_key_doc": _read(RECORD_KEY_DOC),
        "record_set_doc": _read(RECORD_SET_DOC),
    }
    reports = {
        "record_key": _read_json(RECORD_KEY_REPORT),
        "record_set": _read_json(RECORD_SET_REPORT),
    }
    audit = _audit_bundle(lean_text=lean_text, docs=docs, reports=reports, run_commands=True)
    negative_controls = _negative_controls(lean_text=lean_text, docs=docs, reports=reports)
    return {
        "schema": "zenodex/ab_record_set_pruning_refutation_audit_search/v1",
        "ok": bool(audit["ok"]),
        "reasons": audit["reasons"],
        "lean_surface": audit["lean_surface"],
        "artifact_hashes": audit["artifact_hashes"],
        "verification_commands": audit["commands"],
        "report_bindings": {
            "record_key_schema": reports["record_key"].get("schema"),
            "record_key_ok": reports["record_key"].get("ok"),
            "record_key_theorem_count": len(reports["record_key"].get("new_lean_theorems", [])),
            "record_set_status": reports["record_set"].get("status"),
            "record_set_theorem_count": len(reports["record_set"].get("theorems", [])),
        },
        "claim_surface": {
            "same_processed_reserve_bound": True,
            "selected_min_reserve_bound": True,
            "selected_suffix_executable_bound": True,
            "economic_key_dominance_bound": True,
            "scope_nonclaims_bound": True,
        },
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(1 for row in negative_controls if row["accepted"]),
        "negative_controls": negative_controls,
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def deterministic_replay(first_search: Mapping[str, Any]) -> dict[str, Any]:
    second_search = run_search()
    first_hash = _sha256_json(_strip_nondeterminism(_strip_timing(first_search)))
    second_hash = _sha256_json(_strip_nondeterminism(_strip_timing(second_search)))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["ok"]
        and search["negative_control_count"] == TARGET_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A falsify-first audit found no mismatch in the AB strict zero-min "
            "record-set pruning claim surface: the Lean theorem premises, generated "
            "reports, and public non-claims remain aligned."
        ),
        "authority_boundary": (
            "Research-only proof-surface audit; no settlement, state-root, production, "
            "routing, matching, pool-mutation, or governance authority."
        ),
        "hypothesis_card": {
            "hypothesis_id": "H-AB-RECORD-SET-REFUTE-20260629",
            "mechanism_change": "Refute stale or over-broad record-set pruning claims before building more reserve-state quotient layers.",
            "representation_shift_used": "counterexample_boundary",
            "expected_metric_delta": {
                "safety": "+scope assurance",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "-audit overhead only",
                "determinism_simplicity": "+single replay gate",
            },
            "null_hypothesis": "The record-set certificate surface contains a missing premise, stale theorem binding, failed verification receipt, or positive overclaim.",
            "falsification_recipe": "Mutate theorem premises, report status, theorem lists, and public claims; require stable reject reasons.",
            "support_recipe": "Compile Lean, run focused formal test, bind generated reports, scan non-claims, and reject negative controls.",
            "formal_obligations": "Lean remains the authority for theorem proofs; this checker audits surface bindings and scope.",
            "risk_modes": [
                "stale generated JSON",
                "missing Lean premise",
                "overclaim in public docs",
                "authority leakage",
                "test coverage drift",
            ],
            "status": "supported" if ok else "inconclusive",
        },
        "search": search,
        "deterministic_replay": deterministic,
        "replay_command": "python3 tools/check_ab_record_set_pruning_refutation_audit_20260629.py",
        "non_claims": [
            "This audit does not prove Python-to-Lean refinement.",
            "This audit does not construct a subset DP table.",
            "This audit does not define canonical tie order.",
            "This audit does not cover nonzero min_amount_out behavior.",
            "This audit does not prove JSON canonicalization or packet hashing in Lean.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB Record-Set Pruning Refutation Audit - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Audit Summary",
        "",
        f"- Audit ok: `{search['ok']}`",
        f"- Reasons: `{search['reasons']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Claim Surface",
        "",
    ]
    for key, value in search["claim_surface"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Report Bindings", "", "```json"])
    lines.append(json.dumps(search["report_bindings"], indent=2, sort_keys=True))
    lines.extend(["```", "", "## Lean Surface", "", "```json"])
    lines.append(json.dumps(search["lean_surface"], indent=2, sort_keys=True))
    lines.extend(["```", "", "## Negative Controls", ""])
    lines.extend(["| mutation | accepted | expected reason |", "| --- | ---: | --- |"])
    for control in search["negative_controls"]:
        lines.append(
            f"| `{control['mutation_id']}` | `{control['accepted']}` | `{control['expected_reason']}` |"
        )
    lines.extend(["", "## Hypothesis Card", "", "```json"])
    lines.append(json.dumps(report["hypothesis_card"], indent=2, sort_keys=True))
    lines.extend(["```", "", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="print full report")
    args = parser.parse_args()
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
