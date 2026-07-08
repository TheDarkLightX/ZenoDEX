#!/usr/bin/env python3
"""Replay the AB transition-group compression Lean-bridge Tau certificate."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

_TAU_RUNNER_SPEC = importlib.util.spec_from_file_location(
    "zenodex_tau_runner_direct", REPO_ROOT / "src" / "integration" / "tau_runner.py"
)
if _TAU_RUNNER_SPEC is None or _TAU_RUNNER_SPEC.loader is None:
    raise RuntimeError("could not load tau_runner.py")
_TAU_RUNNER = importlib.util.module_from_spec(_TAU_RUNNER_SPEC)
sys.modules[_TAU_RUNNER_SPEC.name] = _TAU_RUNNER
_TAU_RUNNER_SPEC.loader.exec_module(_TAU_RUNNER)
find_tau_bin = _TAU_RUNNER.find_tau_bin
run_tau_spec_steps = _TAU_RUNNER.run_tau_spec_steps

SPEC_ID = "ab_transition_group_compression_lean_bridge_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
LEAN_BRIDGE_TOOL = REPO_ROOT / "tools" / "check_ab_transition_group_compression_lean_bridge_20260629.py"
LEAN_BRIDGE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_transition_group_compression_lean_bridge_20260629"
    / "report.json"
)
UPSTREAM_TAU_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_transition_group_compression_tau_certificate_20260629"
    / "report.json"
)
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_transition_group_compression_lean_bridge_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_TRANSITION_GROUP_COMPRESSION_LEAN_BRIDGE_TAU_CERTIFICATE_20260629.md"
)

EXPECTED_LEAN_BRIDGE_SCHEMA = "zenodex/ab_transition_group_compression_lean_bridge/v1"
EXPECTED_LEAN_BRIDGE_REPORT_HASH = "ce267d142cbbf67ebcfd31580f9c12852d19f7700547db5418472a31ceaac5f1"
EXPECTED_LEAN_FILE_HASH = "sha256:71b6325c1db9cde527a9c26e7b53f76d56d1b9f4cedb79079e8ade98f3c57d98"
EXPECTED_AGGREGATOR_HASH = "sha256:57868a31fffe2ecb6e3f8028efdee91c5d2ced53863b9c838ef804cefb0dce04"
EXPECTED_FORMAL_TEST_HASH = "sha256:32244a83355331c366a0f9b6d80800a7ba48499aff190f5f923067404c733dd0"
EXPECTED_REQUIRED_LEAN_MARKER_COUNT = 14
EXPECTED_UPSTREAM_SCHEMA = (
    "zenodex.ab_child_frontier_transition_group_compression_tau_certificate_report.v1"
)
EXPECTED_UPSTREAM_REPORT_HASH = "9ca5e4b8ab6f368d1fdd00347e5ca734ee6841f769891488e5fb43dfa591a7d2"
EXPECTED_UPSTREAM_SPEC_ID = "ab_child_frontier_transition_group_compression_scope_certificate_v1"
EXPECTED_UPSTREAM_TAU_CASES = 15
EXPECTED_UPSTREAM_SOURCE_ROWS = 2_777
EXPECTED_UPSTREAM_COMPRESSED_ROWS = 864


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _display_path(path: str | Path | None) -> str | None:
    if path is None:
        return None
    resolved = Path(path).resolve()
    try:
        return str(resolved.relative_to(REPO_ROOT))
    except ValueError:
        return str(resolved)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _run_command(args: list[str], cwd: Path, timeout_s: int) -> dict[str, Any]:
    proc = subprocess.run(
        args,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout_s,
        check=False,
    )
    ok = proc.returncode == 0
    return {
        "command": " ".join(args),
        "cwd": _display_path(cwd),
        "returncode": proc.returncode,
        "ok": ok,
        "stdout_tail": "" if ok else proc.stdout[-2000:],
        "stderr_tail": "" if ok else proc.stderr[-2000:],
    }


def _refresh_lean_bridge_report() -> dict[str, Any]:
    proc = _run_command(
        [sys.executable, str(LEAN_BRIDGE_TOOL.relative_to(REPO_ROOT))],
        REPO_ROOT,
        120,
    )
    if not proc["ok"]:
        return {"ok": False, "refresh": proc}
    report = _read_json(LEAN_BRIDGE_REPORT)
    report["refresh"] = proc
    return report


def _text_contains_all(text: str, needles: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return all(needle.lower() in lowered for needle in needles)


def _authority_boundary_ok(report: Mapping[str, Any]) -> bool:
    text = " ".join(
        [
            str(report.get("authority_boundary", "")),
            " ".join(str(item) for item in report.get("non_claims", [])),
        ]
    ).lower()
    return (
        "research proof component" in text
        and "no settlement" in text
        and "state-root" in text
        and "production" in text
        and "governance" in text
        and "routing" in text
        and "matching" in text
        and "pool-mutation" in text
    )


def _upstream_compression_tau_binding_ok(upstream: Mapping[str, Any], upstream_hash: str) -> bool:
    compression = upstream.get("compression", {})
    breakthrough = upstream.get("breakthrough", {})
    tau = upstream.get("tau", {})
    return (
        upstream.get("schema") == EXPECTED_UPSTREAM_SCHEMA
        and upstream_hash == EXPECTED_UPSTREAM_REPORT_HASH
        and bool(tau.get("ok")) is True
        and int(tau.get("invalid_accepts", -1)) == 0
        and breakthrough.get("spec_id") == EXPECTED_UPSTREAM_SPEC_ID
        and int(breakthrough.get("tau_cases", -1)) == EXPECTED_UPSTREAM_TAU_CASES
        and int(compression.get("source_transition_row_count", -1))
        == EXPECTED_UPSTREAM_SOURCE_ROWS
        and int(compression.get("compressed_row_count", -1)) == EXPECTED_UPSTREAM_COMPRESSED_ROWS
    )


def _fact_bundle(
    lean_report: Mapping[str, Any],
    lean_report_hash: str,
    upstream_report: Mapping[str, Any],
    upstream_hash: str,
    lean_compile: Mapping[str, Any],
    formal_test: Mapping[str, Any],
) -> dict[str, int]:
    artifacts = lean_report.get("artifacts", {})
    checks = lean_report.get("checks", {})
    missing = lean_report.get("missing", {})
    non_claims_text = " ".join(str(item) for item in lean_report.get("non_claims", []))
    replay_commands = lean_report.get("replay_commands", [])
    required_markers = lean_report.get("required_lean_markers", [])

    lean_bridge_report_ok = (
        bool(lean_report.get("ok")) is True
        and lean_report.get("schema") == EXPECTED_LEAN_BRIDGE_SCHEMA
        and lean_report_hash == EXPECTED_LEAN_BRIDGE_REPORT_HASH
    )
    lean_file_pinned = (
        artifacts.get("lean_file") == "lean-mathlib/Proofs/ABTransitionGroupCompression.lean"
        and artifacts.get("lean_sha256") == EXPECTED_LEAN_FILE_HASH
        and int(artifacts.get("lean_line_count", -1)) > 0
    )
    aggregator_import_bound = (
        bool(checks.get("aggregator_import_present")) is True
        and artifacts.get("aggregator") == "lean-mathlib/Proofs.lean"
        and artifacts.get("aggregator_sha256") == EXPECTED_AGGREGATOR_HASH
    )
    theorem_surface_bound = (
        bool(checks.get("required_lean_markers_present")) is True
        and isinstance(required_markers, list)
        and len(required_markers) == EXPECTED_REQUIRED_LEAN_MARKER_COUNT
        and "theorem transitionGroupCompression_preserves_generatedChildImage"
        in required_markers
        and "theorem transitionGroupCompressionHostTable_validates" in required_markers
        and missing.get("lean_markers") == []
    )
    placeholder_scan_clean = (
        bool(checks.get("lean_placeholder_scan_clean")) is True
        and missing.get("forbidden_lean_terms") == []
    )
    formal_test_receipt_ok = (
        bool(formal_test.get("ok")) is True
        and artifacts.get("formal_test")
        == "tests/formal/test_lean_ab_transition_group_compression.py"
        and artifacts.get("formal_test_sha256") == EXPECTED_FORMAL_TEST_HASH
        and missing.get("test_markers") == []
    )
    nonclaims_bound = _text_contains_all(
        non_claims_text,
        (
            "no python-to-lean refinement",
            "json canonicalization",
            "host generated-image construction",
            "nonzero min_amount_out",
            "no settlement",
        ),
    )
    replay_commands_bound = (
        isinstance(replay_commands, list)
        and "cd lean-mathlib && lake env lean Proofs/ABTransitionGroupCompression.lean"
        in replay_commands
        and "PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_transition_group_compression.py"
        in replay_commands
        and "python3 tools/check_ab_transition_group_compression_lean_bridge_20260629.py"
        in replay_commands
    )
    corpus_nonvacuous = (
        int(artifacts.get("lean_line_count", 0)) > 0
        and int(artifacts.get("formal_test_line_count", 0)) > 0
        and len(required_markers) > 0
    )
    return {
        "lean_bridge_report_ok": int(lean_bridge_report_ok),
        "lean_file_pinned": int(lean_file_pinned),
        "aggregator_import_bound": int(aggregator_import_bound),
        "theorem_surface_bound": int(theorem_surface_bound),
        "placeholder_scan_clean": int(placeholder_scan_clean),
        "lean_compile_receipt_ok": int(bool(lean_compile.get("ok"))),
        "formal_test_receipt_ok": int(formal_test_receipt_ok),
        "upstream_compression_tau_binding_ok": int(
            _upstream_compression_tau_binding_ok(upstream_report, upstream_hash)
        ),
        "nonclaims_bound": int(nonclaims_bound),
        "authority_boundary_ok": int(_authority_boundary_ok(lean_report)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(corpus_nonvacuous),
        "replay_commands_bound": int(replay_commands_bound),
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["lean_bridge_report_ok"]),
        "i3": int(facts["lean_file_pinned"]),
        "i4": int(facts["aggregator_import_bound"]),
        "i5": int(facts["theorem_surface_bound"]),
        "i6": int(facts["placeholder_scan_clean"]),
        "i7": int(facts["lean_compile_receipt_ok"]),
        "i8": int(facts["formal_test_receipt_ok"]),
        "i9": int(facts["upstream_compression_tau_binding_ok"]),
        "i10": int(facts["nonclaims_bound"]),
        "i11": int(facts["authority_boundary_ok"]),
        "i12": int(facts["no_authority_effect"]),
        "i13": int(facts["corpus_nonvacuous"]),
        "i14": int(facts["replay_commands_bound"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "lean_bridge_scope_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 1, "o8": 0},
            "All scoped host facts admit the Lean-bridge scope certificate.",
        ),
        TauCase(
            "missing_lean_bridge_report_reject",
            {**pass_step, "i2": 0},
            {"o1": 0, "o7": 0},
            "The Lean bridge report must be successful and hash-pinned.",
        ),
        TauCase(
            "lean_file_unpinned_reject",
            {**pass_step, "i3": 0},
            {"o1": 0, "o7": 0},
            "The Lean source hash and line count must remain pinned.",
        ),
        TauCase(
            "aggregator_import_missing_reject",
            {**pass_step, "i4": 0},
            {"o1": 0, "o7": 0},
            "The proof must remain imported by Proofs.lean.",
        ),
        TauCase(
            "theorem_surface_unbound_reject",
            {**pass_step, "i5": 0},
            {"o2": 0, "o7": 0},
            "The required theorem and definition surface must remain present.",
        ),
        TauCase(
            "placeholder_scan_failed_reject",
            {**pass_step, "i6": 0},
            {"o2": 0, "o7": 0},
            "The Lean proof must remain free of forbidden proof placeholders.",
        ),
        TauCase(
            "lean_compile_missing_reject",
            {**pass_step, "i7": 0},
            {"o2": 0, "o6": 0, "o7": 0},
            "The Lean file must typecheck in the current checkout.",
        ),
        TauCase(
            "formal_test_missing_reject",
            {**pass_step, "i8": 0},
            {"o2": 0, "o6": 0, "o7": 0},
            "The focused formal regression test must pass.",
        ),
        TauCase(
            "upstream_compression_tau_unbound_reject",
            {**pass_step, "i9": 0},
            {"o3": 0, "o7": 0},
            "The Lean bridge certificate must bind the upstream compression Tau certificate.",
        ),
        TauCase(
            "nonclaims_missing_reject",
            {**pass_step, "i10": 0},
            {"o4": 0, "o7": 0},
            "The Python-to-Lean and production-authority non-claims must remain explicit.",
        ),
        TauCase(
            "authority_boundary_missing_reject",
            {**pass_step, "i11": 0},
            {"o4": 0, "o5": 0, "o7": 0},
            "The research-only authority boundary must remain explicit.",
        ),
        TauCase(
            "authority_effect_reject",
            {**pass_step, "i12": 0},
            {"o4": 0, "o5": 0, "o7": 0},
            "The certificate cannot carry settlement, state-root, governance, or pool-mutation authority.",
        ),
        TauCase(
            "empty_corpus_reject",
            {**pass_step, "i13": 0},
            {"o1": 0, "o7": 0},
            "The certificate must bind a nonempty Lean theorem surface.",
        ),
        TauCase(
            "replay_commands_unbound_reject",
            {**pass_step, "i14": 0},
            {"o3": 0, "o6": 0, "o7": 0},
            "The replay command surface must remain bound.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o7": 0, "o8": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        ),
    )


def _run_tau(facts: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    cases = _tau_cases(facts)
    if not tau_bin:
        return {
            "ok": False,
            "skipped": True,
            "error": "latest Tau binary not found",
            "case_results": [],
            "invalid_accepts": 0,
            "tau_bin": None,
            "tau_version": None,
        }
    proc = subprocess.run(
        [tau_bin, "--version"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=20.0,
    )
    invalid_accepts = 0
    case_results = []
    ok = True
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        if case.expected.get("o7") == 0 and got.get("o7") == 1:
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
        "skipped": False,
        "case_results": case_results,
        "invalid_accepts": invalid_accepts,
        "tau_bin": _display_path(tau_bin),
        "tau_version": (proc.stdout + proc.stderr).strip(),
    }


def build_report() -> dict[str, Any]:
    lean_report = _refresh_lean_bridge_report()
    lean_report_hash = _sha256(LEAN_BRIDGE_REPORT) if LEAN_BRIDGE_REPORT.exists() else ""
    upstream_report = _read_json(UPSTREAM_TAU_REPORT)
    upstream_hash = _sha256(UPSTREAM_TAU_REPORT)
    lean_compile = _run_command(
        ["lake", "env", "lean", "Proofs/ABTransitionGroupCompression.lean"],
        REPO_ROOT / "lean-mathlib",
        120,
    )
    formal_test = _run_command(
        [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/formal/test_lean_ab_transition_group_compression.py",
        ],
        REPO_ROOT,
        180,
    )
    facts = _fact_bundle(
        lean_report,
        lean_report_hash,
        upstream_report,
        upstream_hash,
        lean_compile,
        formal_test,
    )
    tau = _run_tau(facts)
    artifacts = lean_report.get("artifacts", {})
    upstream_compression = upstream_report.get("compression", {})
    return {
        "schema": "zenodex.ab_transition_group_compression_lean_bridge_tau_certificate_report.v1",
        "date": "2026-06-29",
        "authority_boundary": (
            "research evidence only; no settlement, state-root, production, governance, "
            "routing, matching, or pool-mutation authority"
        ),
        "spec": {
            "id": SPEC_ID,
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
        },
        "lean_bridge_report": {
            "path": str(LEAN_BRIDGE_REPORT.relative_to(REPO_ROOT)),
            "sha256": lean_report_hash,
            "ok": bool(lean_report.get("ok")),
            "schema": lean_report.get("schema"),
            "claim_scope": lean_report.get("claim_scope"),
        },
        "lean_bridge_artifacts": {
            "lean_file": artifacts.get("lean_file"),
            "lean_sha256": artifacts.get("lean_sha256"),
            "lean_line_count": artifacts.get("lean_line_count"),
            "aggregator": artifacts.get("aggregator"),
            "aggregator_sha256": artifacts.get("aggregator_sha256"),
            "formal_test": artifacts.get("formal_test"),
            "formal_test_sha256": artifacts.get("formal_test_sha256"),
            "formal_test_line_count": artifacts.get("formal_test_line_count"),
            "required_lean_marker_count": len(lean_report.get("required_lean_markers", [])),
        },
        "upstream_compression_tau_report": {
            "path": str(UPSTREAM_TAU_REPORT.relative_to(REPO_ROOT)),
            "sha256": upstream_hash,
            "schema": upstream_report.get("schema"),
            "tau_ok": upstream_report.get("tau", {}).get("ok"),
            "invalid_accepts": upstream_report.get("tau", {}).get("invalid_accepts"),
            "tau_cases": upstream_report.get("breakthrough", {}).get("tau_cases"),
            "source_transition_row_count": upstream_compression.get("source_transition_row_count"),
            "compressed_row_count": upstream_compression.get("compressed_row_count"),
        },
        "receipts": {
            "lean_bridge_report_refresh": lean_report.get("refresh"),
            "lean_compile": lean_compile,
            "formal_test": formal_test,
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB transition-group compression Lean-bridge Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the Lean bridge report is present, successful, and hash-pinned",
                "the ABTransitionGroupCompression Lean source and Proofs.lean import are pinned",
                "the transition-group image-preservation theorem surface is bound",
                "Lean typechecking and the focused formal regression pass in the current checkout",
                "the upstream n=7 transition-group compression Tau certificate is bound",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate composes host facts; it does not run Lean inside Tau.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove JSON canonicalization, packet hashing, Merkle membership, or digest computation in Lean.",
            "This certificate does not prove host generated-image construction.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-TRANSITION-GROUP-COMPRESSION-LEAN-BRIDGE-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over the transition-group compression Lean bridge.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": {
                "safety": "positive for proof-artifact scoping",
                "cap_efficiency": "neutral",
                "execution_quality": "neutral",
                "proof_cost": "positive by binding Lean and Tau evidence into one replayable envelope",
                "determinism": "positive via hash pins and missing-fact negative cases",
            },
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the Lean bridge report.",
            "support_recipe": "Host checks the Lean bridge report, runs Lean and formal tests, binds upstream Tau evidence, then Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, remove the no-authority rail, alter theorem markers, or break upstream compression binding and require Tau rejection.",
            "formal_obligations": "Production use still needs Python-to-Lean refinement, host generated-image construction proof, digest proof, and nonzero min_amount_out coverage.",
        },
        "replay_command": "python3 tools/check_ab_transition_group_compression_lean_bridge_tau_certificate_20260629.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Transition-Group Compression Lean-Bridge Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        (
            "`ab_transition_group_compression_lean_bridge_scope_certificate_v1` admits "
            "the Lean bridge research bundle only when the Lean bridge report, pinned "
            "Lean/test artifacts, theorem-surface markers, placeholder scan, Lean "
            "compile receipt, focused formal test receipt, upstream compression Tau "
            "certificate binding, replay-command surface, non-claims, and no-authority "
            "rail are all present."
        ),
        "",
        (
            "Research-only evidence. No settlement, state-root, production, governance, "
            "routing, matching, or pool-mutation authority is derived from this artifact."
        ),
        "",
        "## Facts",
        "",
    ]
    for key, value in report["facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Artifact Pins",
            "",
            f"- Lean bridge report hash: `{report['lean_bridge_report']['sha256']}`",
            f"- Lean file: `{report['lean_bridge_artifacts']['lean_file']}`",
            f"- Lean SHA-256: `{report['lean_bridge_artifacts']['lean_sha256']}`",
            f"- Required Lean markers: `{report['lean_bridge_artifacts']['required_lean_marker_count']}`",
            f"- Formal test SHA-256: `{report['lean_bridge_artifacts']['formal_test_sha256']}`",
            f"- Upstream compression Tau report hash: `{report['upstream_compression_tau_report']['sha256']}`",
            f"- Upstream source rows: `{report['upstream_compression_tau_report']['source_transition_row_count']}`",
            f"- Upstream compressed rows: `{report['upstream_compression_tau_report']['compressed_row_count']}`",
            "",
            "## Receipts",
            "",
            f"- Lean compile ok: `{report['receipts']['lean_compile']['ok']}`",
            f"- Formal test ok: `{report['receipts']['formal_test']['ok']}`",
            f"- Tau ok: `{report['tau']['ok']}`",
            f"- Tau invalid accepts: `{report['tau']['invalid_accepts']}`",
            "",
            "## Tau Cases",
            "",
            "| case | ok | admitted |",
            "| --- | --- | ---: |",
        ]
    )
    for case in report["tau"]["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o7')}` |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    ok = (
        all(value == 1 for value in report["facts"].values())
        and bool(report["tau"]["ok"])
        and int(report["tau"]["invalid_accepts"]) == 0
    )
    print(
        json.dumps(
            {
                "ok": bool(ok),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "tau_cases": report["breakthrough"]["tau_cases"],
                "invalid_accepts": report["breakthrough"]["invalid_accepts"],
                "lean_compile_ok": report["receipts"]["lean_compile"]["ok"],
                "formal_test_ok": report["receipts"]["formal_test"]["ok"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
