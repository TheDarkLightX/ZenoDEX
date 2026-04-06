#!/usr/bin/env python3
"""Public assurance CLI for replaying and auditing the publishable evidence surface."""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

try:
    from tools.render_assurance_release_snapshot import RenderError, _load_snapshot, render_targets
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from render_assurance_release_snapshot import RenderError, _load_snapshot, render_targets

try:
    from tools.render_tla_claim_summary import OUTPUT_PATH as TLA_SUMMARY_PATH, RenderError as TlaRenderError, render_summary_text
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from render_tla_claim_summary import OUTPUT_PATH as TLA_SUMMARY_PATH, RenderError as TlaRenderError, render_summary_text


REPO_ROOT = Path(__file__).resolve().parents[1]

PUBLIC_SCOPE_GLOBS: tuple[str, ...] = (
    ".gitignore",
    "docs/ASSURANCE_GLOSSARY.md",
    "docs/ASSURANCE_RELEASE_SNAPSHOT.md",
    "docs/PUBLIC_ASSURANCE_REPLAY.md",
    "docs/RC1_SUPPORTED_RUNTIME_PATH.md",
    "docs/RC1_VERIFIED_SURFACE_MATRIX.md",
    "docs/TLA_CLAIM_SUMMARY.md",
    "docs/assurance_release_snapshot.json",
    "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
    "src/core/amm_dispatch.py",
    "src/core/batch_clearing.py",
    "src/kernels/python/batch_auction_settler_v1_witness.py",
    "src/kernels/python/settlement_swap_runtime_v1.py",
    "tests/core/test_batch_auction_settler_v1_ref_parity.py",
    "tests/core/test_batch_auction_settler_v1_witness.py",
    "tests/core/test_batch_clearing.py",
    "tests/core/test_settlement_swap_runtime_v1.py",
    "tests/integration/test_permissionless_assurance_cli.py",
    "tools/check_derivatives_evidence_manifest.py",
    "tools/check_spot_proof_assurance_manifest.py",
    "tools/dex_kernel_assurance.py",
    "tools/derivatives_evidence_manifest.json",
    "tools/kernel_assurance_manifest.json",
    "tools/permissionless_assurance.py",
    "tools/render_rc1_supported_runtime_path.py",
    "tools/render_rc1_verified_surface_matrix.py",
    "tools/render_assurance_release_snapshot.py",
    "tools/render_tla_claim_summary.py",
    "tools/run_critical_quality_gate.sh",
    "tools/run_release_gate.sh",
    "tools/run_perps_evidence.sh",
    "tools/run_spot_evidence.sh",
    "tools/run_spot_proof_assurance_gate.sh",
    "tools/spot_proof_assurance_manifest.json",
)

FORBIDDEN_PATH_GLOBS: tuple[str, ...] = (
    "AGENTS.md",
    ".agents/*",
    ".claude/*",
    ".codex_peer_review/*",
    ".mcp.json",
    ".rlm_collab/*",
    ".tmp/*",
    "external/*",
    "internal/*",
    "mcp-servers*.json",
    "node_modules/*",
    "runs/*",
    "setup_*_mcp*.sh",
    "tools/*_mcp/*",
    "tools/_secbin/*",
)

FORBIDDEN_PHRASES: tuple[str, ...] = (
    "DO NOT COMMIT",
    "DO NOT SHARE",
    "# INTERNAL NOTES",
)

PUBLIC_REFS: tuple[str, ...] = (
    "generated/cpmm_python/cpmm_swap_ref.py",
    "generated/dex_v8_python/dex_step_core_v2_ref.py",
    "generated/vault_python/vault_manager_ref.py",
    "generated/volatility_tier_controller_v1_python_ref/volatility_tier_controller_v1_ref.py",
    "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
)


@dataclass(frozen=True)
class Lane:
    name: str
    description: str
    commands: tuple[tuple[str, ...], ...]
    required_files: tuple[str, ...]
    required_environment: tuple[str, ...]
    stars: int


def _python_bin() -> str:
    env_python = os.environ.get("PYTHON", "").strip()
    if env_python:
        return env_python
    venv_python = REPO_ROOT / ".venv" / "bin" / "python"
    if venv_python.is_file():
        return str(venv_python)
    if sys.executable:
        return sys.executable
    return "python3"


PY = _python_bin()

ENVIRONMENT_REQUIREMENT_HINTS: dict[str, str] = {
    "external/ESSO": "clone or update external/ESSO",
    "tau-binary": "set TAU_BIN, put tau on PATH, or build external/tau-lang/build-*/tau",
}

LANES: dict[str, Lane] = {
    "kernel-assurance": Lane(
        name="kernel-assurance",
        description="Re-run the manifest-backed kernel assurance corpus and solver checks.",
        commands=((PY, "tools/dex_kernel_assurance.py", "--pretty"),),
        required_files=("tools/dex_kernel_assurance.py", "tools/kernel_assurance_manifest.json"),
        required_environment=("external/ESSO",),
        stars=3,
    ),
    "spot-proof": Lane(
        name="spot-proof",
        description="Rebuild the spot proof artifacts, then pin-check the manifest.",
        commands=(
            ("bash", "tools/run_spot_proof_assurance_gate.sh"),
            (PY, "tools/check_spot_proof_assurance_manifest.py"),
        ),
        required_files=(
            "tools/run_spot_proof_assurance_gate.sh",
            "tools/check_spot_proof_assurance_manifest.py",
            "tools/spot_proof_assurance_manifest.json",
        ),
        required_environment=("external/ESSO",),
        stars=3,
    ),
    "spot-evidence": Lane(
        name="spot-evidence",
        description="Replay the spot functional-core tests and spot-kernel verify-multi checks.",
        commands=(("bash", "tools/run_spot_evidence.sh"),),
        required_files=(
            "tools/run_spot_evidence.sh",
            "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
        ),
        required_environment=("external/ESSO",),
        stars=2,
    ),
    "derivatives": Lane(
        name="derivatives",
        description="Rebuild the derivatives evidence lane, then pin-check the manifest.",
        commands=(
            ("bash", "tools/run_derivatives_evidence.sh"),
            (PY, "tools/check_derivatives_evidence_manifest.py"),
        ),
        required_files=(
            "tools/run_derivatives_evidence.sh",
            "tools/check_derivatives_evidence_manifest.py",
            "tools/derivatives_evidence_manifest.json",
        ),
        required_environment=("external/ESSO",),
        stars=3,
    ),
    "perps": Lane(
        name="perps",
        description="Replay the perps functional-core tests, micro-gate assurances, kernel verify-multi checks, and Lean safety proofs.",
        commands=(("bash", "tools/run_perps_evidence.sh"),),
        required_files=("tools/run_perps_evidence.sh",),
        required_environment=("external/ESSO",),
        stars=3,
    ),
    "critical": Lane(
        name="critical",
        description="Run the publishable critical quality gate with branch coverage and static checks.",
        commands=(("bash", "tools/run_critical_quality_gate.sh"),),
        required_files=("tools/run_critical_quality_gate.sh",),
        required_environment=(),
        stars=2,
    ),
    "release": Lane(
        name="release",
        description="Run the full release gate, including Tau, proof, evidence, and audit lanes.",
        commands=(("bash", "tools/run_release_gate.sh"),),
        required_files=("tools/run_release_gate.sh",),
        required_environment=("external/ESSO", "tau-binary"),
        stars=4,
    ),
}

LANE_GROUPS: dict[str, tuple[str, ...]] = {
    "public": ("kernel-assurance", "spot-proof", "spot-evidence", "derivatives", "perps"),
    "critical": ("critical",),
    "full": ("release",),
}


def _git_stdout(*args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return proc.stdout.strip()


def _git_status_paths() -> list[str]:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "status", "--porcelain=v1", "--untracked-files=all"],
        check=True,
        capture_output=True,
        text=True,
    )
    out: list[str] = []
    for raw_line in proc.stdout.splitlines():
        line = raw_line.rstrip("\n")
        if not line:
            continue
        path_part = line[3:]
        if " -> " in path_part:
            _, new_path = path_part.split(" -> ", 1)
            path_part = new_path
        out.append(path_part)
    return out


def _is_git_tracked(path: str) -> bool:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "ls-files", "--error-unmatch", path],
        capture_output=True,
        text=True,
    )
    return proc.returncode == 0


def _match_any(path: str, patterns: Sequence[str]) -> bool:
    normalized = path.replace("\\", "/")
    return any(fnmatch.fnmatch(normalized, pattern) for pattern in patterns)


def _public_scope_paths(paths: Iterable[str]) -> list[str]:
    selected = sorted({path for path in paths if _match_any(path, PUBLIC_SCOPE_GLOBS)})
    return selected


def _text_file_phrases(path: Path) -> list[str]:
    if not path.is_file():
        return []
    if path.suffix.lower() not in {".md", ".txt", ".yaml", ".yml"}:
        return []
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    return [phrase for phrase in FORBIDDEN_PHRASES if phrase in text]


def _leak_findings(paths: Iterable[str]) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []
    for rel in sorted(set(paths)):
        if _match_any(rel, FORBIDDEN_PATH_GLOBS):
            findings.append({"path": rel, "kind": "path", "detail": "matches a forbidden private/internal path rule"})
            continue
        for phrase in _text_file_phrases(REPO_ROOT / rel):
            findings.append({"path": rel, "kind": "content", "detail": f"contains forbidden phrase {phrase!r}"})
    return findings


def _bar(completed: int, total: int, *, width: int = 20) -> str:
    if total <= 0:
        return "[" + ("-" * width) + "]"
    filled = max(0, min(width, int(round(width * completed / total))))
    return "[" + ("#" * filled) + ("." * (width - filled)) + "]"


def _tau_binary_ready() -> bool:
    tau_bin = os.environ.get("TAU_BIN", "").strip()
    if tau_bin:
        return Path(tau_bin).is_file() and os.access(tau_bin, os.X_OK)
    if shutil.which("tau"):
        return True
    for candidate in REPO_ROOT.glob("external/tau-lang/build-*/tau"):
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return True
    return False


def _environment_requirement_ready(name: str) -> bool:
    if name == "external/ESSO":
        return (REPO_ROOT / "external" / "ESSO").exists()
    if name == "tau-binary":
        return _tau_binary_ready()
    raise RuntimeError(f"unknown environment requirement: {name}")


def _environment_requirement_hint(name: str) -> str:
    try:
        return ENVIRONMENT_REQUIREMENT_HINTS[name]
    except KeyError as exc:  # pragma: no cover - defensive
        raise RuntimeError(f"unknown environment requirement: {name}") from exc


def _lane_summary() -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for lane in LANES.values():
        missing = [path for path in lane.required_files if not (REPO_ROOT / path).exists()]
        missing_environment = [name for name in lane.required_environment if not _environment_requirement_ready(name)]
        out.append(
            {
                "name": lane.name,
                "description": lane.description,
                "stars": lane.stars,
                "required_files": list(lane.required_files),
                "required_environment": list(lane.required_environment),
                "missing_files": missing,
                "missing_environment": missing_environment,
                "environment_hints": {name: _environment_requirement_hint(name) for name in lane.required_environment},
                "ready": not missing and not missing_environment,
            }
        )
    return out


def _snapshot_status() -> dict[str, object]:
    try:
        snapshot = _load_snapshot()
        rendered = render_targets()
        stale_paths: list[str] = []
        for path, expected in rendered.items():
            current = path.read_text(encoding="utf-8") if path.exists() else ""
            if current != expected:
                stale_paths.append(str(path.relative_to(REPO_ROOT)))
        return {
            "ok": not stale_paths,
            "as_of_date": snapshot["as_of_date"],
            "snapshot_label": snapshot["snapshot_label"],
            "stale_paths": stale_paths,
            "error": None,
        }
    except RenderError as exc:
        return {
            "ok": False,
            "as_of_date": None,
            "snapshot_label": None,
            "stale_paths": [],
            "error": str(exc),
        }


def _tla_summary_status() -> dict[str, object]:
    try:
        expected = render_summary_text()
        current = TLA_SUMMARY_PATH.read_text(encoding="utf-8") if TLA_SUMMARY_PATH.exists() else ""
        return {
            "ok": current == expected,
            "path": str(TLA_SUMMARY_PATH.relative_to(REPO_ROOT)),
            "error": None,
        }
    except TlaRenderError as exc:
        return {
            "ok": False,
            "path": str(TLA_SUMMARY_PATH.relative_to(REPO_ROOT)),
            "error": str(exc),
        }


def _status_payload() -> dict[str, object]:
    branch = _git_stdout("rev-parse", "--abbrev-ref", "HEAD")
    dirty_paths = _git_status_paths()
    public_scope = _public_scope_paths(dirty_paths)
    leak_findings = _leak_findings(public_scope)
    refs = []
    tracked_ready = 0
    for rel in PUBLIC_REFS:
        path = REPO_ROOT / rel
        tracked = _is_git_tracked(rel)
        present = path.is_file()
        ready = present and tracked
        if ready:
            tracked_ready += 1
        refs.append({"path": rel, "present": present, "tracked": tracked, "ready": ready})

    lanes = _lane_summary()
    lanes_ready = sum(1 for lane in lanes if bool(lane["ready"]))
    payload: dict[str, object] = {
        "branch": branch,
        "assurance_snapshot": _snapshot_status(),
        "tla_claim_summary": _tla_summary_status(),
        "dirty_paths": dirty_paths,
        "dirty_count": len(dirty_paths),
        "public_scope_paths": public_scope,
        "public_scope_count": len(public_scope),
        "public_scope_clean": not leak_findings,
        "public_scope_leaks": leak_findings,
        "lanes": lanes,
        "lanes_ready": lanes_ready,
        "lanes_total": len(lanes),
        "public_refs": refs,
        "public_refs_ready": tracked_ready,
        "public_refs_total": len(refs),
        "notes": [
            "internal/ artifacts are intentionally not shipped; replay commands regenerate them locally",
            "public assurance claims should be backed by pinned manifests, tracked exported refs, and replayable gate scripts",
            "public replay lanes may require external toolchains such as external/ESSO or a tau binary; status and replay should fail closed when those prerequisites are absent",
        ],
    }
    return payload


def _print_status(payload: dict[str, object]) -> None:
    lanes_ready = int(payload["lanes_ready"])
    lanes_total = int(payload["lanes_total"])
    refs_ready = int(payload["public_refs_ready"])
    refs_total = int(payload["public_refs_total"])
    print("ZenoDex Permissionless Assurance")
    print(f"branch: {payload['branch']}")
    snapshot = payload["assurance_snapshot"]
    tla_summary = payload["tla_claim_summary"]
    if snapshot["error"]:
        print(f"assurance snapshot: ERROR ({snapshot['error']})")
    else:
        state = "OK" if snapshot["ok"] else "STALE"
        print(f"assurance snapshot: {state} (as of {snapshot['as_of_date']})")
    if tla_summary["error"]:
        print(f"tla claim summary: ERROR ({tla_summary['error']})")
    else:
        tla_state = "OK" if tla_summary["ok"] else "STALE"
        print(f"tla claim summary: {tla_state} ({tla_summary['path']})")
    print(f"dirty tree: {payload['dirty_count']} paths")
    print(f"public merge scope: {payload['public_scope_count']} paths")
    print(f"lane readiness: {lanes_ready}/{lanes_total} {_bar(lanes_ready, lanes_total)}")
    print(f"tracked exported refs: {refs_ready}/{refs_total} {_bar(refs_ready, refs_total)}")
    print()
    print("Proofboard")
    for lane in payload["lanes"]:
        stars = "*" * int(lane["stars"])
        state = "READY" if lane["ready"] else "MISSING"
        print(f"  [{state:<7}] {lane['name']:<16} {stars}  {lane['description']}")
        missing = list(lane["missing_files"])
        for rel in missing:
            print(f"    missing: {rel}")
        missing_environment = list(lane["missing_environment"])
        for env_name in missing_environment:
            print(f"    missing env: {env_name}")
    print()
    print("Tracked exported refs")
    for ref in payload["public_refs"]:
        state = "OK" if ref["ready"] else "WARN"
        tracked = "tracked" if ref["tracked"] else "untracked"
        present = "present" if ref["present"] else "missing"
        print(f"  [{state}] {ref['path']} ({tracked}, {present})")
    if payload["public_scope_leaks"]:
        print()
        print("Leak warnings")
        for finding in payload["public_scope_leaks"]:
            print(f"  [BLOCK] {finding['path']}: {finding['detail']}")
    else:
        print()
        print("Leak warnings")
        print("  [OK] no blocked paths or forbidden internal markers in the scoped public merge set")
    if snapshot["stale_paths"]:
        print()
        print("Snapshot drift")
        for rel in snapshot["stale_paths"]:
            print(f"  [STALE] {rel}")


def _expand_lane_names(items: Sequence[str]) -> list[str]:
    requested = list(items) or ["public"]
    expanded: list[str] = []
    for item in requested:
        if item in LANE_GROUPS:
            expanded.extend(LANE_GROUPS[item])
            continue
        if item not in LANES:
            raise SystemExit(f"unknown lane or group: {item}")
        expanded.append(item)
    # Preserve order while removing duplicates.
    out: list[str] = []
    seen: set[str] = set()
    for name in expanded:
        if name in seen:
            continue
        seen.add(name)
        out.append(name)
    return out


def _missing_files(paths: Sequence[str]) -> list[str]:
    return [rel for rel in paths if not (REPO_ROOT / rel).exists()]


def _missing_environment(names: Sequence[str]) -> list[dict[str, str]]:
    return [
        {"name": name, "hint": _environment_requirement_hint(name)}
        for name in names
        if not _environment_requirement_ready(name)
    ]


def _run_lane(lane: Lane) -> dict[str, object]:
    missing_files = _missing_files(lane.required_files)
    if missing_files:
        return {
            "name": lane.name,
            "ok": False,
            "duration_s": 0.0,
            "missing_files": missing_files,
            "error": "missing required files",
        }
    missing_environment = _missing_environment(lane.required_environment)
    if missing_environment:
        return {
            "name": lane.name,
            "ok": False,
            "duration_s": 0.0,
            "missing_environment": missing_environment,
            "error": "missing required environment",
        }
    started = time.monotonic()
    for command in lane.commands:
        proc = subprocess.run(command, cwd=REPO_ROOT)
        if proc.returncode != 0:
            duration = time.monotonic() - started
            return {
                "name": lane.name,
                "ok": False,
                "duration_s": round(duration, 3),
                "failed_command": list(command),
                "error": "command failed",
            }
    duration = time.monotonic() - started
    return {"name": lane.name, "ok": True, "duration_s": round(duration, 3)}


def cmd_status(args: argparse.Namespace) -> int:
    payload = _status_payload()
    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        _print_status(payload)
    return 0


def cmd_stage_scope(args: argparse.Namespace) -> int:
    scope = _public_scope_paths(_git_status_paths())
    payload = {
        "scope": "public-assurance",
        "paths": scope,
        "count": len(scope),
        "git_add_command": (["git", "add", "--", *scope] if scope else ["git", "add", "--"]),
    }
    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print("Public assurance stage scope")
        for rel in scope:
            print(rel)
        print()
        if scope:
            joined = " ".join(f'"{rel}"' for rel in scope)
            print(f"git add -- {joined}")
        else:
            print("scope is empty")
    return 0


def cmd_leak_check(args: argparse.Namespace) -> int:
    if args.paths:
        paths = list(args.paths)
    else:
        paths = _public_scope_paths(_git_status_paths())
    findings = _leak_findings(paths)
    payload = {"paths": paths, "findings": findings, "ok": not findings}
    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        if findings:
            print("Leak check")
            for finding in findings:
                print(f"[BLOCK] {finding['path']}: {finding['detail']}")
        else:
            print("Leak check")
            print("[OK] no forbidden paths or internal markers found")
    return 0 if not findings else 1


def cmd_replay(args: argparse.Namespace) -> int:
    lane_names = _expand_lane_names(args.lanes)
    plan = []
    for name in lane_names:
        lane = LANES[name]
        plan.append(
            {
                "name": lane.name,
                "description": lane.description,
                "commands": [list(command) for command in lane.commands],
                "required_files": list(lane.required_files),
                "required_environment": list(lane.required_environment),
            }
        )
    if args.plan:
        payload = {"lanes": plan}
        if args.format == "json":
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print("Replay plan")
            for lane in plan:
                print(f"{lane['name']}: {lane['description']}")
                for env_name in lane["required_environment"]:
                    print(f"  requires: {env_name}")
                for command in lane["commands"]:
                    print("  " + " ".join(command))
        return 0

    results = []
    overall_ok = True
    for name in lane_names:
        lane = LANES[name]
        if args.format != "json":
            print(f"== assurance: {lane.name} ==")
        result = _run_lane(lane)
        results.append(result)
        overall_ok = overall_ok and bool(result["ok"])
        if args.format != "json":
            status = "OK" if result["ok"] else "FAIL"
            print(f"[{status}] {lane.name} ({result['duration_s']}s)")
            for rel in result.get("missing_files", []):
                print(f"  missing: {rel}")
            for env_item in result.get("missing_environment", []):
                print(f"  missing env: {env_item['name']} ({env_item['hint']})")
            if result.get("error") == "command failed":
                print("  failed command: " + " ".join(result["failed_command"]))
        if not result["ok"] and not args.keep_going:
            break

    if args.format == "json":
        print(json.dumps({"results": results, "ok": overall_ok}, indent=2, sort_keys=True))
    return 0 if overall_ok else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Public assurance CLI for replayable, merge-safe ZenoDex assurance surfaces."
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_status = sub.add_parser("status", help="Show the public replay surface, tracked refs, and scoped merge readiness.")
    p_status.add_argument("--format", choices=("text", "json"), default="text")
    p_status.set_defaults(func=cmd_status)

    p_scope = sub.add_parser("stage-scope", help="List the narrow public-assurance file set worth staging from the dirty tree.")
    p_scope.add_argument("--format", choices=("text", "json"), default="text")
    p_scope.set_defaults(func=cmd_stage_scope)

    p_leak = sub.add_parser("leak-check", help="Block obvious private/internal paths and markers before commit or merge.")
    p_leak.add_argument("paths", nargs="*", help="Optional explicit repo-relative paths. Defaults to the public stage scope.")
    p_leak.add_argument("--format", choices=("text", "json"), default="text")
    p_leak.set_defaults(func=cmd_leak_check)

    p_replay = sub.add_parser("replay", help="Plan or execute replayable assurance lanes.")
    p_replay.add_argument("lanes", nargs="*", help="Lane or group names. Groups: public, critical, full")
    p_replay.add_argument("--plan", action="store_true", help="Print commands without running them.")
    p_replay.add_argument("--keep-going", action="store_true", help="Continue after a lane fails.")
    p_replay.add_argument("--format", choices=("text", "json"), default="text")
    p_replay.set_defaults(func=cmd_replay)

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
