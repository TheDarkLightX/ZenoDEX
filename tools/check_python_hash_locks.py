#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
LOCKFILES = (
    "requirements-core.lock.txt",
    "requirements-agents.lock.txt",
    "requirements-dev.lock.txt",
)
INSTALL_SURFACE_GLOBS = (
    "README.md",
    "Dockerfile",
    ".github/workflows/*.yml",
    ".github/workflows/*.yaml",
    "docs/SECURITY_POSTURE.md",
    "docs/SSDF_GAP_CHECKLIST.md",
    "docs/tau_testnet_local_node.md",
    "tools/README.md",
    "tools/**/*.sh",
    "tools/**/*.py",
)
HASH_RE = re.compile(r"--hash=sha256:[0-9a-f]{64}\b")
REQUIREMENT_RE = re.compile(
    r"^[A-Za-z0-9][A-Za-z0-9_.-]*(?:\[[A-Za-z0-9_,.-]+\])?==[^\s\\;]+"
    r"(?:\s*;\s*[^\\]+)?(?:\s*\\)?$"
)
LIVE_INCLUDE_RE = re.compile(r"^(?:-r|--requirement|-c|--constraint)\s+")
PIP_INSTALL_RE = re.compile(r"\bpip(?:[0-9.]+)?\s+install\b")
ROOT_LOCK_RE = re.compile(r"requirements-(?:core|agents|dev)\.lock\.txt")
ROOT_UNLOCKED_RE = re.compile(r"requirements-(?:core|agents|dev)\.txt")
LOCK_VAR_RE = re.compile(
    r"\$(?:\{(?:DEV_LOCK|RUNTIME_LOCK|AGENTS_LOCK|CORE_LOCK)\}|"
    r"(?:DEV_LOCK|RUNTIME_LOCK|AGENTS_LOCK|CORE_LOCK)(?![A-Za-z0-9_]))"
)

ALLOWLISTED_UNHASHED_INSTALLS = (
    (
        "docs/tau_testnet_local_node.md",
        "external/tau-testnet/requirements.txt",
        "optional local Tau Testnet checkout dependencies; outside production and release gates",
    ),
    (
        "tools/run_tau_testnet_local_smoke.sh",
        "external/tau-testnet/requirements.txt",
        "optional local Tau Testnet checkout dependencies; outside production and release gates",
    ),
    (
        "tools/run_local_tau_node_container.sh",
        "external/tau-testnet/requirements.txt",
        "optional local Tau Testnet checkout dependencies; outside production and release gates",
    ),
    (
        "tools/runpod_esso.py",
        "pip install -q -U pip",
        "remote ESSO experiment bootstrap; outside production and release gates",
    ),
    (
        "tools/runpod_esso.py",
        "pip install -q PyYAML z3-solver",
        "remote ESSO experiment bootstrap; outside production and release gates",
    ),
    (
        "tools/gpu_env_check.py",
        "https://download.pytorch.org/whl/cu124",
        "printed optional GPU backend recommendation; outside production and release gates",
    ),
    (
        "tools/gpu_env_check.py",
        "https://download.pytorch.org/whl/cu121",
        "printed optional GPU backend recommendation; outside production and release gates",
    ),
    (
        "tools/gpu_env_check.py",
        "cupy-cuda12x",
        "printed optional GPU backend recommendation; outside production and release gates",
    ),
    (
        "tools/gpu_env_check.py",
        "pip install --upgrade torch",
        "printed optional GPU backend recommendation; outside production and release gates",
    ),
    (
        "tools/README.md",
        "pyinstaller>=6,<7",
        "optional native oracle bundle builder dependency; outside production and release gates",
    ),
    (
        "tools/check_python_hash_lock_install_surface.py",
        "pip install",
        "checker source inspects install text and is not an install surface",
    ),
)


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    code: str
    message: str

    def to_json(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "line": self.line,
            "code": self.code,
            "message": self.message,
        }


@dataclass
class RequirementBlock:
    name: str
    line: int
    hash_count: int = 0


def _display_path(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _strip_inline_comment(line: str) -> str:
    if " #" not in line:
        return line
    return line.split(" #", 1)[0].rstrip()


def _requirement_name(line: str) -> str:
    return line.split("==", 1)[0].strip()


def _allowlisted_unhashed_install_reason(display: str, line: str) -> str | None:
    for path, needle, reason in ALLOWLISTED_UNHASHED_INSTALLS:
        if display == path and needle in line:
            return reason
    return None


def audit_lockfile(path: Path, root: Path = ROOT) -> dict[str, Any]:
    display = _display_path(path, root)
    findings: list[Finding] = []
    packages = 0
    hashes = 0

    if not path.is_file():
        findings.append(Finding(display, 0, "missing_lockfile", "required lockfile is missing"))
        return {
            "path": display,
            "ok": False,
            "packages": packages,
            "hashes": hashes,
            "findings": [finding.to_json() for finding in findings],
        }

    lines = path.read_text(encoding="utf-8").splitlines()
    header = "\n".join(lines[:10])
    if "pip-compile" not in header or "--generate-hashes" not in header:
        findings.append(
            Finding(
                display,
                1,
                "missing_hash_generation_header",
                "lockfile header must record pip-compile --generate-hashes",
            )
        )

    current: RequirementBlock | None = None

    def finish_current() -> None:
        nonlocal current
        if current is not None and current.hash_count == 0:
            findings.append(
                Finding(
                    display,
                    current.line,
                    "missing_hash",
                    f"requirement {current.name!r} has no sha256 hash entries",
                )
            )
        current = None

    for line_no, raw_line in enumerate(lines, start=1):
        stripped = _strip_inline_comment(raw_line.strip())
        if not stripped or stripped.startswith("#"):
            continue
        if LIVE_INCLUDE_RE.match(stripped):
            finish_current()
            findings.append(
                Finding(
                    display,
                    line_no,
                    "live_include_in_lockfile",
                    "lockfiles must be flattened; live -r/-c includes are not allowed",
                )
            )
            continue
        line_hashes = HASH_RE.findall(stripped)
        if line_hashes:
            if current is None:
                findings.append(
                    Finding(
                        display,
                        line_no,
                        "orphan_hash",
                        "hash entry appears before a requirement line",
                    )
                )
            else:
                current.hash_count += len(line_hashes)
                hashes += len(line_hashes)
            continue
        if REQUIREMENT_RE.match(stripped):
            finish_current()
            current = RequirementBlock(_requirement_name(stripped), line_no)
            packages += 1
            continue
        finish_current()
        findings.append(
            Finding(
                display,
                line_no,
                "unsupported_lockfile_line",
                "lockfile contains an unsupported live directive or unpinned requirement line",
            )
        )

    finish_current()
    return {
        "path": display,
        "ok": not findings,
        "packages": packages,
        "hashes": hashes,
        "findings": [finding.to_json() for finding in findings],
    }


def _logical_lines(text: str) -> Iterable[tuple[int, str]]:
    start_line = 1
    pending = ""
    for line_no, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.rstrip()
        if pending:
            pending = f"{pending} {line.strip()}"
        else:
            pending = line
            start_line = line_no
        if line.endswith("\\"):
            pending = pending[:-1].rstrip()
            continue
        yield start_line, pending
        pending = ""
    if pending:
        yield start_line, pending


def audit_install_surface(path: Path, root: Path = ROOT) -> dict[str, Any]:
    display = _display_path(path, root)
    findings: list[Finding] = []
    allowlisted_unhashed_installs: list[dict[str, Any]] = []
    pip_install_commands = 0
    root_dependency_commands = 0
    hash_locked_non_root_commands = 0
    for line_no, line in _logical_lines(path.read_text(encoding="utf-8")):
        if not PIP_INSTALL_RE.search(line):
            continue
        if display == "tools/check_python_hash_locks.py" and "pip install of a root lockfile" in line:
            continue
        pip_install_commands += 1
        root_lock_install = ROOT_LOCK_RE.search(line) or LOCK_VAR_RE.search(line)
        root_manifest_install = ROOT_UNLOCKED_RE.search(line)
        if root_lock_install or root_manifest_install:
            root_dependency_commands += 1
        if root_lock_install and "--require-hashes" not in line:
            findings.append(
                Finding(
                    display,
                    line_no,
                    "missing_require_hashes",
                    "pip install of a root lockfile must include --require-hashes",
                )
            )
        if root_manifest_install:
            findings.append(
                Finding(
                    display,
                    line_no,
                    "unlocked_root_requirements_install",
                    "supported install surfaces must install root lockfiles, not unlocked root requirement manifests",
                )
            )
        if not root_lock_install and not root_manifest_install and "--require-hashes" in line:
            hash_locked_non_root_commands += 1
        if not root_lock_install and not root_manifest_install and "--require-hashes" not in line:
            reason = _allowlisted_unhashed_install_reason(display, line)
            if reason is None:
                findings.append(
                    Finding(
                        display,
                        line_no,
                        "untracked_unhashed_python_install",
                        "pip install commands outside root lockfiles must be hash-locked or explicitly allowlisted",
                    )
                )
            else:
                allowlisted_unhashed_installs.append(
                    {
                        "line": line_no,
                        "reason": reason,
                    }
                )
    return {
        "path": display,
        "ok": not findings,
        "pip_install_commands": pip_install_commands,
        "root_dependency_commands": root_dependency_commands,
        "hash_locked_non_root_commands": hash_locked_non_root_commands,
        "allowlisted_unhashed_installs": allowlisted_unhashed_installs,
        "allowlisted_unhashed_install_commands": len(allowlisted_unhashed_installs),
        "findings": [finding.to_json() for finding in findings],
    }


def _iter_install_surfaces(root: Path) -> list[Path]:
    paths: set[Path] = set()
    self_path = Path(__file__).resolve()
    for pattern in INSTALL_SURFACE_GLOBS:
        paths.update(
            path
            for path in root.glob(pattern)
            if path.is_file() and path.resolve() != self_path
        )
    return sorted(paths)


def check_python_hash_locks(root: Path = ROOT) -> dict[str, Any]:
    lock_reports = [audit_lockfile(root / name, root=root) for name in LOCKFILES]
    surface_reports = []
    for path in _iter_install_surfaces(root):
        report = audit_install_surface(path, root=root)
        if (
            report["pip_install_commands"]
            or report["root_dependency_commands"]
            or report["hash_locked_non_root_commands"]
            or report["allowlisted_unhashed_install_commands"]
            or report["findings"]
        ):
            surface_reports.append(report)
    root_dependency_commands = sum(int(report["root_dependency_commands"]) for report in surface_reports)
    hash_locked_non_root_commands = sum(
        int(report["hash_locked_non_root_commands"])
        for report in surface_reports
    )
    pip_install_commands = sum(int(report["pip_install_commands"]) for report in surface_reports)
    allowlisted_unhashed_install_commands = sum(
        int(report["allowlisted_unhashed_install_commands"])
        for report in surface_reports
    )
    global_findings: list[Finding] = []
    if root_dependency_commands == 0:
        global_findings.append(
            Finding(
                "install-surfaces",
                0,
                "missing_hashed_root_install_command",
                "supported install surfaces must include at least one root lockfile install command",
            )
        )
    findings = [
        finding
        for report in lock_reports + surface_reports
        for finding in report["findings"]
    ] + [finding.to_json() for finding in global_findings]
    return {
        "schema": "zenodex/python_hash_lock_audit/v0",
        "ok": not findings,
        "lockfiles": lock_reports,
        "install_surfaces": surface_reports,
        "pip_install_commands": pip_install_commands,
        "root_dependency_commands": root_dependency_commands,
        "hash_locked_non_root_commands": hash_locked_non_root_commands,
        "allowlisted_unhashed_install_commands": allowlisted_unhashed_install_commands,
        "findings": findings,
    }


def _print_human(report: dict[str, Any]) -> None:
    if report["ok"]:
        print("ok")
        return
    print("error: python dependency hash-lock audit failed", file=sys.stderr)
    for finding in report["findings"]:
        line = finding["line"]
        location = finding["path"] if line == 0 else f"{finding['path']}:{line}"
        print(f"  - {location}: {finding['code']}: {finding['message']}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verify root Python lockfiles are hash-complete and supported installs use --require-hashes."
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable audit output")
    args = parser.parse_args(argv)

    report = check_python_hash_locks(ROOT)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
