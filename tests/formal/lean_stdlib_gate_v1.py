"""Small isolated gate for proof files whose transitive imports are Std-only.

Each caller copies one proof into a fresh source tree, compiles that copy with
the pinned Lean toolchain, and then compiles an independent consumer module.
The consumer receives the fresh ``.olean`` through a setup manifest, so the
process does not inherit a project or ambient ``LEAN_PATH``.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PINNED_VERSION = "4.27.0"
PINNED_TOOLCHAIN = f"leanprover/lean4:v{PINNED_VERSION}"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FORBIDDEN_SOURCE_TOKENS = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|ofReduceBool)\b",
    re.IGNORECASE,
)
WARNING_DIAGNOSTIC = re.compile(r"\bwarning:", re.IGNORECASE)


@dataclass(frozen=True)
class TheoremReference:
    """A named theorem and its independently checked consumer type."""

    qualified_name: str
    type_expression: str


@dataclass(frozen=True)
class LeanStdlibReceipt:
    """Evidence returned after both the source and consumer compile."""

    module_name: str
    source_sha256: str
    olean_sha256: str
    probe_output: str


def _pinned_lean_executable() -> Path:
    """Return the installed pinned compiler, exposing absence as a skip."""

    toolchain = (LEAN_PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != PINNED_TOOLCHAIN:
        pytest.fail(f"lean-toolchain is {toolchain!r}, expected {PINNED_TOOLCHAIN!r}")

    executable = (
        Path.home()
        / ".elan"
        / "toolchains"
        / "leanprover--lean4---v4.27.0"
        / "bin"
        / "lean"
    )
    if not executable.is_file():
        pytest.skip(f"installed pinned Lean {PINNED_VERSION} is unavailable: {executable}")

    version = subprocess.run(
        [str(executable), "--version"],
        cwd=LEAN_PROJECT,
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    if version.returncode != 0:
        pytest.fail(version.stdout + version.stderr)
    if f"version {PINNED_VERSION}," not in version.stdout:
        pytest.fail(f"unexpected pinned Lean version: {version.stdout + version.stderr}")
    return executable


def _clean_environment() -> dict[str, str]:
    """Keep compiler discovery deterministic and remove inherited library paths."""

    environment = dict(os.environ)
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    return environment


def _run(
    executable: Path,
    arguments: list[str],
    *,
    cwd: Path,
) -> subprocess.CompletedProcess[str]:
    try:
        result = subprocess.run(
            [str(executable), *arguments],
            cwd=cwd,
            env=_clean_environment(),
            capture_output=True,
            text=True,
            check=False,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.fail(f"pinned Lean timed out after {exc.timeout}s: {' '.join(arguments)}")

    diagnostics = result.stdout + result.stderr
    if result.returncode != 0:
        pytest.fail(diagnostics)
    if WARNING_DIAGNOSTIC.search(diagnostics):
        pytest.fail(f"pinned Lean emitted a warning:\n{diagnostics}")
    return result


def _module_name(relative_source: Path) -> str:
    return ".".join(relative_source.with_suffix("").parts)


def _check_axioms(output: str, references: tuple[TheoremReference, ...]) -> None:
    for reference in references:
        pattern = re.compile(
            rf"'{re.escape(reference.qualified_name)}' "
            r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
        )
        matches = pattern.findall(output)
        if len(matches) != 1:
            pytest.fail(
                f"missing unique #print axioms result for {reference.qualified_name}:\n{output}"
            )
        reported = {
            item.strip()
            for item in matches[0].split(",")
            if item.strip()
        }
        unexpected = reported - ALLOWED_AXIOMS
        if unexpected:
            pytest.fail(
                f"{reference.qualified_name} depends on non-standard axioms: {sorted(unexpected)}"
            )


def check_lean_stdlib_source(
    relative_source: str,
    references: tuple[TheoremReference, ...],
    tmp_path: Path,
) -> LeanStdlibReceipt:
    """Compile a fresh proof copy and a separate typed theorem consumer."""

    relative = Path(relative_source)
    original = LEAN_PROJECT / relative
    if not original.is_file():
        pytest.fail(f"Lean subject is missing: {original}")
    source_text = original.read_text(encoding="utf-8")
    if FORBIDDEN_SOURCE_TOKENS.search(source_text):
        pytest.fail(f"Lean subject contains a forbidden proof token: {original}")

    executable = _pinned_lean_executable()
    source_root = tmp_path / "source"
    library_root = tmp_path / "library"
    captured = source_root / relative
    olean = library_root / relative.with_suffix(".olean")
    captured.parent.mkdir(parents=True, exist_ok=True)
    olean.parent.mkdir(parents=True, exist_ok=True)
    captured.write_bytes(original.read_bytes())
    module = _module_name(relative)
    source_result = _run(
        executable,
        [
            "-DwarningAsError=true",
            "-R",
            str(source_root),
            "-o",
            str(olean),
            str(captured),
        ],
        cwd=source_root,
    )
    if source_result.stdout or source_result.stderr:
        pytest.fail(
            f"pinned Lean source compile was not silent:\n"
            f"{source_result.stdout}{source_result.stderr}"
        )

    probe_root = tmp_path / "probe"
    probe_root.mkdir(parents=True, exist_ok=True)
    probe = probe_root / "TheoremConsumer.lean"
    consumer_lines = [f"import {module}"]
    for reference in references:
        consumer_lines.extend(
            (
                f"example : {reference.type_expression} := @{reference.qualified_name}",
                f"#print axioms {reference.qualified_name}",
            )
        )
    probe.write_text("\n".join(consumer_lines) + "\n", encoding="utf-8")
    setup: dict[str, object] = {
        "name": "TheoremConsumer",
        "package?": None,
        "isModule": False,
        "imports?": None,
        "importArts": {module: [str(olean)]},
        "dynlibs": [],
        "plugins": [],
        "options": {},
    }
    setup_path = tmp_path / "theorem-consumer-setup.json"
    setup_path.write_text(json.dumps(setup), encoding="utf-8")
    probe_result = _run(
        executable,
        [
            "-DwarningAsError=true",
            "-R",
            str(probe_root),
            "--setup",
            str(setup_path),
            str(probe),
        ],
        cwd=probe_root,
    )
    if probe_result.stderr:
        pytest.fail(f"pinned Lean theorem consumer wrote stderr:\n{probe_result.stderr}")
    _check_axioms(probe_result.stdout, references)
    return LeanStdlibReceipt(
        module_name=module,
        source_sha256=hashlib.sha256(captured.read_bytes()).hexdigest(),
        olean_sha256=hashlib.sha256(olean.read_bytes()).hexdigest(),
        probe_output=probe_result.stdout,
    )
