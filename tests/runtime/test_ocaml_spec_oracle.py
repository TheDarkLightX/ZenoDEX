"""OCaml executable-spec oracle regression.

The OCaml runtime is a third implementation for small consensus-critical
surfaces. It is an assurance sidecar, not an authority path, but it helps catch
shared Python/Rust mistakes when its committed vectors stay fresh and its dune
test passes.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
OCAML_RUNTIME = REPO / "ocaml-runtime"


def test_ocaml_spec_vectors_are_current() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/runtime/ocaml_spec_vectors.py", "--check"],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr


def test_ocaml_spec_oracle_matches_python_vectors() -> None:
    if shutil.which("opam") is None:  # pragma: no cover - environment dependent
        pytest.skip("opam unavailable; OCaml oracle cannot run")

    dune_check = subprocess.run(
        ["opam", "exec", "--", "dune", "--version"],
        cwd=str(OCAML_RUNTIME),
        capture_output=True,
        text=True,
    )
    if dune_check.returncode != 0:  # pragma: no cover - environment dependent
        pytest.skip(f"dune unavailable in opam switch: {dune_check.stderr}")

    proc = subprocess.run(
        ["opam", "exec", "--", "dune", "test"],
        cwd=str(OCAML_RUNTIME),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
