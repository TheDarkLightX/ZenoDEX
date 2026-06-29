from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_ab_transition_group_compression_typechecks_without_placeholders() -> None:
    root = Path(__file__).resolve().parents[2]
    target = root / "lean-mathlib" / "Proofs" / "ABTransitionGroupCompression.lean"
    aggregator = root / "lean-mathlib" / "Proofs.lean"
    text = target.read_text(encoding="utf-8")
    aggregator_text = aggregator.read_text(encoding="utf-8")

    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert not forbidden.search(text)
    assert "import Proofs.ABTransitionGroupCompression" in aggregator_text
    assert "structure TransitionRow" in text
    assert "structure CompressedTransitionGroup" in text
    assert "def transitionGeneratedChildren" in text
    assert "def compressedGeneratedChildren" in text
    assert "def compressedTransitionGroupSound" in text
    assert "def compressionCoversTransitions" in text
    assert "def compressionHasNoExtraTransitions" in text
    assert "structure TransitionGroupCompressionHostTable" in text
    assert "def transitionGroupCompressionHostTableValid" in text
    assert "theorem compressedTransitionGroup_representative_mem_transitions" in text
    assert "theorem transitionGroupCompression_preserves_generatedChildImage" in text
    assert "theorem transitionGroupCompression_nonempty_groups_of_nonempty_transitions" in text
    assert "theorem transitionGroupCompressionHostTable_validates" in text
    assert "theorem witness_transitionGroupCompressionHostTable_validates" in text
    assert "does not prove Python-to-Lean" in text
    assert "refinement, JSON canonicalization" in text
    assert "settlement, state-root, production" in text

    lake = shutil.which("lake")
    if not lake:
        return
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "Proofs/ABTransitionGroupCompression.lean"],
            cwd=root / "lean-mathlib",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(
            f"lake env lean timed out after {exc.timeout}s for ABTransitionGroupCompression"
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
