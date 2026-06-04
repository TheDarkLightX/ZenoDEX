"""run_release_gate.sh must invoke the CBC production-claim gate as a NON-BLOCKING
advisory step.

The gate reports the per-surface production_security_claim and exits 1 while any
surface is unproven (which is every surface today, by design). Under the release
script's `set -e`, that would abort the release — so the invocation MUST be
non-blocking (a `||` fallback), and clearly labeled advisory. The gate becomes a
hard requirement only when a scope is genuinely declared production-ready; it must
never be flipped to blocking by assertion.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATE_SH = ROOT / "tools" / "run_release_gate.sh"


def test_release_gate_invokes_cbc_gate_non_blocking() -> None:
    text = GATE_SH.read_text(encoding="utf-8")
    assert "tools/gate_cbc_matrix_closure.py" in text, "release gate must invoke the CBC gate"

    lines = text.splitlines()
    idx = next(i for i, line in enumerate(lines) if "gate_cbc_matrix_closure.py" in line)
    # The invocation + its line-continuation must carry a `||` so a blocked claim
    # (exit 1) does not abort the release under `set -e`.
    window = " ".join(lines[idx : idx + 3])
    assert "||" in window, "CBC gate invocation must be non-blocking (|| fallback)"

    assert "advisory" in text.lower()
    assert "non-blocking" in text.lower()
