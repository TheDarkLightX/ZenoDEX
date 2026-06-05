"""run_release_gate.sh must invoke the CBC production-claim gate and DISTINGUISH
its exit codes — advisory on a blocked claim, fail-closed on an infrastructure error.

The gate's exit contract:
  0  = every in-scope surface clear
  1  = blocked claim (surfaces unproven — the expected state today)
  2+ = structural/infrastructure failure (missing/corrupt registry, import, etc.)

A blanket ``|| echo`` would swallow exit 2 the same as exit 1, letting the release
reach ``ok`` with a missing/corrupt registry — a fail-open hole (Codex P2). So the
release gate must treat only exit 1 as advisory and FAIL CLOSED on exit 2+.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATE_SH = ROOT / "tools" / "run_release_gate.sh"
RELEASE_INTEGRITY_YML = ROOT / ".github" / "workflows" / "release-integrity.yml"


def test_release_gate_distinguishes_advisory_from_infrastructure_failure() -> None:
    text = GATE_SH.read_text(encoding="utf-8")
    assert "tools/gate_cbc_matrix_closure.py" in text, "release gate must invoke the CBC gate"

    lines = text.splitlines()
    idx = next(i for i, line in enumerate(lines) if "gate_cbc_matrix_closure.py" in line)
    block = "\n".join(lines[idx : idx + 14])

    # Capture the exit code rather than swallow it with a blanket `|| echo`.
    assert "cbc_status" in block, "must capture the gate exit code, not blanket-swallow it"
    # Exit 1 (blocked claim) is the only advisory/non-blocking path.
    assert "1)" in block and "advisory" in block.lower()
    # Exit 2+ (structural/infrastructure) FAILS CLOSED — the script re-exits.
    assert 'exit "$cbc_status"' in block or "exit $cbc_status" in block, \
        "structural/infra failure (exit 2+) must fail closed, not be swallowed"


def test_release_integrity_workflow_runs_cbc_gate_with_same_exit_contract() -> None:
    text = RELEASE_INTEGRITY_YML.read_text(encoding="utf-8")
    assert "tools/gate_cbc_matrix_closure.py --json" in text

    lines = text.splitlines()
    idx = next(i for i, line in enumerate(lines) if "gate_cbc_matrix_closure.py" in line)
    block = "\n".join(lines[idx : idx + 12])

    assert "cbc_status" in block
    assert "1)" in block and "advisory" in block.lower()
    assert 'exit "$cbc_status"' in block or "exit $cbc_status" in block
