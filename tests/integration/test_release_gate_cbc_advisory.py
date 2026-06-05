"""run_release_gate.sh must invoke the CBC production-claim gate and distinguish
its exit codes.

The gate's exit contract:
  0  = every in-scope surface clear
  1  = blocked claim / production_security_claim=false
  2+ = structural/infrastructure failure (missing/corrupt registry, import, etc.)

The matrix is now reviewed-green. A future exit 1 is a regression and must fail
the release lane, just like infrastructure errors.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATE_SH = ROOT / "tools" / "run_release_gate.sh"
RELEASE_INTEGRITY_YML = ROOT / ".github" / "workflows" / "release-integrity.yml"


def test_release_gate_fails_on_blocked_claim_and_infrastructure_failure() -> None:
    text = GATE_SH.read_text(encoding="utf-8")
    assert "tools/gate_cbc_matrix_closure.py" in text, "release gate must invoke the CBC gate"

    lines = text.splitlines()
    idx = next(i for i, line in enumerate(lines) if "gate_cbc_matrix_closure.py" in line)
    block = "\n".join(lines[idx : idx + 14])

    # Capture the exit code rather than swallow it with a blanket `|| echo`.
    assert "cbc_status" in block, "must capture the gate exit code, not blanket-swallow it"
    # REVIEW [A- -> A]: exit 1 was advisory during promotion. With a reviewed
    # true claim, a blocked matrix is now a regression and must stop release.
    assert "1)" in block and "regressed to false" in block
    assert "advisory" not in block.lower()
    # Exit 2+ (structural/infrastructure) also FAILS CLOSED — the script re-exits.
    assert 'exit "$cbc_status"' in block or "exit $cbc_status" in block, \
        "structural/infra failure (exit 2+) must fail closed, not be swallowed"


def test_release_integrity_workflow_runs_cbc_gate_with_same_exit_contract() -> None:
    text = RELEASE_INTEGRITY_YML.read_text(encoding="utf-8")
    assert "tools/gate_cbc_matrix_closure.py --json" in text

    lines = text.splitlines()
    idx = next(i for i, line in enumerate(lines) if "gate_cbc_matrix_closure.py" in line)
    block = "\n".join(lines[idx : idx + 12])

    assert "cbc_status" in block
    assert "1)" in block and "regressed" in block.lower()
    assert "advisory" not in block.lower()
    assert 'exit "$cbc_status"' in block or "exit $cbc_status" in block


def test_release_integrity_workflow_runs_state_root_surface_gate() -> None:
    text = RELEASE_INTEGRITY_YML.read_text(encoding="utf-8")
    assert "tools/check_state_root_surface_evidence.py check --pretty" in text
    assert "tests/test_check_state_root_surface_evidence.py" in text


def test_release_integrity_workflow_runs_nonce_proof_binding_gates() -> None:
    text = RELEASE_INTEGRITY_YML.read_text(encoding="utf-8")
    # REVIEW [B+ -> A-]: runtime-shadow ran these through broad runtime tests,
    # but release-integrity only checked the kernel receipt. The future nonces
    # proof_artifact/formal_spec/running_impl flip depends on the exact-range
    # proof-to-live binding, ESSO structural gate, the formal-spec contract, and
    # coupled transition atomicity, so the release lane now runs them explicitly
    # instead of relying on an indirect receipt-only check.
    assert "tools/check_nonce_batch_formal_spec_contract.py check --pretty" in text
    assert "tests/test_check_nonce_batch_formal_spec_contract.py" in text
    assert "tests/runtime/test_nonce_esso_model.py" in text
    assert "tests/runtime/test_nonces_batch_wrapper_lean_property_binding.py" in text
    assert "tests/runtime/test_nonces_batch_binding.py" in text
    assert "tests/runtime/test_nonces_coupled_transition_atomicity.py" in text
