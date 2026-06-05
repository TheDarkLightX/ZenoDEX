from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RUNTIME_SHADOW_YML = ROOT / ".github" / "workflows" / "runtime-shadow.yml"


def _workflow_text() -> str:
    return RUNTIME_SHADOW_YML.read_text(encoding="utf-8")


def _assert_watched_on_pull_request_and_push(path: str) -> None:
    text = _workflow_text()
    needle = f'- "{path}"'
    assert text.count(needle) == 2, f"{path} must be watched for pull_request and push"


def test_runtime_shadow_watches_spot_receipt_lean_sources() -> None:
    # Review grade: A- CI gate. These are source-pinned by the spot receipt, so
    # editing either proof file must trigger the per-PR receipt drift check.
    for path in (
        "lean-mathlib/Proofs/CPMMInvariants.lean",
        "lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean",
        "lean-mathlib/Proofs/CpmmSwapV8ExactInAdmissibility.lean",
        "lean-mathlib/Proofs/ZenoDEXNonces.lean",
        "src/kernels/dex/nonce_batch_sequencing_v1.yaml",
    ):
        _assert_watched_on_pull_request_and_push(path)


def test_runtime_shadow_watches_cbc_matrix_gate_surface() -> None:
    # The registry and pure evaluator are the production-claim boundary. A
    # config-only claim edit must still run the matrix closure tests in CI.
    for path in (
        "config/production/cbc_surface_evidence_v1.json",
        "tools/gate_cbc_matrix_closure.py",
        "src/integration/surface_security_claim.py",
        "tests/integration/test_gate_cbc_matrix_closure.py",
        "tests/integration/test_surface_security_claim.py",
    ):
        _assert_watched_on_pull_request_and_push(path)


def test_runtime_shadow_watches_state_root_surface_receipt_boundary() -> None:
    # Review grade: B -> A-. The state-root receipt source envelope now includes
    # node live-path code and both workflows, so changing any of them must run the
    # per-PR drift checker.
    for path in (
        "tools/check_state_root_surface_evidence.py",
        "tools/zeno_ledger_run_local.py",
        "tools/zeno_ledger_node.py",
        "tests/test_check_state_root_surface_evidence.py",
        "tests/integration/test_zeno_ledger_node_state_root_binding.py",
        "src/kernels/dex/state_root_v5_scope_contract.json",
        ".github/workflows/runtime-shadow.yml",
        ".github/workflows/release-integrity.yml",
    ):
        _assert_watched_on_pull_request_and_push(path)


def test_state_root_authority_mode_runs_only_in_rust_shadow_job() -> None:
    text = _workflow_text()
    assert "--ignore=tests/runtime/test_state_root_live_path.py" in text
    assert "tests/runtime/test_state_root_live_path.py \\" in text
    assert "tools/check_state_root_surface_evidence.py check --pretty --test-profile python" in text
    assert "tools/check_state_root_surface_evidence.py check --pretty --test-profile rust" in text
