"""K03 AST/token static no-bypass checker tests."""

from __future__ import annotations

from experiments.fcis_m6_k03_static_no_bypass_check import run_checks
from tools.check_fcis_m6_k03_static_no_bypass import (
    load_policy,
    run_static_scan,
    scan_python_source,
    scan_rust_source,
)


def test_k03_current_protected_slice_passes() -> None:
    report = run_static_scan()
    assert report["ok"] is True
    assert report["python_checked_file_count"] == 4
    assert report["rust_checked_file_count"] == 0
    assert report["rust_scope_status"] == "unmounted_no_m6_rust_publisher"


def test_k03_mutation_campaign_passes() -> None:
    run_checks()


def test_k03_python_ast_catches_legacy_and_port_bypass() -> None:
    policy = load_policy()
    legacy = scan_python_source(
        "def bypass(source):\n    return evaluate_refinement_v1(source)\n",
        "src/integration/bypass.py",
        policy,
    )
    port = scan_python_source(
        "def bypass(port, state, request):\n    return publish_v1(port, state, request)\n",
        "src/integration/bypass_port.py",
        policy,
    )
    assert {str(item["kind"]) for item in legacy} == {"legacy_publisher_call"}
    assert {str(item["kind"]) for item in port} == {"direct_publication_port_bypass"}


def test_k03_rust_token_scan_catches_forbidden_module_and_call() -> None:
    policy = load_policy()
    issues = scan_rust_source(
        "use std::process::Command;\nfn bypass(connection: Conn) { connection.commit(); }\n",
        "rust-runtime/src/bypass.rs",
        policy,
    )
    kinds = {str(item["kind"]) for item in issues}
    assert "forbidden_rust_import" in kinds
    assert "forbidden_rust_effect_call" in kinds
