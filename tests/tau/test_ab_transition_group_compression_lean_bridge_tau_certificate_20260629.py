from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_transition_group_compression_lean_bridge_tau_certificate_20260629 import (
    EXPECTED_LEAN_BRIDGE_REPORT_HASH,
    EXPECTED_LEAN_FILE_HASH,
    EXPECTED_REQUIRED_LEAN_MARKER_COUNT,
    EXPECTED_UPSTREAM_COMPRESSED_ROWS,
    EXPECTED_UPSTREAM_SOURCE_ROWS,
    REPORT_JSON,
    build_report,
    find_tau_bin,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def tau_certificate_report() -> dict[str, object]:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")
    return build_report()


def test_lean_bridge_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    assert tau_certificate_report["schema"] == (
        "zenodex.ab_transition_group_compression_lean_bridge_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_transition_group_compression_lean_bridge_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 15
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert tau_certificate_report["lean_bridge_report"]["sha256"] == (
        EXPECTED_LEAN_BRIDGE_REPORT_HASH
    )
    assert tau_certificate_report["lean_bridge_artifacts"]["lean_sha256"] == (
        EXPECTED_LEAN_FILE_HASH
    )
    assert tau_certificate_report["lean_bridge_artifacts"]["required_lean_marker_count"] == (
        EXPECTED_REQUIRED_LEAN_MARKER_COUNT
    )
    assert tau_certificate_report["upstream_compression_tau_report"][
        "source_transition_row_count"
    ] == EXPECTED_UPSTREAM_SOURCE_ROWS
    assert tau_certificate_report["upstream_compression_tau_report"][
        "compressed_row_count"
    ] == EXPECTED_UPSTREAM_COMPRESSED_ROWS
    assert tau_certificate_report["receipts"]["lean_compile"]["ok"] is True
    assert tau_certificate_report["receipts"]["formal_test"]["ok"] is True


def test_lean_bridge_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["lean_bridge_scope_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "missing_lean_bridge_report_reject",
        "lean_file_unpinned_reject",
        "aggregator_import_missing_reject",
        "theorem_surface_unbound_reject",
        "placeholder_scan_failed_reject",
        "lean_compile_missing_reject",
        "formal_test_missing_reject",
        "upstream_compression_tau_unbound_reject",
        "nonclaims_missing_reject",
        "authority_boundary_missing_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
        "replay_commands_unbound_reject",
    ):
        assert cases[case_id]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 1


def test_lean_bridge_tau_scope_and_nonclaims(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    scoped_claims = "\n".join(tau_certificate_report["breakthrough"]["scoped_claims"])

    assert "does not run Lean inside Tau" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "JSON canonicalization" in nonclaims
    assert "host generated-image construction" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims
    assert "upstream n=7 transition-group compression Tau certificate is bound" in scoped_claims


def test_lean_bridge_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_transition_group_compression_lean_bridge_tau_certificate_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert report["receipts"]["lean_compile"]["ok"] is True
    assert report["receipts"]["formal_test"]["ok"] is True
