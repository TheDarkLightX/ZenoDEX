from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

from docs.research.discrete_argmax_proximity_test import Pool, _curvature_module
from tools.check_nonendpoint_hybrid_root_guard_20260630 import (
    M_SOURCE_INTERVAL_CERTIFICATE,
    GuardReject,
    RejectedGuard,
    build_nonendpoint_hybrid_root_guard_certificate,
    build_report,
    corpus_replay,
    negative_replay,
    unsafe_fixture_replay,
    verify_nonendpoint_hybrid_root_guard_certificate_bytes,
)

ROOT = Path(__file__).resolve().parents[2]


def test_nonendpoint_hybrid_root_guard_report_contract() -> None:
    report = build_report()

    assert report["schema"] == "zenodex.nonendpoint_hybrid_root_guard_report.v1"
    assert report["ok"] is True
    assert "exact root-side certificate" in report["claim"]
    assert "does not alter production routing" in " ".join(report["non_claims"])

    corpus = report["corpus"]
    assert corpus["case_count"] == 160
    assert corpus["accepted_count"] == 160
    assert corpus["interval_count"] == 80
    assert corpus["stationary_count"] == 80
    assert corpus["shrink_count"] > 0
    assert corpus["max_distance_over_radius"] <= 1.0


def test_unsafe_stationary_fixture_is_repaired_by_root_guard() -> None:
    replay = unsafe_fixture_replay()

    assert replay["ok"] is True
    assert replay["failure_family_repaired"] == "stationary_m_hybrid_under_radius"
    accepted = replay["accepted"]
    assert accepted["m_source"] == "stationary_curvature_certificate"
    assert accepted["distance_over_radius"] <= 1.0
    assert accepted["endpoint_over_source_radius"] > 1.0


def test_corpus_replay_is_nonvacuous() -> None:
    replay = corpus_replay(interval_count=20, stationary_count=20)

    assert replay["ok"] is True
    assert replay["case_count"] == 40
    assert replay["accepted_count"] == 40
    assert replay["shrink_count"] > 0
    assert replay["max_endpoint_over_source_radius"] > 1.0


def test_nonendpoint_hybrid_root_guard_requires_resolved_m_artifact() -> None:
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    D = 100
    interval_raw = _curvature_module().build_refined_interval_curvature_m_certificate(p0, p1, D, 1, 4)
    interval_hash = hashlib.sha256(interval_raw).hexdigest()
    raw = build_nonendpoint_hybrid_root_guard_certificate(
        p0,
        p1,
        D,
        M_SOURCE_INTERVAL_CERTIFICATE,
        interval_raw,
    )

    missing = verify_nonendpoint_hybrid_root_guard_certificate_bytes(p0, p1, D, raw)
    tampered = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        D,
        raw,
        {interval_hash: interval_raw + b"\n"},
    )
    accepted = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        D,
        raw,
        {interval_hash: interval_raw},
    )

    assert isinstance(missing, RejectedGuard)
    assert missing.rejects == (GuardReject.M_CERTIFICATE_MISSING,)
    assert isinstance(tampered, RejectedGuard)
    assert tampered.rejects == (GuardReject.M_CERTIFICATE_HASH_MISMATCH,)
    assert not isinstance(accepted, RejectedGuard)


def test_boolean_values_do_not_cross_root_guard_integer_boundaries() -> None:
    p0 = Pool(1_000_000, 1, 0)
    p1 = Pool(1_000_000, 1, 0)
    curvature = _curvature_module()
    interval_raw = curvature.build_refined_interval_curvature_m_certificate(p0, p1, 1, 1, 4)
    interval_hash = hashlib.sha256(interval_raw).hexdigest()

    with pytest.raises(ValueError, match="step count outside bounds"):
        build_nonendpoint_hybrid_root_guard_certificate(
            p0,
            p1,
            1,
            M_SOURCE_INTERVAL_CERTIFICATE,
            interval_raw,
            bracket_steps=True,
        )

    payload = json.loads(
        build_nonendpoint_hybrid_root_guard_certificate(
            p0,
            p1,
            1,
            M_SOURCE_INTERVAL_CERTIFICATE,
            interval_raw,
        ).decode("utf-8")
    )
    assert payload["prod_anchor"] == 0
    assert payload["prod_argmax"] == 0
    payload["prod_anchor"] = False
    payload["prod_argmax"] = False
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")

    result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        1,
        raw,
        {interval_hash: interval_raw},
    )

    assert isinstance(result, RejectedGuard)
    assert result.rejects == (GuardReject.STALE_PROD,)


def test_root_guard_rejects_non_bytes_packets_and_resolver_values() -> None:
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    D = 100
    interval_raw = _curvature_module().build_refined_interval_curvature_m_certificate(p0, p1, D, 1, 4)
    interval_hash = hashlib.sha256(interval_raw).hexdigest()
    raw = build_nonendpoint_hybrid_root_guard_certificate(
        p0,
        p1,
        D,
        M_SOURCE_INTERVAL_CERTIFICATE,
        interval_raw,
    )

    packet_result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        D,
        bytearray(raw),  # type: ignore[arg-type]
    )
    resolver_result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        D,
        raw,
        {interval_hash: bytearray(interval_raw)},  # type: ignore[dict-item]
    )
    malformed_artifact = b"{}"
    malformed_hash = hashlib.sha256(malformed_artifact).hexdigest()
    malformed_payload = json.loads(raw.decode("utf-8"))
    malformed_payload["m_certificate_sha256"] = malformed_hash
    malformed_raw = json.dumps(malformed_payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    malformed_result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        D,
        malformed_raw,
        {malformed_hash: malformed_artifact},
    )

    assert isinstance(packet_result, RejectedGuard)
    assert [reject.value for reject in packet_result.rejects] == ["bad_packet_type"]
    assert isinstance(resolver_result, RejectedGuard)
    assert [reject.value for reject in resolver_result.rejects] == ["bad_m_certificate_resolver"]
    assert isinstance(malformed_result, RejectedGuard)
    assert malformed_result.rejects == (GuardReject.M_CERTIFICATE_REJECTED,)


def test_negative_replay_keeps_stable_rejects() -> None:
    replay = negative_replay()

    expected = {
        GuardReject.DUPLICATE_KEY.value,
        GuardReject.NONCANONICAL_BYTES.value,
        GuardReject.AUTHORITY_EFFECTS_PRESENT.value,
        GuardReject.BAD_M_SOURCE.value,
        GuardReject.M_CERTIFICATE_MISSING.value,
        GuardReject.M_CERTIFICATE_HASH_MISMATCH.value,
        GuardReject.DERIVATIVE_BRACKET_FAILED.value,
        GuardReject.STALE_ALPHA.value,
        GuardReject.STALE_RADIUS.value,
        GuardReject.STALE_DISTANCE.value,
        GuardReject.ARGMAX_NOT_CANONICAL_MAX.value,
    }

    assert replay["ok"] is True
    assert replay["case_count"] == len(expected)
    assert {case["expected_reject"] for case in replay["cases"]} == expected
    assert all(case["expected_reject"] in case["rejects"] for case in replay["cases"])


def test_nonendpoint_hybrid_root_guard_cli(tmp_path: Path) -> None:
    output_json = tmp_path / "report.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_nonendpoint_hybrid_root_guard_20260630.py",
            "--output-json",
            str(output_json),
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(output_json.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["unsafe_fixture"]["ok"] is True
