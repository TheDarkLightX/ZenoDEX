from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest

from docs.research.discrete_argmax_proximity_test import Pool, _curvature_module
from tools.check_tight_argmax_exact_interval_certificate_20260630 import (
    MAX_D,
    AcceptedExactInterval,
    ExactReject,
    RejectedExactInterval,
    boundary_replay,
    build_exact_interval_certificate,
    build_interval_m_backed_exact_interval_certificate,
    build_report,
    negative_replay,
    valid_corpus_replay,
    verify_exact_interval_certificate_bytes,
)

ROOT = Path(__file__).resolve().parents[2]


def test_valid_corpus_exercises_nonvacuous_interior_intervals() -> None:
    replay = valid_corpus_replay()

    assert replay["ok"] is True
    assert replay["accepted_count"] == replay["case_count"]
    assert replay["random_case_count"] == 80
    assert replay["interior_case_count"] == 8
    assert replay["nonzero_interval_count"] >= 8
    assert replay["nonzero_window_count"] > 0
    assert replay["max_interval_width"] > 0.0


def test_boundary_certificates_keep_zero_width_endpoint_brackets() -> None:
    replay = boundary_replay()

    assert replay["ok"] is True
    cases = {case["case_id"]: case["accepted"] for case in replay["cases"]}
    assert cases["left_boundary"]["anchor"] == 0
    assert cases["right_boundary"]["anchor"] == 40
    assert cases["left_boundary"]["interval_width"] == 0.0
    assert cases["right_boundary"]["interval_width"] == 0.0


def test_accepted_certificate_has_exact_radius_obligation() -> None:
    p0 = Pool(1137, 1211, 0)
    p1 = Pool(1137, 1211, 0)
    D = 50

    raw = build_exact_interval_certificate(p0, p1, D)
    result = verify_exact_interval_certificate_bytes(p0, p1, D, raw)

    assert isinstance(result, AcceptedExactInterval)
    assert result.interval_lo <= result.interval_hi
    assert result.distance_sq_upper <= result.radius_sq
    assert result.radius_sq == Fraction(2) * result.tau_upper / result.m
    assert result.prod_argmax >= 0


def test_interval_m_backed_certificate_requires_referenced_artifact() -> None:
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    D = 100
    curvature = _curvature_module()
    interval_raw = curvature.build_refined_interval_curvature_m_certificate(p0, p1, D, 1, 4)
    interval_hash = hashlib.sha256(interval_raw).hexdigest()

    endpoint = verify_exact_interval_certificate_bytes(p0, p1, D, build_exact_interval_certificate(p0, p1, D))
    raw = build_interval_m_backed_exact_interval_certificate(p0, p1, D, interval_raw)
    missing = verify_exact_interval_certificate_bytes(p0, p1, D, raw)
    accepted = verify_exact_interval_certificate_bytes(p0, p1, D, raw, {interval_hash: interval_raw})
    tampered = verify_exact_interval_certificate_bytes(p0, p1, D, raw, {interval_hash: interval_raw + b"\n"})

    assert isinstance(endpoint, AcceptedExactInterval)
    assert isinstance(missing, RejectedExactInterval)
    assert missing.rejects == (ExactReject.M_CERTIFICATE_MISSING,)
    assert isinstance(accepted, AcceptedExactInterval)
    assert accepted.m_source == "interval_curvature_certificate"
    assert accepted.m_certificate_sha256 == interval_hash
    assert accepted.m >= endpoint.m
    assert accepted.radius_sq <= endpoint.radius_sq
    assert isinstance(tampered, RejectedExactInterval)
    assert tampered.rejects == (ExactReject.M_CERTIFICATE_HASH_MISMATCH,)


def test_negative_replay_keeps_stable_reject_family() -> None:
    replay = negative_replay()

    expected = {
        ExactReject.DUPLICATE_KEY.value,
        ExactReject.NONCANONICAL_BYTES.value,
        ExactReject.AUTHORITY_EFFECTS_PRESENT.value,
        ExactReject.BAD_RATIO.value,
        ExactReject.DOMAIN_HASH_MISMATCH.value,
        ExactReject.DERIVATIVE_BRACKET_FAILED.value,
        ExactReject.STALE_PROD.value,
        ExactReject.STALE_TAU.value,
        ExactReject.STALE_RADIUS.value,
        ExactReject.ARGMAX_NOT_CANONICAL_MAX.value,
    }

    assert replay["ok"] is True
    assert replay["case_count"] == len(expected)
    assert {case["expected_reject"] for case in replay["cases"]} == expected
    assert all(case["expected_reject"] in case["rejects"] for case in replay["cases"])


def test_domain_bound_is_fail_closed() -> None:
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    raw = build_exact_interval_certificate(p0, p1, MAX_D)

    with pytest.raises(ValueError, match="domain outside exact interval certificate bounds"):
        build_exact_interval_certificate(p0, p1, MAX_D + 1)

    result = verify_exact_interval_certificate_bytes(p0, p1, MAX_D + 1, raw)
    assert isinstance(result, RejectedExactInterval)
    assert result.rejects == (ExactReject.BAD_DOMAIN,)


def test_boolean_values_do_not_cross_integer_boundaries() -> None:
    p0 = Pool(1_000_000, 1, 0)
    p1 = Pool(1_000_000, 1, 0)

    with pytest.raises(ValueError, match="domain outside exact interval certificate bounds"):
        build_exact_interval_certificate(Pool(True, 1, 0), p1, 1)
    with pytest.raises(ValueError, match="domain outside exact interval certificate bounds"):
        build_exact_interval_certificate(object(), p1, 1)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="interval steps outside bounds"):
        build_exact_interval_certificate(p0, p1, 1, steps=True)

    payload = json.loads(build_exact_interval_certificate(p0, p1, 1).decode("utf-8"))
    assert payload["prod_anchor"] == 0
    assert payload["prod_argmax"] == 0
    payload["prod_anchor"] = False
    payload["prod_argmax"] = False
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")

    result = verify_exact_interval_certificate_bytes(p0, p1, 1, raw)

    assert isinstance(result, RejectedExactInterval)
    assert result.rejects == (ExactReject.STALE_PROD,)


def test_verifier_rejects_non_bytes_packets_and_resolver_values() -> None:
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    D = 100
    curvature = _curvature_module()
    interval_raw = curvature.build_refined_interval_curvature_m_certificate(p0, p1, D, 1, 4)
    interval_hash = hashlib.sha256(interval_raw).hexdigest()
    raw = build_interval_m_backed_exact_interval_certificate(p0, p1, D, interval_raw)

    packet_result = verify_exact_interval_certificate_bytes(p0, p1, D, bytearray(raw))  # type: ignore[arg-type]
    resolver_result = verify_exact_interval_certificate_bytes(
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
    malformed_result = verify_exact_interval_certificate_bytes(
        p0,
        p1,
        D,
        malformed_raw,
        {malformed_hash: malformed_artifact},
    )

    assert isinstance(packet_result, RejectedExactInterval)
    assert [reject.value for reject in packet_result.rejects] == ["bad_packet_type"]
    assert isinstance(resolver_result, RejectedExactInterval)
    assert [reject.value for reject in resolver_result.rejects] == ["bad_m_certificate_resolver"]
    assert isinstance(malformed_result, RejectedExactInterval)
    assert malformed_result.rejects == (ExactReject.M_CERTIFICATE_REJECTED,)


def test_report_contract_records_non_claims_and_replay_surface() -> None:
    report = build_report()

    assert report["ok"] is True
    assert report["valid_corpus"]["ok"] is True
    assert report["boundary_replay"]["ok"] is True
    assert report["negative_replay"]["ok"] is True
    assert report["schema"] == "zenodex.tight_argmax_exact_interval_report.v1"
    assert "D <= 4096" in " ".join(report["non_claims"])
    assert "research checker" in " ".join(report["non_claims"])


def test_exact_interval_cli_replay(tmp_path: Path) -> None:
    output_json = tmp_path / "report.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_tight_argmax_exact_interval_certificate_20260630.py",
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
    assert report["valid_corpus"]["nonzero_interval_count"] > 0
