from __future__ import annotations

import json

from tools.zenodex_proof_mining_slot_batch_breakthrough_20260627 import (
    assignment_objective_key,
    build_cases,
    build_certificate,
    build_report,
    exact_batch_assignment,
    proposal_for_preferred_slot,
    sequential_linear_assignment,
    verify_certificate,
)


def test_exact_batch_assignment_lowers_worst_case_collision_displacement() -> None:
    proposals = [proposal_for_preferred_slot(slot, idx) for idx, slot in enumerate((0, 1, 0))]

    sequential = sequential_linear_assignment({}, proposals)
    exact, candidate_count = exact_batch_assignment({}, proposals)

    assert candidate_count == 336
    assert assignment_objective_key(proposals, exact) < assignment_objective_key(proposals, sequential)
    assert assignment_objective_key(proposals, sequential)[0] == 2
    assert assignment_objective_key(proposals, exact)[0] == 1


def test_certificates_verify_and_match_expected_lift_flags() -> None:
    cases = build_cases()
    certificates = [build_certificate(case) for case in cases]

    assert all(verify_certificate(certificate) for certificate in certificates)
    assert sum(1 for certificate in certificates if certificate["exact_beats_sequential"]) >= 3
    assert all(
        certificate["exact_beats_sequential"] == certificate["expected_exact_beats_sequential"]
        for certificate in certificates
    )


def test_certificate_rejects_domain_hash_and_assignment_mutations() -> None:
    certificate = build_certificate(build_cases()[1])

    bad_hash = json.loads(json.dumps(certificate))
    bad_hash["domain_hash"] = "0" * 64
    try:
        verify_certificate(bad_hash)
    except ValueError as exc:
        assert str(exc) == "domain hash mismatch"
    else:
        raise AssertionError("bad domain hash accepted")

    bad_slot = json.loads(json.dumps(certificate))
    bad_slot["exact_assignment"][0][1] = bad_slot["exact_assignment"][1][1]
    try:
        verify_certificate(bad_slot)
    except ValueError as exc:
        assert str(exc) == "duplicate assigned slot"
    else:
        raise AssertionError("duplicate slot accepted")


def test_report_replays_tau_and_records_ab_cow_work_items() -> None:
    report = build_report()

    assert report["ok"] is True
    assert report["tau"]["ok"] is True
    assert "ab_cow_exact_solver_envelope_v1.tau" in json.dumps(report["specification_frontier"])
    assert "Hungarian matching" in report["work_items"]["2_cow_matching"]
