"""Focused evidence tests for recursive-STARK exact-once admission."""

from __future__ import annotations

import json

import pytest

from docs.research import recursive_stark_exact_once_smt as model


def _checks_by_name():
    return {check.name: check for check in model.run_checks()}


def test_complete_guards_prove_exact_once_and_reject_noop() -> None:
    checks = model.run_checks()
    assert [check.name for check in checks[:5]] == [
        "accepted_roots_cannot_reuse_root_id",
        "accepted_roots_cannot_reuse_child_id",
        "accepted_roots_cannot_reuse_receipt_id",
        "accepted_roots_cannot_reuse_message_id",
        "rejected_transition_preserves_committed_state",
    ]
    assert all(check.verdict == "UNSAT_PROVED" for check in checks[:5])
    assert all(check.model is None for check in checks[:5])


def test_each_removed_freshness_guard_has_concrete_reuse_model() -> None:
    checks = _checks_by_name()
    for domain in model.ID_DOMAINS:
        check = checks[f"removed_{domain}_freshness_guard_allows_reuse"]
        assert check.verdict == "SAT_COUNTEREXAMPLE"
        assert check.model is not None
        assert check.model[f"{domain}_id_0"] == check.model[f"{domain}_id_1"]
        assert check.model["accepted_0"] is True
        assert check.model["accepted_1"] is True
        assert check.model[f"fresh_{domain}"] is False


def test_removed_reject_noop_guard_has_concrete_state_mutation() -> None:
    check = _checks_by_name()[
        "removed_reject_noop_guard_allows_state_mutation"
    ]
    assert check.verdict == "SAT_COUNTEREXAMPLE"
    assert check.model is not None
    assert check.model["accepted"] is False
    changes = [
        check.model["committed_digest_before"]
        != check.model["committed_digest_after"]
    ]
    changes.extend(
        check.model[f"seen_{domain}_before"]
        != check.model[f"seen_{domain}_after"]
        for domain in model.ID_DOMAINS
    )
    assert any(changes)


def test_report_is_canonical_and_scopes_the_bounded_claim() -> None:
    first = model.build_report()
    second = model.build_report()
    rendered = model.render_report(first)
    assert rendered == model.render_report(second)
    assert json.loads(rendered) == first
    assert first["ok"] is True
    assert first["schema"] == "zenodex.recursive_stark_exact_once_smt.v1"
    assert first["model"]["finite_bounds"]["admission_attempts"] == 2
    assert "unbounded traces or recursion depth" in first["model"]["exclusions"]


@pytest.mark.parametrize("verdict", ["UNKNOWN", "TIMEOUT", "ERROR"])
def test_solver_indeterminacy_is_fail_closed(verdict: str, monkeypatch) -> None:
    failed_check = {
        "expected_verdict": "UNSAT_PROVED",
        "name": "synthetic_solver_failure",
        "verdict": verdict,
    }
    assert model.checks_succeeded([failed_check]) is False
    monkeypatch.setattr(model, "build_report", lambda: {"checks": [failed_check]})
    assert model.main([]) == 1
