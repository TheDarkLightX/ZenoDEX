from __future__ import annotations

from tools import proof_market_key_parity_v2 as parity


def test_source_pinned_ascii_python_rust_golden_vector_is_valid() -> None:
    evidence = parity.build_evidence()

    assert evidence["status"] == "BOUNDED_CROSS_LANGUAGE_GOLDEN_VECTOR"
    assert evidence["ok"] is True
    assert evidence["python"]["ok"] is True
    assert evidence["rust"]["status"] == "PASSED"
    assert evidence["rust"]["passed_tests"] == 2
    assert evidence["rust"]["failed_tests"] == 0
    assert all(evidence["receipt_checks"].values())
