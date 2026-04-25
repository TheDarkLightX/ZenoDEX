from __future__ import annotations

from tools.state_boundary_concolic import explore_all_targets, explore_target


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def test_state_boundary_concolic_canonical_hex_discovers_reject_paths() -> None:
    report = explore_target("canonical_hex_fixed_allow_0x")
    labels = _labels(report)
    assert "ok:0x" + ("aa" * 32) in labels
    assert "TypeError:x must be a str" in labels
    assert "ValueError:x must be 32 bytes (hex length 64)" in labels
    assert "ValueError:x must be valid hex" in labels
    assert "ValueError:nbytes must be a positive int" in labels
    assert report.unique_path_count >= 6


def test_state_boundary_concolic_domain_sep_discovers_reject_paths() -> None:
    report = explore_target("domain_sep_bytes")
    labels = _labels(report)
    assert "ok:b'zenodex:abc:v1\\x00'" in labels
    assert "ValueError:label must not contain NUL" in labels
    assert "ValueError:label must be ASCII" in labels
    assert "TypeError:label must be a non-empty str" in labels
    assert "ValueError:version must be a positive int" in labels
    assert report.unique_path_count >= 5


def test_state_boundary_concolic_bounded_json_discovers_reject_paths() -> None:
    report = explore_target("bounded_json_utf8_size")
    labels = _labels(report)
    assert "ok:11" in labels
    assert "TypeError:dict keys must be str for bounded_json_utf8_size" in labels
    assert "TypeError:floats are not allowed in canonical encoding" in labels
    assert "ValueError:json nesting exceeds max_depth" in labels
    assert "ValueError:json item count exceeds max_items" in labels
    assert "ValueError:json size exceeds max_bytes" in labels
    assert "ValueError:max_bytes must be a positive int" in labels
    assert "ValueError:max_depth must be a positive int" in labels
    assert "ValueError:max_items must be a positive int" in labels
    assert report.unique_path_count >= 9


def test_state_boundary_concolic_nonce_batch_discovers_reject_paths() -> None:
    report = explore_target("validate_and_apply_intent_nonce_batch")
    labels = _labels(report)
    assert "ok:last=0" in labels
    assert "ok:last=2" in labels
    assert "ok:last=7" in labels
    assert "reject:Missing/invalid nonce" in labels
    assert "reject:nonce presence must be consistent across batch" in labels
    assert "reject:duplicate nonce in batch" in labels
    assert "reject:nonce sequence invalid" in labels
    assert any(label.startswith("reject:invalid sender_pubkey for nonce accounting:") for label in labels)
    assert report.unique_path_count >= 10


def test_state_boundary_concolic_all_targets_are_covered() -> None:
    reports = explore_all_targets()
    by_name = {report.target: report for report in reports}
    assert set(by_name) == {
        "canonical_hex_fixed_allow_0x",
        "domain_sep_bytes",
        "bounded_json_utf8_size",
        "validate_and_apply_intent_nonce_batch",
    }
    assert by_name["canonical_hex_fixed_allow_0x"].total_cases >= 6
    assert by_name["domain_sep_bytes"].total_cases >= 5
    assert by_name["bounded_json_utf8_size"].total_cases >= 9
    assert by_name["validate_and_apply_intent_nonce_batch"].total_cases >= 12
