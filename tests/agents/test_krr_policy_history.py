from __future__ import annotations

import pytest

from src.agents.krr_policy_history import (
    _as_str_list,
    _load_history_rows,
    _load_source_rows,
    _report_decision,
    _report_phase,
    _supported_checks_for_report,
    build_autotrader_krr_history,
)


def _compile_report() -> dict[str, object]:
    return {
        "schema": "zenodex/autotrader-policy-compile/v1",
        "ok": True,
        "compile_contract_tau_receipt": {"spec_id": "autotrader_compile_contract_v1"},
        "krr_advice": {
            "phase": "compile",
            "candidate_checks": [
                "policy::compile_guard",
                "tau::compile_contract",
                "policy::template_bounds",
                "policy::owner_binding",
                "policy::budget_guard",
            ],
            "preferred_checks": ["policy::compile_guard", "policy::template_bounds"],
        },
    }


def _shadow_skip_report() -> dict[str, object]:
    return {
        "schema": "zenodex/autotrader-shadow-report/v1",
        "mode": "shadow",
        "decision": {
            "tag": "skip",
            "reason": "quote_receipt_stale:2>1",
            "tau_policy_receipt": None,
        },
        "krr_advice": {
            "phase": "shadow",
            "candidate_checks": [
                "policy::oracle_freshness",
                "quote::receipt_verify",
                "quote::receipt_binding",
            ],
            "preferred_checks": ["policy::oracle_freshness", "quote::receipt_verify"],
        },
    }


def _live_reject_report() -> dict[str, object]:
    return {
        "schema": "zenodex/autotrader-live-report/v1",
        "mode": "live_prepare",
        "decision": {
            "tag": "reject",
            "reason": "signer_pubkey_mismatch",
            "tau_policy_receipt": None,
        },
        "nonce_tau_receipts": [],
        "krr_advice": {
            "phase": "live",
            "candidate_checks": [
                "live::signer_match",
                "live::nonce_guard",
                "live::signed_intent_envelope",
            ],
            "preferred_checks": ["live::signer_match", "live::nonce_guard"],
        },
    }


def test_build_autotrader_krr_history_merges_compile_shadow_and_live_reports() -> None:
    history = build_autotrader_krr_history(
        reports=[_compile_report(), _shadow_skip_report(), _live_reject_report()],
        existing_history={
            "history_check_stats": {
                "policy::budget_guard": {"total": 2, "supported": 1},
            }
        },
    )

    assert history["schema"] == "zenodex/autotrader-krr-history/v1"
    assert history["report_count"] == 3
    assert history["phase_counts"] == {"compile": 1, "live": 1, "shadow": 1}
    rows = history["history_check_stats"]
    assert rows["policy::budget_guard"] == {"total": 3, "supported": 2, "support_rate": 0.666667}
    assert rows["tau::compile_contract"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["policy::oracle_freshness"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["quote::receipt_verify"] == {"total": 1, "supported": 0, "support_rate": 0.0}
    assert rows["live::signer_match"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["live::nonce_guard"] == {"total": 1, "supported": 0, "support_rate": 0.0}
    assert history["history_source_stats"] == {}


def test_build_autotrader_krr_history_maps_tau_and_nonce_receipts_and_ignores_bad_rows() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {"schema": "bad", "krr_advice": []},
            {
                "schema": "zenodex/autotrader-shadow-report/v1",
                "mode": "shadow",
                "decision": {
                    "tag": "reject",
                    "reason": "tau_policy_mismatch:local=1,tau=0,expected=1",
                    "tau_policy_receipt": {"spec_id": "autotrader_signal_provenance_guard_v1"},
                },
                "krr_advice": {
                    "phase": "shadow",
                    "candidate_checks": [
                        "policy::tau_bundle",
                        "tau::signal_provenance_guard",
                        "policy::signal_provenance",
                    ],
                },
            },
            {
                "schema": "zenodex/autotrader-live-report/v1",
                "mode": "live_prepare",
                "decision": {
                    "tag": "reject",
                    "reason": "nonce_tau_mismatch:intent_id=x,local=1,tau=0",
                    "tau_policy_receipt": None,
                },
                "nonce_tau_receipts": [{"spec_id": "autotrader_nonce_guard_v1"}],
                "krr_advice": {
                    "phase": "live",
                    "candidate_checks": ["live::nonce_guard", "tau::nonce_guard"],
                },
            },
        ]
    )

    rows = history["history_check_stats"]
    assert rows["policy::tau_bundle"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["tau::signal_provenance_guard"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["policy::signal_provenance"] == {"total": 1, "supported": 0, "support_rate": 0.0}
    assert rows["live::nonce_guard"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["tau::nonce_guard"] == {"total": 1, "supported": 1, "support_rate": 1.0}


def test_build_autotrader_krr_history_maps_compile_tau_receipt_on_reject() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {
                "schema": "zenodex/autotrader-policy-compile/v1",
                "ok": False,
                "error": "compile_contract_rejected",
                "compile_contract_tau_receipt": {"spec_id": "autotrader_compile_contract_v1"},
                "krr_advice": {
                    "phase": "compile",
                    "candidate_checks": ["tau::compile_contract", "policy::compile_guard"],
                },
            }
        ]
    )

    rows = history["history_check_stats"]
    assert rows["tau::compile_contract"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["policy::compile_guard"] == {"total": 1, "supported": 0, "support_rate": 0.0}


def test_report_decision_rejects_truthy_string_compile_ok() -> None:
    decision, reason, detail = _report_decision(
        {"schema": "zenodex/autotrader-policy-compile/v1", "ok": "false", "error": "compile_failed"},
        "compile",
    )

    assert (decision, reason, detail) == ("reject", "compile_failed", None)


def test_build_autotrader_krr_history_maps_session_state_guards() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {
                "schema": "zenodex/autotrader-live-report/v1",
                "mode": "live_prepare",
                "decision": {
                    "tag": "reject",
                    "reason": "session_state_revoked:5>=5",
                    "tau_policy_receipt": {"spec_id": "autotrader_session_state_guard_v1"},
                },
                "krr_advice": {
                    "phase": "live",
                    "candidate_checks": ["live::session_state", "tau::session_state_guard"],
                },
            }
        ]
    )

    rows = history["history_check_stats"]
    assert rows["live::session_state"] == {"total": 1, "supported": 1, "support_rate": 1.0}
    assert rows["tau::session_state_guard"] == {"total": 1, "supported": 1, "support_rate": 1.0}


def test_build_autotrader_krr_history_ignores_unknown_compile_tau_receipts() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {
                "schema": "zenodex/autotrader-policy-compile/v1",
                "ok": False,
                "error": "compile_failed",
                "compile_contract_tau_receipt": {"spec_id": "unknown_compile_spec"},
                "krr_advice": {
                    "phase": "compile",
                    "candidate_checks": ["policy::compile_guard"],
                },
            }
        ]
    )

    rows = history["history_check_stats"]
    assert "tau::compile_contract" not in rows
    assert rows["policy::compile_guard"] == {"total": 1, "supported": 0, "support_rate": 0.0}


def test_krr_history_helpers_cover_input_normalization_and_empty_paths() -> None:
    assert _as_str_list("bad") == []
    assert _as_str_list(["", "a", "a", "b"]) == ["a", "b"]

    rows = _load_history_rows(
        {
            "history_check_stats": {
                "": {"total": 1},
                "bad-row": "bad",
                "rate-only": {"total": "bad", "support_rate": "bad"},
                "supported-bad": {"total": 2, "supported": "bad"},
                "negative-total": {"total": -4, "supported": 1},
            }
        }
    )
    assert rows["rate-only"] == {"total": 0, "supported": 0, "support_rate": 0.0}
    assert rows["supported-bad"] == {"total": 2, "supported": 0, "support_rate": 0.0}
    assert rows["negative-total"] == {"total": 0, "supported": 0, "support_rate": 0.0}
    assert _load_history_rows({"history_check_stats": "bad"}) == {}
    assert _load_history_rows(None) == {}
    source_rows = _load_source_rows(
        {
            "history_source_stats": {
                "alpha": {
                    "total": 3.9,
                    "submit": True,
                    "reject": "bad",
                    "skip": 1,
                    "trusted": 2,
                    "advisory": 1,
                    "registered": 2,
                    "auth_ok": 3,
                    "freshness_ok": [],
                },
                "bad": "row",
                "beta": {"total": -1, "submit": 3},
            }
        }
    )
    assert source_rows["alpha"] == {
        "total": 3,
        "submit": 1,
        "reject": 0,
        "skip": 1,
        "trusted": 2,
        "advisory": 1,
        "registered": 2,
        "auth_ok": 3,
        "freshness_ok": 0,
        "submit_rate": 1 / 3,
    }
    assert source_rows["beta"] == {
        "total": 0,
        "submit": 0,
        "reject": 0,
        "skip": 0,
        "trusted": 0,
        "advisory": 0,
        "registered": 0,
        "auth_ok": 0,
        "freshness_ok": 0,
        "submit_rate": 0.0,
    }
    assert _load_source_rows({"history_source_stats": "bad"}) == {}
    assert _load_source_rows(None) == {}

    assert _report_phase({"mode": "shadow"}, {}) == "shadow"
    assert _report_phase({"mode": "live"}, {}) == "live"
    assert _report_phase({"schema": "zenodex/autotrader-policy-compile/v1"}, {}) == "compile"
    assert _report_phase({}, {}) == "unknown"

    assert _report_decision({"ok": False, "error": "bad"}, "compile") == ("reject", "bad", None)
    assert _report_decision({}, "unknown") == ("unknown", "", None)


def test_krr_history_rows_propagate_unexpected_numeric_failures() -> None:
    class BrokenInt:
        def __int__(self) -> int:
            raise RuntimeError("broken numeric source")

    class BrokenFloat(float):
        def __int__(self) -> int:
            raise RuntimeError("broken numeric source")

    with pytest.raises(RuntimeError, match="broken numeric source"):
        _load_history_rows({"history_check_stats": {"x": {"total": BrokenInt()}}})
    with pytest.raises(RuntimeError, match="broken numeric source"):
        _load_history_rows({"history_check_stats": {"x": {"total": 1, "supported": BrokenInt()}}})
    with pytest.raises(RuntimeError, match="broken numeric source"):
        _load_source_rows({"history_source_stats": {"source": {"total": BrokenFloat(1.0)}}})


@pytest.mark.parametrize(
    ("reason", "phase", "extra_report", "expected"),
    [
        ("tau_tool_unavailable:missing", "shadow", {}, {"policy::tau_bundle"}),
        ("tau_policy_backend_requires_enabled_tau_config", "shadow", {}, {"policy::tau_bundle"}),
        ("strategy_window_not_open:5<7", "shadow", {}, {"policy::window_guard", "tau::execution_guard"}),
        ("cadence_not_elapsed:5<7", "shadow", {}, {"policy::cadence_guard", "tau::execution_guard"}),
        ("max_live_orders_reached:3>2", "shadow", {}, {"policy::live_order_cap", "tau::execution_guard"}),
        ("budget_guard_rejected:kill_switch_active", "shadow", {}, {"policy::kill_switch", "policy::budget_guard", "tau::budget_guard"}),
        ("budget_guard_rejected:window_budget_exceeded", "shadow", {}, {"policy::budget_guard", "tau::budget_guard"}),
        ("budget_window_roll_failed:oob", "shadow", {}, {"policy::budget_guard"}),
        ("budget_window_regression:4<5", "shadow", {}, {"policy::budget_guard"}),
        ("lifetime_cap_exceeded:12>10", "shadow", {}, {"policy::lifetime_cap"}),
        ("receipt_missing_quote_epoch", "shadow", {}, {"policy::oracle_freshness", "tau::oracle_freshness_guard"}),
        ("receipt_invalid_quote_epoch", "shadow", {}, {"policy::oracle_freshness", "tau::oracle_freshness_guard"}),
        (
            "signal_provenance_rejected:signal_auth_invalid",
            "shadow",
            {},
            {"policy::signal_provenance", "quote::receipt_verify", "quote::receipt_binding"},
        ),
        ("unsupported_receipt_kind:exact_out", "shadow", {}, {"quote::receipt_verify", "quote::receipt_binding"}),
        ("receipt_asset_mismatch:want=A/B,got=A/C", "shadow", {}, {"quote::receipt_verify", "quote::receipt_binding"}),
        ("intent_construction_failed:ValueError:oops", "shadow", {}, {"quote::receipt_verify", "quote::receipt_binding"}),
        ("intent_amount_missing_or_invalid:index=0", "shadow", {}, {"quote::receipt_verify", "quote::receipt_binding"}),
        ("wallet_capability_disabled", "live", {}, {"live::wallet_capability"}),
        ("strategy_action_not_allowed:place_swap_exact_in", "shadow", {}, {"policy::compile_guard", "policy::template_bounds"}),
        ("unsupported_strategy_template:dca2", "shadow", {}, {"policy::compile_guard", "policy::template_bounds"}),
        (
            "tau_policy_mismatch:local=1,tau=0,expected=1",
            "shadow",
            {"decision": {"tau_policy_receipt": {"spec_id": "unknown_spec"}}},
            {"policy::tau_bundle"},
        ),
        (
            "nonce_tau_mismatch:intent_id=x,local=1,tau=0",
            "live",
            {"nonce_tau_receipts": [{"spec_id": "autotrader_nonce_guard_v1"}]},
            {"live::nonce_guard", "tau::nonce_guard"},
        ),
        (
            "live_nonce_validation_failed:bad_nonce",
            "live",
            {"nonce_tau_receipts": [{"spec_id": "autotrader_nonce_guard_v1"}]},
            {"live::nonce_guard", "tau::nonce_guard"},
        ),
    ],
)
def test_supported_checks_for_report_reason_taxonomy(
    reason: str,
    phase: str,
    extra_report: dict[str, object],
    expected: set[str],
) -> None:
    report: dict[str, object] = {
        "decision": {"tag": "reject", "reason": reason, "tau_policy_receipt": None},
        "nonce_tau_receipts": [],
    }
    report.update(extra_report)
    checks = {
        "policy::tau_bundle",
        "policy::window_guard",
        "tau::execution_guard",
        "policy::cadence_guard",
        "policy::live_order_cap",
        "policy::kill_switch",
        "policy::budget_guard",
        "tau::budget_guard",
        "policy::lifetime_cap",
        "policy::oracle_freshness",
        "tau::oracle_freshness_guard",
        "quote::receipt_verify",
        "quote::receipt_binding",
        "policy::signal_provenance",
        "policy::compile_guard",
        "policy::template_bounds",
        "live::wallet_capability",
        "live::nonce_guard",
        "tau::signal_provenance_guard",
        "tau::nonce_guard",
    }
    assert _supported_checks_for_report(
        report=report,
        phase=phase,
        decision_tag="reject",
        reason=reason,
        candidate_checks=checks,
    ) == expected


def test_build_autotrader_krr_history_ignores_empty_check_sets_and_empty_decisions() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {"schema": "ignored", "krr_advice": {}},
            {
                "schema": "zenodex/autotrader-shadow-report/v1",
                "mode": "shadow",
                "decision": {"tag": "", "reason": "", "tau_policy_receipt": None},
                "krr_advice": {"phase": "shadow", "preferred_checks": ["policy::window_guard"]},
            },
        ]
    )

    assert history["report_count"] == 1
    assert history["decision_counts"] == {}
    assert history["reason_counts"] == {}
    assert history["history_check_stats"]["policy::window_guard"] == {
        "total": 1,
        "supported": 0,
        "support_rate": 0.0,
    }


def test_supported_checks_for_report_ignores_unmatched_live_nonce_reason() -> None:
    assert _supported_checks_for_report(
        report={
            "decision": {"tag": "reject", "reason": "signer_pubkey_mismatch", "tau_policy_receipt": None},
            "nonce_tau_receipts": [{"spec_id": "autotrader_nonce_guard_v1"}],
        },
        phase="live",
        decision_tag="reject",
        reason="signer_pubkey_mismatch",
        candidate_checks={"live::nonce_guard", "tau::nonce_guard", "live::signer_match"},
    ) == {"live::signer_match"}


def test_build_autotrader_krr_history_collects_external_source_stats() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {
                "schema": "zenodex/autotrader-live-report/v1",
                "mode": "live_prepare",
                "decision": {"tag": "submit", "reason": "", "tau_policy_receipt": None},
                "external_signals": [
                    {
                        "signal_id": "sig.1",
                        "source_id": "oracle.alpha",
                        "trust_tier": "verified",
                        "auth_ok": True,
                        "freshness_ok": True,
                        "advisory_only": False,
                    },
                    {
                        "signal_id": "sig.2",
                        "source_id": "news.beta",
                        "trust_tier": "advisory",
                        "auth_ok": False,
                        "freshness_ok": True,
                        "advisory_only": True,
                    },
                ],
                "signal_source_registry": {
                    "entries": [
                        "bad",
                        {"source_id": ""},
                        {"source_id": "oracle.alpha"},
                    ]
                },
                "krr_advice": {
                    "phase": "live",
                    "candidate_checks": ["signal::source_registry", "signal::source_history"],
                },
            },
            {
                "schema": "zenodex/autotrader-shadow-report/v1",
                "mode": "shadow",
                "decision": {"tag": "reject", "reason": "quote_receipt_stale:2>1", "tau_policy_receipt": None},
                "external_signals": [
                    {
                        "signal_id": "sig.3",
                        "source_id": "oracle.alpha",
                        "trust_tier": "verified",
                        "auth_ok": True,
                        "freshness_ok": False,
                        "advisory_only": False,
                    }
                ],
                "signal_source_registry": {
                    "entries": [
                        {"source_id": "oracle.alpha"},
                    ]
                },
                "krr_advice": {
                    "phase": "shadow",
                    "candidate_checks": ["policy::oracle_freshness"],
                },
            },
        ]
    )

    source_rows = history["history_source_stats"]
    assert source_rows["oracle.alpha"] == {
        "total": 2,
        "submit": 1,
        "reject": 1,
        "skip": 0,
        "trusted": 2,
        "advisory": 0,
        "registered": 2,
        "auth_ok": 2,
        "freshness_ok": 1,
        "submit_rate": 0.5,
    }
    assert source_rows["news.beta"] == {
        "total": 1,
        "submit": 1,
        "reject": 0,
        "skip": 0,
        "trusted": 0,
        "advisory": 1,
        "registered": 0,
        "auth_ok": 0,
        "freshness_ok": 1,
        "submit_rate": 1.0,
    }


def test_build_autotrader_krr_history_ignores_bad_external_signal_rows() -> None:
    history = build_autotrader_krr_history(
        reports=[
            {
                "schema": "zenodex/autotrader-shadow-report/v1",
                "mode": "shadow",
                "decision": {"tag": "unknown", "reason": "", "tau_policy_receipt": None},
                "external_signals": [
                    "bad",
                    {},
                    {"source_id": "", "trust_tier": "advisory"},
                    {"source_id": "alpha", "trust_tier": "advisory", "auth_ok": False, "freshness_ok": False},
                ],
                "signal_source_registry": {"entries": "bad"},
                "krr_advice": {
                    "phase": "shadow",
                    "candidate_checks": ["signal::source_history"],
                },
            }
        ]
    )

    assert history["history_source_stats"]["alpha"] == {
        "total": 1,
        "submit": 0,
        "reject": 0,
        "skip": 0,
        "trusted": 0,
        "advisory": 1,
        "registered": 0,
        "auth_ok": 0,
        "freshness_ok": 0,
        "submit_rate": 0.0,
    }
