from __future__ import annotations

from collections import Counter
from typing import Mapping

_AUTOTRADER_KRR_HISTORY_SCHEMA = "zenodex/autotrader-krr-history/v1"

_TAU_SPEC_TO_CHECK: dict[str, str] = {
    "autotrader_budget_guard_v1": "tau::budget_guard",
    "autotrader_compile_contract_v1": "tau::compile_contract",
    "autotrader_execution_guard_v1": "tau::execution_guard",
    "autotrader_oracle_freshness_guard_v1": "tau::oracle_freshness_guard",
    "autotrader_session_state_guard_v1": "tau::session_state_guard",
    "autotrader_signal_provenance_guard_v1": "tau::signal_provenance_guard",
    "autotrader_wallet_capability_guard_v1": "tau::wallet_capability_guard",
    "autotrader_nonce_guard_v1": "tau::nonce_guard",
}


def _as_str_list(value: object) -> list[str]:
    if not isinstance(value, list):
        return []
    out: list[str] = []
    seen: set[str] = set()
    for raw in value:
        item = str(raw).strip()
        if not item or item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _load_history_rows(existing: Mapping[str, object] | None) -> dict[str, dict[str, int | float]]:
    if not isinstance(existing, Mapping):
        return {}
    root = existing.get("history_check_stats", existing)
    if not isinstance(root, Mapping):
        return {}
    out: dict[str, dict[str, int | float]] = {}
    for raw_check, raw_stats in root.items():
        check = str(raw_check).strip()
        if not check or not isinstance(raw_stats, Mapping):
            continue
        total_raw = raw_stats.get("total", 0)
        supported_raw = raw_stats.get("supported")
        rate_raw = raw_stats.get("support_rate", 0.0)
        try:
            total = max(0, int(total_raw))
        except Exception:
            total = 0
        if supported_raw is None:
            try:
                supported = max(0, min(total, int(round(float(rate_raw) * float(total)))))
            except Exception:
                supported = 0
        else:
            try:
                supported = max(0, min(total, int(supported_raw)))
            except Exception:
                supported = 0
        out[check] = {
            "total": total,
            "supported": supported,
            "support_rate": (float(supported) / float(total)) if total > 0 else 0.0,
        }
    return out


def _load_source_rows(existing: Mapping[str, object] | None) -> dict[str, dict[str, int | float]]:
    if not isinstance(existing, Mapping):
        return {}
    root = existing.get("history_source_stats", {})
    if not isinstance(root, Mapping):
        return {}
    out: dict[str, dict[str, int | float]] = {}
    for raw_source_id, raw_stats in root.items():
        source_id = str(raw_source_id).strip()
        if not source_id or not isinstance(raw_stats, Mapping):
            continue

        def _as_row_int(row: Mapping[str, object], name: str) -> int:
            raw = row.get(name, 0)
            try:
                if isinstance(raw, bool):
                    return int(raw)
                if isinstance(raw, int):
                    return max(0, raw)
                if isinstance(raw, float):
                    return max(0, int(raw))
                if isinstance(raw, str):
                    return max(0, int(raw))
            except Exception:
                pass
            return 0

        total = _as_row_int(raw_stats, "total")
        submit = min(total, _as_row_int(raw_stats, "submit"))
        reject = min(total, _as_row_int(raw_stats, "reject"))
        skip = min(total, _as_row_int(raw_stats, "skip"))
        trusted = min(total, _as_row_int(raw_stats, "trusted"))
        advisory = min(total, _as_row_int(raw_stats, "advisory"))
        registered = min(total, _as_row_int(raw_stats, "registered"))
        auth_ok = min(total, _as_row_int(raw_stats, "auth_ok"))
        freshness_ok = min(total, _as_row_int(raw_stats, "freshness_ok"))
        out[source_id] = {
            "total": total,
            "submit": submit,
            "reject": reject,
            "skip": skip,
            "trusted": trusted,
            "advisory": advisory,
            "registered": registered,
            "auth_ok": auth_ok,
            "freshness_ok": freshness_ok,
            "submit_rate": (float(submit) / float(total)) if total > 0 else 0.0,
        }
    return out


def _report_phase(report: Mapping[str, object], advice: Mapping[str, object]) -> str:
    phase = str(advice.get("phase", "")).strip()
    if phase:
        return phase
    mode = str(report.get("mode", "")).strip().lower()
    if mode in {"shadow", "live"}:
        return mode
    schema = str(report.get("schema", "")).strip().lower()
    if "policy-compile" in schema:
        return "compile"
    return "unknown"


def _report_decision(report: Mapping[str, object], phase: str) -> tuple[str, str, Mapping[str, object] | None]:
    if phase == "compile":
        ok = bool(report.get("ok", False))
        return ("submit" if ok else "reject"), ("compile_ok" if ok else str(report.get("error", ""))), None
    decision = report.get("decision")
    if not isinstance(decision, Mapping):
        return "unknown", "", None
    return (
        str(decision.get("tag", "")).strip().lower(),
        str(decision.get("reason", "")).strip(),
        decision,
    )


def _supported_checks_for_report(
    *,
    report: Mapping[str, object],
    phase: str,
    decision_tag: str,
    reason: str,
    candidate_checks: set[str],
) -> set[str]:
    if decision_tag == "submit":
        return set(candidate_checks)

    supported: set[str] = set()
    lowered_reason = reason.lower()

    decision = report.get("decision")
    tau_policy_receipt = decision.get("tau_policy_receipt") if isinstance(decision, Mapping) else None
    if isinstance(tau_policy_receipt, Mapping):
        spec_id = str(tau_policy_receipt.get("spec_id", "")).strip()
        mapped = _TAU_SPEC_TO_CHECK.get(spec_id)
        if mapped:
            supported.add(mapped)
        supported.add("policy::tau_bundle")

    compile_tau_receipt = report.get("compile_contract_tau_receipt")
    if isinstance(compile_tau_receipt, Mapping):
        spec_id = str(compile_tau_receipt.get("spec_id", "")).strip()
        mapped = _TAU_SPEC_TO_CHECK.get(spec_id)
        if mapped:
            supported.add(mapped)

    nonce_tau_receipts = report.get("nonce_tau_receipts")
    if isinstance(nonce_tau_receipts, list) and nonce_tau_receipts and phase == "live":
        if lowered_reason.startswith(("nonce_tau_", "live_nonce_validation_failed:")):
            supported.update({"live::nonce_guard", "tau::nonce_guard"})

    if lowered_reason == "signer_pubkey_mismatch":
        supported.add("live::signer_match")
    elif lowered_reason.startswith("live_nonce_validation_failed:"):
        supported.add("live::nonce_guard")
    elif lowered_reason.startswith("tau_tool_unavailable:"):
        supported.add("policy::tau_bundle")
    elif lowered_reason == "tau_policy_backend_requires_enabled_tau_config":
        supported.add("policy::tau_bundle")
    elif lowered_reason.startswith(("strategy_window_not_open:", "strategy_window_expired:")):
        supported.update({"policy::window_guard", "tau::execution_guard"})
    elif lowered_reason.startswith("cadence_not_elapsed:"):
        supported.update({"policy::cadence_guard", "tau::execution_guard"})
    elif lowered_reason.startswith("max_live_orders_reached:"):
        supported.update({"policy::live_order_cap", "tau::execution_guard"})
    elif lowered_reason.startswith("budget_guard_rejected:kill_switch_active"):
        supported.update({"policy::kill_switch", "policy::budget_guard", "tau::budget_guard"})
    elif lowered_reason.startswith("budget_guard_rejected:window_budget_exceeded"):
        supported.update({"policy::budget_guard", "tau::budget_guard"})
    elif lowered_reason.startswith(("budget_window_roll_failed:", "budget_window_regression:")):
        supported.add("policy::budget_guard")
    elif lowered_reason.startswith("lifetime_cap_exceeded:"):
        supported.add("policy::lifetime_cap")
    elif lowered_reason.startswith(
        (
            "receipt_missing_quote_epoch",
            "receipt_invalid_quote_epoch",
            "quote_receipt_stale:",
        )
    ):
        supported.update({"policy::oracle_freshness", "tau::oracle_freshness_guard"})
    elif lowered_reason.startswith("session_state_"):
        supported.add("live::session_state")
    elif lowered_reason.startswith("signal_provenance_rejected:"):
        supported.update({"policy::signal_provenance", "quote::receipt_verify", "quote::receipt_binding"})
    elif lowered_reason.startswith(
        (
            "unsupported_receipt_kind:",
            "receipt_asset_mismatch:",
            "receipt_amount_mismatch:",
            "intent_construction_failed:",
            "intent_amount_missing_or_invalid:",
            "intent_amount_mismatch:",
        )
    ):
        supported.update({"quote::receipt_verify", "quote::receipt_binding"})
    elif lowered_reason.startswith("wallet_capability_"):
        supported.add("live::wallet_capability")
    elif lowered_reason.startswith(("strategy_action_not_allowed:", "unsupported_strategy_template:", "strategy_assets_outside_universe", "slippage_limit_exceeded:")):
        supported.update({"policy::compile_guard", "policy::template_bounds"})

    return supported.intersection(candidate_checks)


def build_autotrader_krr_history(
    *,
    reports: list[Mapping[str, object]],
    existing_history: Mapping[str, object] | None = None,
) -> dict[str, object]:
    history_rows = _load_history_rows(existing_history)
    source_rows = _load_source_rows(existing_history)
    phase_counts: Counter[str] = Counter()
    decision_counts: Counter[str] = Counter()
    reason_counts: Counter[str] = Counter()
    processed_reports = 0

    for report in reports:
        advice = report.get("krr_advice")
        if not isinstance(advice, Mapping):
            continue
        candidate_checks = set(_as_str_list(advice.get("candidate_checks")))
        if not candidate_checks:
            candidate_checks = set(_as_str_list(advice.get("preferred_checks")))
        if not candidate_checks:
            continue
        phase = _report_phase(report, advice)
        decision_tag, reason, _decision = _report_decision(report, phase)
        processed_reports += 1
        phase_counts[phase] += 1
        if decision_tag:
            decision_counts[decision_tag] += 1
        if reason:
            reason_counts[reason] += 1
        supported = _supported_checks_for_report(
            report=report,
            phase=phase,
            decision_tag=decision_tag,
            reason=reason,
            candidate_checks=candidate_checks,
        )
        for check in candidate_checks:
            row = history_rows.setdefault(check, {"total": 0, "supported": 0, "support_rate": 0.0})
            total = int(row.get("total", 0)) + 1
            supported_count = int(row.get("supported", 0)) + (1 if check in supported else 0)
            row["total"] = total
            row["supported"] = supported_count
            row["support_rate"] = (float(supported_count) / float(total)) if total > 0 else 0.0

        external_signals = report.get("external_signals")
        registry = report.get("signal_source_registry")
        registered_source_ids: set[str] = set()
        if isinstance(registry, Mapping):
            entries = registry.get("entries")
            if isinstance(entries, list):
                for raw_entry in entries:
                    if not isinstance(raw_entry, Mapping):
                        continue
                    source_id = str(raw_entry.get("source_id", "")).strip()
                    if source_id:
                        registered_source_ids.add(source_id)
        if isinstance(external_signals, list):
            for raw_signal in external_signals:
                if not isinstance(raw_signal, Mapping):
                    continue
                source_id = str(raw_signal.get("source_id", "")).strip()
                if not source_id:
                    continue
                trust_tier = str(raw_signal.get("trust_tier", "")).strip().lower()
                row = source_rows.setdefault(
                    source_id,
                    {
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
                    },
                )
                total = int(row.get("total", 0)) + 1
                row["total"] = total
                if decision_tag in {"submit", "reject", "skip"}:
                    row[decision_tag] = int(row.get(decision_tag, 0)) + 1
                if trust_tier == "advisory":
                    row["advisory"] = int(row.get("advisory", 0)) + 1
                else:
                    row["trusted"] = int(row.get("trusted", 0)) + 1
                if source_id in registered_source_ids:
                    row["registered"] = int(row.get("registered", 0)) + 1
                if bool(raw_signal.get("auth_ok", False)):
                    row["auth_ok"] = int(row.get("auth_ok", 0)) + 1
                if bool(raw_signal.get("freshness_ok", False)):
                    row["freshness_ok"] = int(row.get("freshness_ok", 0)) + 1
                row["submit_rate"] = (
                    float(int(row.get("submit", 0))) / float(total)
                ) if total > 0 else 0.0

    history_check_stats = {
        check: {
            "total": int(row["total"]),
            "supported": int(row["supported"]),
            "support_rate": round(float(row["support_rate"]), 6),
        }
        for check, row in sorted(history_rows.items())
    }
    history_source_stats = {
        source_id: {
            "total": int(row["total"]),
            "submit": int(row["submit"]),
            "reject": int(row["reject"]),
            "skip": int(row["skip"]),
            "trusted": int(row["trusted"]),
            "advisory": int(row["advisory"]),
            "registered": int(row["registered"]),
            "auth_ok": int(row["auth_ok"]),
            "freshness_ok": int(row["freshness_ok"]),
            "submit_rate": round(float(row["submit_rate"]), 6),
        }
        for source_id, row in sorted(source_rows.items())
    }
    return {
        "schema": _AUTOTRADER_KRR_HISTORY_SCHEMA,
        "report_count": processed_reports,
        "phase_counts": dict(sorted(phase_counts.items())),
        "decision_counts": dict(sorted(decision_counts.items())),
        "reason_counts": dict(sorted(reason_counts.items())),
        "history_check_stats": history_check_stats,
        "history_source_stats": history_source_stats,
    }


__all__ = ["build_autotrader_krr_history"]
