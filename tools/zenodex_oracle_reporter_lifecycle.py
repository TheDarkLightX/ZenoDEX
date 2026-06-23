#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle reporter lifecycle traces."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


LIFECYCLE_SCHEMA = "zenodex.oracle.reporter_lifecycle.v1"
RESULT_SCHEMA = "zenodex.oracle.reporter_lifecycle_verify_result.v1"
MAX_LIFECYCLE_BYTES = 250_000
MAX_EVENTS = 64
MAX_AMOUNT = 10**24
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
PUBKEY_RE = re.compile(r"^0x[0-9a-f]{96}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,95}$")
TOP_LEVEL_KEYS = {"schema", "reporter_id", "reporter_pubkey", "required_bond", "events"}
EVENT_KEYS_BY_TYPE = {
    "register": {"type", "epoch"},
    "deposit_bond": {"type", "epoch", "amount"},
    "submit_report": {"type", "epoch", "report_id", "query_id", "value_hash"},
    "open_dispute": {"type", "epoch", "report_id", "dispute_id", "dispute_bond"},
    "slash": {"type", "epoch", "dispute_id", "amount"},
    "resolve_dispute": {"type", "epoch", "dispute_id", "outcome"},
    "unregister": {"type", "epoch"},
    "withdraw_bond": {"type", "epoch", "amount"},
}
DISPUTE_OUTCOMES = {"upheld", "rejected"}
NOT_CLAIMED = [
    "does_not_claim_reporter_honesty",
    "does_not_claim_source_correctness",
    "does_not_claim_production_reporter_registry_live",
]


@dataclass(frozen=True)
class ReporterLifecycleResult:
    status: str
    errors: list[str]
    reporter_id: str | None = None
    active: bool | None = None
    bond_available: int | None = None
    required_bond: int | None = None
    reports_submitted: int | None = None
    disputes_open: int | None = None
    disputes_resolved: int | None = None
    total_slashed: int | None = None
    total_withdrawn: int | None = None
    last_epoch: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "reporter_id": self.reporter_id,
            "active": self.active,
            "bond_available": self.bond_available,
            "required_bond": self.required_bond,
            "reports_submitted": self.reports_submitted,
            "disputes_open": self.disputes_open,
            "disputes_resolved": self.disputes_resolved,
            "total_slashed": self.total_slashed,
            "total_withdrawn": self.total_withdrawn,
            "last_epoch": self.last_epoch,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def sample_lifecycle() -> dict[str, Any]:
    report_id = sample_hash("zenodex-oracle-sample-report")
    dispute_id = sample_hash("zenodex-oracle-sample-dispute")
    return {
        "schema": LIFECYCLE_SCHEMA,
        "reporter_id": "reporter.sample",
        "reporter_pubkey": "0x" + ("11" * 48),
        "required_bond": 100,
        "events": [
            {"type": "register", "epoch": 1},
            {"type": "deposit_bond", "epoch": 2, "amount": 100},
            {
                "type": "submit_report",
                "epoch": 3,
                "report_id": report_id,
                "query_id": sample_hash("zenodex-oracle-sample-query"),
                "value_hash": sample_hash("zenodex-oracle-sample-value"),
            },
            {
                "type": "open_dispute",
                "epoch": 4,
                "report_id": report_id,
                "dispute_id": dispute_id,
                "dispute_bond": 20,
            },
            {"type": "slash", "epoch": 5, "dispute_id": dispute_id, "amount": 10},
            {"type": "resolve_dispute", "epoch": 6, "dispute_id": dispute_id, "outcome": "upheld"},
            {"type": "unregister", "epoch": 7},
            {"type": "withdraw_bond", "epoch": 8, "amount": 90},
        ],
    }


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: set[str],
    label: str,
    errors: list[str],
) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _pubkey(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not PUBKEY_RE.match(value):
        errors.append(f"{key}_must_be_hex_48bytes")
        return None
    return str(value)


def _int_amount(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > MAX_AMOUNT:
        errors.append(f"{key}_must_be_int_between_0_and_{MAX_AMOUNT}")
        return None
    return int(value)


def _epoch(obj: Mapping[str, Any], errors: list[str]) -> int | None:
    value = obj.get("epoch")
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        errors.append("epoch_must_be_int_ge_0")
        return None
    return int(value)


def _events(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("events")
    if not isinstance(raw, list):
        errors.append("events_must_be_list")
        return []
    if len(raw) > MAX_EVENTS:
        errors.append(f"events_exceed_max:{len(raw)}>{MAX_EVENTS}")
    events: list[Mapping[str, Any]] = []
    for pos, event in enumerate(raw[:MAX_EVENTS]):
        if not isinstance(event, Mapping):
            errors.append(f"event_{pos}_must_be_object")
            continue
        events.append(event)
    return events


def verify_lifecycle_trace(obj: Mapping[str, Any]) -> ReporterLifecycleResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="lifecycle", errors=errors)
    if obj.get("schema") != LIFECYCLE_SCHEMA:
        errors.append("lifecycle_schema_mismatch")
    reporter_id = _token(obj, "reporter_id", errors)
    _pubkey(obj, "reporter_pubkey", errors)
    required_bond = _int_amount(obj, "required_bond", errors)
    events = _events(obj, errors)

    active = False
    ever_registered = False
    bond_available = 0
    reports: set[str] = set()
    disputes: dict[str, dict[str, Any]] = {}
    total_slashed = 0
    total_withdrawn = 0
    last_epoch: int | None = None

    for pos, event in enumerate(events):
        event_type = event.get("type")
        if not isinstance(event_type, str):
            errors.append(f"event_{pos}_type_must_be_string")
            continue
        allowed_keys = EVENT_KEYS_BY_TYPE.get(event_type)
        if allowed_keys is None:
            errors.append(f"unsupported_event_type:{event_type}")
            continue
        _unknown_fields(event, allowed=allowed_keys, label=f"event_{event_type}", errors=errors)

        epoch = _epoch(event, errors)
        if epoch is not None:
            if last_epoch is not None and epoch < last_epoch:
                errors.append(f"event_epoch_regression:{pos}")
            last_epoch = epoch if last_epoch is None else max(last_epoch, epoch)

        if event_type == "register":
            if active:
                errors.append("reporter_already_active")
            if ever_registered:
                errors.append("reporter_duplicate_registration")
            active = True
            ever_registered = True
        elif event_type == "deposit_bond":
            amount = _int_amount(event, "amount", errors)
            if not ever_registered:
                errors.append("bond_deposit_before_registration")
            if amount is not None:
                bond_available += amount
        elif event_type == "submit_report":
            report_id = _hash(event, "report_id", errors)
            _hash(event, "query_id", errors)
            _hash(event, "value_hash", errors)
            if not active:
                errors.append("report_submitted_by_inactive_reporter")
            if required_bond is not None and bond_available < required_bond:
                errors.append("report_submitted_under_required_bond")
            if report_id is not None:
                if report_id in reports:
                    errors.append(f"duplicate_report_id:{report_id}")
                reports.add(report_id)
        elif event_type == "open_dispute":
            report_id = _hash(event, "report_id", errors)
            dispute_id = _hash(event, "dispute_id", errors)
            dispute_bond = _int_amount(event, "dispute_bond", errors)
            if report_id is not None and report_id not in reports:
                errors.append("dispute_for_unknown_report")
            if dispute_id is not None and dispute_id in disputes:
                errors.append(f"duplicate_dispute_id:{dispute_id}")
            if dispute_bond == 0:
                errors.append("dispute_bond_required")
            if dispute_id is not None:
                disputes[dispute_id] = {
                    "open": True,
                    "resolved": False,
                    "slashed": False,
                }
        elif event_type == "slash":
            dispute_id = _hash(event, "dispute_id", errors)
            amount = _int_amount(event, "amount", errors)
            dispute = disputes.get(dispute_id) if dispute_id is not None else None
            slash_allowed = False
            if dispute is None:
                errors.append("slash_without_open_dispute")
            elif not dispute["open"] or dispute["resolved"]:
                errors.append("slash_after_dispute_closed")
            elif dispute["slashed"]:
                errors.append("dispute_already_slashed")
            else:
                slash_allowed = True
            if amount == 0:
                errors.append("slash_amount_required")
                slash_allowed = False
            if amount is not None and slash_allowed:
                if amount > bond_available:
                    errors.append("slash_exceeds_reporter_bond")
                else:
                    bond_available -= amount
                    total_slashed += amount
                    if dispute is not None:
                        dispute["slashed"] = True
        elif event_type == "resolve_dispute":
            dispute_id = _hash(event, "dispute_id", errors)
            outcome = event.get("outcome")
            if outcome not in DISPUTE_OUTCOMES:
                errors.append("dispute_outcome_invalid")
            dispute = disputes.get(dispute_id) if dispute_id is not None else None
            if dispute is None:
                errors.append("resolve_unknown_dispute")
            elif not dispute["open"] or dispute["resolved"]:
                errors.append("resolve_closed_dispute")
            else:
                dispute["open"] = False
                dispute["resolved"] = True
        elif event_type == "unregister":
            if not active:
                errors.append("unregister_inactive_reporter")
            if any(dispute["open"] for dispute in disputes.values()):
                errors.append("unregister_with_open_dispute")
            active = False
        elif event_type == "withdraw_bond":
            amount = _int_amount(event, "amount", errors)
            if active:
                errors.append("withdraw_while_reporter_active")
            if any(dispute["open"] for dispute in disputes.values()):
                errors.append("withdraw_with_open_dispute")
            if amount == 0:
                errors.append("withdraw_amount_required")
            if amount is not None:
                if amount > bond_available:
                    errors.append("withdraw_exceeds_bond")
                else:
                    bond_available -= amount
                    total_withdrawn += amount

    disputes_open = sum(1 for dispute in disputes.values() if dispute["open"])
    disputes_resolved = sum(1 for dispute in disputes.values() if dispute["resolved"])
    return ReporterLifecycleResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        reporter_id=reporter_id,
        active=active,
        bond_available=bond_available,
        required_bond=required_bond,
        reports_submitted=len(reports),
        disputes_open=disputes_open,
        disputes_resolved=disputes_resolved,
        total_slashed=total_slashed,
        total_withdrawn=total_withdrawn,
        last_epoch=last_epoch,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_LIFECYCLE_BYTES:
        raise ValueError(f"lifecycle_file_too_large:{size}>{MAX_LIFECYCLE_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("lifecycle root must be a JSON object")
    return obj


def _write_result(result: ReporterLifecycleResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        trace = _load_json(Path(args.trace))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = ReporterLifecycleResult(status="inconclusive", errors=[f"lifecycle_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_lifecycle_trace(trace)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_lifecycle(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle reporter lifecycle trace")
    verify.add_argument("trace", help="path to a reporter lifecycle JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted reporter lifecycle trace")
    sample.add_argument("--output", help="optional output path for the sample trace JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
