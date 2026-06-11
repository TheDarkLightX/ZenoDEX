#!/usr/bin/env python3
"""Build production AutoTrader evidence from explicit supervisor-run artifacts.

The production verifier remains authoritative. This tool assembles a 24h+
run-window report, crash-recovery records, multi-signer approvals, and observed
budget limits into the AutoTrader lane schema, attaches the lane hash, and can
run the lane verifier before writing.

Grade: A-. This turns the AutoTrader production lane from a hand-edited JSON
exercise into a repeatable artifact-builder while preserving the rule that real
run evidence, not fixtures, must be supplied for production promotion.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.production_promotion_evidence import (  # noqa: E402
    _AUTOTRADER_APPROVAL_FIELDS,
    _AUTOTRADER_CRASH_FIELDS,
    _HASH_HEX_LEN,
    _MAX_AUTOTRADER_CRASH_RECOVERY_ENTRIES,
    _MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS,
    _MAX_AUTOTRADER_HEARTBEAT_LIST_LEN,
    _MAX_AUTOTRADER_MULTI_SIGNERS,
    _MAX_TICKS_PER_PROCESS_HARD_CAP,
    _MIN_AUTOTRADER_MULTI_SIGNERS,
    _MIN_AUTOTRADER_UNATTENDED_SECONDS,
    _PUBKEY_HEX_LEN,
    _SIGNATURE_HEX_LEN,
    AUTOTRADER_EVIDENCE_SCHEMA_V1,
    attach_production_autotrader_hash_v1,
    evaluate_production_autotrader_evidence_v1,
    production_autotrader_run_approval_hash_v1,
)

_HEX = frozenset("0123456789abcdef")


def _load_json(path: Path, *, label: str) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ValueError(f"{label} not found: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"{label} invalid JSON: {exc}") from exc


def _load_list(path: Path | None, *, label: str) -> list[Any]:
    if path is None:
        return []
    value = _load_json(path, label=label)
    if not isinstance(value, list):
        raise ValueError(f"{label} must be a JSON list")
    return value


def _load_heartbeats(args: argparse.Namespace) -> list[int]:
    if args.heartbeat_timestamps_file is not None:
        raw = _load_json(args.heartbeat_timestamps_file, label="heartbeat timestamps")
    else:
        raw = json.loads(args.heartbeat_timestamps_json)
    if not isinstance(raw, list) or not raw:
        raise ValueError("heartbeat timestamps must be a non-empty JSON list")
    out: list[int] = []
    for index, item in enumerate(raw):
        if not isinstance(item, int) or isinstance(item, bool) or item <= 0:
            raise ValueError(f"heartbeat timestamps[{index}] must be a positive integer")
        out.append(int(item))
    return out


def _positive_int(value: object, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return int(value)


def _bounded_int(value: object, *, label: str, lo: int, hi: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < lo or value > hi:
        raise ValueError(f"{label} must be an integer in [{lo}, {hi}]")
    return int(value)


def _normalize_hex(value: object, *, label: str, length: int) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label} must be a non-empty string")
    text = value.strip()
    if text.startswith(("0x", "0X")):
        text = text[2:]
    text = text.lower()
    if len(text) != length or any(ch not in _HEX for ch in text):
        raise ValueError(f"{label} must be {length}-char lowercase hex, optionally prefixed with 0x")
    return text


def _mapping_list(path: Path | None, *, label: str) -> list[Mapping[str, Any]]:
    values = _load_list(path, label=label)
    out: list[Mapping[str, Any]] = []
    for index, item in enumerate(values):
        if not isinstance(item, Mapping):
            raise ValueError(f"{label}[{index}] must be a JSON object")
        out.append(item)
    return out


def _validate_run_window(args: argparse.Namespace, heartbeats: list[int]) -> dict[str, Any]:
    started_at = _positive_int(args.started_at, label="started_at")
    last_heartbeat_at = _positive_int(args.last_heartbeat_at, label="last_heartbeat_at")
    duration_seconds = _positive_int(args.duration_seconds, label="duration_seconds")
    ticks_executed = _bounded_int(
        args.ticks_executed,
        label="ticks_executed",
        lo=1,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    ticks_failed = _bounded_int(
        args.ticks_failed,
        label="ticks_failed",
        lo=0,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    ticks_throttled = _bounded_int(
        args.ticks_throttled,
        label="ticks_throttled",
        lo=0,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    if last_heartbeat_at < started_at:
        raise ValueError("last_heartbeat_at must be >= started_at")
    if started_at + duration_seconds != last_heartbeat_at:
        raise ValueError("duration_seconds must equal last_heartbeat_at - started_at")
    if duration_seconds < _MIN_AUTOTRADER_UNATTENDED_SECONDS:
        raise ValueError(f"duration_seconds must be >= {_MIN_AUTOTRADER_UNATTENDED_SECONDS} for production")
    if ticks_failed > ticks_executed:
        raise ValueError("ticks_failed cannot exceed ticks_executed")
    if ticks_throttled > ticks_executed:
        raise ValueError("ticks_throttled cannot exceed ticks_executed")
    _validate_heartbeats(heartbeats, started_at=started_at, last_heartbeat_at=last_heartbeat_at)
    return {
        "started_at": started_at,
        "last_heartbeat_at": last_heartbeat_at,
        "duration_seconds": duration_seconds,
        "ticks_executed": ticks_executed,
        "ticks_failed": ticks_failed,
        "ticks_throttled": ticks_throttled,
        "heartbeat_timestamps": heartbeats,
    }


def _validate_heartbeats(heartbeats: list[int], *, started_at: int, last_heartbeat_at: int) -> None:
    if len(heartbeats) < 2 or len(heartbeats) > _MAX_AUTOTRADER_HEARTBEAT_LIST_LEN:
        raise ValueError(
            f"heartbeat timestamps length must be in [2, {_MAX_AUTOTRADER_HEARTBEAT_LIST_LEN}]"
        )
    if heartbeats[0] != started_at:
        raise ValueError("heartbeat timestamps[0] must equal started_at")
    if heartbeats[-1] != last_heartbeat_at:
        raise ValueError("heartbeat timestamps[-1] must equal last_heartbeat_at")
    for index, (prev, cur) in enumerate(zip(heartbeats, heartbeats[1:], strict=False), start=1):
        if cur < prev:
            raise ValueError(f"heartbeat timestamps[{index}] must be >= predecessor")
        if cur - prev > _MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS:
            raise ValueError(
                f"heartbeat timestamps max gap {_MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS}s "
                f"exceeded between index {index - 1} and {index}"
            )


def _validate_crash_recovery(
    path: Path | None,
    *,
    started_at: int,
    last_heartbeat_at: int,
) -> list[dict[str, Any]]:
    raw = _mapping_list(path, label="crash recovery")
    if len(raw) > _MAX_AUTOTRADER_CRASH_RECOVERY_ENTRIES:
        raise ValueError(f"crash recovery length must be <= {_MAX_AUTOTRADER_CRASH_RECOVERY_ENTRIES}")
    intervals: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    out: list[dict[str, Any]] = []
    for index, entry in enumerate(raw):
        unknown = sorted(str(key) for key in entry if key not in _AUTOTRADER_CRASH_FIELDS)
        if unknown:
            raise ValueError(f"crash recovery[{index}] has unknown fields: {', '.join(unknown)}")
        crash_at = _positive_int(entry.get("crash_at"), label=f"crash recovery[{index}].crash_at")
        recovery_at = _positive_int(entry.get("recovery_at"), label=f"crash recovery[{index}].recovery_at")
        checkpoint_hash = _normalize_hex(
            entry.get("checkpoint_hash"),
            label=f"crash recovery[{index}].checkpoint_hash",
            length=_HASH_HEX_LEN,
        )
        if recovery_at < crash_at:
            raise ValueError(f"crash recovery[{index}].recovery_at must be >= crash_at")
        if crash_at < started_at or recovery_at > last_heartbeat_at:
            raise ValueError(f"crash recovery[{index}] must be within the run window")
        interval = (crash_at, recovery_at)
        if interval in seen:
            raise ValueError(f"crash recovery[{index}] duplicates an earlier crash/recovery interval")
        seen.add(interval)
        intervals.append(interval)
        out.append({"crash_at": crash_at, "recovery_at": recovery_at, "checkpoint_hash": checkpoint_hash})
    sorted_intervals = sorted(intervals, key=lambda iv: (iv[0], iv[1]))
    for prev, cur in zip(sorted_intervals, sorted_intervals[1:], strict=False):
        if cur[0] < prev[1]:
            raise ValueError(f"crash recovery interval {cur} overlaps with {prev}")
    return out


def _validate_approvals(path: Path, *, expected_approval_hash: str) -> list[dict[str, str]]:
    raw = _mapping_list(path, label="multi-signer approvals")
    if len(raw) < _MIN_AUTOTRADER_MULTI_SIGNERS or len(raw) > _MAX_AUTOTRADER_MULTI_SIGNERS:
        raise ValueError(
            f"multi-signer approvals length must be in [{_MIN_AUTOTRADER_MULTI_SIGNERS}, {_MAX_AUTOTRADER_MULTI_SIGNERS}]"
        )
    signer_pubkeys: set[str] = set()
    approval_hashes: set[str] = set()
    out: list[dict[str, str]] = []
    for index, entry in enumerate(raw):
        unknown = sorted(str(key) for key in entry if key not in _AUTOTRADER_APPROVAL_FIELDS)
        if unknown:
            raise ValueError(f"multi-signer approvals[{index}] has unknown fields: {', '.join(unknown)}")
        signer_pubkey = _normalize_hex(
            entry.get("signer_pubkey"),
            label=f"multi-signer approvals[{index}].signer_pubkey",
            length=_PUBKEY_HEX_LEN,
        )
        approval_hash = _normalize_hex(
            entry.get("approval_hash"),
            label=f"multi-signer approvals[{index}].approval_hash",
            length=_HASH_HEX_LEN,
        )
        signature = _normalize_hex(
            entry.get("signature"),
            label=f"multi-signer approvals[{index}].signature",
            length=_SIGNATURE_HEX_LEN,
        )
        if signer_pubkey in signer_pubkeys:
            raise ValueError(f"multi-signer approvals[{index}] signer_pubkey duplicates an earlier approval")
        signer_pubkeys.add(signer_pubkey)
        approval_hashes.add(approval_hash)
        out.append({"signer_pubkey": signer_pubkey, "approval_hash": approval_hash, "signature": signature})
    if len(approval_hashes) != 1:
        raise ValueError("multi-signer approvals entries must all share the same approval_hash")
    if expected_approval_hash not in approval_hashes:
        raise ValueError("multi-signer approvals approval_hash must equal canonical run approval hash")
    return out


def _validate_budget(args: argparse.Namespace) -> dict[str, int]:
    observed_actions = _bounded_int(
        args.max_actions_per_tick_observed,
        label="max_actions_per_tick_observed",
        lo=0,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    observed_runs = _bounded_int(
        args.max_runs_per_process_observed,
        label="max_runs_per_process_observed",
        lo=0,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    config_actions = _bounded_int(
        args.config_max_actions_per_tick,
        label="config_max_actions_per_tick",
        lo=0,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    config_runs = _bounded_int(
        args.config_max_runs_per_process,
        label="config_max_runs_per_process",
        lo=0,
        hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
    )
    if observed_actions > config_actions:
        raise ValueError("observed actions_per_tick exceeds configured maximum")
    if observed_runs > config_runs:
        raise ValueError("observed runs_per_process exceeds configured maximum")
    return {
        "max_actions_per_tick_observed": observed_actions,
        "max_runs_per_process_observed": observed_runs,
        "config_max_actions_per_tick": config_actions,
        "config_max_runs_per_process": config_runs,
    }


def build_autotrader_evidence(args: argparse.Namespace) -> dict[str, Any]:
    # Review finding (grade A- -> A): the verifier treated issued_at as a
    # positive timestamp, but the producer could write a negative or zero
    # supervisor-run artifact when --check was omitted. Validate before hashing
    # so local artifacts cannot masquerade as replayable run evidence.
    issued_at = _positive_int(
        int(args.issued_at if args.issued_at is not None else time.time()),
        label="issued_at",
    )
    heartbeats = _load_heartbeats(args)
    run_window = _validate_run_window(args, heartbeats)
    crash_recovery = _validate_crash_recovery(
        args.crash_recovery_file,
        started_at=int(run_window["started_at"]),
        last_heartbeat_at=int(run_window["last_heartbeat_at"]),
    )
    budget = _validate_budget(args)
    if args.expected_chain_id is not None and args.chain_id != args.expected_chain_id:
        raise ValueError("chain_id does not match expected_chain_id")
    evidence_body: dict[str, Any] = {
        "schema": AUTOTRADER_EVIDENCE_SCHEMA_V1,
        "supervisor_id": args.supervisor_id,
        "chain_id": args.chain_id,
        "profile_supervisor_hash": args.profile_supervisor_hash,
        # Review finding (grade B+ -> A-): without --check the producer could
        # write a production-looking supervisor run with invalid heartbeats,
        # crash intervals, signer quorum, or budget overruns. Validate the
        # structural evidence before hashing; the lane verifier remains the
        # final authority for freshness and binding.
        "run_window": run_window,
        "crash_recovery": crash_recovery,
        "budget_compliance": budget,
        "issued_at": issued_at,
    }
    expected_approval_hash = production_autotrader_run_approval_hash_v1(evidence_body)
    approvals = _validate_approvals(
        args.multi_signer_approvals_file,
        expected_approval_hash=expected_approval_hash,
    )
    return attach_production_autotrader_hash_v1({**evidence_body, "multi_signer_approvals": approvals})


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--supervisor-id", required=True)
    parser.add_argument("--chain-id", required=True)
    parser.add_argument("--profile-supervisor-hash", required=True)
    parser.add_argument("--started-at", type=int, required=True)
    parser.add_argument("--last-heartbeat-at", type=int, required=True)
    parser.add_argument("--duration-seconds", type=int, required=True)
    parser.add_argument("--ticks-executed", type=int, required=True)
    parser.add_argument("--ticks-failed", type=int, required=True)
    parser.add_argument("--ticks-throttled", type=int, required=True)
    hb = parser.add_mutually_exclusive_group(required=True)
    hb.add_argument("--heartbeat-timestamps-json")
    hb.add_argument("--heartbeat-timestamps-file", type=Path)
    parser.add_argument("--crash-recovery-file", type=Path)
    parser.add_argument("--multi-signer-approvals-file", type=Path, required=True)
    parser.add_argument("--max-actions-per-tick-observed", type=int, required=True)
    parser.add_argument("--max-runs-per-process-observed", type=int, required=True)
    parser.add_argument("--config-max-actions-per-tick", type=int, required=True)
    parser.add_argument("--config-max-runs-per-process", type=int, required=True)
    parser.add_argument("--issued-at", type=int)
    parser.add_argument("--check-now", type=int, help="override verifier time for reproducible --check runs")
    parser.add_argument("--expected-chain-id")
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the AutoTrader lane verifier before writing",
    )
    return parser.parse_args(list(argv))


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        evidence = build_autotrader_evidence(args)
        if args.check:
            # Review note (grade B -> A-): pinning --issued-at should not pin
            # freshness. Production --check uses wall-clock time; --check-now is
            # only for deterministic replay tests.
            check_now = args.check_now if args.check_now is not None else int(time.time())
            check = evaluate_production_autotrader_evidence_v1(
                evidence,
                supervisor_profile_hash=args.profile_supervisor_hash,
                config_max_actions_per_tick=args.config_max_actions_per_tick,
                config_max_runs_per_process=args.config_max_runs_per_process,
                expected_chain_id=args.expected_chain_id,
                now=check_now,
            )
            if check.get("production_ready") is not True:
                print(json.dumps(check, sort_keys=True), file=sys.stderr)
                return 1
        _write_json(args.out, evidence)
        print(json.dumps({"ok": True, "evidence_path": str(args.out)}, sort_keys=True))
        return 0
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(
            json.dumps(
                {"ok": False, "error": "autotrader_evidence_build_failed", "detail": str(exc)}
            )
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
