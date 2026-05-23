#!/usr/bin/env python3
"""Local HTTP devnet service for the Zeno Oracle verifier shell.

This service is intentionally a devnet transport and receipt store around the
existing verifier kernels. It does not assert production truth; it only persists
artifacts after the same local MVP gates accept them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import parse_qs, urlparse

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from src.state.canonical import canonical_json_bytes  # noqa: E402
from zenodex_oracle import verify_bundle  # noqa: E402
from zenodex_oracle_adapter import (  # noqa: E402
    ACTION_SCHEMA,
    PROFILE_SCHEMA,
    profile_content_hash,
)
from zenodex_oracle_admitted_median3 import (  # noqa: E402
    ADMITTED_MEDIAN3_SCHEMA,
    aggregate_content_hash,
    verify_admitted_median3_aggregate,
)
from zenodex_oracle_aggregate_adapter import (  # noqa: E402
    AGGREGATE_ADAPTER_SCHEMA,
    aggregate_adapter_content_hash,
    verify_aggregate_adapter_bridge,
)
from zenodex_oracle_aggregate_read import (  # noqa: E402
    AGGREGATE_READ_SCHEMA,
    _bundle_for_aggregate,
    aggregate_read_value_hash,
    bridge_content_hash,
    verify_aggregate_read_bridge,
)
from zenodex_oracle_budget import verify_budget_transition  # noqa: E402
from zenodex_oracle_feed_registry import verify_feed_registry  # noqa: E402
from zenodex_oracle_report_admission import (  # noqa: E402
    ADMISSION_SCHEMA,
    admission_content_hash,
    verify_report_admission,
)
from zenodex_oracle_reporter_lifecycle import (  # noqa: E402
    LIFECYCLE_SCHEMA,
    verify_lifecycle_trace,
)
from zenodex_oracle_signed_report import (  # noqa: E402
    SUBMISSION_SCHEMA,
    submission_content_hash,
    verify_signed_report_submission,
)


SERVICE_SCHEMA = "zenodex.oracle.devnet_service.v1"
EVENT_SCHEMA = "zenodex.oracle.devnet_event.v1"
REPLAY_SCHEMA = "zenodex.oracle.devnet_replay_receipt.v1"
REPORTER_SCHEMA = "zenodex.oracle.devnet_reporter_registration.v1"
ECONOMIC_EVENT_SCHEMA = "zenodex.oracle.devnet_economic_event.v1"
MAX_BODY_BYTES = 2_000_000
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
HEX_48_RE = re.compile(r"^0x[0-9a-fA-F]{96}$")


def _now_ms() -> int:
    return int(time.time() * 1000)


def _content_hash(obj: Mapping[str, Any], *, omit_key: str | None = None) -> str:
    body = dict(obj)
    if omit_key is not None:
        body.pop(omit_key, None)
    return "sha256:" + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _hash_to_filename(value: str) -> str:
    if not isinstance(value, str) or not value.startswith("sha256:"):
        raise ValueError(f"expected sha256 id, got {value!r}")
    return value.split(":", 1)[1] + ".json"


def _json_response(status: str, errors: list[str] | None = None, **extra: Any) -> dict[str, Any]:
    return {
        "schema": SERVICE_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "errors": [] if errors is None else list(errors),
        **extra,
    }


def _load_json_file(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{path} did not contain a JSON object")
    return obj


def _write_json_file(path: Path, obj: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


class OracleDevnetStore:
    """Append-only receipt store for the local Zeno Oracle devnet."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.events_path = self.root / "events.jsonl"
        self._event_lock = threading.Lock()
        for name in (
            "reporters",
            "feeds",
            "signed_reports",
            "admissions",
            "aggregates",
            "reads",
            "adapter_bridges",
            "economics",
            "replay",
        ):
            (self.root / name).mkdir(parents=True, exist_ok=True)

    def _event_count(self) -> int:
        if not self.events_path.exists():
            return 0
        with self.events_path.open("r", encoding="utf-8") as handle:
            return sum(1 for line in handle if line.strip())

    def append_event(
        self,
        *,
        event_type: str,
        status: str,
        artifact_id: str | None,
        artifact_path: Path | None,
        receipt: Mapping[str, Any],
    ) -> dict[str, Any]:
        with self._event_lock:
            event = {
                "schema": EVENT_SCHEMA,
                "event_seq": self._event_count(),
                "event_type": event_type,
                "status": status,
                "artifact_id": artifact_id,
                "artifact_path": None if artifact_path is None else str(artifact_path.relative_to(self.root)),
                "artifact_sha256": None
                if artifact_path is None or not artifact_path.is_file()
                else _file_sha256(artifact_path),
                "receipt": dict(receipt),
                "created_at_ms": _now_ms(),
            }
            event["event_id"] = _content_hash(event, omit_key="event_id")
            self.events_path.parent.mkdir(parents=True, exist_ok=True)
            with self.events_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(event, sort_keys=True, separators=(",", ":")) + "\n")
            return event

    def persist_artifact(self, folder: str, artifact_id: str, obj: Mapping[str, Any]) -> Path:
        path = self.root / folder / _hash_to_filename(artifact_id)
        _write_json_file(path, obj)
        return path

    def latest_feed_for_query(self, query_id: str) -> tuple[dict[str, Any], dict[str, Any]] | None:
        newest: tuple[int, dict[str, Any], dict[str, Any]] | None = None
        for path in sorted((self.root / "feeds").glob("*.json")):
            registry = _load_json_file(path)
            current_epoch = int(registry.get("current_epoch", 0))
            feeds = registry.get("feeds", [])
            if not isinstance(feeds, list):
                continue
            for feed in feeds:
                if not isinstance(feed, dict):
                    continue
                spec = feed.get("query_spec")
                if isinstance(spec, dict) and spec.get("query_id") == query_id:
                    if newest is None or current_epoch >= newest[0]:
                        newest = (current_epoch, registry, feed)
        if newest is None:
            return None
        return newest[1], newest[2]

    def latest_artifact(self, folder: str, key: str, value: str) -> dict[str, Any] | None:
        newest: tuple[int, dict[str, Any]] | None = None
        for path in sorted((self.root / folder).glob("*.json")):
            obj = _load_json_file(path)
            if obj.get(key) != value:
                continue
            stat = path.stat()
            marker = int(stat.st_mtime_ns)
            if newest is None or marker >= newest[0]:
                newest = (marker, obj)
        return None if newest is None else newest[1]

    def latest_artifact_for_query(self, folder: str, schema: str, query_id: str) -> dict[str, Any] | None:
        newest: tuple[int, dict[str, Any]] | None = None
        for path in sorted((self.root / folder).glob("*.json")):
            obj = _load_json_file(path)
            if obj.get("schema") != schema or _artifact_query_id(obj) != query_id:
                continue
            marker = int(path.stat().st_mtime_ns)
            if newest is None or marker >= newest[0]:
                newest = (marker, obj)
        return None if newest is None else newest[1]

    def all_report_admissions(self, query_id: str) -> list[dict[str, Any]]:
        admissions: list[dict[str, Any]] = []
        for path in sorted((self.root / "admissions").glob("*.json")):
            admission = _load_json_file(path)
            result = verify_report_admission(admission)
            if result.status == "accepted" and result.query_id == query_id:
                admissions.append(admission)
        return admissions


def register_reporter(store: OracleDevnetStore, obj: Mapping[str, Any]) -> dict[str, Any]:
    reporter_id = obj.get("reporter_id")
    reporter_pubkey = obj.get("reporter_pubkey")
    required_bond = obj.get("required_bond", 100)
    bond_amount = obj.get("bond_amount", required_bond)
    epoch = obj.get("epoch", 1)
    errors: list[str] = []
    if not isinstance(reporter_id, str) or not TOKEN_RE.match(reporter_id):
        errors.append("reporter_id_must_be_token")
    if not isinstance(reporter_pubkey, str) or not HEX_48_RE.match(reporter_pubkey):
        errors.append("reporter_pubkey_must_be_48_byte_hex")
    for label, value in (
        ("required_bond", required_bond),
        ("bond_amount", bond_amount),
        ("epoch", epoch),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            errors.append(f"{label}_must_be_int_ge_0")
    if errors:
        receipt = _json_response("rejected", errors, operation="register_reporter")
        store.append_event(event_type="reporter.register", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    lifecycle = {
        "schema": LIFECYCLE_SCHEMA,
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "required_bond": required_bond,
        "events": [
            {"type": "register", "epoch": epoch},
            {"type": "deposit_bond", "epoch": epoch + 1, "amount": bond_amount},
        ],
    }
    lifecycle_result = verify_lifecycle_trace(lifecycle)
    if lifecycle_result.status != "accepted":
        receipt = _json_response("rejected", lifecycle_result.errors, operation="register_reporter")
        store.append_event(event_type="reporter.register", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    registration = {
        "schema": REPORTER_SCHEMA,
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "required_bond": required_bond,
        "bond_amount": bond_amount,
        "lifecycle": lifecycle,
    }
    registration["registration_id"] = _content_hash(registration, omit_key="registration_id")
    path = store.persist_artifact("reporters", str(registration["registration_id"]), registration)
    receipt = _json_response(
        "accepted",
        operation="register_reporter",
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        registration_id=registration["registration_id"],
        stored_path=str(path),
    )
    store.append_event(
        event_type="reporter.register",
        status="accepted",
        artifact_id=str(registration["registration_id"]),
        artifact_path=path,
        receipt=receipt,
    )
    return receipt


def _registered_reporter(store: OracleDevnetStore, reporter_id: str) -> dict[str, Any] | None:
    for path in sorted((store.root / "reporters").glob("*.json")):
        registration = _load_json_file(path)
        if registration.get("reporter_id") == reporter_id:
            return registration
    return None


def register_feed(store: OracleDevnetStore, registry: Mapping[str, Any]) -> dict[str, Any]:
    result = verify_feed_registry(registry)
    if result.status != "accepted" or result.registry_id is None:
        receipt = _json_response("rejected", result.errors, operation="register_feed", verifier=result.to_json_obj())
        store.append_event(event_type="feed.register", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt
    path = store.persist_artifact("feeds", result.registry_id, registry)
    receipt = _json_response(
        "accepted",
        operation="register_feed",
        registry_id=result.registry_id,
        feed_count=result.feed_count,
        query_ids=result.query_ids or [],
        stored_path=str(path),
        verifier=result.to_json_obj(),
    )
    store.append_event(
        event_type="feed.register",
        status="accepted",
        artifact_id=result.registry_id,
        artifact_path=path,
        receipt=receipt,
    )
    return receipt


def _split_single_report_submission(submission: Mapping[str, Any], report: Mapping[str, Any]) -> dict[str, Any]:
    single = {
        "schema": SUBMISSION_SCHEMA,
        "chain_id": submission["chain_id"],
        "reporter_id": submission["reporter_id"],
        "reporter_pubkey": submission["reporter_pubkey"],
        "reports": [dict(report)],
    }
    single["submission_id"] = submission_content_hash(single)
    return single


def _reporter_lifecycle_for_submission(
    registered: Mapping[str, Any],
    single_submission: Mapping[str, Any],
) -> dict[str, Any]:
    lifecycle = dict(registered["lifecycle"])
    events = list(lifecycle["events"])
    report = dict(single_submission["reports"][0])
    events.append(
        {
            "type": "submit_report",
            "epoch": int(report["observed_epoch"]),
            "report_id": str(report["report_id"]),
            "query_id": str(report["query_id"]),
            "value_hash": str(report["payload_hash"]),
        }
    )
    return dict(lifecycle, events=events)


def submit_report(store: OracleDevnetStore, submission: Mapping[str, Any]) -> dict[str, Any]:
    result = verify_signed_report_submission(submission)
    if result.status != "accepted" or result.submission_id is None:
        receipt = _json_response("rejected", result.errors, operation="submit_report", verifier=result.to_json_obj())
        store.append_event(event_type="report.submit", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    registered = _registered_reporter(store, str(result.reporter_id))
    errors: list[str] = []
    if registered is None:
        errors.append("reporter_not_registered")
    elif registered.get("reporter_pubkey") != result.reporter_pubkey:
        errors.append("reporter_pubkey_mismatch")

    reports = submission.get("reports", [])
    if not isinstance(reports, list):
        errors.append("reports_must_be_list")
        reports = []
    admissions: list[dict[str, Any]] = []
    for pos, report in enumerate(reports):
        if not isinstance(report, Mapping):
            continue
        query_id = report.get("query_id")
        if not isinstance(query_id, str):
            errors.append(f"report_{pos}_query_id_malformed")
            continue
        feed = store.latest_feed_for_query(query_id)
        if feed is None:
            errors.append(f"no_registered_feed_for_query:{query_id}")
            continue
        _registry, feed_obj = feed
        policy = feed_obj.get("aggregate_policy")
        source_diversity = feed_obj.get("source_diversity")
        if not isinstance(policy, Mapping) or not isinstance(source_diversity, Mapping):
            errors.append(f"registered_feed_malformed:{query_id}")
            continue
        current_epoch = int(_registry.get("current_epoch", report.get("observed_epoch", 0)))
        max_staleness_epochs = int(policy.get("freshness_window_epochs", 0))
        evidence_class = str(policy.get("evidence_floor", "O3"))
        single_submission = _split_single_report_submission(submission, report)
        reporter_lifecycle = _reporter_lifecycle_for_submission(registered, single_submission)
        admission = {
            "schema": ADMISSION_SCHEMA,
            "current_epoch": current_epoch,
            "max_staleness_epochs": max_staleness_epochs,
            "evidence_class": evidence_class,
            "signed_submission": single_submission,
            "reporter_lifecycle": reporter_lifecycle,
            "source_diversity": dict(source_diversity),
        }
        admission["admission_id"] = admission_content_hash(admission)
        admission_result = verify_report_admission(admission)
        if admission_result.status != "accepted":
            errors.extend(f"report_{pos}_admission:{error}" for error in admission_result.errors)
            continue
        admissions.append(admission)

    if errors:
        receipt = _json_response("rejected", errors, operation="submit_report", verifier=result.to_json_obj())
        store.append_event(event_type="report.submit", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    submission_path = store.persist_artifact("signed_reports", result.submission_id, submission)
    admission_ids: list[str] = []
    for admission in admissions:
        admission_id = str(admission["admission_id"])
        admission_ids.append(admission_id)
        path = store.persist_artifact("admissions", admission_id, admission)
        store.append_event(
            event_type="report.admit",
            status="accepted",
            artifact_id=admission_id,
            artifact_path=path,
            receipt=_json_response(
                "accepted",
                operation="admit_report",
                admission_id=admission_id,
                submission_id=result.submission_id,
            ),
        )

    receipt = _json_response(
        "accepted",
        operation="submit_report",
        submission_id=result.submission_id,
        reporter_id=result.reporter_id,
        report_count=result.report_count,
        admission_ids=admission_ids,
        stored_path=str(submission_path),
        verifier=result.to_json_obj(),
    )
    store.append_event(
        event_type="report.submit",
        status="accepted",
        artifact_id=result.submission_id,
        artifact_path=submission_path,
        receipt=receipt,
    )
    return receipt


def _selected_three_admissions(store: OracleDevnetStore, query_id: str) -> list[dict[str, Any]]:
    chosen: list[dict[str, Any]] = []
    reporters: set[str] = set()
    sources: set[str] = set()
    for admission in store.all_report_admissions(query_id):
        result = verify_report_admission(admission)
        reports = list(result.admitted_reports or [])
        if len(reports) != 1:
            continue
        reporter_id = reports[0].get("reporter_id")
        source_id = reports[0].get("source_id")
        if not isinstance(reporter_id, str) or not isinstance(source_id, str):
            continue
        if reporter_id in reporters or source_id in sources:
            continue
        chosen.append(admission)
        reporters.add(reporter_id)
        sources.add(source_id)
        if len(chosen) == 3:
            break
    return chosen


def build_aggregate(store: OracleDevnetStore, obj: Mapping[str, Any]) -> dict[str, Any]:
    query_id = obj.get("query_id")
    if not isinstance(query_id, str):
        return _json_response("rejected", ["query_id_must_be_string"], operation="build_aggregate")
    feed = store.latest_feed_for_query(query_id)
    if feed is None:
        receipt = _json_response("rejected", [f"no_registered_feed_for_query:{query_id}"], operation="build_aggregate")
        store.append_event(event_type="aggregate.build", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt
    registry, feed_obj = feed
    policy = feed_obj.get("aggregate_policy")
    if not isinstance(policy, Mapping):
        receipt = _json_response("rejected", ["registered_feed_policy_malformed"], operation="build_aggregate")
        store.append_event(event_type="aggregate.build", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    admissions = _selected_three_admissions(store, query_id)
    if len(admissions) != 3:
        receipt = _json_response(
            "rejected",
            [f"need_3_distinct_admissions:{len(admissions)}"],
            operation="build_aggregate",
            query_id=query_id,
        )
        store.append_event(event_type="aggregate.build", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    current_epoch = int(obj.get("current_epoch", registry.get("current_epoch", 0)))
    max_staleness_epochs = int(policy.get("freshness_window_epochs", 0))
    evidence_floor = str(policy.get("evidence_floor", "O3"))
    max_deviation_bps = int(policy.get("max_deviation_bps", 0))
    min_distinct_sources = int(policy.get("min_sources", 3))
    admitted_results = [verify_report_admission(admission) for admission in admissions]
    admitted_reports = [result.admitted_reports[0] for result in admitted_results if result.admitted_reports]
    values = [int(report["value_e8"]) for report in admitted_reports]
    epochs = [int(report["observed_epoch"]) for report in admitted_reports]
    median = sorted(values)[1]
    confidence = max(abs(value - median) for value in values)
    deviation = (confidence * 10_000 + median - 1) // median
    aggregate = {
        "schema": ADMITTED_MEDIAN3_SCHEMA,
        "query_id": query_id,
        "current_epoch": current_epoch,
        "max_staleness_epochs": max_staleness_epochs,
        "evidence_floor": evidence_floor,
        "evidence_class": evidence_floor,
        "max_deviation_bps": max_deviation_bps,
        "min_distinct_sources": min_distinct_sources,
        "report_admissions": admissions,
        "aggregate": {
            "value_e8": median,
            "confidence_e8": confidence,
            "deviation_bps": deviation,
            "observed_epoch": max(epochs),
            "report_count": 3,
        },
    }
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)
    aggregate_result = verify_admitted_median3_aggregate(aggregate)
    if aggregate_result.status != "accepted" or aggregate_result.aggregate_id is None:
        receipt = _json_response(
            "rejected",
            aggregate_result.errors,
            operation="build_aggregate",
            verifier=aggregate_result.to_json_obj(),
        )
        store.append_event(event_type="aggregate.build", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt

    aggregate_path = store.persist_artifact("aggregates", aggregate_result.aggregate_id, aggregate)
    store.append_event(
        event_type="aggregate.build",
        status="accepted",
        artifact_id=aggregate_result.aggregate_id,
        artifact_path=aggregate_path,
        receipt=_json_response(
            "accepted",
            operation="build_aggregate",
            aggregate_id=aggregate_result.aggregate_id,
            query_id=query_id,
            value_e8=aggregate_result.value_e8,
            confidence_e8=aggregate_result.confidence_e8,
            deviation_bps=aggregate_result.deviation_bps,
            verifier=aggregate_result.to_json_obj(),
        ),
    )

    freshness_window_epochs = int(policy.get("freshness_window_epochs", 1))
    value_hash = aggregate_read_value_hash(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_e8=int(aggregate_result.value_e8),
        confidence_e8=int(aggregate_result.confidence_e8),
        deviation_bps=int(aggregate_result.deviation_bps),
        observed_epoch=int(aggregate_result.observed_epoch),
        report_count=int(aggregate_result.report_count),
        admission_count=int(aggregate_result.admission_count),
    )
    aggregate_read = {
        "schema": AGGREGATE_READ_SCHEMA,
        "freshness_window_epochs": freshness_window_epochs,
        "aggregate": aggregate,
        "receipt_bundle": _bundle_for_aggregate(
            aggregate_id=str(aggregate_result.aggregate_id),
            query_id=str(aggregate_result.query_id),
            value_hash=value_hash,
            observed_epoch=int(aggregate_result.observed_epoch),
            freshness_window_epochs=freshness_window_epochs,
        ),
    }
    aggregate_read["bridge_id"] = bridge_content_hash(aggregate_read)
    read_result = verify_aggregate_read_bridge(aggregate_read)
    if read_result.status != "accepted" or read_result.bridge_id is None:
        receipt = _json_response("rejected", read_result.errors, operation="build_read", verifier=read_result.to_json_obj())
        store.append_event(event_type="read.build", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt
    read_path = store.persist_artifact("reads", read_result.bridge_id, aggregate_read)
    store.append_event(
        event_type="read.build",
        status="accepted",
        artifact_id=read_result.bridge_id,
        artifact_path=read_path,
        receipt=_json_response("accepted", operation="build_read", bridge_id=read_result.bridge_id, query_id=query_id),
    )

    bundle_result = verify_bundle(aggregate_read["receipt_bundle"])
    action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": bundle_result.consumer_module,
        "action_kind": bundle_result.action_kind,
        "action_id": bundle_result.action_id,
        "action_epoch": bundle_result.action_epoch,
        "query_id": bundle_result.query_id,
        "value_hash": bundle_result.value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": bundle_result.freshness_window_epochs,
        "read_receipt_id": bundle_result.read_receipt_id,
        "consumer_action_receipt_id": bundle_result.consumer_action_receipt_id,
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": bundle_result.consumer_module,
        "action_kind": bundle_result.action_kind,
        "query_id": bundle_result.query_id,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": bundle_result.freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    adapter = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": aggregate_read,
        "action": action,
        "profile": profile,
    }
    adapter["bridge_id"] = aggregate_adapter_content_hash(adapter)
    adapter_result = verify_aggregate_adapter_bridge(adapter)
    if adapter_result.status != "accepted" or adapter_result.bridge_id is None:
        receipt = _json_response("rejected", adapter_result.errors, operation="build_adapter", verifier=adapter_result.to_json_obj())
        store.append_event(event_type="adapter.build", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt
    adapter_path = store.persist_artifact("adapter_bridges", adapter_result.bridge_id, adapter)
    store.append_event(
        event_type="adapter.build",
        status="accepted",
        artifact_id=adapter_result.bridge_id,
        artifact_path=adapter_path,
        receipt=_json_response("accepted", operation="build_adapter", bridge_id=adapter_result.bridge_id, query_id=query_id),
    )

    return _json_response(
        "accepted",
        operation="build_aggregate_pipeline",
        query_id=query_id,
        aggregate_id=aggregate_result.aggregate_id,
        read_bridge_id=read_result.bridge_id,
        adapter_bridge_id=adapter_result.bridge_id,
        value_e8=aggregate_result.value_e8,
        confidence_e8=aggregate_result.confidence_e8,
        deviation_bps=aggregate_result.deviation_bps,
    )


def persist_economic_event(store: OracleDevnetStore, obj: Mapping[str, Any]) -> dict[str, Any]:
    event_kind = obj.get("event_kind")
    if event_kind not in {"bond", "reward", "dispute", "slash", "burn", "treasury"}:
        receipt = _json_response("rejected", ["event_kind_unsupported"], operation="economic_event")
        store.append_event(event_type="economic.event", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
        return receipt
    budget = obj.get("budget_transition")
    budget_result_obj: dict[str, Any] | None = None
    if budget is not None:
        if not isinstance(budget, Mapping):
            receipt = _json_response("rejected", ["budget_transition_must_be_object"], operation="economic_event")
            store.append_event(event_type="economic.event", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
            return receipt
        budget_result = verify_budget_transition(budget)
        budget_result_obj = budget_result.to_json_obj()
        if budget_result.status != "accepted":
            receipt = _json_response(
                "rejected",
                budget_result.errors,
                operation="economic_event",
                verifier=budget_result_obj,
            )
            store.append_event(event_type="economic.event", status="rejected", artifact_id=None, artifact_path=None, receipt=receipt)
            return receipt
    event = {
        "schema": ECONOMIC_EVENT_SCHEMA,
        "event_kind": event_kind,
        "reporter_id": obj.get("reporter_id"),
        "amount": obj.get("amount", 0),
        "budget_transition": budget,
        "budget_verify_result": budget_result_obj,
    }
    event["economic_event_id"] = _content_hash(event, omit_key="economic_event_id")
    path = store.persist_artifact("economics", str(event["economic_event_id"]), event)
    receipt = _json_response(
        "accepted",
        operation="economic_event",
        event_kind=event_kind,
        economic_event_id=event["economic_event_id"],
        stored_path=str(path),
        verifier=budget_result_obj,
    )
    store.append_event(
        event_type="economic.event",
        status="accepted",
        artifact_id=str(event["economic_event_id"]),
        artifact_path=path,
        receipt=receipt,
    )
    return receipt


def replay_store(store: OracleDevnetStore) -> dict[str, Any]:
    event_count = 0
    accepted_count = 0
    rejected_count = 0
    event_type_counts: dict[str, int] = {}
    missing_artifacts: list[str] = []
    artifact_hash_mismatches: list[str] = []
    malformed_events: list[str] = []
    duplicate_event_ids: list[str] = []
    duplicate_event_sequences: list[str] = []
    event_sequence_errors: list[str] = []
    latest_by_type: dict[str, str] = {}
    seen_event_ids: set[str] = set()
    seen_event_sequences: set[int] = set()
    expected_event_seq = 0
    if store.events_path.exists():
        with store.events_path.open("r", encoding="utf-8") as handle:
            for line_no, line in enumerate(handle, start=1):
                if not line.strip():
                    continue
                event_count += 1
                try:
                    event = json.loads(line)
                except json.JSONDecodeError as exc:
                    malformed_events.append(f"line_{line_no}:json_invalid:{exc.msg}")
                    continue
                if not isinstance(event, dict):
                    malformed_events.append(f"line_{line_no}:event_must_be_object")
                    continue

                event_id = event.get("event_id")
                if not isinstance(event_id, str):
                    malformed_events.append(f"line_{line_no}:event_id_missing_or_malformed")
                elif event_id in seen_event_ids:
                    duplicate_event_ids.append(f"line_{line_no}:{event_id}")
                else:
                    seen_event_ids.add(event_id)

                event_seq = event.get("event_seq")
                if not isinstance(event_seq, int) or isinstance(event_seq, bool) or event_seq < 0:
                    malformed_events.append(f"line_{line_no}:event_seq_missing_or_malformed")
                else:
                    if event_seq in seen_event_sequences:
                        duplicate_event_sequences.append(f"line_{line_no}:{event_seq}")
                    seen_event_sequences.add(event_seq)
                    if event_seq != expected_event_seq:
                        event_sequence_errors.append(f"line_{line_no}:expected_{expected_event_seq}:got_{event_seq}")
                    expected_event_seq += 1

                event_type_raw = event.get("event_type")
                event_type = event_type_raw if isinstance(event_type_raw, str) else "unknown"
                event_type_counts[event_type] = event_type_counts.get(event_type, 0) + 1
                if event.get("status") == "accepted":
                    accepted_count += 1
                else:
                    rejected_count += 1
                artifact_id = event.get("artifact_id")
                if isinstance(artifact_id, str):
                    latest_by_type[event_type] = artifact_id
                artifact_path = event.get("artifact_path")
                if isinstance(artifact_path, str):
                    full_artifact_path = store.root / artifact_path
                    if not full_artifact_path.is_file():
                        missing_artifacts.append(f"line_{line_no}:{artifact_path}")
                        continue
                    expected_sha256 = event.get("artifact_sha256")
                    if isinstance(expected_sha256, str):
                        actual_sha256 = _file_sha256(full_artifact_path)
                        if actual_sha256 != expected_sha256:
                            artifact_hash_mismatches.append(
                                f"line_{line_no}:{artifact_path}:expected_{expected_sha256}:got_{actual_sha256}"
                            )
    ok = not (
        missing_artifacts
        or artifact_hash_mismatches
        or malformed_events
        or duplicate_event_ids
        or duplicate_event_sequences
        or event_sequence_errors
    )
    receipt = {
        "schema": REPLAY_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "store": str(store.root),
        "event_count": event_count,
        "accepted_event_count": accepted_count,
        "rejected_event_count": rejected_count,
        "event_type_counts": event_type_counts,
        "latest_by_type": latest_by_type,
        "missing_artifacts": missing_artifacts,
        "artifact_hash_mismatches": artifact_hash_mismatches,
        "malformed_events": malformed_events,
        "duplicate_event_ids": duplicate_event_ids,
        "duplicate_event_sequences": duplicate_event_sequences,
        "event_sequence_errors": event_sequence_errors,
        "not_claimed": [
            "does_not_claim_production_oracle_network_live",
            "does_not_claim_true_market_price",
            "does_not_claim_reporter_honesty",
        ],
    }
    _write_json_file(store.root / "replay" / "latest_replay_receipt.json", receipt)
    return receipt


class ZenoOracleDevnetHandler(BaseHTTPRequestHandler):
    server_version = "ZenoOracleDevnet/0.1"

    @property
    def oracle_store(self) -> OracleDevnetStore:
        return self.server.oracle_store  # type: ignore[attr-defined]

    def log_message(self, fmt: str, *args: object) -> None:  # pragma: no cover - keeps tests quiet.
        return

    def _send(self, status: HTTPStatus, obj: Mapping[str, Any]) -> None:
        raw = json.dumps(obj, indent=2, sort_keys=True).encode("utf-8") + b"\n"
        self.send_response(int(status))
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _read_body(self) -> dict[str, Any] | None:
        length = int(self.headers.get("Content-Length", "0"))
        if length > MAX_BODY_BYTES:
            self._send(HTTPStatus.REQUEST_ENTITY_TOO_LARGE, _json_response("rejected", ["body_too_large"]))
            return None
        raw = self.rfile.read(length)
        try:
            obj = json.loads(raw.decode("utf-8") if raw else "{}")
        except Exception as exc:
            self._send(HTTPStatus.BAD_REQUEST, _json_response("rejected", [f"body_json_invalid:{exc}"]))
            return None
        if not isinstance(obj, dict):
            self._send(HTTPStatus.BAD_REQUEST, _json_response("rejected", ["body_must_be_json_object"]))
            return None
        return obj

    def do_GET(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        query = parse_qs(parsed.query)
        if parsed.path == "/health":
            self._send(
                HTTPStatus.OK,
                {
                    "schema": "zenodex.oracle.devnet_health.v1",
                    "ok": True,
                    "status": "accepted",
                    "store": str(self.oracle_store.root),
                },
            )
            return
        if parsed.path == "/state":
            self._send(HTTPStatus.OK, replay_store(self.oracle_store))
            return
        if parsed.path in {"/reads/latest", "/adapter/latest"}:
            query_id = query.get("query_id", [None])[0]
            if not isinstance(query_id, str):
                self._send(HTTPStatus.BAD_REQUEST, _json_response("rejected", ["query_id_required"]))
                return
            folder = "reads" if parsed.path == "/reads/latest" else "adapter_bridges"
            schema = AGGREGATE_READ_SCHEMA if folder == "reads" else AGGREGATE_ADAPTER_SCHEMA
            artifact = self.oracle_store.latest_artifact_for_query(folder, schema, query_id)
            if artifact is None:
                self._send(HTTPStatus.NOT_FOUND, _json_response("rejected", ["no_latest_artifact_for_query"], query_id=query_id))
                return
            self._send(HTTPStatus.OK, _json_response("accepted", query_id=query_id, artifact=artifact))
            return
        self._send(HTTPStatus.NOT_FOUND, _json_response("rejected", [f"unknown_path:{parsed.path}"]))

    def do_POST(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        body = self._read_body()
        if body is None:
            return
        if parsed.path == "/reporters/register":
            receipt = register_reporter(self.oracle_store, body)
        elif parsed.path == "/feeds/register":
            receipt = register_feed(self.oracle_store, body)
        elif parsed.path == "/reports/submit":
            receipt = submit_report(self.oracle_store, body)
        elif parsed.path == "/aggregates/build":
            receipt = build_aggregate(self.oracle_store, body)
        elif parsed.path == "/economics/event":
            receipt = persist_economic_event(self.oracle_store, body)
        elif parsed.path == "/replay":
            receipt = replay_store(self.oracle_store)
        else:
            self._send(HTTPStatus.NOT_FOUND, _json_response("rejected", [f"unknown_path:{parsed.path}"]))
            return
        status = HTTPStatus.OK if receipt.get("status") == "accepted" else HTTPStatus.BAD_REQUEST
        self._send(status, receipt)


def _artifact_query_id(artifact: Mapping[str, Any]) -> str | None:
    if artifact.get("schema") == AGGREGATE_READ_SCHEMA:
        aggregate = artifact.get("aggregate")
        if isinstance(aggregate, Mapping) and isinstance(aggregate.get("query_id"), str):
            return str(aggregate["query_id"])
    if artifact.get("schema") == AGGREGATE_ADAPTER_SCHEMA:
        read = artifact.get("aggregate_read")
        if isinstance(read, Mapping):
            return _artifact_query_id(read)
    return None


def run_server(*, store: Path, host: str, port: int) -> None:
    oracle_store = OracleDevnetStore(store)
    httpd = ThreadingHTTPServer((host, port), ZenoOracleDevnetHandler)
    httpd.oracle_store = oracle_store  # type: ignore[attr-defined]
    actual_host, actual_port = httpd.server_address[:2]
    sys.stdout.write(
        json.dumps(
            {
                "schema": "zenodex.oracle.devnet_startup.v1",
                "ok": True,
                "host": actual_host,
                "port": actual_port,
                "store": str(store),
            },
            sort_keys=True,
        )
        + "\n"
    )
    sys.stdout.flush()
    httpd.serve_forever()


def cmd_serve(args: argparse.Namespace) -> int:
    run_server(store=Path(args.store), host=args.host, port=int(args.port))
    return 0


def cmd_replay(args: argparse.Namespace) -> int:
    store = OracleDevnetStore(Path(args.store))
    receipt = replay_store(store)
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    serve = subparsers.add_parser("serve", help="run the local Zeno Oracle devnet HTTP service")
    serve.add_argument("--store", required=True, help="devnet receipt store directory")
    serve.add_argument("--host", default="127.0.0.1", help="bind host")
    serve.add_argument("--port", default=8008, type=int, help="bind port; use 0 for an ephemeral port")
    serve.set_defaults(func=cmd_serve)

    replay = subparsers.add_parser("replay", help="reconstruct devnet state from stored receipt events")
    replay.add_argument("--store", required=True, help="devnet receipt store directory")
    replay.add_argument("--output", help="optional replay receipt output path")
    replay.set_defaults(func=cmd_replay)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
