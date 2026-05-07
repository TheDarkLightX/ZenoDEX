#!/usr/bin/env python3
"""Deterministic Zeno Oracle devnet disaster-state harness.

This harness promotes a bounded slice of Oracle devnet "what if" states into
named replay receipts. Each case constructs the bad shape directly and requires
the devnet verifier/replay layer to reject it.
"""

from __future__ import annotations

import argparse
import copy
import json
import shutil
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_aggregate_adapter import sample_aggregate_adapter_bridge, verify_aggregate_adapter_bridge  # noqa: E402
from zenodex_oracle_devnet_service import (  # noqa: E402
    AGGREGATE_ADAPTER_SCHEMA,
    AGGREGATE_READ_SCHEMA,
    OracleDevnetStore,
    build_aggregate,
    persist_economic_event,
    register_feed,
    register_reporter,
    replay_store,
    submit_report,
)
from zenodex_oracle_feed_registry import content_hash, sample_feed_registry  # noqa: E402
from zenodex_oracle_signed_report import G2Basic, _build_report, submission_content_hash  # noqa: E402


RECEIPT_SCHEMA = "zenodex.oracle.devnet_disaster_harness_receipt.v1"
CHAIN_ID = "zenodex.oracle.local"


def _case_receipt(
    disaster_state: str,
    *,
    ok: bool,
    expected: str,
    observed: Mapping[str, Any],
    evidence: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "disaster_state": disaster_state,
        "ok": bool(ok),
        "status": "unreachable" if ok else "failed",
        "expected": expected,
        "observed": dict(observed),
        "evidence": {} if evidence is None else dict(evidence),
    }


def _query_context(registry: Mapping[str, Any]) -> tuple[str, list[str]]:
    feed = registry["feeds"][0]
    query_id = str(feed["query_spec"]["query_id"])
    sources = [str(source["source_id"]) for source in feed["source_diversity"]["sources"]]
    return query_id, sources


def _reporter_pubkey(private_key: int) -> str:
    return "0x" + G2Basic.SkToPk(private_key).hex()


def _single_report_submission(
    *,
    private_key: int,
    reporter_id: str,
    query_id: str,
    source_id: str,
    value_e8: int,
    observed_epoch: int,
) -> dict[str, Any]:
    reporter_pubkey = _reporter_pubkey(private_key)
    report = _build_report(
        private_key=private_key,
        chain_id=CHAIN_ID,
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        query_id=query_id,
        source_id=source_id,
        value_e8=value_e8,
        observed_epoch=observed_epoch,
        sequence=0,
        previous_report_id=None,
    )
    submission = {
        "schema": "zenodex.oracle.signed_report_submission.v1",
        "chain_id": CHAIN_ID,
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "reports": [report],
    }
    submission["submission_id"] = submission_content_hash(submission)
    return submission


def _new_store(root: Path, name: str) -> OracleDevnetStore:
    path = root / name
    shutil.rmtree(path, ignore_errors=True)
    return OracleDevnetStore(path)


def _accepted_pipeline_store(root: Path, name: str) -> OracleDevnetStore:
    template = root / "_accepted_pipeline_template"
    if not (template / "events.jsonl").is_file():
        template_store = OracleDevnetStore(template)
        _build_accepted_pipeline(template_store)
    target = root / name
    shutil.rmtree(target, ignore_errors=True)
    shutil.copytree(template, target)
    return OracleDevnetStore(target)


def _register_sample_feed(store: OracleDevnetStore) -> tuple[dict[str, Any], str, list[str]]:
    registry = sample_feed_registry()
    receipt = register_feed(store, registry)
    if receipt["status"] != "accepted":
        raise AssertionError(f"sample feed rejected: {receipt}")
    query_id, sources = _query_context(registry)
    return registry, query_id, sources


def _admit_three_reports(
    store: OracleDevnetStore,
    *,
    values: tuple[int, int, int] = (100_000_000, 101_000_000, 99_500_000),
) -> tuple[str, list[str]]:
    _registry, query_id, sources = _register_sample_feed(store)
    reporters = [
        (71, "reporter.alpha", sources[0], values[0], 8),
        (72, "reporter.beta", sources[1], values[1], 9),
        (73, "reporter.gamma", sources[2], values[2], 10),
    ]
    for private_key, reporter_id, source_id, value_e8, observed_epoch in reporters:
        registration = register_reporter(
            store,
            {
                "reporter_id": reporter_id,
                "reporter_pubkey": _reporter_pubkey(private_key),
                "required_bond": 100,
                "bond_amount": 100,
                "epoch": 1,
            },
        )
        if registration["status"] != "accepted":
            raise AssertionError(f"reporter rejected: {registration}")
        submission = _single_report_submission(
            private_key=private_key,
            reporter_id=reporter_id,
            query_id=query_id,
            source_id=source_id,
            value_e8=value_e8,
            observed_epoch=observed_epoch,
        )
        receipt = submit_report(store, submission)
        if receipt["status"] != "accepted":
            raise AssertionError(f"report submission rejected: {receipt}")
    return query_id, sources


def _build_accepted_pipeline(store: OracleDevnetStore) -> str:
    query_id, _sources = _admit_three_reports(store)
    aggregate = build_aggregate(store, {"query_id": query_id})
    if aggregate["status"] != "accepted":
        raise AssertionError(f"aggregate pipeline rejected: {aggregate}")
    economic = persist_economic_event(
        store,
        {
            "event_kind": "reward",
            "reporter_id": "reporter.alpha",
            "amount": 5,
            "budget_transition": {
                "schema": "zenodex.oracle.budget_transition.v1",
                "query_budget_remaining": 100,
                "query_reward_paid": 5,
                "reporter_bond_available": 100,
                "reporter_slash_paid": 0,
                "dispute_bond_available": 10,
                "dispute_slash_paid": 0,
                "fee_paid": 10,
                "reporter_fee_share": 5,
                "treasury_fee_share": 3,
                "burn_fee_share": 2,
            },
        },
    )
    if economic["status"] != "accepted":
        raise AssertionError(f"economic event rejected: {economic}")
    return query_id


def _first_artifact_event(store: OracleDevnetStore) -> dict[str, Any]:
    with store.events_path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if not line.strip():
                continue
            event = json.loads(line)
            if isinstance(event, dict) and isinstance(event.get("artifact_path"), str):
                return event
    raise AssertionError("accepted pipeline did not produce artifact events")


def _case_no_read_without_aggregate(root: Path) -> dict[str, Any]:
    store = _new_store(root, "no-read-without-aggregate")
    _registry, query_id, _sources = _register_sample_feed(store)
    artifact = store.latest_artifact_for_query("reads", AGGREGATE_READ_SCHEMA, query_id)
    return _case_receipt(
        "accepted_read_without_accepted_aggregate",
        ok=artifact is None,
        expected="no read artifact exists before an accepted aggregate pipeline",
        observed={"query_id": query_id, "artifact_found": artifact is not None},
    )


def _case_no_adapter_without_read(root: Path) -> dict[str, Any]:
    store = _new_store(root, "no-adapter-without-read")
    _registry, query_id, _sources = _register_sample_feed(store)
    artifact = store.latest_artifact_for_query("adapter_bridges", AGGREGATE_ADAPTER_SCHEMA, query_id)
    return _case_receipt(
        "adapter_bridge_without_matching_read",
        ok=artifact is None,
        expected="no adapter bridge exists before an accepted aggregate read",
        observed={"query_id": query_id, "artifact_found": artifact is not None},
    )


def _case_unregistered_reporter_rejected(root: Path) -> dict[str, Any]:
    store = _new_store(root, "unregistered-reporter")
    _registry, query_id, sources = _register_sample_feed(store)
    submission = _single_report_submission(
        private_key=81,
        reporter_id="reporter.unregistered",
        query_id=query_id,
        source_id=sources[0],
        value_e8=100_000_000,
        observed_epoch=8,
    )
    receipt = submit_report(store, submission)
    return _case_receipt(
        "revoked_or_unregistered_reporter_admitted",
        ok=receipt["status"] == "rejected" and "reporter_not_registered" in receipt["errors"],
        expected="report submission rejects an unregistered reporter before admission is persisted",
        observed=receipt,
    )


def _case_aggregate_needs_three(root: Path) -> dict[str, Any]:
    store = _new_store(root, "aggregate-needs-three")
    _registry, query_id, _sources = _register_sample_feed(store)
    receipt = build_aggregate(store, {"query_id": query_id})
    return _case_receipt(
        "accepted_read_without_accepted_aggregate.need_three_admissions",
        ok=receipt["status"] == "rejected" and any(str(error).startswith("need_3_distinct_admissions:") for error in receipt["errors"]),
        expected="aggregate pipeline rejects before creating read/adapter artifacts when fewer than three distinct admissions exist",
        observed=receipt,
    )


def _case_high_uncertainty_rejected(root: Path) -> dict[str, Any]:
    store = _new_store(root, "high-uncertainty")
    query_id, _sources = _admit_three_reports(store, values=(100_000_000, 140_000_000, 60_000_000))
    receipt = build_aggregate(store, {"query_id": query_id})
    read = store.latest_artifact_for_query("reads", AGGREGATE_READ_SCHEMA, query_id)
    adapter = store.latest_artifact_for_query("adapter_bridges", AGGREGATE_ADAPTER_SCHEMA, query_id)
    return _case_receipt(
        "high_uncertainty_price_used_by_critical_action",
        ok=(
            receipt["status"] == "rejected"
            and "aggregate_deviation_exceeds_policy" in receipt["errors"]
            and read is None
            and adapter is None
        ),
        expected="high-deviation aggregate rejects and cannot mint read or adapter artifacts",
        observed={**receipt, "read_created": read is not None, "adapter_created": adapter is not None},
    )


def _case_policy_downgrade_rejected(root: Path) -> dict[str, Any]:
    store = _new_store(root, "policy-downgrade")
    registry = sample_feed_registry()
    downgraded = copy.deepcopy(registry)
    policy = downgraded["feeds"][0]["aggregate_policy"]
    policy["evidence_floor"] = "O2"
    policy["policy_id"] = content_hash(policy, omit_key="policy_id")
    downgraded["feeds"][0]["feed_id"] = content_hash(downgraded["feeds"][0], omit_key="feed_id")
    downgraded["registry_id"] = content_hash(downgraded, omit_key="registry_id")
    receipt = register_feed(store, downgraded)
    return _case_receipt(
        "policy_downgrade_changes_existing_query_semantics",
        ok=receipt["status"] == "rejected" and "evidence_floor_below_critical_minimum" in receipt["errors"],
        expected="registry policy with lower-than-critical evidence floor rejects even with consistent content hashes",
        observed=receipt,
    )


def _case_receipt_borrowing_rejected(_root: Path) -> dict[str, Any]:
    adapter = sample_aggregate_adapter_bridge()
    borrowed = copy.deepcopy(adapter)
    borrowed["action"]["consumer_module"] = "perp_v2"
    result = verify_aggregate_adapter_bridge(borrowed).to_json_obj()
    return _case_receipt(
        "receipt_borrowed_across_consumer_action",
        ok=result["status"] == "rejected"
        and any(
            str(error).endswith(":adapter_consumer_module_mismatch")
            or str(error).endswith(":profile_consumer_module_mismatch")
            or str(error) in {"adapter_consumer_module_mismatch", "profile_consumer_module_mismatch"}
            for error in result["errors"]
        ),
        expected="adapter rejects when a valid receipt is borrowed into a different consumer action",
        observed=result,
    )


def _case_missing_consumer_profile_rejected(_root: Path) -> dict[str, Any]:
    adapter = sample_aggregate_adapter_bridge()
    missing_profile = copy.deepcopy(adapter)
    missing_profile.pop("profile", None)
    result = verify_aggregate_adapter_bridge(missing_profile).to_json_obj()
    return _case_receipt(
        "critical_action_without_consumer_profile",
        ok=result["status"] == "rejected" and "profile_must_be_object" in result["errors"],
        expected="aggregate adapter verifier rejects critical actions without a concrete consumer profile",
        observed=result,
    )


def _case_replay_matches_live_state(root: Path) -> dict[str, Any]:
    store = _accepted_pipeline_store(root, "replay-live-match")
    query_id = ""
    for path in sorted((store.root / "reads").glob("*.json")):
        read_candidate = json.loads(path.read_text(encoding="utf-8"))
        aggregate = read_candidate.get("aggregate")
        if isinstance(aggregate, dict) and isinstance(aggregate.get("query_id"), str):
            query_id = aggregate["query_id"]
            break
    if not query_id:
        raise AssertionError("accepted pipeline template has no aggregate read query_id")
    replay = replay_store(store)
    read = store.latest_artifact_for_query("reads", AGGREGATE_READ_SCHEMA, query_id)
    adapter = store.latest_artifact_for_query("adapter_bridges", AGGREGATE_ADAPTER_SCHEMA, query_id)
    latest_values = set(replay["latest_by_type"].values())
    ok = (
        replay["status"] == "accepted"
        and read is not None
        and adapter is not None
        and read["bridge_id"] in latest_values
        and adapter["bridge_id"] in latest_values
    )
    return _case_receipt(
        "replay_state_differs_from_live_state",
        ok=ok,
        expected="accepted replay latest IDs include the same read and adapter artifacts exposed by live state",
        observed={
            "replay": replay,
            "read_bridge_id": None if read is None else read.get("bridge_id"),
            "adapter_bridge_id": None if adapter is None else adapter.get("bridge_id"),
        },
    )


def _case_missing_artifact_replay_rejected(root: Path) -> dict[str, Any]:
    store = _accepted_pipeline_store(root, "missing-artifact")
    event = _first_artifact_event(store)
    artifact_path = store.root / str(event["artifact_path"])
    artifact_path.unlink()
    replay = replay_store(store)
    return _case_receipt(
        "missing_artifact_survives_replay",
        ok=replay["status"] == "rejected" and replay["missing_artifacts"],
        expected="replay rejects when an accepted event points at a missing artifact",
        observed=replay,
    )


def _case_tampered_artifact_replay_rejected(root: Path) -> dict[str, Any]:
    store = _accepted_pipeline_store(root, "tampered-artifact")
    event = _first_artifact_event(store)
    artifact_path = store.root / str(event["artifact_path"])
    obj = json.loads(artifact_path.read_text(encoding="utf-8"))
    obj["tampered_by_disaster_harness"] = True
    artifact_path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    replay = replay_store(store)
    return _case_receipt(
        "tampered_artifact_survives_replay",
        ok=replay["status"] == "rejected" and replay["artifact_hash_mismatches"],
        expected="replay rejects when an accepted artifact byte hash no longer matches its event receipt",
        observed=replay,
    )


def _case_duplicate_event_replay_rejected(root: Path) -> dict[str, Any]:
    store = _accepted_pipeline_store(root, "duplicate-event")
    lines = [line for line in store.events_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    store.events_path.write_text("\n".join([*lines, lines[0]]) + "\n", encoding="utf-8")
    replay = replay_store(store)
    return _case_receipt(
        "duplicate_event_changes_balance_or_reward",
        ok=replay["status"] == "rejected" and replay["duplicate_event_ids"] and replay["duplicate_event_sequences"],
        expected="replay rejects duplicate event ids/sequences before duplicated economic side effects can be accepted",
        observed=replay,
    )


def _case_reordered_event_replay_rejected(root: Path) -> dict[str, Any]:
    store = _accepted_pipeline_store(root, "reordered-event")
    lines = [line for line in store.events_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if len(lines) < 2:
        raise AssertionError("accepted pipeline produced fewer than two events")
    lines[0], lines[1] = lines[1], lines[0]
    store.events_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    replay = replay_store(store)
    return _case_receipt(
        "reordered_event_survives_replay",
        ok=replay["status"] == "rejected" and replay["event_sequence_errors"],
        expected="replay rejects non-monotonic event ordering",
        observed=replay,
    )


def _case_partial_event_write_rejected(root: Path) -> dict[str, Any]:
    store = _accepted_pipeline_store(root, "partial-event")
    with store.events_path.open("a", encoding="utf-8") as handle:
        handle.write('{"schema":"zenodex.oracle.devnet_event.v1","event_seq":999')
    replay = replay_store(store)
    return _case_receipt(
        "partial_event_write_survives_replay",
        ok=replay["status"] == "rejected" and replay["malformed_events"],
        expected="replay rejects a truncated JSON event line instead of silently accepting the journal",
        observed=replay,
    )


def _budget_case(root: Path, name: str, budget_overrides: Mapping[str, int], expected_error: str) -> dict[str, Any]:
    store = _new_store(root, name)
    budget = {
        "schema": "zenodex.oracle.budget_transition.v1",
        "query_budget_remaining": 100,
        "query_reward_paid": 5,
        "reporter_bond_available": 100,
        "reporter_slash_paid": 0,
        "dispute_bond_available": 10,
        "dispute_slash_paid": 0,
        "fee_paid": 10,
        "reporter_fee_share": 5,
        "treasury_fee_share": 3,
        "burn_fee_share": 2,
        **dict(budget_overrides),
    }
    receipt = persist_economic_event(
        store,
        {
            "event_kind": "reward",
            "reporter_id": "reporter.alpha",
            "amount": int(budget.get("query_reward_paid", 0)),
            "budget_transition": budget,
        },
    )
    return _case_receipt(
        name,
        ok=receipt["status"] == "rejected" and expected_error in receipt["errors"],
        expected=f"economic event rejects with {expected_error}",
        observed=receipt,
    )


CASES: tuple[Callable[[Path], dict[str, Any]], ...] = (
    _case_no_read_without_aggregate,
    _case_no_adapter_without_read,
    _case_unregistered_reporter_rejected,
    _case_aggregate_needs_three,
    _case_high_uncertainty_rejected,
    _case_policy_downgrade_rejected,
    _case_receipt_borrowing_rejected,
    _case_missing_consumer_profile_rejected,
    _case_replay_matches_live_state,
    _case_missing_artifact_replay_rejected,
    _case_tampered_artifact_replay_rejected,
    _case_duplicate_event_replay_rejected,
    _case_reordered_event_replay_rejected,
    _case_partial_event_write_rejected,
    lambda root: _budget_case(root, "reward_exceeds_verified_budget", {"query_reward_paid": 101}, "query_reward_exceeds_budget"),
    lambda root: _budget_case(root, "slash_exceeds_bond", {"reporter_slash_paid": 101}, "reporter_slash_exceeds_bond"),
    lambda root: _budget_case(root, "fee_split_exceeds_fee_paid", {"burn_fee_share": 3}, "fee_shares_exceed_fee_paid"),
)


def run_harness(root: Path) -> dict[str, Any]:
    shutil.rmtree(root / "_accepted_pipeline_template", ignore_errors=True)
    cases: list[dict[str, Any]] = []
    for case in CASES:
        try:
            cases.append(case(root))
        except Exception as exc:  # pragma: no cover - test suite keeps this path closed.
            cases.append(
                _case_receipt(
                    getattr(case, "__name__", "anonymous_case"),
                    ok=False,
                    expected="case executes without uncaught exception",
                    observed={"exception": f"{type(exc).__name__}:{exc}"},
                )
            )
    failed = [case for case in cases if not case["ok"]]
    return {
        "schema": RECEIPT_SCHEMA,
        "status": "accepted" if not failed else "rejected",
        "ok": not failed,
        "store_root": str(root),
        "selected_disaster_state_count": len(cases),
        "unreachable_count": len(cases) - len(failed),
        "failed_count": len(failed),
        "inconclusive_count": 0,
        "cases": cases,
        "not_claimed": [
            "does_not_claim_exhaustive_production_oracle_safety",
            "does_not_claim_true_market_price",
            "does_not_claim_reporter_honesty",
            "does_not_claim_network_liveness",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store-root", help="optional root directory for per-case stores")
    parser.add_argument("--output", help="optional output path for the harness receipt")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.store_root:
        root = Path(args.store_root)
        root.mkdir(parents=True, exist_ok=True)
        receipt = run_harness(root)
    else:
        with tempfile.TemporaryDirectory(prefix="zeno-oracle-disaster-") as tmp:
            receipt = run_harness(Path(tmp))

    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    if args.format == "json":
        sys.stdout.write(text)
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"selected_disaster_state_count = {receipt['selected_disaster_state_count']}",
                    f"unreachable_count = {receipt['unreachable_count']}",
                    f"failed_count = {receipt['failed_count']}",
                    f"inconclusive_count = {receipt['inconclusive_count']}",
                ]
            )
            + "\n"
        )
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
