from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any
from urllib import request


REPO = Path(__file__).resolve().parents[1]
CLI = [sys.executable, "tools/zenodex_oracle_cli.py"]


def _post_json(base: str, path: str, obj: dict[str, Any]) -> dict[str, Any]:
    data = json.dumps(obj).encode("utf-8")
    req = request.Request(
        base + path,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with request.urlopen(req, timeout=10) as resp:  # noqa: S310 - local test service.
        payload = json.loads(resp.read().decode("utf-8"))
    assert isinstance(payload, dict)
    return payload


def _get_json(base: str, path: str) -> dict[str, Any]:
    with request.urlopen(base + path, timeout=10) as resp:  # noqa: S310 - local test service.
        payload = json.loads(resp.read().decode("utf-8"))
    assert isinstance(payload, dict)
    return payload


def _single_report_submission(
    *,
    private_key: int,
    reporter_id: str,
    query_id: str,
    source_id: str,
    value_e8: int,
    observed_epoch: int,
) -> dict[str, Any]:
    sys.path.insert(0, str(REPO / "tools"))
    from zenodex_oracle_signed_report import G2Basic, _build_report, submission_content_hash

    reporter_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
    report = _build_report(
        private_key=private_key,
        chain_id="zenodex.oracle.local",
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
        "chain_id": "zenodex.oracle.local",
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "reports": [report],
    }
    submission["submission_id"] = submission_content_hash(submission)
    return submission


def test_oracle_devnet_service_replays_http_pipeline(tmp_path: Path) -> None:
    store = tmp_path / "oracle-devnet"
    proc = subprocess.Popen(
        [*CLI, "serve", "--store", str(store), "--host", "127.0.0.1", "--port", "0"],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        assert proc.stdout is not None
        startup_line = proc.stdout.readline()
        assert startup_line, proc.stderr.read() if proc.stderr is not None else ""
        startup = json.loads(startup_line)
        base = f"http://127.0.0.1:{startup['port']}"

        for _ in range(50):
            try:
                health = _get_json(base, "/health")
                if health["ok"] is True:
                    break
            except Exception:
                time.sleep(0.05)
        else:  # pragma: no cover - indicates service startup failure.
            raise AssertionError("devnet service did not become healthy")

        sys.path.insert(0, str(REPO / "tools"))
        from zenodex_oracle_feed_registry import sample_feed_registry
        from zenodex_oracle_signed_report import G2Basic

        registry = sample_feed_registry()
        feed = registry["feeds"][0]
        query_id = feed["query_spec"]["query_id"]
        sources = feed["source_diversity"]["sources"]

        feed_receipt = _post_json(base, "/feeds/register", registry)
        assert feed_receipt["status"] == "accepted"

        reporters = [
            (51, "reporter.alpha", sources[0]["source_id"], 100_000_000, 8),
            (52, "reporter.beta", sources[1]["source_id"], 101_000_000, 9),
            (53, "reporter.gamma", sources[2]["source_id"], 99_500_000, 10),
        ]
        for private_key, reporter_id, source_id, value_e8, observed_epoch in reporters:
            reporter_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
            registration = _post_json(
                base,
                "/reporters/register",
                {
                    "reporter_id": reporter_id,
                    "reporter_pubkey": reporter_pubkey,
                    "required_bond": 100,
                    "bond_amount": 100,
                    "epoch": 1,
                },
            )
            assert registration["status"] == "accepted"
            submission = _single_report_submission(
                private_key=private_key,
                reporter_id=reporter_id,
                query_id=query_id,
                source_id=source_id,
                value_e8=value_e8,
                observed_epoch=observed_epoch,
            )
            submit_receipt = _post_json(base, "/reports/submit", submission)
            assert submit_receipt["status"] == "accepted"
            assert len(submit_receipt["admission_ids"]) == 1

        aggregate_receipt = _post_json(base, "/aggregates/build", {"query_id": query_id})
        assert aggregate_receipt["status"] == "accepted"
        assert aggregate_receipt["value_e8"] == 100_000_000
        assert aggregate_receipt["deviation_bps"] == 100

        read = _get_json(base, f"/reads/latest?query_id={query_id}")
        assert read["status"] == "accepted"
        assert read["artifact"]["schema"] == "zenodex.oracle.aggregate_read_bridge.v1"

        adapter = _get_json(base, f"/adapter/latest?query_id={query_id}")
        assert adapter["status"] == "accepted"
        assert adapter["artifact"]["schema"] == "zenodex.oracle.aggregate_adapter_bridge.v1"

        economic = _post_json(
            base,
            "/economics/event",
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
        assert economic["status"] == "accepted"

        replay = _post_json(base, "/replay", {})
        assert replay["status"] == "accepted"
        assert replay["accepted_event_count"] >= 13
        assert replay["missing_artifacts"] == []
        assert replay["artifact_hash_mismatches"] == []
        assert replay["duplicate_event_ids"] == []
        assert replay["duplicate_event_sequences"] == []
        assert replay["event_sequence_errors"] == []
        assert replay["malformed_events"] == []
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:  # pragma: no cover - cleanup fallback.
            proc.kill()
            proc.wait(timeout=10)


def test_oracle_devnet_replay_cli_reads_receipt_store(tmp_path: Path) -> None:
    store = tmp_path / "oracle-devnet"
    store.mkdir()
    proc = subprocess.run(
        [*CLI, "replay", "--store", str(store)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.devnet_replay_receipt.v1"
    assert receipt["status"] == "accepted"
    assert receipt["event_count"] == 0
    assert receipt["artifact_hash_mismatches"] == []
    assert receipt["duplicate_event_ids"] == []
    assert receipt["duplicate_event_sequences"] == []
    assert receipt["event_sequence_errors"] == []
    assert receipt["malformed_events"] == []


def test_submit_report_rejects_underbonded_reporter(tmp_path: Path) -> None:
    sys.path.insert(0, str(REPO / "tools"))
    from zenodex_oracle_feed_registry import sample_feed_registry
    from zenodex_oracle_signed_report import G2Basic
    from zenodex_oracle_devnet_service import OracleDevnetStore, register_feed, register_reporter, submit_report

    store = OracleDevnetStore(tmp_path / "oracle-devnet")
    registry = sample_feed_registry()
    query_id = registry["feeds"][0]["query_spec"]["query_id"]
    source_id = registry["feeds"][0]["source_diversity"]["sources"][0]["source_id"]
    assert register_feed(store, registry)["status"] == "accepted"

    reporter_id = "reporter.lowbond"
    private_key = 77
    reporter_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
    registration = register_reporter(
        store,
        {
            "reporter_id": reporter_id,
            "reporter_pubkey": reporter_pubkey,
            "required_bond": 100,
            "bond_amount": 0,
            "epoch": 1,
        },
    )
    assert registration["status"] == "accepted"
    submission = _single_report_submission(
        private_key=private_key,
        reporter_id=reporter_id,
        query_id=query_id,
        source_id=source_id,
        value_e8=100_000_000,
        observed_epoch=5,
    )
    receipt = submit_report(store, submission)
    assert receipt["status"] == "rejected"
    assert any("report_submitted_under_required_bond" in error for error in receipt["errors"])
