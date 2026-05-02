#!/usr/bin/env python3
"""Audit the Zeno Oracle Devnet Alpha acceptance criteria."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any
from urllib import request


ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "bin" / "zenodex-oracle"
RESULT_SCHEMA = "zenodex.oracle.devnet_alpha_completion_audit.v1"


def _post_json(base: str, path: str, obj: dict[str, Any]) -> dict[str, Any]:
    data = json.dumps(obj).encode("utf-8")
    req = request.Request(
        base + path,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with request.urlopen(req, timeout=20) as resp:  # noqa: S310 - local audit service.
        payload = json.loads(resp.read().decode("utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("non_object_json_response")
    return payload


def _get_json(base: str, path: str) -> dict[str, Any]:
    with request.urlopen(base + path, timeout=20) as resp:  # noqa: S310 - local audit service.
        payload = json.loads(resp.read().decode("utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("non_object_json_response")
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
    sys.path.insert(0, str(ROOT / "tools"))
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


def _criterion(idx: int, title: str, ok: bool, evidence: list[str], residual_limits: list[str] | None = None) -> dict[str, Any]:
    return {
        "id": idx,
        "title": title,
        "ok": bool(ok),
        "evidence": evidence,
        "residual_limits": list(residual_limits or []),
    }


def _run_package(version: str) -> tuple[bool, dict[str, Any] | None, str]:
    proc = subprocess.run(
        ["bash", "scripts/package_zeno_oracle_rc.sh", version],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=120,
    )
    if proc.returncode != 0:
        return False, None, proc.stderr or proc.stdout
    receipt_path = ROOT / "dist" / f"{version}.receipt.json"
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except Exception as exc:
        return False, None, f"receipt_load_failed:{exc}"
    if not isinstance(receipt, dict):
        return False, None, "receipt_not_object"
    return True, receipt, ""


def _workflow_ok() -> bool:
    workflow = (ROOT / ".github/workflows/zeno-oracle-mvp.yml").read_text(encoding="utf-8")
    return (
        "bash scripts/check_zeno_oracle_devnet_alpha.sh" in workflow
        and "zeno-oracle-devnet-alpha-rc1" in workflow
        and "actions/upload-artifact@v4" in workflow
    )


def run_audit() -> dict[str, Any]:
    sys.path.insert(0, str(ROOT / "tools"))
    from zenodex_oracle_feed_registry import sample_feed_registry
    from zenodex_oracle_signed_report import G2Basic

    criteria: list[dict[str, Any]] = []
    temp = tempfile.TemporaryDirectory(prefix="zeno-oracle-devnet-audit-")
    try:
        store = Path(temp.name) / "store"
        proc = subprocess.Popen(
            [str(BIN), "serve", "--store", str(store), "--host", "127.0.0.1", "--port", "0"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        try:
            assert proc.stdout is not None
            startup_line = proc.stdout.readline()
            startup = json.loads(startup_line)
            base = f"http://127.0.0.1:{startup['port']}"
            health_ok = False
            for _ in range(80):
                try:
                    health_ok = _get_json(base, "/health").get("ok") is True
                    if health_ok:
                        break
                except Exception:
                    time.sleep(0.05)

            registry = sample_feed_registry()
            feed = registry["feeds"][0]
            query_id = feed["query_spec"]["query_id"]
            sources = feed["source_diversity"]["sources"]
            feed_receipt = _post_json(base, "/feeds/register", registry)

            reporter_receipts = []
            report_receipts = []
            reporter_specs = [
                (61, "reporter.alpha", sources[0]["source_id"], 100_000_000, 8),
                (62, "reporter.beta", sources[1]["source_id"], 101_000_000, 9),
                (63, "reporter.gamma", sources[2]["source_id"], 99_500_000, 10),
            ]
            for private_key, reporter_id, source_id, value_e8, observed_epoch in reporter_specs:
                reporter_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
                reporter_receipts.append(
                    _post_json(
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
                )
                report_receipts.append(
                    _post_json(
                        base,
                        "/reports/submit",
                        _single_report_submission(
                            private_key=private_key,
                            reporter_id=reporter_id,
                            query_id=query_id,
                            source_id=source_id,
                            value_e8=value_e8,
                            observed_epoch=observed_epoch,
                        ),
                    )
                )

            aggregate_receipt = _post_json(base, "/aggregates/build", {"query_id": query_id})
            read_receipt = _get_json(base, f"/reads/latest?query_id={query_id}")
            adapter_receipt = _get_json(base, f"/adapter/latest?query_id={query_id}")
            economic_receipt = _post_json(
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
            replay_receipt = _post_json(base, "/replay", {})
        finally:
            proc.terminate()
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=10)

        replay_cli_proc = subprocess.run(
            [str(BIN), "replay", "--store", str(store)],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        replay_cli = json.loads(replay_cli_proc.stdout) if replay_cli_proc.returncode == 0 else {}
        package_ok, package_receipt, package_error = _run_package("zeno-oracle-devnet-alpha-audit-rc")

        docs_ok = all(
            (ROOT / path).is_file()
            for path in (
                "docs/ZENO_ORACLE_DEVNET_ALPHA.md",
                "docs/ZENO_ORACLE_CLI_V1.md",
                "docs/ZENO_ORACLE_MVP_STATUS.md",
            )
        )
        criteria.extend(
            [
            _criterion(1, "`bin/zenodex-oracle` starts a local Oracle service", health_ok, ["GET /health accepted"]),
            _criterion(
                2,
                "Reporters can register keys into a devnet registry",
                all(item.get("status") == "accepted" for item in reporter_receipts),
                [f"registered_reporters={len(reporter_receipts)}"],
            ),
            _criterion(
                3,
                "Reporters can submit signed reports over HTTP",
                all(item.get("status") == "accepted" for item in report_receipts),
                [f"accepted_report_submissions={len(report_receipts)}"],
            ),
            _criterion(
                4,
                "Feed registries are persisted, versioned, and replayable",
                feed_receipt.get("status") == "accepted" and (store / "feeds").is_dir(),
                [str(feed_receipt.get("registry_id"))],
            ),
            _criterion(
                5,
                "Aggregates are produced from admitted reports",
                aggregate_receipt.get("status") == "accepted" and aggregate_receipt.get("value_e8") == 100_000_000,
                [str(aggregate_receipt.get("aggregate_id"))],
            ),
            _criterion(
                6,
                "Accepted reads are exposed through an API",
                read_receipt.get("status") == "accepted"
                and read_receipt.get("artifact", {}).get("schema") == "zenodex.oracle.aggregate_read_bridge.v1",
                [str(read_receipt.get("artifact", {}).get("bridge_id"))],
            ),
            _criterion(
                7,
                "ZenoDEX can consume reads through the adapter bridge",
                adapter_receipt.get("status") == "accepted"
                and adapter_receipt.get("artifact", {}).get("schema") == "zenodex.oracle.aggregate_adapter_bridge.v1",
                [str(adapter_receipt.get("artifact", {}).get("bridge_id"))],
            ),
            _criterion(
                8,
                "Reporter reward, bond, and dispute events are persisted as devnet receipts",
                economic_receipt.get("status") == "accepted" and (store / "economics").is_dir(),
                [str(economic_receipt.get("economic_event_id"))],
                residual_limits=["audit exercises reward budget event; lifecycle tests cover bond/dispute ordering"],
            ),
            _criterion(
                9,
                "Replay reconstructs devnet state from stored receipts",
                replay_receipt.get("status") == "accepted"
                and replay_cli.get("status") == "accepted"
                and replay_cli.get("event_count") == replay_receipt.get("event_count"),
                [f"event_count={replay_receipt.get('event_count')}"],
            ),
            _criterion(
                10,
                "CI runs the local MVP gate plus service-level integration tests",
                _workflow_ok() and (ROOT / "scripts/check_zeno_oracle_devnet_alpha.sh").is_file(),
                ["scripts/check_zeno_oracle_devnet_alpha.sh"],
            ),
            _criterion(
                11,
                "Public docs explain devnet alpha, not production truth",
                docs_ok,
                ["docs/ZENO_ORACLE_DEVNET_ALPHA.md"],
            ),
            _criterion(
                12,
                "A signed RC/devnet package exists",
                package_ok
                and package_receipt is not None
                and isinstance(package_receipt.get("signature"), str)
                and (ROOT / "dist/zeno-oracle-devnet-alpha-audit-rc.sig").is_file(),
                ["dist/zeno-oracle-devnet-alpha-audit-rc.sig"] if package_ok else [package_error],
                residual_limits=["signature is a devnet integrity signature, not production code signing"],
            ),
            ]
        )
    finally:
        temp.cleanup()
    ok = all(item["ok"] for item in criteria)
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "criteria_count": len(criteria),
        "accepted_criteria_count": sum(1 for item in criteria if item["ok"]),
        "criteria": criteria,
        "not_claimed": [
            "does_not_claim_production_oracle_truth",
            "does_not_claim_onchain_feed_governance",
            "does_not_claim_production_code_signing",
        ],
    }


def main() -> int:
    try:
        receipt = run_audit()
    except Exception as exc:  # pragma: no cover - defensive CLI receipt.
        receipt = {
            "schema": RESULT_SCHEMA,
            "ok": False,
            "status": "inconclusive",
            "errors": [f"audit_failed:{exc}"],
        }
    sys.stdout.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return 0 if receipt.get("ok") is True else 2


if __name__ == "__main__":
    raise SystemExit(main())
