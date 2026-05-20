#!/usr/bin/env python3
"""Run WES-ranked disaster probes against the multi-Docker ZenoLedger harness.

WES ranks probe order only. Deterministic validators and replay helpers decide
whether a probe is accepted, rejected, or a disaster witness.
"""

from __future__ import annotations

import argparse
import io
import json
import os
import sys
import tarfile
import tempfile
from pathlib import Path
from time import perf_counter
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

WES_SRC = ROOT / "external/WitnessEnergySearch/src"
if WES_SRC.exists() and str(WES_SRC) not in sys.path:
    sys.path.insert(0, str(WES_SRC))

from tools.zeno_ledger_multidocker_scenario import (
    _auth_token_from_env,
    _extract_bundle_archive,
    _post_json,
    _require_http_base_url,
    _write_bundle_archive,
    build_multidocker_plan_v0,
    derive_docker_node_hash_v0,
    validate_controller_config_v0,
)


SYSTEM_ID = "zeno_ledger_multidocker_disaster_boundary"
CHECKER_ID = "zeno_ledger_multidocker_disaster_boundary_checker"
TARGET_BOUNDARY_REJECTED = "invalid_multidocker_boundary_rejected"
TARGET_VALID_ACCEPTED = "valid_multidocker_boundary_accepted"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget", type=int, default=64)
    parser.add_argument("--top-k", type=int, default=24)
    parser.add_argument("--out-dir", type=Path, default=Path("runs/wes/zeno_ledger_multidocker_disaster"))
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = run_multidocker_wes_disaster_search(
        budget=args.budget,
        top_k=args.top_k,
        out_dir=args.out_dir,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def run_multidocker_wes_disaster_search(*, budget: int, top_k: int, out_dir: Path) -> dict[str, Any]:
    Candidate, _CheckResult, _ResultLabel, LinearEnergyRanker, compare_candidate_search_policies = _wes_api()
    candidates = build_multidocker_wes_candidates()
    ranker = LinearEnergyRanker(
        weights={
            "constraint.invalid_expected": -3.0,
            "constraint.path_escape": -2.5,
            "constraint.credentialed_url": -2.2,
            "constraint.role_cardinality": -2.0,
            "constraint.archive_link": -1.9,
            "constraint.request_size": -1.7,
            "checker_budget_cost": 0.02,
        }
    )
    started = perf_counter()
    wes_report = compare_candidate_search_policies(
        candidates=candidates,
        out_dir=out_dir,
        checker=check_multidocker_wes_candidate,
        budget=max(1, budget),
        seed="zeno-ledger-multidocker-disaster-v0",
        ranker=ranker,
        run_id="WES-ZENO-LEDGER-MULTIDOCKER-DISASTER-001",
        top_k=max(1, top_k),
        online_learning_rate=0.02,
        online_window=64,
    )
    elapsed_ms = (perf_counter() - started) * 1000.0
    summary = _summarize_wes_report(wes_report)
    ok = (
        summary["input_candidates"] == len(candidates)
        and summary["checked_total"] > 0
        and summary["disaster_count"] == 0
        and summary["model_online_useful_at_k"] > 0
    )
    return {
        "schema": "zenodex/zeno_ledger/multidocker_wes_disaster_search/v0",
        "ok": ok,
        "wes_commit": _wes_commit(),
        "budget": budget,
        "top_k": top_k,
        "input_candidates": len(candidates),
        "wall_clock_ms": elapsed_ms,
        "summary": summary,
        "wes_report": wes_report,
        "safety": {
            "wes_ranks_only": True,
            "deterministic_checker_authoritative": True,
            "scorer_authorizes_network_or_settlement": False,
            "invalid_accept_count": summary["disaster_count"],
        },
        "limits": [
            "This checks local deterministic multi-Docker harness boundaries.",
            "It does not replace a physical host run, WAN/NAT testing, or live firewall testing.",
            "A passing WES search report means the selected probes were rejected or accepted as expected under these bounded cases.",
        ],
    }


def build_multidocker_wes_candidates() -> list[Any]:
    Candidate, _CheckResult, _ResultLabel, _LinearEnergyRanker, _compare = _wes_api()
    rows = _candidate_rows()
    candidates: list[Any] = []
    for index, row in enumerate(rows):
        expected_reject = row["expected"] == "reject"
        candidates.append(
            Candidate(
                system_id=SYSTEM_ID,
                candidate_id=f"multidocker-boundary-{index:03d}-{row['case_id']}",
                source_lane=str(row["family"]),
                state_features={
                    "case_index": index,
                    "family": row["family"],
                },
                action_features={
                    "kind": row["kind"],
                    "expected_reject": expected_reject,
                },
                constraint_features={
                    "declared_energy": float(row["priority"]),
                    "invalid_expected": expected_reject,
                    "path_escape": row["case_id"] in {"archive_path_escape", "url_file_scheme"},
                    "credentialed_url": row["case_id"] == "url_embedded_credentials",
                    "role_cardinality": row["family"] == "controller_config",
                    "archive_link": row["case_id"] == "archive_symlink",
                    "request_size": row["case_id"] == "post_request_too_large",
                },
                checker_budget_cost=1.0,
                expected_checker=CHECKER_ID,
                target_predicates=(
                    TARGET_BOUNDARY_REJECTED if expected_reject else TARGET_VALID_ACCEPTED,
                ),
                deterministic_seed=f"zeno-ledger-multidocker-disaster:{index}:{row['case_id']}",
                payload={
                    "schema": "zenodex/zeno_ledger/multidocker_wes_candidate_payload/v0",
                    **row,
                },
            )
        )
    return candidates


def check_multidocker_wes_candidate(candidate: Any) -> Any:
    _Candidate, CheckResult, ResultLabel, _LinearEnergyRanker, _compare = _wes_api()
    started = perf_counter()
    payload = candidate.payload
    if not isinstance(payload, dict):
        return CheckResult(
            result=ResultLabel.MALFORMED,
            checker=CHECKER_ID,
            checker_ms=(perf_counter() - started) * 1000.0,
            notes="candidate payload must be an object",
        )
    expected_reject = payload.get("expected") == "reject"
    try:
        _evaluate_payload(payload)
        accepted = True
        errors: list[str] = []
    except Exception as exc:
        accepted = False
        errors = [f"{type(exc).__name__}:{exc}"]

    telemetry = {
        "case_id": payload.get("case_id"),
        "family": payload.get("family"),
        "kind": payload.get("kind"),
        "expected": payload.get("expected"),
        "accepted": accepted,
        "errors": errors,
    }
    if expected_reject and not accepted:
        return CheckResult(
            result=ResultLabel.NEAR_MISS,
            checker=CHECKER_ID,
            checker_ms=(perf_counter() - started) * 1000.0,
            violated_predicate=TARGET_BOUNDARY_REJECTED,
            witness_value=0.7,
            telemetry=telemetry,
            notes="invalid multi-Docker boundary was rejected",
        )
    if expected_reject and accepted:
        return CheckResult(
            result=ResultLabel.DISASTER,
            checker=CHECKER_ID,
            checker_ms=(perf_counter() - started) * 1000.0,
            violated_predicate=TARGET_BOUNDARY_REJECTED,
            witness_value=1.0,
            telemetry=telemetry,
            notes="invalid multi-Docker boundary was accepted",
        )
    if not expected_reject and accepted:
        return CheckResult(
            result=ResultLabel.NEAR_MISS,
            checker=CHECKER_ID,
            checker_ms=(perf_counter() - started) * 1000.0,
            violated_predicate=TARGET_VALID_ACCEPTED,
            witness_value=0.5,
            telemetry=telemetry,
            notes="valid multi-Docker boundary was accepted",
        )
    return CheckResult(
        result=ResultLabel.INVARIANT_VIOLATION,
        checker=CHECKER_ID,
        checker_ms=(perf_counter() - started) * 1000.0,
        violated_predicate=TARGET_VALID_ACCEPTED,
        witness_value=0.85,
        telemetry=telemetry,
        notes="valid multi-Docker boundary was rejected",
    )


def _evaluate_payload(payload: dict[str, Any]) -> None:
    kind = str(payload["kind"])
    args = payload.get("args", {})
    if not isinstance(args, dict):
        raise ValueError("payload args must be an object")
    if kind == "plan":
        build_multidocker_plan_v0(
            machine_count=int(args["machine_count"]),
            network_id=str(args["network_id"]),
            chain_id=str(args["chain_id"]),
        )
        return
    if kind == "node_hash":
        derive_docker_node_hash_v0(
            network_id=str(args["network_id"]),
            chain_id=str(args["chain_id"]),
            node_identity=str(args["node_identity"]),
        )
        return
    if kind == "url":
        _require_http_base_url(str(args["url"]), name="url")
        return
    if kind == "controller_config":
        report = validate_controller_config_v0(
            machine_count=int(args["machine_count"]),
            writer_url=str(args["writer_url"]),
            forwarder_url=args.get("forwarder_url"),
            readonly_url=args.get("readonly_url"),
            node_data_dirs=[Path(str(item)) for item in args.get("node_data_dirs", [])],
        )
        if not report["ok"]:
            raise ValueError(",".join(report["errors"]))
        return
    if kind == "archive":
        _evaluate_archive_case(str(args["archive_case"]))
        return
    if kind == "post_json":
        _post_json(str(args["url"]), {"body": "x" * int(args["body_size"])}, token=None, timeout=0.01)
        return
    if kind == "auth_env":
        _evaluate_auth_env(str(args["env_name"]), args.get("env_value"))
        return
    raise ValueError(f"unknown candidate kind: {kind}")


def _evaluate_auth_env(env_name: str, env_value: object) -> None:
    old = os.environ.get(env_name)
    try:
        if env_value is None:
            os.environ.pop(env_name, None)
        else:
            os.environ[env_name] = str(env_value)
        _auth_token_from_env(env_name)
    finally:
        if old is None:
            os.environ.pop(env_name, None)
        else:
            os.environ[env_name] = old


def _evaluate_archive_case(case: str) -> None:
    with tempfile.TemporaryDirectory(prefix="zeno-ledger-multidocker-wes-") as tmp:
        root = Path(tmp)
        archive = root / "bundle.tar.gz"
        out = root / "out" / "bundle"
        if case == "valid":
            bundle = root / "bundle"
            bundle.mkdir()
            (bundle / "public_testnet_manifest.json").write_text('{"ok": true}\n', encoding="utf-8")
            _write_bundle_archive(bundle_root=bundle, tar_out=archive)
        elif case == "path_escape":
            with tarfile.open(archive, "w:gz") as tar:
                info = tarfile.TarInfo("../escape.txt")
                payload = b"bad"
                info.size = len(payload)
                tar.addfile(info, io.BytesIO(payload))
        elif case == "symlink":
            with tarfile.open(archive, "w:gz") as tar:
                root_info = tarfile.TarInfo("bundle")
                root_info.type = tarfile.DIRTYPE
                tar.addfile(root_info)
                link = tarfile.TarInfo("bundle/public_testnet_manifest.json")
                link.type = tarfile.SYMTYPE
                link.linkname = "/etc/passwd"
                tar.addfile(link)
        elif case == "missing_manifest":
            bundle = root / "bundle"
            bundle.mkdir()
            (bundle / "other.json").write_text('{"ok": true}\n', encoding="utf-8")
            _write_bundle_archive(bundle_root=bundle, tar_out=archive)
        elif case == "empty":
            with tarfile.open(archive, "w:gz"):
                pass
        else:
            raise ValueError(f"unknown archive case: {case}")
        _extract_bundle_archive(archive_path=archive, bundle_root=out)


def _candidate_rows() -> list[dict[str, Any]]:
    return [
        _row("plan_valid_two", "plan", "plan", "accept", 0.5, machine_count=2, network_id="n", chain_id="c"),
        _row("plan_valid_three", "plan", "plan", "accept", 0.5, machine_count=3, network_id="n", chain_id="c"),
        _row("plan_machine_count_zero", "plan", "plan", "reject", 0.1, machine_count=0, network_id="n", chain_id="c"),
        _row("plan_machine_count_four", "plan", "plan", "reject", 0.1, machine_count=4, network_id="n", chain_id="c"),
        _row("plan_empty_network", "plan", "plan", "reject", 0.2, machine_count=2, network_id="", chain_id="c"),
        _row("node_hash_empty_identity", "node_hash", "node_hash", "reject", 0.2, network_id="n", chain_id="c", node_identity=""),
        _row("node_hash_valid", "node_hash", "node_hash", "accept", 0.6, network_id="n", chain_id="c", node_identity="node"),
        _row("url_valid_http", "url", "url", "accept", 0.6, url="http://machine-a.local:8787"),
        _row("url_valid_https_path", "url", "url", "accept", 0.6, url="https://example.test/base"),
        _row("url_file_scheme", "url", "url", "reject", 0.1, url="file:///etc/passwd"),
        _row("url_embedded_credentials", "url", "url", "reject", 0.1, url="http://user:pass@example.test:8787"),
        _row("url_query", "url", "url", "reject", 0.2, url="http://example.test:8787/?x=1"),
        _row("url_fragment", "url", "url", "reject", 0.2, url="http://example.test:8787/#x"),
        _row("controller_valid_two", "controller_config", "controller_config", "accept", 0.6, **_controller_args(2)),
        _row("controller_valid_three", "controller_config", "controller_config", "accept", 0.6, **_controller_args(3)),
        _row(
            "controller_missing_forwarder",
            "controller_config",
            "controller_config",
            "reject",
            0.1,
            **{**_controller_args(2), "forwarder_url": None},
        ),
        _row(
            "controller_missing_readonly",
            "controller_config",
            "controller_config",
            "reject",
            0.1,
            **{**_controller_args(3), "readonly_url": None},
        ),
        _row(
            "controller_readonly_on_two_machine",
            "controller_config",
            "controller_config",
            "reject",
            0.1,
            **{**_controller_args(2), "readonly_url": "http://node-c:8787"},
        ),
        _row(
            "controller_credentialed_writer_url",
            "controller_config",
            "controller_config",
            "reject",
            0.1,
            **{**_controller_args(2), "writer_url": "http://u:p@node-a:8787"},
        ),
        _row("archive_valid", "archive", "archive", "accept", 0.6, archive_case="valid"),
        _row("archive_path_escape", "archive", "archive", "reject", 0.1, archive_case="path_escape"),
        _row("archive_symlink", "archive", "archive", "reject", 0.1, archive_case="symlink"),
        _row("archive_missing_manifest", "archive", "archive", "reject", 0.2, archive_case="missing_manifest"),
        _row("archive_empty", "archive", "archive", "reject", 0.2, archive_case="empty"),
        _row("post_request_too_large", "post_json", "post_json", "reject", 0.1, url="http://127.0.0.1:1/faucet", body_size=2_097_153),
        _row("auth_env_valid", "auth_env", "auth_env", "accept", 0.6, env_name="ZENO_WES_TEST_TOKEN", env_value="ok"),
        _row("auth_env_unset", "auth_env", "auth_env", "reject", 0.2, env_name="ZENO_WES_TEST_TOKEN_UNSET", env_value=None),
        _row("auth_env_empty", "auth_env", "auth_env", "reject", 0.2, env_name="ZENO_WES_TEST_TOKEN_EMPTY", env_value=""),
    ]


def _controller_args(machine_count: int) -> dict[str, Any]:
    args: dict[str, Any] = {
        "machine_count": machine_count,
        "writer_url": "http://node-a:8787",
        "forwarder_url": "http://node-b:8787",
        "readonly_url": None,
        "node_data_dirs": ["/tmp/node-a", "/tmp/node-b"],
    }
    if machine_count == 3:
        args["readonly_url"] = "http://node-c:8787"
        args["node_data_dirs"] = ["/tmp/node-a", "/tmp/node-b", "/tmp/node-c"]
    return args


def _row(
    case_id: str,
    family: str,
    kind: str,
    expected: str,
    priority: float,
    **args: Any,
) -> dict[str, Any]:
    return {
        "case_id": case_id,
        "family": family,
        "kind": kind,
        "expected": expected,
        "priority": priority,
        "args": args,
    }


def _summarize_wes_report(report: dict[str, object]) -> dict[str, Any]:
    runs = report["runs"]
    if not isinstance(runs, dict):
        raise TypeError("WES report runs must be a mapping")
    summary: dict[str, Any] = {
        "input_candidates": int(report["input_candidates"]),
        "top_k": int(report["top_k"]),
        "checked_total": 0,
        "disaster_count": 0,
        "invariant_violation_count": 0,
    }
    for name, run in runs.items():
        if not isinstance(run, dict):
            continue
        counts = run.get("result_counts", {})
        order = run.get("actual_search_order", {})
        if not isinstance(counts, dict) or not isinstance(order, dict):
            continue
        checked = int(run["checked"])
        summary["checked_total"] += checked
        summary["disaster_count"] += int(counts.get("disaster", 0))
        summary["invariant_violation_count"] += int(counts.get("invariant_violation", 0))
        summary[f"{name}_checked"] = checked
        summary[f"{name}_useful_at_k"] = int(order["useful_at_k"])
        summary[f"{name}_calls_to_first_useful"] = order["calls_to_first_useful"]
        summary[f"{name}_near_misses_at_k"] = int(order["near_misses_at_k"])
        summary[f"{name}_non_useful_at_k"] = int(order["non_useful_at_k"])
        summary[f"{name}_disasters"] = int(counts.get("disaster", 0))
    return summary


def _wes_api() -> tuple[Any, Any, Any, Any, Any]:
    if not WES_SRC.exists():
        raise RuntimeError(
            "external/WitnessEnergySearch is required; clone git@github.com:TheDarkLightX/WitnessEnergySearch.git into external/"
        )
    try:
        from wes.ranker import LinearEnergyRanker
        from wes.schema import Candidate, CheckResult, ResultLabel
        from wes.search import compare_candidate_search_policies
    except ModuleNotFoundError as exc:
        raise RuntimeError("WES is not importable from external/WitnessEnergySearch/src") from exc
    return Candidate, CheckResult, ResultLabel, LinearEnergyRanker, compare_candidate_search_policies


def _wes_commit() -> str | None:
    head = ROOT / "external/WitnessEnergySearch/.git/HEAD"
    if not head.exists():
        return None
    text = head.read_text(encoding="utf-8").strip()
    if text.startswith("ref: "):
        ref_path = ROOT / "external/WitnessEnergySearch/.git" / text.removeprefix("ref: ")
        return ref_path.read_text(encoding="utf-8").strip() if ref_path.exists() else None
    return text


def _markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# ZenoLedger Multi-Docker WES Disaster Search",
        "",
        "WES ranks multi-Docker boundary probes. Deterministic validators label every probe.",
        "",
        f"WES commit: `{report['wes_commit']}`",
        "",
        "| policy | checked | useful@k | calls to first useful | disasters |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for policy in (
        "model_online",
        "model_frozen",
        "declared_priority",
        "cheap_first",
        "input_order",
        "random_seeded",
    ):
        lines.append(
            "| {policy} | {checked} | {useful} | {calls} | {disasters} |".format(
                policy=policy,
                checked=summary.get(f"{policy}_checked", 0),
                useful=summary.get(f"{policy}_useful_at_k", 0),
                calls=summary.get(f"{policy}_calls_to_first_useful"),
                disasters=summary.get(f"{policy}_disasters", 0),
            )
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- WES changes probe order only.",
            "- Deterministic validators decide whether a probe is accepted or rejected.",
            "- The report is local harness evidence and does not replace physical host evidence.",
            "",
        ]
    )
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
