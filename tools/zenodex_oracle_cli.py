#!/usr/bin/env python3
"""Unified local CLI for the Zeno Oracle MVP verifier shell."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import os
import stat
import tempfile
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[1]
TOOLS = REPO / "tools"

SURFACES: dict[str, str] = {
    "receipt": "zenodex_oracle.py",
    "budget": "zenodex_oracle_budget.py",
    "reporter-lifecycle": "zenodex_oracle_reporter_lifecycle.py",
    "signed-report": "zenodex_oracle_signed_report.py",
    "report-admission": "zenodex_oracle_report_admission.py",
    "median3": "zenodex_oracle_median3.py",
    "admitted-median3": "zenodex_oracle_admitted_median3.py",
    "aggregate-read": "zenodex_oracle_aggregate_read.py",
    "aggregate-adapter": "zenodex_oracle_aggregate_adapter.py",
    "feed": "zenodex_oracle_feed_registry.py",
    "source-diversity": "zenodex_oracle_source_diversity.py",
    "query-policy": "zenodex_oracle_query_policy.py",
    "adapter": "zenodex_oracle_adapter.py",
    "consumer-profiles": "zenodex_oracle_consumer_profiles.py",
    "economic-security": "zenodex_oracle_economic_security.py",
}

ALIASES: dict[str, str] = {
    "feed-registry": "feed",
    "reports": "signed-report",
    "lifecycle": "reporter-lifecycle",
    "admission": "report-admission",
    "source": "source-diversity",
    "profiles": "consumer-profiles",
    "economic": "economic-security",
}

CHAOS_SURFACES: dict[str, str] = {
    "receipt": "zenodex_oracle_chaos.py",
    "budget": "zenodex_oracle_budget_chaos.py",
    "reporter-lifecycle": "zenodex_oracle_reporter_lifecycle_chaos.py",
    "signed-report": "zenodex_oracle_signed_report_chaos.py",
    "report-admission": "zenodex_oracle_report_admission_chaos.py",
    "median3": "zenodex_oracle_median3_chaos.py",
    "admitted-median3": "zenodex_oracle_admitted_median3_chaos.py",
    "aggregate-read": "zenodex_oracle_aggregate_read_chaos.py",
    "aggregate-adapter": "zenodex_oracle_aggregate_adapter_chaos.py",
    "feed": "zenodex_oracle_feed_registry_chaos.py",
    "source-diversity": "zenodex_oracle_source_diversity_chaos.py",
    "query-policy": "zenodex_oracle_query_policy_chaos.py",
    "adapter": "zenodex_oracle_adapter_chaos.py",
    "consumer-profiles": "zenodex_oracle_consumer_profiles_chaos.py",
    "economic-security": "zenodex_oracle_economic_security_chaos.py",
}


def _resolve_surface(name: str, *, chaos: bool = False) -> str:
    resolved = ALIASES.get(name, name)
    known = CHAOS_SURFACES if chaos else SURFACES
    if resolved not in known:
        choices = ", ".join(sorted(known))
        raise SystemExit(f"unknown Oracle surface {name!r}; expected one of: {choices}")
    return resolved


def _script_path(script: str) -> Path:
    path = TOOLS / script
    if not path.is_file():
        raise SystemExit(f"missing Oracle tool: {path}")
    return path


def _run_script(script: str, args: list[str]) -> int:
    path = _script_path(script)
    proc = subprocess.run(
        [sys.executable, str(path), *args],
        cwd=REPO,
        check=False,
    )
    return int(proc.returncode)


def _run_script_json(script: str, args: list[str]) -> tuple[int, dict[str, Any] | None, str]:
    path = _script_path(script)
    proc = subprocess.run(
        [sys.executable, str(path), *args],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return int(proc.returncode), None, proc.stderr or proc.stdout
    try:
        obj = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return 3, None, f"{script} returned non-json output: {exc}"
    if not isinstance(obj, dict):
        return 3, None, f"{script} returned non-object JSON"
    return 0, obj, ""


def _write_json(obj: dict[str, Any], output: Path | None) -> None:
    text = json.dumps(obj, indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")


def _result_ok(obj: dict[str, Any] | None) -> bool:
    if obj is None:
        return False
    status = obj.get("status")
    if status is not None:
        return status == "accepted"
    return obj.get("ok") is True


def _summarize_result(obj: dict[str, Any] | None) -> dict[str, Any]:
    if obj is None:
        return {}
    summary: dict[str, Any] = {}
    for key in (
        "schema",
        "ok",
        "status",
        "registry_id",
        "submission_id",
        "aggregate_receipt_id",
        "read_receipt_id",
        "consumer_action_receipt_id",
        "profile_id",
        "reporter_id",
        "errors",
    ):
        if key in obj:
            summary[key] = obj[key]
    return summary


def _ensure_private_new_workdir(root: Path) -> None:
    """Create a user-requested dry-run workdir as a new private directory."""
    try:
        root.mkdir(parents=True, exist_ok=False, mode=0o700)
    except FileExistsError as exc:
        raise SystemExit(
            f"refusing to use existing dry-run workdir {root}; provide a new path"
        ) from exc

    root_stat = root.stat()
    mode = stat.S_IMODE(root_stat.st_mode)
    if root_stat.st_uid != os.getuid():
        raise SystemExit(f"dry-run workdir must be owned by current user: {root}")
    if mode & 0o077:
        raise SystemExit(f"dry-run workdir must not be group/world accessible: {root}")


def _dry_run_root(workdir: str | None) -> tuple[Path, tempfile.TemporaryDirectory[str] | None]:
    if workdir:
        root = Path(workdir)
        _ensure_private_new_workdir(root)
        return root, None
    temp = tempfile.TemporaryDirectory(prefix="zeno-oracle-dry-run-")
    return Path(temp.name), temp


def _hash_to_filename(value: str) -> str:
    if not value.startswith("sha256:"):
        raise SystemExit(f"expected sha256 id, got {value!r}")
    return value.split(":", 1)[1] + ".json"


def cmd_list(_args: argparse.Namespace) -> int:
    obj = {
        "schema": "zenodex.oracle.cli_surface_list.v1",
        "surfaces": sorted(SURFACES),
        "aliases": dict(sorted(ALIASES.items())),
        "chaos_surfaces": sorted(CHAOS_SURFACES),
    }
    sys.stdout.write(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    return 0


def cmd_doctor(_args: argparse.Namespace) -> int:
    missing = []
    for script in sorted(set(SURFACES.values()) | set(CHAOS_SURFACES.values())):
        if not (TOOLS / script).is_file():
            missing.append(script)
    obj = {
        "schema": "zenodex.oracle.cli_doctor.v1",
        "ok": not missing,
        "surface_count": len(SURFACES),
        "chaos_surface_count": len(CHAOS_SURFACES),
        "missing_scripts": missing,
    }
    sys.stdout.write(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    return 0 if not missing else 2


def cmd_sample(args: argparse.Namespace) -> int:
    surface = _resolve_surface(args.surface)
    return _run_script(SURFACES[surface], ["sample", *args.args])


def cmd_verify(args: argparse.Namespace) -> int:
    surface = _resolve_surface(args.surface)
    return _run_script(SURFACES[surface], ["verify", *args.args])


def cmd_chaos(args: argparse.Namespace) -> int:
    if args.surface != "all":
        surface = _resolve_surface(args.surface, chaos=True)
        return _run_script(CHAOS_SURFACES[surface], args.args)

    results: list[dict[str, Any]] = []
    ok = True
    for surface, script in sorted(CHAOS_SURFACES.items()):
        code, obj, err = _run_script_json(script, args.args)
        surface_ok = code == 0 and obj is not None and obj.get("ok") is True
        ok = ok and surface_ok
        results.append(
            {
                "surface": surface,
                "script": script,
                "ok": surface_ok,
                "returncode": code,
                "case_count": None if obj is None else obj.get("case_count"),
                "rejected_case_count": None if obj is None else obj.get("rejected_case_count"),
                "failed_case_count": None if obj is None else obj.get("failed_case_count"),
                "error": err,
            }
        )
    receipt = {
        "schema": "zenodex.oracle.cli_chaos_all.v1",
        "ok": ok,
        "surface_count": len(results),
        "case_count": sum(int(item["case_count"] or 0) for item in results),
        "rejected_case_count": sum(int(item["rejected_case_count"] or 0) for item in results),
        "failed_case_count": sum(int(item["failed_case_count"] or 0) for item in results),
        "results": results,
    }
    sys.stdout.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return 0 if ok else 2


def cmd_register_feed(args: argparse.Namespace) -> int:
    registry_path = Path(args.registry)
    code, result, err = _run_script_json(SURFACES["feed"], ["verify", str(registry_path)])
    if code != 0 or result is None or result.get("status") != "accepted":
        if result is not None:
            _write_json(result, Path(args.receipt_output) if args.receipt_output else None)
        elif err:
            sys.stderr.write(err)
        return code if code != 0 else 2

    registry_id = str(result["registry_id"])
    store_dir = Path(args.store)
    feed_dir = store_dir / "feeds"
    feed_dir.mkdir(parents=True, exist_ok=True)
    stored_path = feed_dir / _hash_to_filename(registry_id)
    shutil.copyfile(registry_path, stored_path)
    receipt = {
        "schema": "zenodex.oracle.cli_feed_registration_receipt.v1",
        "ok": True,
        "status": "accepted",
        "registry_id": registry_id,
        "feed_count": result.get("feed_count"),
        "active_feed_count": result.get("active_feed_count"),
        "stored_path": str(stored_path),
        "not_claimed": [
            "does_not_claim_onchain_feed_governance",
            "does_not_claim_network_broadcast",
        ],
    }
    _write_json(receipt, Path(args.receipt_output) if args.receipt_output else None)
    return 0


def cmd_submit_report(args: argparse.Namespace) -> int:
    submission_path = Path(args.submission)
    code, result, err = _run_script_json(SURFACES["signed-report"], ["verify", str(submission_path)])
    if code != 0 or result is None or result.get("status") != "accepted":
        if result is not None:
            _write_json(result, Path(args.receipt_output) if args.receipt_output else None)
        elif err:
            sys.stderr.write(err)
        return code if code != 0 else 2

    submission_id = str(result["submission_id"])
    store_dir = Path(args.store)
    report_dir = store_dir / "signed_reports"
    report_dir.mkdir(parents=True, exist_ok=True)
    stored_path = report_dir / _hash_to_filename(submission_id)
    shutil.copyfile(submission_path, stored_path)
    receipt = {
        "schema": "zenodex.oracle.cli_report_submission_receipt.v1",
        "ok": True,
        "status": "accepted",
        "submission_id": submission_id,
        "reporter_id": result.get("reporter_id"),
        "report_count": result.get("report_count"),
        "stored_path": str(stored_path),
        "not_claimed": [
            "does_not_claim_report_value_true",
            "does_not_claim_reporter_registered_or_bonded",
            "does_not_claim_network_broadcast",
        ],
    }
    _write_json(receipt, Path(args.receipt_output) if args.receipt_output else None)
    return 0


def cmd_dry_run(args: argparse.Namespace) -> int:
    root, temp = _dry_run_root(args.workdir)
    steps: list[dict[str, Any]] = []

    def add_step(
        name: str,
        *,
        code: int,
        path: Path | None = None,
        result: dict[str, Any] | None = None,
        error: str = "",
    ) -> bool:
        ok = code == 0 and (result is None or _result_ok(result))
        item: dict[str, Any] = {
            "name": name,
            "ok": ok,
            "returncode": int(code),
        }
        if path is not None:
            item["path"] = str(path)
        if result is not None:
            item["result"] = _summarize_result(result)
        if error:
            item["error"] = error
        steps.append(item)
        return ok

    try:
        store = root / "store"
        feed_path = root / "feed-registry.json"
        feed_receipt_path = root / "feed-registration-receipt.json"
        report_path = root / "signed-report.json"
        report_receipt_path = root / "report-submission-receipt.json"
        lifecycle_path = root / "reporter-lifecycle.json"
        budget_path = root / "token-budget-transition.json"
        admitted_path = root / "admitted-median3.json"
        read_path = root / "aggregate-read.json"
        aggregate_adapter_path = root / "aggregate-adapter.json"
        adapter_action_path = root / "adapter-action.json"
        adapter_bundle_path = root / "adapter-bundle.json"
        adapter_profile_path = root / "adapter-profile.json"

        sample_plan = [
            ("sample_feed", "feed", feed_path),
            ("sample_signed_report", "signed-report", report_path),
            ("sample_reporter_lifecycle", "reporter-lifecycle", lifecycle_path),
            ("sample_token_budget", "budget", budget_path),
            ("sample_admitted_median3", "admitted-median3", admitted_path),
            ("sample_aggregate_read", "aggregate-read", read_path),
            ("sample_aggregate_adapter", "aggregate-adapter", aggregate_adapter_path),
        ]
        for name, surface, path in sample_plan:
            add_step(
                name,
                code=_run_script(SURFACES[surface], ["sample", "--output", str(path)]),
                path=path,
            )

        code = _run_script(
            SURFACES["adapter"],
            [
                "sample",
                "--action-output",
                str(adapter_action_path),
                "--bundle-output",
                str(adapter_bundle_path),
                "--profile-output",
                str(adapter_profile_path),
            ],
        )
        add_step("sample_adapter_bundle", code=code, path=adapter_bundle_path)

        verify_plan = [
            ("verify_feed", "feed", feed_path),
            ("verify_signed_report", "signed-report", report_path),
            ("verify_reporter_lifecycle", "reporter-lifecycle", lifecycle_path),
            ("verify_token_budget", "budget", budget_path),
            ("verify_admitted_median3", "admitted-median3", admitted_path),
            ("verify_aggregate_read", "aggregate-read", read_path),
            ("verify_aggregate_adapter", "aggregate-adapter", aggregate_adapter_path),
        ]
        for name, surface, path in verify_plan:
            code, result, err = _run_script_json(SURFACES[surface], ["verify", str(path)])
            add_step(name, code=code, path=path, result=result, error=err)

        code, result, err = _run_script_json(
            SURFACES["adapter"],
            [
                "verify",
                "--action",
                str(adapter_action_path),
                "--bundle",
                str(adapter_bundle_path),
                "--profile",
                str(adapter_profile_path),
            ],
        )
        add_step("verify_adapter_bundle", code=code, path=adapter_bundle_path, result=result, error=err)

        register_code = cmd_register_feed(
            argparse.Namespace(
                registry=str(feed_path),
                store=str(store),
                receipt_output=str(feed_receipt_path),
            )
        )
        register_result = json.loads(feed_receipt_path.read_text(encoding="utf-8")) if feed_receipt_path.exists() else None
        add_step("register_feed_to_local_store", code=register_code, path=feed_receipt_path, result=register_result)

        submit_code = cmd_submit_report(
            argparse.Namespace(
                submission=str(report_path),
                store=str(store),
                receipt_output=str(report_receipt_path),
            )
        )
        submit_result = json.loads(report_receipt_path.read_text(encoding="utf-8")) if report_receipt_path.exists() else None
        add_step("submit_report_to_local_store", code=submit_code, path=report_receipt_path, result=submit_result)

        ok = all(bool(step["ok"]) for step in steps)
        receipt = {
            "schema": "zenodex.oracle.cli_dry_run_receipt.v1",
            "ok": ok,
            "status": "accepted" if ok else "rejected",
            "step_count": len(steps),
            "accepted_step_count": sum(1 for step in steps if step["ok"]),
            "artifact_dir": str(root) if args.workdir else None,
            "artifacts_persisted": bool(args.workdir),
            "local_store": str(store) if args.workdir else None,
            "steps": steps,
            "not_claimed": [
                "does_not_claim_network_broadcast",
                "does_not_claim_onchain_feed_governance",
                "does_not_claim_live_reporter_registry",
            ],
        }
        _write_json(receipt, Path(args.output) if args.output else None)
        return 0 if ok else 2
    finally:
        if temp is not None:
            temp.cleanup()


def cmd_serve(args: argparse.Namespace) -> int:
    from zenodex_oracle_devnet_service import cmd_serve as service_cmd_serve  # pylint: disable=import-outside-toplevel

    return int(service_cmd_serve(args))


def cmd_replay(args: argparse.Namespace) -> int:
    from zenodex_oracle_devnet_service import cmd_replay as service_cmd_replay  # pylint: disable=import-outside-toplevel

    return int(service_cmd_replay(args))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_cmd = subparsers.add_parser("list", help="list available Oracle verifier surfaces")
    list_cmd.set_defaults(func=cmd_list)

    doctor = subparsers.add_parser("doctor", help="check local Oracle CLI tool availability")
    doctor.set_defaults(func=cmd_doctor)

    sample = subparsers.add_parser("sample", help="emit a sample artifact for a verifier surface")
    sample.add_argument("surface", help="surface name, for example feed or signed-report")
    sample.add_argument("args", nargs=argparse.REMAINDER, help="arguments forwarded to the surface sample command")
    sample.set_defaults(func=cmd_sample)

    verify = subparsers.add_parser("verify", help="verify an artifact for a verifier surface")
    verify.add_argument("surface", help="surface name, for example feed or signed-report")
    verify.add_argument("args", nargs=argparse.REMAINDER, help="arguments forwarded to the surface verify command")
    verify.set_defaults(func=cmd_verify)

    chaos = subparsers.add_parser("chaos", help="run a chaos replay for one surface or all surfaces")
    chaos.add_argument("surface", help="surface name or all")
    chaos.add_argument("args", nargs=argparse.REMAINDER, help="arguments forwarded to the chaos command")
    chaos.set_defaults(func=cmd_chaos)

    register_feed = subparsers.add_parser("register-feed", help="verify and store a feed registry locally")
    register_feed.add_argument("registry", help="path to a feed registry JSON file")
    register_feed.add_argument("--store", required=True, help="local Oracle store directory")
    register_feed.add_argument("--receipt-output", help="optional output path for the registration receipt")
    register_feed.set_defaults(func=cmd_register_feed)

    submit_report = subparsers.add_parser("submit-report", help="verify and store a signed report submission locally")
    submit_report.add_argument("submission", help="path to a signed report submission JSON file")
    submit_report.add_argument("--store", required=True, help="local Oracle store directory")
    submit_report.add_argument("--receipt-output", help="optional output path for the submission receipt")
    submit_report.set_defaults(func=cmd_submit_report)

    dry_run = subparsers.add_parser("dry-run", help="run a complete local Oracle MVP happy path")
    dry_run.add_argument("--workdir", help="optional directory where generated artifacts are kept")
    dry_run.add_argument("--output", help="optional output path for the dry-run receipt")
    dry_run.set_defaults(func=cmd_dry_run)

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
