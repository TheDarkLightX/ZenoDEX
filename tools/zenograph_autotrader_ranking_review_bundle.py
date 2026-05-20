#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenograph_ranking_review_summary import (  # noqa: E402
    render_zenograph_ranking_review_markdown,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a signed replay ranking review bundle: baseline report, gate report, "
            "and markdown operator summary."
        ),
        epilog=(
            "Advanced experimental automation review tool. "
            "This only produces non-executing review artifacts."
        ),
    )
    parser.add_argument("--out-dir", type=Path, default=None)
    parser.add_argument(
        "--campaign-root",
        type=Path,
        default=ROOT / "internal" / "zenograph_shadow",
    )
    parser.add_argument("--run-id", type=str, default=None)
    parser.add_argument("--timestamp-utc", type=str, default=None)
    parser.add_argument("--baseline-report-out", type=Path, default=None)
    parser.add_argument("--baseline-log-out", type=Path, default=None)
    parser.add_argument("--gate-report-out", type=Path, default=None)
    parser.add_argument("--summary-out", type=Path, default=None)
    parser.add_argument("--instructions-out", type=Path, default=None)
    parser.add_argument("--manifest-out", type=Path, default=None)
    parser.add_argument("--operator-release-enable", action="store_true")
    args = parser.parse_args(argv)

    (
        resolved_out_dir,
        baseline_report_out,
        baseline_log_out,
        gate_report_out,
        summary_out,
        instructions_out,
        manifest_out,
    ) = _resolve_output_paths(
        out_dir=args.out_dir,
        campaign_root=args.campaign_root,
        run_id=args.run_id,
        timestamp_utc=args.timestamp_utc,
        baseline_report_out=args.baseline_report_out,
        baseline_log_out=args.baseline_log_out,
        gate_report_out=args.gate_report_out,
        summary_out=args.summary_out,
        instructions_out=args.instructions_out,
        manifest_out=args.manifest_out,
    )

    baseline_cmd = [
        sys.executable,
        str(ROOT / "tools" / "zenograph_autotrader_shadow_compare_baseline.py"),
        "--report-out",
        str(baseline_report_out),
    ]
    if baseline_log_out is not None:
        baseline_cmd.extend(["--log-out", str(baseline_log_out)])
    subprocess.run(
        baseline_cmd,
        check=True,
        capture_output=True,
        text=True,
        cwd=str(ROOT),
    )

    gate_cmd = [
        sys.executable,
        str(ROOT / "tools" / "zenograph_autotrader_ranking_promotion_gate.py"),
        "--report-file",
        str(baseline_report_out),
        "--out",
        str(gate_report_out),
    ]
    if args.operator_release_enable:
        gate_cmd.append("--operator-release-enable")
    subprocess.run(
        gate_cmd,
        check=True,
        capture_output=True,
        text=True,
        cwd=str(ROOT),
    )

    baseline_report = json.loads(baseline_report_out.read_text(encoding="utf-8"))
    gate_report = json.loads(gate_report_out.read_text(encoding="utf-8"))
    summary = render_zenograph_ranking_review_markdown(baseline_report, gate_report)
    summary_out.parent.mkdir(parents=True, exist_ok=True)
    summary_out.write_text(summary, encoding="utf-8")
    instructions_out.parent.mkdir(parents=True, exist_ok=True)
    instructions_out.write_text(
        _render_bundle_instructions(
            bundle_dir=resolved_out_dir,
            manifest_out=manifest_out,
            operator_release_enabled=bool(args.operator_release_enable),
        ),
        encoding="utf-8",
    )
    generated_at_utc = datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")

    payload = {
        "schema": "zenodex/zenograph-autotrader-ranking-review-bundle/v1",
        "bundle_dir": str(resolved_out_dir),
        "baseline_report_path": str(baseline_report_out),
        "baseline_log_path": None if baseline_log_out is None else str(baseline_log_out),
        "gate_report_path": str(gate_report_out),
        "summary_path": str(summary_out),
        "instructions_path": str(instructions_out),
        "manifest_path": None if manifest_out is None else str(manifest_out),
        "ranking_influence_allowed": gate_report["gate"]["ranking_influence_allowed"],
        "block_reason": gate_report["gate"]["block_reason"],
        "operator_release_enabled": bool(args.operator_release_enable),
        "run_id": resolved_out_dir.name,
        "metadata": {
            "generated_at_utc": generated_at_utc,
            "repo_root": str(ROOT),
            "git_commit": _git_stdout(["rev-parse", "HEAD"]),
            "git_commit_short": _git_stdout(["rev-parse", "--short", "HEAD"]),
            "git_dirty": _git_is_dirty(),
            "python_version": sys.version.split()[0],
            "python_executable": sys.executable,
            "platform": platform.platform(),
            "tool_versions": {
                "bundle_cli": "zenograph_autotrader_ranking_review_bundle/v1",
                "baseline_cli": "zenograph_autotrader_shadow_compare_baseline/v1",
                "gate_cli": "zenograph_autotrader_ranking_promotion_gate/v1",
            "summary_renderer": "zenograph_ranking_review_summary/v1",
                "bundle_verify_cli": "zenograph_autotrader_ranking_review_bundle_verify/v1",
            },
        },
        "artifacts": _artifact_manifest(
            baseline_report_out=baseline_report_out,
            baseline_log_out=baseline_log_out,
            gate_report_out=gate_report_out,
            summary_out=summary_out,
            instructions_out=instructions_out,
        ),
    }
    if manifest_out is not None:
        manifest_out.parent.mkdir(parents=True, exist_ok=True)
        manifest_out.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    sys.stdout.write(json.dumps(payload, sort_keys=True) + "\n")
    return 0


def _resolve_output_paths(
    *,
    out_dir: Path | None,
    campaign_root: Path,
    run_id: str | None,
    timestamp_utc: str | None,
    baseline_report_out: Path | None,
    baseline_log_out: Path | None,
    gate_report_out: Path | None,
    summary_out: Path | None,
    instructions_out: Path | None,
    manifest_out: Path | None,
) -> tuple[Path, Path, Path | None, Path, Path, Path, Path | None]:
    if out_dir is None and (
        baseline_report_out is None
        and baseline_log_out is None
        and gate_report_out is None
        and summary_out is None
        and manifest_out is None
    ):
        timestamp = (
            _normalize_timestamp_utc(timestamp_utc)
            if timestamp_utc is not None
            else datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
        )
        suffix = _normalize_run_id(run_id) if run_id is not None else "auto"
        out_dir = campaign_root / f"{timestamp}_{suffix}"

    if out_dir is None:
        if baseline_report_out is None or gate_report_out is None or summary_out is None:
            raise ValueError(
                "either --out-dir, no explicit output flags, or all of --baseline-report-out, --gate-report-out, --summary-out is required"
            )
        base_dir = baseline_report_out.parent
        return (
            base_dir,
            baseline_report_out,
            baseline_log_out,
            gate_report_out,
            summary_out,
            instructions_out,
            manifest_out,
        )

    return (
        out_dir,
        baseline_report_out or (out_dir / "baseline_report.json"),
        baseline_log_out or (out_dir / "baseline_log.jsonl"),
        gate_report_out or (out_dir / "gate_report.json"),
        summary_out or (out_dir / "ranking_review.md"),
        instructions_out or (out_dir / "README.md"),
        manifest_out or (out_dir / "manifest.json"),
    )


def _normalize_timestamp_utc(value: str) -> str:
    parsed = datetime.strptime(value, "%Y%m%dT%H%M%SZ")
    return parsed.strftime("%Y%m%dT%H%M%SZ")


def _normalize_run_id(value: str) -> str:
    cleaned = "".join(ch if ch.isalnum() or ch in ("-", "_") else "_" for ch in value.strip())
    cleaned = cleaned.strip("_")
    if not cleaned:
        raise ValueError("run-id must contain at least one alphanumeric, '-' or '_' character")
    return cleaned


def _git_stdout(args: list[str]) -> str | None:
    try:
        completed = subprocess.run(
            ["git", *args],
            check=True,
            capture_output=True,
            text=True,
            cwd=str(ROOT),
        )
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None
    text = completed.stdout.strip()
    return text or None


def _git_is_dirty() -> bool | None:
    try:
        completed = subprocess.run(
            ["git", "status", "--porcelain"],
            check=True,
            capture_output=True,
            text=True,
            cwd=str(ROOT),
        )
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None
    return bool(completed.stdout.strip())


def _artifact_manifest(
    *,
    baseline_report_out: Path,
    baseline_log_out: Path | None,
    gate_report_out: Path,
    summary_out: Path,
    instructions_out: Path,
) -> dict[str, object]:
    artifacts = {
        "baseline_report": _artifact_entry(baseline_report_out),
        "gate_report": _artifact_entry(gate_report_out),
        "summary": _artifact_entry(summary_out),
        "instructions": _artifact_entry(instructions_out),
    }
    if baseline_log_out is not None:
        artifacts["baseline_log"] = _artifact_entry(baseline_log_out)
    return artifacts


def _artifact_entry(path: Path) -> dict[str, object]:
    data = path.read_bytes()
    return {
        "path": str(path),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _render_bundle_instructions(
    *,
    bundle_dir: Path,
    manifest_out: Path | None,
    operator_release_enabled: bool,
) -> str:
    manifest_path = manifest_out or (bundle_dir / "manifest.json")
    build_cmd = (
        f"python3 tools/zenograph_autotrader_ranking_review_bundle.py --out-dir {bundle_dir}"
        + (" --operator-release-enable" if operator_release_enabled else "")
    )
    verify_cmd = (
        "python3 tools/zenograph_autotrader_ranking_review_bundle_verify.py "
        f"--manifest-file {manifest_path} --pretty"
    )
    return (
        "# ZenoGraph Ranking Review Bundle\n\n"
        "Advanced experimental automation review bundle. At your own risk.\n\n"
        "This bundle is non-executing. It does not change controller execution.\n\n"
        "## Build Command\n\n"
        f"```bash\n{build_cmd}\n```\n\n"
        "## Verify Command\n\n"
        f"```bash\n{verify_cmd}\n```\n\n"
        "## Artifacts\n\n"
        "- `baseline_report.json`\n"
        "- `baseline_log.jsonl`\n"
        "- `gate_report.json`\n"
        "- `ranking_review.md`\n"
        "- `manifest.json`\n\n"
        "Use the verifier after copying or archiving this bundle.\n"
    )


if __name__ == "__main__":
    raise SystemExit(main())
