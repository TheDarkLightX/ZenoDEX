"""Index and summarize release-candidate receipt directories."""

from __future__ import annotations

import csv
import json
import io
from pathlib import Path
from typing import Any


def _campaign_timestamp(bundle_dir: Path) -> str | None:
    name = bundle_dir.name.strip()
    if "_" not in name:
        return None
    ts, _rest = name.split("_", 1)
    return ts or None


def _run_id(bundle_dir: Path) -> str:
    name = bundle_dir.name.strip()
    if "_" not in name:
        return name
    _ts, rest = name.split("_", 1)
    return rest or name


def _load_candidate_report(path: Path) -> dict[str, Any] | None:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(data, dict):
        return None
    if data.get("schema") != "zenodex/rc1-candidate-report/v1":
        return None
    return data


def _row_from_report(bundle_dir: Path, report_path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    readiness = payload.get("readiness", {})
    unmet = payload.get("unmet_criteria", []) or readiness.get("unmet_criteria", [])
    if not isinstance(unmet, list):
        unmet = []
    return {
        "run_id": _run_id(bundle_dir),
        "campaign_timestamp_utc": _campaign_timestamp(bundle_dir),
        "bundle_dir": str(bundle_dir),
        "report_path": str(report_path),
        "historical_release_label": str(payload.get("historical_release_label", "RC1")),
        "active_candidate_label": str(payload.get("active_candidate_label", "RC2")),
        "overall_ok": bool(payload.get("overall_ok")),
        "blocked_before_run": bool(payload.get("blocked_before_run")),
        "dirty_count": int(readiness.get("dirty_count", payload.get("dirty_count", 0)) or 0),
        "branch": readiness.get("assurance", {}).get("branch") if isinstance(readiness, dict) else None,
        "unmet_criteria": [str(item) for item in unmet],
    }


def load_candidate_rows(
    campaign_root: Path,
    *,
    ready_state: str | None = None,
    run_id_prefix: str | None = None,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not campaign_root.exists():
        return rows
    for report_path in sorted(campaign_root.glob("*/candidate_report.json")):
        payload = _load_candidate_report(report_path)
        if payload is None:
            continue
        row = _row_from_report(report_path.parent, report_path, payload)
        if ready_state == "ready" and not row["overall_ok"]:
            continue
        if ready_state == "blocked" and row["overall_ok"]:
            continue
        if run_id_prefix and not str(row["run_id"]).startswith(run_id_prefix):
            continue
        rows.append(row)
    rows.sort(key=lambda item: (str(item["campaign_timestamp_utc"] or ""), str(item["run_id"])), reverse=True)
    return rows


def build_candidate_index_payload(
    campaign_root: Path,
    *,
    ready_state: str | None = None,
    run_id_prefix: str | None = None,
) -> dict[str, Any]:
    rows = load_candidate_rows(
        campaign_root,
        ready_state=ready_state,
        run_id_prefix=run_id_prefix,
    )
    ready_count = sum(1 for row in rows if bool(row["overall_ok"]))
    blocked_count = len(rows) - ready_count
    unmet_counts: dict[str, int] = {}
    for row in rows:
        for item in row["unmet_criteria"]:
            unmet_counts[item] = unmet_counts.get(item, 0) + 1
    active_candidate_label = str(rows[0]["active_candidate_label"]) if rows else "RC2"
    historical_release_label = str(rows[0]["historical_release_label"]) if rows else "RC1"
    return {
        "schema": "zenodex/rc1-candidate-index/v1",
        "historical_release_label": historical_release_label,
        "active_candidate_label": active_candidate_label,
        "campaign_root": str(campaign_root),
        "filters": {
            "ready_state": ready_state,
            "run_id_prefix": run_id_prefix,
        },
        "candidate_count": len(rows),
        "ready_count": ready_count,
        "blocked_count": blocked_count,
        "unmet_criteria_counts": dict(sorted(unmet_counts.items())),
        "candidates": rows,
    }


def render_candidate_index_text(payload: dict[str, Any]) -> str:
    active_label = str(payload.get("active_candidate_label", "RC2"))
    historical_label = str(payload.get("historical_release_label", "RC1"))
    lines = [
        f"ZenoDex {active_label} Candidate Index",
        f"historical baseline: {historical_label}",
        f"campaign_root: {payload['campaign_root']}",
        f"candidate_count: {payload['candidate_count']}",
        f"ready_count: {payload['ready_count']}",
        f"blocked_count: {payload['blocked_count']}",
        "",
        "Candidates",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"- {row['campaign_timestamp_utc'] or 'unknown'} {row['run_id']} "
            f"[{'READY' if row['overall_ok'] else 'BLOCKED'}] "
            f"dirty={row['dirty_count']} unmet={','.join(row['unmet_criteria']) or 'none'}"
        )
    if payload["unmet_criteria_counts"]:
        lines.extend(["", "Unmet criteria counts"])
        for key, value in payload["unmet_criteria_counts"].items():
            lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def render_candidate_index_markdown(payload: dict[str, Any]) -> str:
    active_label = str(payload.get("active_candidate_label", "RC2"))
    historical_label = str(payload.get("historical_release_label", "RC1"))
    lines = [
        f"# ZenoDex {active_label} Candidate Index",
        "",
        f"- historical baseline: `{historical_label}`",
        f"- campaign_root: `{payload['campaign_root']}`",
        f"- candidate_count: `{payload['candidate_count']}`",
        f"- ready_count: `{payload['ready_count']}`",
        f"- blocked_count: `{payload['blocked_count']}`",
        "",
        "## Candidates",
        "",
        "| Timestamp | Run ID | Status | Dirty Count | Unmet Criteria |",
        "| --- | --- | --- | ---: | --- |",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"| {row['campaign_timestamp_utc'] or 'unknown'} | {row['run_id']} | "
            f"{'READY' if row['overall_ok'] else 'BLOCKED'} | {row['dirty_count']} | "
            f"{', '.join(row['unmet_criteria']) or 'none'} |"
        )
    if payload["unmet_criteria_counts"]:
        lines.extend(["", "## Unmet Criteria Counts", ""])
        for key, value in payload["unmet_criteria_counts"].items():
            lines.append(f"- `{key}`: `{value}`")
    return "\n".join(lines) + "\n"


def render_candidate_index_csv(payload: dict[str, Any]) -> str:
    buffer = io.StringIO()
    writer = csv.DictWriter(
        buffer,
        fieldnames=[
            "campaign_timestamp_utc",
            "run_id",
            "status",
            "dirty_count",
            "branch",
            "unmet_criteria",
            "bundle_dir",
            "report_path",
        ],
    )
    writer.writeheader()
    for row in payload["candidates"]:
        writer.writerow(
            {
                "campaign_timestamp_utc": row["campaign_timestamp_utc"] or "",
                "run_id": row["run_id"],
                "status": "READY" if row["overall_ok"] else "BLOCKED",
                "dirty_count": row["dirty_count"],
                "branch": row["branch"] or "",
                "unmet_criteria": ",".join(row["unmet_criteria"]),
                "bundle_dir": row["bundle_dir"],
                "report_path": row["report_path"],
            }
        )
    return buffer.getvalue()
