from __future__ import annotations

import csv
import json
from datetime import datetime
from io import StringIO
from pathlib import Path
from typing import Mapping


ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA = (
    "zenodex/zenograph-autotrader-ranking-review-campaign-index/v1"
)


def build_zenograph_ranking_review_campaign_index(
    *,
    campaign_root: Path,
    limit: int | None = None,
    gate_status: str | None = None,
    run_id_prefix: str | None = None,
    git_prefix: str | None = None,
    dirty_state: str | None = None,
    generated_since_utc: str | None = None,
    generated_until_utc: str | None = None,
) -> dict[str, object]:
    if not isinstance(campaign_root, Path):
        raise TypeError("campaign_root must be a Path")
    if limit is not None and (not isinstance(limit, int) or limit < 1):
        raise ValueError("limit must be a positive integer when present")
    if gate_status is not None and gate_status not in {"allowed", "blocked"}:
        raise ValueError("gate_status must be 'allowed' or 'blocked' when present")
    if run_id_prefix is not None and not isinstance(run_id_prefix, str):
        raise TypeError("run_id_prefix must be a string when present")
    if git_prefix is not None and not isinstance(git_prefix, str):
        raise TypeError("git_prefix must be a string when present")
    if dirty_state is not None and dirty_state not in {"clean", "dirty"}:
        raise ValueError("dirty_state must be 'clean' or 'dirty' when present")
    if generated_since_utc is not None:
        _parse_generated_at_utc(generated_since_utc)
    if generated_until_utc is not None:
        _parse_generated_at_utc(generated_until_utc)

    entries: list[dict[str, object]] = []
    if campaign_root.exists():
        for child in campaign_root.iterdir():
            if not child.is_dir():
                continue
            manifest_path = child / "manifest.json"
            if not manifest_path.exists():
                continue
            try:
                payload = json.loads(manifest_path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                continue
            if not isinstance(payload, Mapping):
                continue
            if payload.get("schema") != "zenodex/zenograph-autotrader-ranking-review-bundle/v1":
                continue
            metadata = payload.get("metadata")
            if metadata is not None and not isinstance(metadata, Mapping):
                continue
            entries.append(
                {
                    "run_id": payload.get("run_id"),
                    "bundle_dir": str(child),
                    "manifest_path": str(manifest_path),
                    "baseline_report_path": payload.get("baseline_report_path"),
                    "gate_report_path": payload.get("gate_report_path"),
                    "summary_path": payload.get("summary_path"),
                    "instructions_path": payload.get("instructions_path"),
                    "campaign_timestamp_utc": _extract_campaign_timestamp_utc(child.name),
                    "generated_at_utc": None if metadata is None else metadata.get("generated_at_utc"),
                    "git_commit_short": None if metadata is None else metadata.get("git_commit_short"),
                    "git_dirty": None if metadata is None else metadata.get("git_dirty"),
                    "ranking_influence_allowed": payload.get("ranking_influence_allowed"),
                    "block_reason": payload.get("block_reason"),
                }
            )

    if gate_status is not None:
        expect_allowed = gate_status == "allowed"
        entries = [
            item
            for item in entries
            if isinstance(item.get("ranking_influence_allowed"), bool)
            and item["ranking_influence_allowed"] is expect_allowed
        ]
    if run_id_prefix is not None:
        entries = [
            item
            for item in entries
            if isinstance(item.get("run_id"), str)
            and str(item["run_id"]).startswith(run_id_prefix)
        ]
    if git_prefix is not None:
        entries = [
            item
            for item in entries
            if isinstance(item.get("git_commit_short"), str)
            and str(item["git_commit_short"]).startswith(git_prefix)
        ]
    if dirty_state is not None:
        expect_dirty = dirty_state == "dirty"
        entries = [
            item
            for item in entries
            if isinstance(item.get("git_dirty"), bool)
            and item["git_dirty"] is expect_dirty
        ]
    if generated_since_utc is not None:
        entries = [
            item
            for item in entries
            if (timestamp := _entry_timestamp_for_filter(item)) is not None
            and timestamp >= generated_since_utc
        ]
    if generated_until_utc is not None:
        entries = [
            item
            for item in entries
            if (timestamp := _entry_timestamp_for_filter(item)) is not None
            and timestamp <= generated_until_utc
        ]

    entries.sort(
        key=lambda item: (
            str(item.get("campaign_timestamp_utc") or ""),
            str(item.get("generated_at_utc") or ""),
            str(item.get("run_id") or ""),
        ),
        reverse=True,
    )
    if limit is not None:
        entries = entries[:limit]

    block_reason_counts: dict[str, int] = {}
    gate_status_counts: dict[str, int] = {}
    campaign_day_counts: dict[str, int] = {}
    campaign_day_gate_status_counts: dict[str, dict[str, int]] = {}
    block_reason_spans: dict[str, dict[str, object]] = {}
    for item in entries:
        gate_label = _render_gate(item.get("ranking_influence_allowed"))
        gate_status_counts[gate_label] = gate_status_counts.get(gate_label, 0) + 1
        block_reason = _optional_str(item.get("block_reason")) or "none"
        block_reason_counts[block_reason] = block_reason_counts.get(block_reason, 0) + 1
        campaign_day = _campaign_day_label(item)
        campaign_day_counts[campaign_day] = campaign_day_counts.get(campaign_day, 0) + 1
        day_gate_counts = campaign_day_gate_status_counts.setdefault(campaign_day, {})
        day_gate_counts[gate_label] = day_gate_counts.get(gate_label, 0) + 1
        span = block_reason_spans.setdefault(
            block_reason,
            {
                "count": 0,
                "first_campaign_day": campaign_day,
                "last_campaign_day": campaign_day,
            },
        )
        span["count"] = _require_int(span["count"], name=f"block_reason_spans.{block_reason}.count") + 1
        first_day = _require_str(
            span["first_campaign_day"], name=f"block_reason_spans.{block_reason}.first_campaign_day"
        )
        last_day = _require_str(
            span["last_campaign_day"], name=f"block_reason_spans.{block_reason}.last_campaign_day"
        )
        span["first_campaign_day"] = min(first_day, campaign_day)
        span["last_campaign_day"] = max(last_day, campaign_day)

    latest_gate_status, latest_gate_status_streak_length = _compute_streak(
        entries,
        label_fn=lambda item: _render_gate(item.get("ranking_influence_allowed")),
    )
    latest_block_reason, latest_block_reason_streak_length = _compute_streak(
        entries,
        label_fn=lambda item: _optional_str(item.get("block_reason")) or "none",
    )

    return {
        "schema": ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA,
        "campaign_root": str(campaign_root),
        "filters": {
            "gate_status": gate_status,
            "run_id_prefix": run_id_prefix,
            "git_prefix": git_prefix,
            "dirty_state": dirty_state,
            "generated_since_utc": generated_since_utc,
            "generated_until_utc": generated_until_utc,
        },
        "bundle_count": len(entries),
        "gate_status_counts": dict(sorted(gate_status_counts.items())),
        "block_reason_counts": dict(sorted(block_reason_counts.items())),
        "campaign_day_counts": dict(sorted(campaign_day_counts.items())),
        "campaign_day_gate_status_counts": {
            key: dict(sorted(value.items()))
            for key, value in sorted(campaign_day_gate_status_counts.items())
        },
        "block_reason_spans": {
            key: {
                "count": _require_int(value["count"], name=f"block_reason_spans.{key}.count"),
                "first_campaign_day": _require_str(
                    value["first_campaign_day"],
                    name=f"block_reason_spans.{key}.first_campaign_day",
                ),
                "last_campaign_day": _require_str(
                    value["last_campaign_day"],
                    name=f"block_reason_spans.{key}.last_campaign_day",
                ),
            }
            for key, value in sorted(block_reason_spans.items())
        },
        "latest_gate_status": latest_gate_status,
        "latest_gate_status_streak_length": latest_gate_status_streak_length,
        "latest_block_reason": latest_block_reason,
        "latest_block_reason_streak_length": latest_block_reason_streak_length,
        "entries": entries,
    }


def render_zenograph_ranking_review_campaign_index_markdown(
    payload: Mapping[str, object],
) -> str:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA:
        raise ValueError("unsupported campaign index schema")

    campaign_root = _require_str(payload.get("campaign_root"), name="campaign_root")
    bundle_count = _require_int(payload.get("bundle_count"), name="bundle_count")
    filters = payload.get("filters")
    if not isinstance(filters, Mapping):
        raise TypeError("filters must be a mapping")
    entries = payload.get("entries")
    if not isinstance(entries, list):
        raise TypeError("entries must be a list")
    gate_status_counts = payload.get("gate_status_counts")
    if not isinstance(gate_status_counts, Mapping):
        raise TypeError("gate_status_counts must be a mapping")
    block_reason_counts = payload.get("block_reason_counts")
    if not isinstance(block_reason_counts, Mapping):
        raise TypeError("block_reason_counts must be a mapping")
    campaign_day_counts = payload.get("campaign_day_counts")
    if not isinstance(campaign_day_counts, Mapping):
        raise TypeError("campaign_day_counts must be a mapping")
    campaign_day_gate_status_counts = payload.get("campaign_day_gate_status_counts")
    if not isinstance(campaign_day_gate_status_counts, Mapping):
        raise TypeError("campaign_day_gate_status_counts must be a mapping")
    block_reason_spans = payload.get("block_reason_spans")
    if not isinstance(block_reason_spans, Mapping):
        raise TypeError("block_reason_spans must be a mapping")
    latest_gate_status = _require_str(payload.get("latest_gate_status"), name="latest_gate_status")
    latest_gate_status_streak_length = _require_int(
        payload.get("latest_gate_status_streak_length"),
        name="latest_gate_status_streak_length",
    )
    latest_block_reason = _require_str(payload.get("latest_block_reason"), name="latest_block_reason")
    latest_block_reason_streak_length = _require_int(
        payload.get("latest_block_reason_streak_length"),
        name="latest_block_reason_streak_length",
    )

    lines = [
        "# ZenoGraph Ranking Review Campaign Index",
        "",
        f"- Campaign root: `{campaign_root}`",
        f"- Bundle count: `{bundle_count}`",
        "",
    ]
    gate_status_filter = _optional_str(filters.get("gate_status"))
    run_id_prefix_filter = _optional_str(filters.get("run_id_prefix"))
    git_prefix_filter = _optional_str(filters.get("git_prefix"))
    dirty_state_filter = _optional_str(filters.get("dirty_state"))
    generated_since_filter = _optional_str(filters.get("generated_since_utc"))
    generated_until_filter = _optional_str(filters.get("generated_until_utc"))
    if (
        gate_status_filter is not None
        or run_id_prefix_filter is not None
        or git_prefix_filter is not None
        or dirty_state_filter is not None
        or generated_since_filter is not None
        or generated_until_filter is not None
    ):
        lines.append("## Filters")
        lines.append("")
        lines.append(f"- Gate status: `{gate_status_filter or 'none'}`")
        lines.append(f"- Run ID prefix: `{run_id_prefix_filter or 'none'}`")
        lines.append(f"- Git prefix: `{git_prefix_filter or 'none'}`")
        lines.append(f"- Dirty state: `{dirty_state_filter or 'none'}`")
        lines.append(f"- Generated since UTC: `{generated_since_filter or 'none'}`")
        lines.append(f"- Generated until UTC: `{generated_until_filter or 'none'}`")
        lines.append("")
    if not entries:
        lines.append("No bundle manifests found.")
        return "\n".join(lines) + "\n"

    lines.append("## Summary")
    lines.append("")
    lines.append("- Gate status counts:")
    for key, value in sorted(gate_status_counts.items()):
        lines.append(f"  - `{key}`: `{_require_int(value, name=f'gate_status_counts.{key}')}`")
    lines.append("- Block reason counts:")
    for key, value in sorted(block_reason_counts.items()):
        lines.append(f"  - `{key}`: `{_require_int(value, name=f'block_reason_counts.{key}')}`")
    lines.append("- Campaign day counts:")
    for key, value in sorted(campaign_day_counts.items()):
        lines.append(f"  - `{key}`: `{_require_int(value, name=f'campaign_day_counts.{key}')}`")
    lines.append(
        f"- Latest gate status streak: `{latest_gate_status}` x `{latest_gate_status_streak_length}`"
    )
    lines.append(
        f"- Latest block reason streak: `{latest_block_reason}` x `{latest_block_reason_streak_length}`"
    )
    lines.append("")
    lines.append("## Campaign Day Trends")
    lines.append("")
    lines.append("| Campaign Day | Bundle Count | Gate Status Counts |")
    lines.append("| --- | --- | --- |")
    for key, value in sorted(campaign_day_counts.items()):
        gate_counts = campaign_day_gate_status_counts.get(key)
        if not isinstance(gate_counts, Mapping):
            raise TypeError("campaign_day_gate_status_counts entries must be mappings")
        gate_counts_text = ", ".join(
            f"{gate_key}={_require_int(gate_value, name=f'campaign_day_gate_status_counts.{key}.{gate_key}')}"
            for gate_key, gate_value in sorted(gate_counts.items())
        )
        lines.append(
            f"| `{key}` | `{_require_int(value, name=f'campaign_day_counts.{key}')}` | `{gate_counts_text or 'none'}` |"
        )
    lines.append("")
    lines.append("## Block Reason Spans")
    lines.append("")
    lines.append("| Block Reason | Count | First Day | Last Day |")
    lines.append("| --- | --- | --- | --- |")
    for key, value in sorted(block_reason_spans.items()):
        if not isinstance(value, Mapping):
            raise TypeError("block_reason_spans entries must be mappings")
        lines.append(
            "| `{}` | `{}` | `{}` | `{}` |".format(
                key,
                _require_int(value.get("count"), name=f"block_reason_spans.{key}.count"),
                _require_str(
                    value.get("first_campaign_day"),
                    name=f"block_reason_spans.{key}.first_campaign_day",
                ),
                _require_str(
                    value.get("last_campaign_day"),
                    name=f"block_reason_spans.{key}.last_campaign_day",
                ),
            )
        )
    lines.append("")

    lines.append("| Run ID | Generated UTC | Gate | Block Reason | Git | Dirty |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    for item in entries:
        if not isinstance(item, Mapping):
            raise TypeError("entries must contain objects")
        run_id = _optional_str(item.get("run_id")) or "unknown"
        generated_at_utc = _optional_str(item.get("generated_at_utc")) or "unknown"
        gate = _render_gate(item.get("ranking_influence_allowed"))
        block_reason = _optional_str(item.get("block_reason")) or "none"
        git_commit_short = _optional_str(item.get("git_commit_short")) or "unknown"
        git_dirty = _render_dirty(item.get("git_dirty"))
        lines.append(
            f"| `{run_id}` | `{generated_at_utc}` | `{gate}` | `{block_reason}` | `{git_commit_short}` | `{git_dirty}` |"
        )
    return "\n".join(lines) + "\n"


def render_zenograph_ranking_review_campaign_index_csv(
    payload: Mapping[str, object],
) -> str:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA:
        raise ValueError("unsupported campaign index schema")
    entries = payload.get("entries")
    if not isinstance(entries, list):
        raise TypeError("entries must be a list")

    output = StringIO()
    writer = csv.writer(output)
    writer.writerow(
        [
            "run_id",
            "campaign_timestamp_utc",
            "generated_at_utc",
            "ranking_influence_allowed",
            "gate_status",
            "block_reason",
            "git_commit_short",
            "git_dirty",
            "bundle_dir",
            "manifest_path",
        ]
    )
    for item in entries:
        if not isinstance(item, Mapping):
            raise TypeError("entries must contain objects")
        writer.writerow(
            [
                _optional_str(item.get("run_id")) or "",
                _optional_str(item.get("campaign_timestamp_utc")) or "",
                _optional_str(item.get("generated_at_utc")) or "",
                _render_bool(item.get("ranking_influence_allowed")),
                _render_gate(item.get("ranking_influence_allowed")),
                _optional_str(item.get("block_reason")) or "",
                _optional_str(item.get("git_commit_short")) or "",
                _render_dirty(item.get("git_dirty")),
                _optional_str(item.get("bundle_dir")) or "",
                _optional_str(item.get("manifest_path")) or "",
            ]
        )
    return output.getvalue()


def render_zenograph_ranking_review_campaign_index_daily_csv(
    payload: Mapping[str, object],
) -> str:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA:
        raise ValueError("unsupported campaign index schema")
    campaign_day_counts = payload.get("campaign_day_counts")
    if not isinstance(campaign_day_counts, Mapping):
        raise TypeError("campaign_day_counts must be a mapping")
    campaign_day_gate_status_counts = payload.get("campaign_day_gate_status_counts")
    if not isinstance(campaign_day_gate_status_counts, Mapping):
        raise TypeError("campaign_day_gate_status_counts must be a mapping")

    output = StringIO()
    writer = csv.writer(output)
    writer.writerow(
        [
            "campaign_day",
            "bundle_count",
            "allowed_count",
            "blocked_count",
            "unknown_count",
            "gate_status_counts",
        ]
    )
    for campaign_day, bundle_count_obj in sorted(campaign_day_counts.items()):
        if not isinstance(campaign_day, str):
            raise TypeError("campaign_day_counts keys must be strings")
        bundle_count = _require_int(bundle_count_obj, name=f"campaign_day_counts.{campaign_day}")
        gate_counts_obj = campaign_day_gate_status_counts.get(campaign_day, {})
        if not isinstance(gate_counts_obj, Mapping):
            raise TypeError("campaign_day_gate_status_counts entries must be mappings")
        allowed_count = _require_int(gate_counts_obj.get("allowed", 0), name=f"{campaign_day}.allowed_count")
        blocked_count = _require_int(gate_counts_obj.get("blocked", 0), name=f"{campaign_day}.blocked_count")
        unknown_count = _require_int(gate_counts_obj.get("unknown", 0), name=f"{campaign_day}.unknown_count")
        gate_counts_text = ";".join(
            f"{gate_key}={_require_int(gate_value, name=f'{campaign_day}.{gate_key}')}"
            for gate_key, gate_value in sorted(gate_counts_obj.items())
        )
        writer.writerow(
            [
                campaign_day,
                bundle_count,
                allowed_count,
                blocked_count,
                unknown_count,
                gate_counts_text,
            ]
        )
    return output.getvalue()


def render_zenograph_ranking_review_campaign_index_daily_block_reason_csv(
    payload: Mapping[str, object],
) -> str:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA:
        raise ValueError("unsupported campaign index schema")
    entries = payload.get("entries")
    if not isinstance(entries, list):
        raise TypeError("entries must be a list")

    counts: dict[tuple[str, str], int] = {}
    for item in entries:
        if not isinstance(item, Mapping):
            raise TypeError("entries must contain objects")
        campaign_day = _campaign_day_label(item)
        block_reason = _optional_str(item.get("block_reason")) or "none"
        key = (campaign_day, block_reason)
        counts[key] = counts.get(key, 0) + 1

    output = StringIO()
    writer = csv.writer(output)
    writer.writerow(["campaign_day", "block_reason", "count"])
    for (campaign_day, block_reason), count in sorted(counts.items()):
        writer.writerow([campaign_day, block_reason, count])
    return output.getvalue()


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return value


def _require_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return value


def _optional_str(value: object) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str):
        raise TypeError("expected a string or null")
    return value


def _render_gate(value: object) -> str:
    if isinstance(value, bool):
        return "allowed" if value else "blocked"
    return "unknown"


def _render_bool(value: object) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    return ""


def _render_dirty(value: object) -> str:
    if isinstance(value, bool):
        return "dirty" if value else "clean"
    return "unknown"


def _entry_timestamp_for_filter(item: Mapping[str, object]) -> str | None:
    campaign_timestamp = item.get("campaign_timestamp_utc")
    if isinstance(campaign_timestamp, str):
        return campaign_timestamp
    generated_at_utc = item.get("generated_at_utc")
    if isinstance(generated_at_utc, str):
        return generated_at_utc
    return None


def _extract_campaign_timestamp_utc(bundle_dir_name: str) -> str | None:
    if not isinstance(bundle_dir_name, str):
        raise TypeError("bundle_dir_name must be a string")
    prefix, _, _ = bundle_dir_name.partition("_")
    if not prefix:
        return None
    try:
        _parse_generated_at_utc(prefix)
    except ValueError:
        return None
    return prefix


def _campaign_day_label(item: Mapping[str, object]) -> str:
    timestamp = _entry_timestamp_for_filter(item)
    if timestamp is None:
        return "unknown"
    return timestamp[:8]


def _compute_streak(
    entries: list[dict[str, object]],
    *,
    label_fn,
) -> tuple[str, int]:
    if not entries:
        return ("none", 0)
    latest_label = label_fn(entries[0])
    if not isinstance(latest_label, str):
        raise TypeError("streak labels must be strings")
    streak_length = 0
    for item in entries:
        label = label_fn(item)
        if not isinstance(label, str):
            raise TypeError("streak labels must be strings")
        if label != latest_label:
            break
        streak_length += 1
    return latest_label, streak_length


def _parse_generated_at_utc(value: str) -> datetime:
    if not isinstance(value, str):
        raise TypeError("generated UTC filters must be strings when present")
    try:
        return datetime.strptime(value, "%Y%m%dT%H%M%SZ")
    except ValueError as exc:
        raise ValueError(
            "generated UTC filters must use YYYYMMDDTHHMMSSZ format"
        ) from exc
