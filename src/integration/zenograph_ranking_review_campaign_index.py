from __future__ import annotations

import csv
import json
from datetime import datetime
from io import StringIO
from pathlib import Path
from typing import Callable, Mapping

ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA = (
    "zenodex/zenograph-autotrader-ranking-review-campaign-index/v1"
)

_BUNDLE_MANIFEST_SCHEMA = "zenodex/zenograph-autotrader-ranking-review-bundle/v1"


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
    _validate_build_args(campaign_root=campaign_root, limit=limit)
    _validate_build_filter_args(
        gate_status=gate_status,
        run_id_prefix=run_id_prefix,
        git_prefix=git_prefix,
        dirty_state=dirty_state,
    )
    _validate_generated_window_args(
        generated_since_utc=generated_since_utc,
        generated_until_utc=generated_until_utc,
    )

    entries = _scan_campaign_entries(campaign_root)
    entries = _apply_entry_filters(
        entries,
        gate_status=gate_status,
        run_id_prefix=run_id_prefix,
        git_prefix=git_prefix,
        dirty_state=dirty_state,
        generated_since_utc=generated_since_utc,
        generated_until_utc=generated_until_utc,
    )
    entries.sort(key=_entry_sort_key, reverse=True)
    if limit is not None:
        entries = entries[:limit]

    (
        gate_status_counts,
        block_reason_counts,
        campaign_day_counts,
        campaign_day_gate_status_counts,
        block_reason_spans,
    ) = _aggregate_entries(entries)

    latest_gate_status, latest_gate_status_streak_length = _compute_streak(
        entries,
        label_fn=_gate_status_label,
    )
    latest_block_reason, latest_block_reason_streak_length = _compute_streak(
        entries,
        label_fn=_block_reason_label,
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
        "block_reason_spans": _normalized_block_reason_spans(block_reason_spans),
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

    parts = _validated_markdown_payload_parts(payload)

    lines = [
        "# ZenoGraph Ranking Review Campaign Index",
        "",
        f"- Campaign root: `{parts['campaign_root']}`",
        f"- Bundle count: `{parts['bundle_count']}`",
        "",
    ]
    lines.extend(_render_filters_lines(parts["filters"]))
    if not parts["entries"]:
        lines.append("No bundle manifests found.")
        return "\n".join(lines) + "\n"

    lines.extend(
        _render_summary_lines(
            gate_status_counts=parts["gate_status_counts"],
            block_reason_counts=parts["block_reason_counts"],
            campaign_day_counts=parts["campaign_day_counts"],
            latest_gate_status=parts["latest_gate_status"],
            latest_gate_status_streak_length=parts["latest_gate_status_streak_length"],
            latest_block_reason=parts["latest_block_reason"],
            latest_block_reason_streak_length=parts["latest_block_reason_streak_length"],
        )
    )
    lines.extend(
        _render_campaign_day_trend_lines(
            campaign_day_counts=parts["campaign_day_counts"],
            campaign_day_gate_status_counts=parts["campaign_day_gate_status_counts"],
        )
    )
    lines.extend(_render_block_reason_span_lines(parts["block_reason_spans"]))
    lines.extend(_render_entry_table_lines(parts["entries"]))
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


def _require_mapping(value: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
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


# --- build stages -----------------------------------------------------------


def _validate_build_args(*, campaign_root: object, limit: object) -> None:
    if not isinstance(campaign_root, Path):
        raise TypeError("campaign_root must be a Path")
    if limit is not None and (not isinstance(limit, int) or limit < 1):
        raise ValueError("limit must be a positive integer when present")


def _validate_build_filter_args(
    *,
    gate_status: object,
    run_id_prefix: object,
    git_prefix: object,
    dirty_state: object,
) -> None:
    if gate_status is not None and gate_status not in {"allowed", "blocked"}:
        raise ValueError("gate_status must be 'allowed' or 'blocked' when present")
    if run_id_prefix is not None and not isinstance(run_id_prefix, str):
        raise TypeError("run_id_prefix must be a string when present")
    if git_prefix is not None and not isinstance(git_prefix, str):
        raise TypeError("git_prefix must be a string when present")
    if dirty_state is not None and dirty_state not in {"clean", "dirty"}:
        raise ValueError("dirty_state must be 'clean' or 'dirty' when present")


def _validate_generated_window_args(
    *,
    generated_since_utc: object,
    generated_until_utc: object,
) -> None:
    if generated_since_utc is not None:
        _parse_generated_at_utc(generated_since_utc)
    if generated_until_utc is not None:
        _parse_generated_at_utc(generated_until_utc)


def _scan_campaign_entries(campaign_root: Path) -> list[dict[str, object]]:
    entries: list[dict[str, object]] = []
    if not campaign_root.exists():
        return entries
    for child in campaign_root.iterdir():
        if not child.is_dir():
            continue
        entry = _load_bundle_entry(child)
        if entry is not None:
            entries.append(entry)
    return entries


def _load_bundle_entry(child: Path) -> dict[str, object] | None:
    manifest_path = child / "manifest.json"
    if not manifest_path.exists():
        return None
    try:
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if not isinstance(payload, Mapping):
        return None
    if payload.get("schema") != _BUNDLE_MANIFEST_SCHEMA:
        return None
    metadata = payload.get("metadata")
    if metadata is not None and not isinstance(metadata, Mapping):
        return None
    return {
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


def _entry_matches_gate_status(item: Mapping[str, object], gate_status: str) -> bool:
    expect_allowed = gate_status == "allowed"
    value = item.get("ranking_influence_allowed")
    return isinstance(value, bool) and value is expect_allowed


def _entry_matches_run_id_prefix(item: Mapping[str, object], run_id_prefix: str) -> bool:
    value = item.get("run_id")
    return isinstance(value, str) and value.startswith(run_id_prefix)


def _entry_matches_git_prefix(item: Mapping[str, object], git_prefix: str) -> bool:
    value = item.get("git_commit_short")
    return isinstance(value, str) and value.startswith(git_prefix)


def _entry_matches_dirty_state(item: Mapping[str, object], dirty_state: str) -> bool:
    expect_dirty = dirty_state == "dirty"
    value = item.get("git_dirty")
    return isinstance(value, bool) and value is expect_dirty


def _entry_generated_at_or_later(item: Mapping[str, object], generated_since_utc: str) -> bool:
    timestamp = _entry_timestamp_for_filter(item)
    return timestamp is not None and timestamp >= generated_since_utc


def _entry_generated_at_or_earlier(item: Mapping[str, object], generated_until_utc: str) -> bool:
    timestamp = _entry_timestamp_for_filter(item)
    return timestamp is not None and timestamp <= generated_until_utc


def _apply_entry_filters(
    entries: list[dict[str, object]],
    *,
    gate_status: str | None,
    run_id_prefix: str | None,
    git_prefix: str | None,
    dirty_state: str | None,
    generated_since_utc: str | None,
    generated_until_utc: str | None,
) -> list[dict[str, object]]:
    filter_specs: tuple[
        tuple[str | None, Callable[[Mapping[str, object], str], bool]], ...
    ] = (
        (gate_status, _entry_matches_gate_status),
        (run_id_prefix, _entry_matches_run_id_prefix),
        (git_prefix, _entry_matches_git_prefix),
        (dirty_state, _entry_matches_dirty_state),
        (generated_since_utc, _entry_generated_at_or_later),
        (generated_until_utc, _entry_generated_at_or_earlier),
    )
    for filter_value, predicate in filter_specs:
        if filter_value is None:
            continue
        entries = [item for item in entries if predicate(item, filter_value)]
    return entries


def _entry_sort_key(item: Mapping[str, object]) -> tuple[str, str, str]:
    return (
        str(item.get("campaign_timestamp_utc") or ""),
        str(item.get("generated_at_utc") or ""),
        str(item.get("run_id") or ""),
    )


def _gate_status_label(item: Mapping[str, object]) -> str:
    return _render_gate(item.get("ranking_influence_allowed"))


def _block_reason_label(item: Mapping[str, object]) -> str:
    return _optional_str(item.get("block_reason")) or "none"


def _aggregate_entries(
    entries: list[dict[str, object]],
) -> tuple[
    dict[str, int],
    dict[str, int],
    dict[str, int],
    dict[str, dict[str, int]],
    dict[str, dict[str, object]],
]:
    gate_status_counts: dict[str, int] = {}
    block_reason_counts: dict[str, int] = {}
    campaign_day_counts: dict[str, int] = {}
    campaign_day_gate_status_counts: dict[str, dict[str, int]] = {}
    block_reason_spans: dict[str, dict[str, object]] = {}
    for item in entries:
        gate_label = _gate_status_label(item)
        gate_status_counts[gate_label] = gate_status_counts.get(gate_label, 0) + 1
        block_reason = _block_reason_label(item)
        block_reason_counts[block_reason] = block_reason_counts.get(block_reason, 0) + 1
        campaign_day = _campaign_day_label(item)
        campaign_day_counts[campaign_day] = campaign_day_counts.get(campaign_day, 0) + 1
        day_gate_counts = campaign_day_gate_status_counts.setdefault(campaign_day, {})
        day_gate_counts[gate_label] = day_gate_counts.get(gate_label, 0) + 1
        _record_block_reason_span(block_reason_spans, block_reason, campaign_day)
    return (
        gate_status_counts,
        block_reason_counts,
        campaign_day_counts,
        campaign_day_gate_status_counts,
        block_reason_spans,
    )


def _record_block_reason_span(
    block_reason_spans: dict[str, dict[str, object]],
    block_reason: str,
    campaign_day: str,
) -> None:
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


def _normalized_block_reason_spans(
    block_reason_spans: dict[str, dict[str, object]],
) -> dict[str, dict[str, object]]:
    return {
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
    }


# --- markdown sections ------------------------------------------------------


def _validated_markdown_payload_parts(payload: Mapping[str, object]) -> dict[str, object]:
    parts: dict[str, object] = {}
    parts["campaign_root"] = _require_str(payload.get("campaign_root"), name="campaign_root")
    parts["bundle_count"] = _require_int(payload.get("bundle_count"), name="bundle_count")
    parts["filters"] = _require_mapping(payload.get("filters"), name="filters")
    entries = payload.get("entries")
    if not isinstance(entries, list):
        raise TypeError("entries must be a list")
    parts["entries"] = entries
    parts["gate_status_counts"] = _require_mapping(
        payload.get("gate_status_counts"), name="gate_status_counts"
    )
    parts["block_reason_counts"] = _require_mapping(
        payload.get("block_reason_counts"), name="block_reason_counts"
    )
    parts["campaign_day_counts"] = _require_mapping(
        payload.get("campaign_day_counts"), name="campaign_day_counts"
    )
    parts["campaign_day_gate_status_counts"] = _require_mapping(
        payload.get("campaign_day_gate_status_counts"),
        name="campaign_day_gate_status_counts",
    )
    parts["block_reason_spans"] = _require_mapping(
        payload.get("block_reason_spans"), name="block_reason_spans"
    )
    parts["latest_gate_status"] = _require_str(
        payload.get("latest_gate_status"), name="latest_gate_status"
    )
    parts["latest_gate_status_streak_length"] = _require_int(
        payload.get("latest_gate_status_streak_length"),
        name="latest_gate_status_streak_length",
    )
    parts["latest_block_reason"] = _require_str(
        payload.get("latest_block_reason"), name="latest_block_reason"
    )
    parts["latest_block_reason_streak_length"] = _require_int(
        payload.get("latest_block_reason_streak_length"),
        name="latest_block_reason_streak_length",
    )
    return parts


def _render_filters_lines(filters: Mapping[str, object]) -> list[str]:
    labeled_filters = (
        ("Gate status", _optional_str(filters.get("gate_status"))),
        ("Run ID prefix", _optional_str(filters.get("run_id_prefix"))),
        ("Git prefix", _optional_str(filters.get("git_prefix"))),
        ("Dirty state", _optional_str(filters.get("dirty_state"))),
        ("Generated since UTC", _optional_str(filters.get("generated_since_utc"))),
        ("Generated until UTC", _optional_str(filters.get("generated_until_utc"))),
    )
    if all(value is None for _, value in labeled_filters):
        return []
    lines = ["## Filters", ""]
    for label, value in labeled_filters:
        lines.append(f"- {label}: `{value or 'none'}`")
    lines.append("")
    return lines


def _count_lines(
    title: str,
    counts: Mapping[str, object],
    *,
    name_prefix: str,
) -> list[str]:
    lines = [f"- {title}:"]
    for key, value in sorted(counts.items()):
        lines.append(f"  - `{key}`: `{_require_int(value, name=f'{name_prefix}.{key}')}`")
    return lines


def _render_summary_lines(
    *,
    gate_status_counts: Mapping[str, object],
    block_reason_counts: Mapping[str, object],
    campaign_day_counts: Mapping[str, object],
    latest_gate_status: str,
    latest_gate_status_streak_length: int,
    latest_block_reason: str,
    latest_block_reason_streak_length: int,
) -> list[str]:
    lines = ["## Summary", ""]
    lines.extend(
        _count_lines("Gate status counts", gate_status_counts, name_prefix="gate_status_counts")
    )
    lines.extend(
        _count_lines(
            "Block reason counts", block_reason_counts, name_prefix="block_reason_counts"
        )
    )
    lines.extend(
        _count_lines(
            "Campaign day counts", campaign_day_counts, name_prefix="campaign_day_counts"
        )
    )
    lines.append(
        f"- Latest gate status streak: `{latest_gate_status}` x `{latest_gate_status_streak_length}`"
    )
    lines.append(
        f"- Latest block reason streak: `{latest_block_reason}` x `{latest_block_reason_streak_length}`"
    )
    lines.append("")
    return lines


def _render_campaign_day_trend_lines(
    *,
    campaign_day_counts: Mapping[str, object],
    campaign_day_gate_status_counts: Mapping[str, object],
) -> list[str]:
    lines = [
        "## Campaign Day Trends",
        "",
        "| Campaign Day | Bundle Count | Gate Status Counts |",
        "| --- | --- | --- |",
    ]
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
    return lines


def _render_block_reason_span_lines(
    block_reason_spans: Mapping[str, object],
) -> list[str]:
    lines = [
        "## Block Reason Spans",
        "",
        "| Block Reason | Count | First Day | Last Day |",
        "| --- | --- | --- | --- |",
    ]
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
    return lines


def _render_entry_table_lines(entries: list[object]) -> list[str]:
    lines = [
        "| Run ID | Generated UTC | Gate | Block Reason | Git | Dirty |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
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
    return lines
