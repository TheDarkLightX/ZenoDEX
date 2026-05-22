from __future__ import annotations

import html
from pathlib import Path
from typing import Mapping

from src.integration.zenograph_ranking_review_campaign_index import (
    ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA,
)


def render_zenograph_ranking_review_campaign_html(
    payload: Mapping[str, object],
) -> str:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA:
        raise ValueError("unsupported campaign index schema")

    campaign_root = _require_str(payload.get("campaign_root"), name="campaign_root")
    bundle_count = _require_int(payload.get("bundle_count"), name="bundle_count")
    filters = _require_mapping(payload.get("filters"), name="filters")
    entries = _require_list(payload.get("entries"), name="entries")
    gate_status_counts = _require_mapping(payload.get("gate_status_counts"), name="gate_status_counts")
    block_reason_counts = _require_mapping(payload.get("block_reason_counts"), name="block_reason_counts")
    campaign_day_counts = _require_mapping(payload.get("campaign_day_counts"), name="campaign_day_counts")
    campaign_day_gate_status_counts = _require_mapping(
        payload.get("campaign_day_gate_status_counts"),
        name="campaign_day_gate_status_counts",
    )
    block_reason_spans = _require_mapping(payload.get("block_reason_spans"), name="block_reason_spans")
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

    total_gate_count = sum(_require_int(value, name=f"gate_status_counts.{key}") for key, value in gate_status_counts.items())
    max_day_count = max((_require_int(value, name=f"campaign_day_counts.{key}") for key, value in campaign_day_counts.items()), default=1)
    max_block_reason_count = max(
        (_require_int(value, name=f"block_reason_counts.{key}") for key, value in block_reason_counts.items()),
        default=1,
    )
    active_filters = [
        ("Gate status", _optional_str(filters.get("gate_status"))),
        ("Run ID prefix", _optional_str(filters.get("run_id_prefix"))),
        ("Git prefix", _optional_str(filters.get("git_prefix"))),
        ("Dirty state", _optional_str(filters.get("dirty_state"))),
        ("Generated since UTC", _optional_str(filters.get("generated_since_utc"))),
        ("Generated until UTC", _optional_str(filters.get("generated_until_utc"))),
    ]

    gate_cards = "".join(
        _render_stat_card(
            label=key,
            value=str(_require_int(value, name=f"gate_status_counts.{key}")),
            sublabel=f"{_percentage(_require_int(value, name=f'gate_status_counts.{key}'), total_gate_count)} of bundles",
            accent_class=f"accent-{key}",
        )
        for key, value in sorted(gate_status_counts.items())
    )
    block_reason_rows = "".join(
        _render_bar_row(
            label=key,
            value=_require_int(value, name=f"block_reason_counts.{key}"),
            max_value=max_block_reason_count,
        )
        for key, value in sorted(block_reason_counts.items())
    )
    filter_chips = "".join(
        f'<span class="chip">{_escape(label)}: {_escape(value or "none")}</span>'
        for label, value in active_filters
    )
    day_rows = "".join(
        _render_day_row(
            campaign_day=campaign_day,
            count=_require_int(count_obj, name=f"campaign_day_counts.{campaign_day}"),
            max_count=max_day_count,
            gate_counts=_require_mapping(
                campaign_day_gate_status_counts.get(campaign_day, {}),
                name=f"campaign_day_gate_status_counts.{campaign_day}",
            ),
        )
        for campaign_day, count_obj in sorted(campaign_day_counts.items())
    )
    span_rows = "".join(
        _render_block_reason_span_row(
            block_reason=block_reason,
            value=_require_mapping(span_obj, name=f"block_reason_spans.{block_reason}"),
        )
        for block_reason, span_obj in sorted(block_reason_spans.items())
    )
    latest_bundle_panel = _render_latest_bundle_panel(
        _require_mapping(entries[0], name="entries[0]") if entries else None
    )
    entry_rows = "".join(_render_entry_row(_require_mapping(entry, name="entries[]")) for entry in entries)

    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>ZenoGraph Ranking Review Campaign Report</title>
  <style>
    :root {{
      --bg: #f4efe5;
      --panel: rgba(255, 251, 245, 0.88);
      --ink: #1d1a17;
      --muted: #6d6359;
      --line: rgba(29, 26, 23, 0.12);
      --shadow: 0 24px 80px rgba(37, 25, 14, 0.14);
      --accent-blocked: #9d2a2a;
      --accent-allowed: #166c4d;
      --accent-unknown: #8f6a18;
      --accent-neutral: #1f4b99;
    }}

    * {{
      box-sizing: border-box;
    }}

    body {{
      margin: 0;
      min-height: 100vh;
      background:
        radial-gradient(circle at top left, rgba(141, 84, 58, 0.20), transparent 34%),
        radial-gradient(circle at top right, rgba(16, 93, 78, 0.16), transparent 28%),
        linear-gradient(180deg, #f8f2e8 0%, var(--bg) 100%);
      color: var(--ink);
      font-family: "Avenir Next", "Segoe UI", "Helvetica Neue", sans-serif;
      letter-spacing: 0.01em;
    }}

    body::before {{
      content: "";
      position: fixed;
      inset: 0;
      pointer-events: none;
      background:
        linear-gradient(130deg, rgba(255,255,255,0.35), transparent 42%),
        repeating-linear-gradient(
          90deg,
          rgba(29, 26, 23, 0.018) 0,
          rgba(29, 26, 23, 0.018) 1px,
          transparent 1px,
          transparent 22px
        );
      opacity: 0.55;
    }}

    .shell {{
      width: min(1180px, calc(100vw - 40px));
      margin: 28px auto 48px;
      position: relative;
      z-index: 1;
    }}

    .hero {{
      background: linear-gradient(145deg, rgba(255, 250, 244, 0.92), rgba(248, 238, 226, 0.86));
      border: 1px solid rgba(29, 26, 23, 0.10);
      border-radius: 28px;
      box-shadow: var(--shadow);
      padding: 28px 30px 30px;
      overflow: hidden;
      position: relative;
    }}

    .hero::after {{
      content: "";
      position: absolute;
      top: -120px;
      right: -120px;
      width: 260px;
      height: 260px;
      border-radius: 999px;
      background: radial-gradient(circle, rgba(157, 42, 42, 0.16), transparent 70%);
    }}

    .eyebrow {{
      margin: 0 0 10px;
      color: var(--accent-blocked);
      font-size: 12px;
      font-weight: 700;
      letter-spacing: 0.18em;
      text-transform: uppercase;
    }}

    h1, h2 {{
      margin: 0;
      font-family: "Iowan Old Style", "Palatino Linotype", "Book Antiqua", Georgia, serif;
      font-weight: 700;
      letter-spacing: -0.03em;
    }}

    h1 {{
      font-size: clamp(2.4rem, 4vw, 4.6rem);
      line-height: 0.94;
      max-width: 12ch;
    }}

    h2 {{
      font-size: 1.45rem;
      margin-bottom: 14px;
    }}

    .hero-copy {{
      display: grid;
      grid-template-columns: 1.3fr 0.9fr;
      gap: 24px;
      align-items: end;
      margin-top: 18px;
    }}

    .lede {{
      margin: 0;
      color: var(--muted);
      font-size: 1rem;
      line-height: 1.6;
      max-width: 62ch;
    }}

    .warning {{
      padding: 18px 20px;
      background: rgba(157, 42, 42, 0.08);
      border: 1px solid rgba(157, 42, 42, 0.18);
      border-radius: 18px;
      color: #5e1f1f;
      font-size: 0.94rem;
      line-height: 1.55;
    }}

    .grid {{
      display: grid;
      gap: 18px;
      margin-top: 18px;
    }}

    .grid.two {{
      grid-template-columns: 1.2fr 0.8fr;
    }}

    .grid.three {{
      grid-template-columns: repeat(3, minmax(0, 1fr));
    }}

    .panel {{
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 24px;
      box-shadow: var(--shadow);
      padding: 22px;
      backdrop-filter: blur(12px);
    }}

    .chips {{
      display: flex;
      flex-wrap: wrap;
      gap: 10px;
    }}

    .chip {{
      display: inline-flex;
      align-items: center;
      min-height: 34px;
      padding: 0 12px;
      border-radius: 999px;
      background: rgba(29, 26, 23, 0.06);
      color: var(--ink);
      font-size: 0.86rem;
    }}

    .stats {{
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(160px, 1fr));
      gap: 14px;
    }}

    .stat-card {{
      padding: 18px;
      border-radius: 18px;
      background: rgba(255, 255, 255, 0.62);
      border: 1px solid rgba(29, 26, 23, 0.08);
    }}

    .stat-label {{
      display: inline-block;
      padding-left: 12px;
      position: relative;
      font-size: 0.8rem;
      text-transform: uppercase;
      letter-spacing: 0.12em;
      color: var(--muted);
    }}

    .stat-label::before {{
      content: "";
      position: absolute;
      left: 0;
      top: 4px;
      width: 6px;
      height: 6px;
      border-radius: 999px;
      background: currentColor;
    }}

    .accent-blocked .stat-label {{
      color: var(--accent-blocked);
    }}

    .accent-allowed .stat-label {{
      color: var(--accent-allowed);
    }}

    .accent-unknown .stat-label {{
      color: var(--accent-unknown);
    }}

    .stat-value {{
      margin-top: 10px;
      font-size: 2rem;
      line-height: 1;
      font-weight: 700;
    }}

    .stat-sublabel {{
      margin-top: 8px;
      color: var(--muted);
      font-size: 0.88rem;
    }}

    .bar-stack {{
      display: grid;
      gap: 14px;
    }}

    .bar-row {{
      display: grid;
      gap: 6px;
    }}

    .bar-header {{
      display: flex;
      align-items: baseline;
      justify-content: space-between;
      gap: 16px;
      font-size: 0.92rem;
    }}

    .bar-track {{
      width: 100%;
      height: 10px;
      border-radius: 999px;
      background: rgba(29, 26, 23, 0.08);
      overflow: hidden;
    }}

    .bar-fill {{
      height: 100%;
      border-radius: 999px;
      background: linear-gradient(90deg, #2a4872 0%, #9d2a2a 100%);
    }}

    .trend-grid {{
      display: grid;
      grid-template-columns: 1.1fr 0.9fr;
      gap: 18px;
    }}

    .trend-list {{
      display: grid;
      gap: 12px;
    }}

    .trend-row {{
      padding: 14px 16px;
      border-radius: 18px;
      background: rgba(255, 255, 255, 0.64);
      border: 1px solid rgba(29, 26, 23, 0.08);
    }}

    .trend-top {{
      display: flex;
      align-items: baseline;
      justify-content: space-between;
      gap: 16px;
      margin-bottom: 10px;
    }}

    .trend-day {{
      font-family: "Iowan Old Style", "Palatino Linotype", Georgia, serif;
      font-size: 1.15rem;
      font-weight: 700;
    }}

    .micro-bar {{
      width: 100%;
      height: 8px;
      border-radius: 999px;
      background: rgba(29, 26, 23, 0.08);
      overflow: hidden;
      margin-bottom: 10px;
    }}

    .micro-fill {{
      height: 100%;
      border-radius: 999px;
      background: linear-gradient(90deg, #166c4d 0%, #c88632 100%);
    }}

    .trend-meta {{
      color: var(--muted);
      font-size: 0.85rem;
      line-height: 1.5;
    }}

    table {{
      width: 100%;
      border-collapse: collapse;
    }}

    th, td {{
      text-align: left;
      padding: 12px 10px;
      border-bottom: 1px solid rgba(29, 26, 23, 0.10);
      vertical-align: top;
    }}

    th {{
      font-size: 0.76rem;
      color: var(--muted);
      letter-spacing: 0.12em;
      text-transform: uppercase;
    }}

    td {{
      font-size: 0.92rem;
    }}

    .pill {{
      display: inline-flex;
      align-items: center;
      gap: 8px;
      padding: 6px 10px;
      border-radius: 999px;
      font-size: 0.82rem;
      border: 1px solid rgba(29, 26, 23, 0.10);
      background: rgba(255, 255, 255, 0.72);
    }}

    .pill.allowed {{
      color: var(--accent-allowed);
    }}

    .pill.blocked {{
      color: var(--accent-blocked);
    }}

    .code {{
      font-family: "IBM Plex Mono", "SFMono-Regular", Consolas, monospace;
      font-size: 0.84rem;
    }}

    .muted {{
      color: var(--muted);
    }}

    .link-cluster {{
      display: flex;
      flex-wrap: wrap;
      gap: 8px;
    }}

    .artifact-link {{
      display: inline-flex;
      align-items: center;
      min-height: 28px;
      padding: 0 10px;
      border-radius: 999px;
      border: 1px solid rgba(29, 26, 23, 0.12);
      background: rgba(255, 255, 255, 0.72);
      color: var(--accent-neutral);
      text-decoration: none;
      font-size: 0.8rem;
      font-weight: 600;
    }}

    .artifact-link:hover {{
      border-color: rgba(31, 75, 153, 0.36);
      background: rgba(31, 75, 153, 0.08);
    }}

    @media (max-width: 980px) {{
      .hero-copy,
      .grid.two,
      .trend-grid {{
        grid-template-columns: 1fr;
      }}
    }}

    @media (max-width: 640px) {{
      .shell {{
        width: min(100vw - 22px, 1180px);
        margin-top: 12px;
      }}

      .hero,
      .panel {{
        padding: 18px;
        border-radius: 20px;
      }}

      h1 {{
        font-size: 2.25rem;
      }}

      th, td {{
        padding-left: 6px;
        padding-right: 6px;
      }}
    }}
  </style>
</head>
<body>
  <main class="shell">
    <section class="hero">
      <p class="eyebrow">Advanced Experimental Review Surface</p>
      <h1>ZenoGraph Campaign Governance Report</h1>
      <div class="hero-copy">
        <p class="lede">
          Read-only operator report for signed replay governance. This surface summarizes replay bundle posture,
          promotion-gate health, and recurring failure modes. It does not authorize ranking or execution.
        </p>
        <aside class="warning">
          <strong>Use at your own risk.</strong> This is experimental automation review tooling. It is not a safety
          claim, not an execution surface, and not a promise of profitability. Users can still lose everything if bad
          decisions are promoted elsewhere.
        </aside>
      </div>
    </section>

    <section class="grid three">
      {_render_stat_card("campaign root", _escape(campaign_root), f"{bundle_count} bundles indexed", "accent-unknown")}
      {_render_stat_card("latest gate streak", _escape(latest_gate_status), f"{latest_gate_status_streak_length} consecutive bundles", f"accent-{latest_gate_status}")}
      {_render_stat_card("latest block streak", _escape(latest_block_reason), f"{latest_block_reason_streak_length} consecutive bundles", "accent-blocked")}
    </section>

    <section class="grid two">
      <article class="panel">
        <h2>Filters</h2>
        <div class="chips">{filter_chips}</div>
      </article>
      <article class="panel">
        <h2>Gate Status</h2>
        <div class="stats">{gate_cards}</div>
      </article>
    </section>

    <section class="grid two">
      <article class="panel">
        <h2>Block Reason Load</h2>
        <div class="bar-stack">{block_reason_rows}</div>
      </article>
      <article class="panel">
        <h2>Block Reason Spans</h2>
        <table>
          <thead>
            <tr>
              <th>Reason</th>
              <th>Count</th>
              <th>First Day</th>
              <th>Last Day</th>
            </tr>
          </thead>
          <tbody>{span_rows}</tbody>
        </table>
      </article>
    </section>

    <section class="panel">
      <h2>Latest Bundle</h2>
      {latest_bundle_panel}
    </section>

    <section class="panel">
      <h2>Campaign Day Trends</h2>
      <div class="trend-grid">
        <div class="trend-list">{day_rows}</div>
        <div class="warning">
          <strong>Interpretation boundary.</strong> These trends summarize replay governance only. A streak of
          blocked bundles means the signed promotion gate is still doing its job. It does not mean the underlying
          trading logic is safe to ship, only that review evidence still disagrees with runtime posture.
        </div>
      </div>
    </section>

    <section class="panel">
      <h2>Bundle Index</h2>
      <table>
        <thead>
          <tr>
            <th>Run ID</th>
            <th>Campaign UTC</th>
            <th>Gate</th>
            <th>Block Reason</th>
            <th>Git</th>
            <th>Dirty</th>
            <th>Artifacts</th>
          </tr>
        </thead>
        <tbody>{entry_rows}</tbody>
      </table>
    </section>
  </main>
</body>
</html>
"""


def _render_stat_card(label: str, value: str, sublabel: str, accent_class: str) -> str:
    return (
        f'<article class="stat-card {html.escape(accent_class)}">'
        f'<span class="stat-label">{_escape(label)}</span>'
        f'<div class="stat-value">{value}</div>'
        f'<div class="stat-sublabel">{_escape(sublabel)}</div>'
        "</article>"
    )


def _render_bar_row(*, label: str, value: int, max_value: int) -> str:
    width = 0 if max_value <= 0 else max(6, round((value / max_value) * 100))
    return (
        '<div class="bar-row">'
        f'<div class="bar-header"><span>{_escape(label)}</span><strong>{value}</strong></div>'
        f'<div class="bar-track"><div class="bar-fill" style="width:{width}%"></div></div>'
        "</div>"
    )


def _render_day_row(*, campaign_day: str, count: int, max_count: int, gate_counts: Mapping[str, object]) -> str:
    width = 0 if max_count <= 0 else max(8, round((count / max_count) * 100))
    gate_parts = ", ".join(
        f"{gate_key}={_require_int(gate_value, name=f'{campaign_day}.{gate_key}')}"
        for gate_key, gate_value in sorted(gate_counts.items())
    )
    return (
        '<article class="trend-row">'
        f'<div class="trend-top"><div class="trend-day">{_escape(campaign_day)}</div><strong>{count} bundles</strong></div>'
        f'<div class="micro-bar"><div class="micro-fill" style="width:{width}%"></div></div>'
        f'<div class="trend-meta">Gate counts: {_escape(gate_parts or "none")}</div>'
        "</article>"
    )


def _render_block_reason_span_row(*, block_reason: str, value: Mapping[str, object]) -> str:
    count = _require_int(value.get("count"), name=f"block_reason_spans.{block_reason}.count")
    first_day = _require_str(
        value.get("first_campaign_day"),
        name=f"block_reason_spans.{block_reason}.first_campaign_day",
    )
    last_day = _require_str(
        value.get("last_campaign_day"),
        name=f"block_reason_spans.{block_reason}.last_campaign_day",
    )
    return (
        "<tr>"
        f"<td><span class=\"code\">{_escape(block_reason)}</span></td>"
        f"<td>{count}</td>"
        f"<td>{_escape(first_day)}</td>"
        f"<td>{_escape(last_day)}</td>"
        "</tr>"
    )


def _render_latest_bundle_panel(item: Mapping[str, object] | None) -> str:
    if item is None:
        return '<p class="muted">No bundles available.</p>'
    run_id = _optional_str(item.get("run_id")) or "unknown"
    campaign_timestamp_utc = _optional_str(item.get("campaign_timestamp_utc")) or "unknown"
    gate = _render_gate(item.get("ranking_influence_allowed"))
    block_reason = _optional_str(item.get("block_reason")) or "none"
    git_commit_short = _optional_str(item.get("git_commit_short")) or "unknown"
    dirty = _render_dirty(item.get("git_dirty"))
    links = "".join(
        filter(
            None,
            [
                _render_artifact_link(item.get("manifest_path"), "manifest"),
                _render_artifact_link(item.get("summary_path"), "review"),
                _render_artifact_link(item.get("gate_report_path"), "gate"),
                _render_artifact_link(item.get("baseline_report_path"), "baseline"),
                _render_artifact_link(item.get("instructions_path"), "readme"),
            ],
        )
    )
    pill_class = "allowed" if gate == "allowed" else "blocked" if gate == "blocked" else ""
    explanation = (
        "Latest bundle is replay-green at review level. Execution remains separately fenced off."
        if gate == "allowed"
        else f"Latest bundle remains blocked. Lead blocker: {block_reason}."
        if gate == "blocked"
        else "Latest bundle gate posture is unknown."
    )
    return (
        '<div class="trend-row">'
        f'<div class="trend-top"><div class="trend-day">{_escape(run_id)}</div>'
        f'<span class="pill {pill_class}">{_escape(gate)}</span></div>'
        f'<div class="trend-meta">Campaign UTC: <span class="code">{_escape(campaign_timestamp_utc)}</span></div>'
        f'<div class="trend-meta">Block reason: <span class="code">{_escape(block_reason)}</span></div>'
        f'<div class="trend-meta">Git: <span class="code">{_escape(git_commit_short)}</span> | Dirty: {_escape(dirty)}</div>'
        f'<div class="trend-meta">{_escape(explanation)}</div>'
        f'<div class="link-cluster" style="margin-top:12px;">{links or "<span class=\"muted\">none</span>"}</div>'
        "</div>"
    )


def _render_entry_row(item: Mapping[str, object]) -> str:
    run_id = _optional_str(item.get("run_id")) or "unknown"
    campaign_timestamp_utc = _optional_str(item.get("campaign_timestamp_utc")) or "unknown"
    gate = _render_gate(item.get("ranking_influence_allowed"))
    block_reason = _optional_str(item.get("block_reason")) or "none"
    git_commit_short = _optional_str(item.get("git_commit_short")) or "unknown"
    dirty = _render_dirty(item.get("git_dirty"))
    links = "".join(
        filter(
            None,
            [
                _render_artifact_link(item.get("manifest_path"), "manifest"),
                _render_artifact_link(item.get("summary_path"), "review"),
                _render_artifact_link(item.get("gate_report_path"), "gate"),
                _render_artifact_link(item.get("baseline_report_path"), "baseline"),
                _render_artifact_link(item.get("instructions_path"), "readme"),
            ],
        )
    )
    pill_class = "allowed" if gate == "allowed" else "blocked" if gate == "blocked" else ""
    return (
        "<tr>"
        f"<td><span class=\"code\">{_escape(run_id)}</span></td>"
        f"<td><span class=\"code\">{_escape(campaign_timestamp_utc)}</span></td>"
        f"<td><span class=\"pill {pill_class}\">{_escape(gate)}</span></td>"
        f"<td><span class=\"code\">{_escape(block_reason)}</span></td>"
        f"<td><span class=\"code\">{_escape(git_commit_short)}</span></td>"
        f"<td><span class=\"muted\">{_escape(dirty)}</span></td>"
        f"<td><div class=\"link-cluster\">{links or '<span class=\"muted\">none</span>'}</div></td>"
        "</tr>"
    )


def _percentage(count: int, total: int) -> str:
    if total <= 0:
        return "0%"
    return f"{round((count / total) * 100)}%"


def _escape(value: object) -> str:
    return html.escape(str(value))


def _render_artifact_link(path_value: object, label: str) -> str:
    path_str = _optional_str(path_value)
    if path_str is None:
        return ""
    path = Path(path_str)
    if not path.exists():
        return ""
    return (
        f'<a class="artifact-link" href="{html.escape(path.resolve().as_uri())}">'
        f"{_escape(label)}</a>"
    )


def _require_mapping(value: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_list(value: object, *, name: str) -> list[object]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


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


def _render_dirty(value: object) -> str:
    if isinstance(value, bool):
        return "dirty" if value else "clean"
    return "unknown"
