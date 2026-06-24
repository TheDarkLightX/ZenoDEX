"""Static HTML report for release-candidate receipts."""

from __future__ import annotations

import html
from pathlib import Path
from typing import Any


def _esc(value: object) -> str:
    return html.escape(str(value))


def _file_href(path_value: object) -> str | None:
    try:
        path = Path(str(path_value))
    except (TypeError, ValueError):
        return None
    if not str(path_value).strip():
        return None
    try:
        return path.resolve().as_uri()
    except ValueError:
        return None


def _report_link(path_value: object, *, label: str) -> str:
    href = _file_href(path_value)
    text = _esc(label)
    if href is None:
        return text
    return f'<a href="{_esc(href)}">{text}</a>'


def render_candidate_report_html(payload: dict[str, Any]) -> str:
    candidates = payload.get("candidates", [])
    latest = candidates[0] if candidates else None
    active_label = str(payload.get("active_candidate_label", "RC2"))
    historical_label = str(payload.get("historical_release_label", "RC1"))

    latest_html = ""
    if latest is not None:
        latest_html = f"""
        <section class="spotlight">
          <h2>Latest Candidate</h2>
          <div class="grid">
            <div><span>Timestamp</span><strong>{_esc(latest.get("campaign_timestamp_utc") or "unknown")}</strong></div>
            <div><span>Run ID</span><strong>{_esc(latest.get("run_id"))}</strong></div>
            <div><span>Status</span><strong class="{('ready' if latest.get('overall_ok') else 'blocked')}">{'READY' if latest.get('overall_ok') else 'BLOCKED'}</strong></div>
            <div><span>Dirty Count</span><strong>{_esc(latest.get("dirty_count", 0))}</strong></div>
            <div><span>Branch</span><strong>{_esc(latest.get("branch") or "unknown")}</strong></div>
            <div><span>Report</span><strong class="path">{_report_link(latest.get("report_path"), label="candidate_report.json")}</strong></div>
          </div>
          <p class="note">This is a release-governance artifact only. It does not authorize an { _esc(active_label) } cut by itself.</p>
        </section>
        """

    unmet_counts_html = ""
    unmet_counts = payload.get("unmet_criteria_counts", {})
    if unmet_counts:
        items = "\n".join(
            f"<li><span>{_esc(key)}</span><strong>{_esc(value)}</strong></li>"
            for key, value in unmet_counts.items()
        )
        unmet_counts_html = f"""
        <section>
          <h2>Unmet Criteria Counts</h2>
          <ul class="metric-list">
            {items}
          </ul>
        </section>
        """

    rows_html = "\n".join(
        f"""
        <tr>
          <td>{_esc(row.get("campaign_timestamp_utc") or "unknown")}</td>
          <td>{_esc(row.get("run_id"))}</td>
          <td class="{('ready' if row.get('overall_ok') else 'blocked')}">{'READY' if row.get('overall_ok') else 'BLOCKED'}</td>
          <td>{_esc(row.get("dirty_count", 0))}</td>
          <td>{_esc(row.get("branch") or "unknown")}</td>
          <td>{_esc(', '.join(row.get('unmet_criteria') or []) or 'none')}</td>
          <td class="path">{_report_link(row.get("report_path"), label="candidate_report.json")}</td>
        </tr>
        """
        for row in candidates
    )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>ZenoDex {_esc(active_label)} Candidate Report</title>
  <style>
    :root {{
      --bg: #f6f1e8;
      --panel: #fffdf8;
      --ink: #1f1a17;
      --muted: #6c625a;
      --line: #d6c8b4;
      --accent: #0e6b5c;
      --warn: #a44b28;
      --shadow: 0 10px 30px rgba(31, 26, 23, 0.08);
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      font-family: Georgia, "Iowan Old Style", serif;
      background: radial-gradient(circle at top, #fffaf0 0%, var(--bg) 55%, #efe7d7 100%);
      color: var(--ink);
    }}
    main {{
      max-width: 1180px;
      margin: 0 auto;
      padding: 32px 20px 48px;
    }}
    header {{
      margin-bottom: 24px;
    }}
    h1, h2 {{
      margin: 0 0 12px;
      line-height: 1.1;
    }}
    p {{
      margin: 0;
      color: var(--muted);
    }}
    .warning {{
      margin-top: 16px;
      padding: 14px 16px;
      border: 1px solid #e4b88b;
      background: #fff2df;
      color: #6d3d15;
      border-radius: 14px;
    }}
    .summary {{
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
      gap: 14px;
      margin: 24px 0;
    }}
    .card, .spotlight, section {{
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 18px;
      box-shadow: var(--shadow);
    }}
    .card {{
      padding: 18px;
    }}
    .card span, .grid span {{
      display: block;
      font-size: 12px;
      letter-spacing: 0.08em;
      text-transform: uppercase;
      color: var(--muted);
      margin-bottom: 8px;
    }}
    .card strong, .grid strong {{
      font-size: 28px;
    }}
    .spotlight, section {{
      padding: 20px;
      margin-top: 20px;
    }}
    .grid {{
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
      gap: 14px;
    }}
    .note {{
      margin-top: 14px;
      font-size: 14px;
    }}
    .metric-list {{
      list-style: none;
      margin: 0;
      padding: 0;
      display: grid;
      gap: 10px;
    }}
    .metric-list li {{
      display: flex;
      justify-content: space-between;
      padding-bottom: 8px;
      border-bottom: 1px solid var(--line);
    }}
    table {{
      width: 100%;
      border-collapse: collapse;
      margin-top: 10px;
      font-size: 14px;
    }}
    th, td {{
      text-align: left;
      padding: 10px 8px;
      border-bottom: 1px solid var(--line);
      vertical-align: top;
    }}
    th {{
      font-size: 12px;
      letter-spacing: 0.08em;
      text-transform: uppercase;
      color: var(--muted);
    }}
    .ready {{
      color: var(--accent);
      font-weight: 700;
    }}
    .blocked {{
      color: var(--warn);
      font-weight: 700;
    }}
    .path {{
      font-family: "SFMono-Regular", Consolas, monospace;
      font-size: 12px;
      word-break: break-all;
    }}
    a {{
      color: var(--accent);
      text-decoration: none;
      border-bottom: 1px solid rgba(14, 107, 92, 0.25);
    }}
    a:hover {{
      border-bottom-color: var(--accent);
    }}
  </style>
</head>
<body>
  <main>
    <header>
      <h1>ZenoDex {_esc(active_label)} Candidate Report</h1>
      <p>Read-only release-governance summary for conservative {_esc(active_label)} candidate receipts.</p>
      <p>Historical baseline: {_esc(historical_label)} already shipped.</p>
      <div class="warning">
        Experimental and broad advisory/autotrader surfaces remain outside {_esc(active_label)} authority. This report is for release review only.
      </div>
    </header>

    <div class="summary">
      <div class="card"><span>Campaign Root</span><strong class="path">{_esc(payload.get("campaign_root"))}</strong></div>
      <div class="card"><span>Candidates</span><strong>{_esc(payload.get("candidate_count", 0))}</strong></div>
      <div class="card"><span>Ready</span><strong class="ready">{_esc(payload.get("ready_count", 0))}</strong></div>
      <div class="card"><span>Blocked</span><strong class="blocked">{_esc(payload.get("blocked_count", 0))}</strong></div>
    </div>

    {latest_html}
    {unmet_counts_html}

    <section>
      <h2>Candidate Table</h2>
      <table>
        <thead>
          <tr>
            <th>Timestamp</th>
            <th>Run ID</th>
            <th>Status</th>
            <th>Dirty</th>
            <th>Branch</th>
            <th>Unmet Criteria</th>
            <th>Report Path</th>
          </tr>
        </thead>
        <tbody>
          {rows_html}
        </tbody>
      </table>
    </section>
  </main>
</body>
</html>
"""
