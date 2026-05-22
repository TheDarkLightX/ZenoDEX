#!/usr/bin/env python3
"""Build replayable KRR history stats from auto-trader compile/shadow/live reports."""

from __future__ import annotations

import argparse
import glob
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_policy_history import build_autotrader_krr_history  # noqa: E402


def _load_json(path: str | Path) -> Any:
    p = Path(path).expanduser().resolve()
    return json.loads(p.read_text(encoding="utf-8"))


def _expand_paths(files: list[str], globs: list[str]) -> list[Path]:
    seen: set[str] = set()
    out: list[Path] = []
    for raw in list(files) + list(globs):
        for match in ([raw] if raw in files else glob.glob(raw, recursive=True)):
            p = Path(match).expanduser().resolve()
            if not p.is_file():
                continue
            key = str(p)
            if key in seen:
                continue
            seen.add(key)
            out.append(p)
    return out


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--report-file", action="append", default=[], help="Explicit report JSON path")
    ap.add_argument("--report-glob", action="append", default=[], help="Glob for report JSON files")
    ap.add_argument("--history-in", help="Optional existing history JSON to merge into")
    ap.add_argument("--history-out", help="Optional output path for merged history JSON")
    ap.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        report_paths = _expand_paths(list(args.report_file), list(args.report_glob))
        if not report_paths:
            raise ValueError("at least one report file must be provided")
        reports: list[Mapping[str, object]] = []
        used_report_paths: list[str] = []
        for path in report_paths:
            obj = _load_json(path)
            if not isinstance(obj, Mapping):
                raise ValueError(f"report must be a JSON object: {path}")
            reports.append(obj)
            if isinstance(obj.get("krr_advice"), Mapping):
                used_report_paths.append(str(path))
        existing_history = None
        if args.history_in:
            existing = _load_json(args.history_in)
            if not isinstance(existing, Mapping):
                raise ValueError("history-in must be a JSON object")
            existing_history = existing
        payload = build_autotrader_krr_history(
            reports=reports,
            existing_history=existing_history,
        )
        payload["source_reports"] = used_report_paths
        text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stdout.write(text)
        if args.history_out:
            out = Path(args.history_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/autotrader-krr-history/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
