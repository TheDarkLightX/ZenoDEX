#!/usr/bin/env python3
"""Fail-closed profile check for latest-Tau stream add/sub limits."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
PROFILE_PATH = ROOT / "src" / "tau_specs" / "recommended" / "spec_profiles.json"

ADD_SUB_RE = re.compile(r"(?:\+|(?<!-)-(?![=>]))")

GENERIC_BLOCKED_STATUS = "blocked_requires_host_proof_or_upstream_fix"
STRICT_TAU_BLOCKED_STATUS = "blocked_requires_runtime_tau_profile_or_upstream_fix"
STRICT_TAU_COMPONENTS = {"settlement"}


def _strip_comment(line: str) -> str:
    brace_depth = 0
    for idx, ch in enumerate(line):
        if ch == "{":
            brace_depth += 1
        elif ch == "}":
            brace_depth = max(0, brace_depth - 1)
        elif ch == "#" and brace_depth == 0:
            return line[:idx]
    return line


def _add_sub_hits(path: Path) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    text = path.read_text(encoding="utf-8")
    for lineno, raw_line in enumerate(text.splitlines(), 1):
        line = _strip_comment(raw_line).strip()
        if not line:
            continue
        if ADD_SUB_RE.search(line):
            hits.append({"line": lineno, "text": line})
    return hits


def _variant_iter(profiles: Mapping[str, Any]) -> list[tuple[str, Mapping[str, Any]]]:
    out: list[tuple[str, Mapping[str, Any]]] = []
    components = profiles.get("components", {})
    if not isinstance(components, Mapping):
        return out
    for component, cfg in components.items():
        if not isinstance(cfg, Mapping):
            continue
        variants = cfg.get("variants", [])
        if not isinstance(variants, list):
            continue
        for variant in variants:
            if isinstance(variant, Mapping):
                out.append((str(component), variant))
    return out


def build_report(profile_path: Path = PROFILE_PATH) -> dict[str, Any]:
    profiles = json.loads(profile_path.read_text(encoding="utf-8"))
    errors: list[str] = []
    findings: list[dict[str, Any]] = []
    for component, variant in _variant_iter(profiles):
        spec_rel = str(variant.get("spec_path", "")).strip()
        if not spec_rel:
            continue
        spec_path = ROOT / spec_rel
        if not spec_path.exists():
            errors.append(f"{component}.{variant.get('variant_id', '<missing>')}: missing spec {spec_rel}")
            continue
        hits = _add_sub_hits(spec_path)
        if not hits:
            continue

        marker = variant.get("latest_tau_stream_arithmetic")
        expected_status = (
            STRICT_TAU_BLOCKED_STATUS if component in STRICT_TAU_COMPONENTS else GENERIC_BLOCKED_STATUS
        )
        status = marker.get("status") if isinstance(marker, Mapping) else None
        marker_ok = (
            isinstance(marker, Mapping)
            and marker.get("status") == expected_status
            and marker.get("runtime_admission") is False
        )
        finding = {
            "component": component,
            "variant_id": str(variant.get("variant_id", "")),
            "profile": str(variant.get("profile", "")),
            "spec_path": spec_rel,
            "hits": hits,
            "status": status,
            "expected_status": expected_status,
            "marker_ok": bool(marker_ok),
        }
        findings.append(finding)
        if not marker_ok:
            errors.append(
                f"{component}.{variant.get('variant_id', '<missing>')}: bitvector add/sub in {spec_rel} "
                f"requires latest_tau_stream_arithmetic.status={expected_status!r} and runtime_admission=false"
            )

    return {
        "schema": "zenodex/tau-profile-stream-arithmetic/v1",
        "ok": not errors,
        "profile_path": str(profile_path.relative_to(ROOT)),
        "generic_blocked_status": GENERIC_BLOCKED_STATUS,
        "strict_tau_blocked_status": STRICT_TAU_BLOCKED_STATUS,
        "strict_tau_components": sorted(STRICT_TAU_COMPONENTS),
        "findings": findings,
        "errors": errors,
    }


def main() -> int:
    report = build_report()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
