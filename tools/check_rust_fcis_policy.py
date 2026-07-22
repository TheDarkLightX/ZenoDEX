#!/usr/bin/env python3
"""Ratcheted FCIS policy for the consensus-critical Rust core."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
CORE = REPO / "rust-runtime/crates/zenodex-runtime-core/src"
BASELINE = REPO / "config/runtime_fcis/rust_fcis_policy_baseline_v1.json"
RULES = (
    ("UNSAFE", re.compile(r"\bunsafe\b")),
    ("FLOAT", re.compile(r"\b(?:f32|f64)\b")),
    ("HOST_API", re.compile(r"\b(?:std::(?:env|fs|net|process|thread|time)|rand::)")),
    (
        "INTERIOR_MUTABILITY",
        re.compile(r"\b(?:UnsafeCell|Cell|RefCell|Mutex|RwLock|Atomic[A-Za-z0-9_]*)\b"),
    ),
    ("UNORDERED_COLLECTION", re.compile(r"\b(?:HashMap|HashSet)\b")),
    ("PUBLIC_MUT_STATE", re.compile(r"\bpub\s+fn\b[^\n]*&mut\s+[A-Za-z0-9_]*State\b")),
    ("RAW_WIRE_NUMERIC", re.compile(r"\bOption\s*<\s*String\s*>")),
    ("RAW_STRING_REJECT", re.compile(r"Result\s*<[^\n>]+,\s*&(?:'static\s+)?str\s*>")),
    (
        "PANIC_ESCAPE",
        re.compile(r"\b(?:panic!|todo!|unimplemented!|unwrap\s*\(|expect\s*\()"),
    ),
)


@dataclass(frozen=True, order=True)
class Finding:
    rule: str
    path: str
    line: int
    text: str

    @property
    def stable_id(self) -> str:
        normalized = " ".join(self.text.split())
        digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]
        return f"{self.rule}|{self.path}|{digest}"


def scan_source(path: str, text: str) -> tuple[Finding, ...]:
    findings: list[Finding] = []
    in_test_module = False
    pending_test_cfg = False
    for number, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if stripped == "#[cfg(test)]":
            pending_test_cfg = True
            continue
        if pending_test_cfg and re.match(r"(?:pub\s+)?mod\s+tests\b", stripped):
            in_test_module = True
            pending_test_cfg = False
        if in_test_module:
            continue
        pending_test_cfg = False
        code = line.split("//", 1)[0]
        for rule, pattern in RULES:
            if pattern.search(code):
                findings.append(Finding(rule, path, number, stripped))
    return tuple(sorted(findings))


def scan_core() -> tuple[Finding, ...]:
    findings: list[Finding] = []
    for path in sorted(CORE.rglob("*.rs")):
        findings.extend(
            scan_source(
                path.relative_to(REPO).as_posix(),
                path.read_text(encoding="utf-8"),
            )
        )
    return tuple(sorted(findings))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--print-baseline", action="store_true")
    args = parser.parse_args()
    findings = scan_core()
    if args.print_baseline:
        print(json.dumps([item.stable_id for item in findings], indent=2))
        return 0
    raw = json.loads(BASELINE.read_text(encoding="utf-8"))
    if raw.get("schema") != "zenodex/rust_fcis_policy_baseline/v1":
        raise ValueError("invalid Rust FCIS policy baseline schema")
    accepted = frozenset(raw.get("accepted_existing_findings", []))
    current = frozenset(item.stable_id for item in findings)
    unexpected = sorted(current - accepted)
    stale = sorted(accepted - current)
    payload = {
        "schema": "zenodex/rust_fcis_policy_report/v1",
        "claim_status": "released" if args.require_clean and not findings else "blocked",
        "finding_count": len(findings),
        "unexpected_findings": unexpected,
        "stale_baseline_entries": stale,
        "findings": [
            {
                "id": item.stable_id,
                "rule": item.rule,
                "path": item.path,
                "line": item.line,
                "text": item.text,
            }
            for item in findings
        ],
    }
    if unexpected or stale or args.require_clean:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    return 1 if unexpected or stale or (args.require_clean and findings) else 0


if __name__ == "__main__":
    raise SystemExit(main())
