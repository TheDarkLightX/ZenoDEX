from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DEFAULT_PATHS = (
    "tools/dex-ui/src",
    "tools/dex-ui/README.md",
    "tools/dex-ui/index.html",
)

TEXT_SUFFIXES = {
    ".css",
    ".html",
    ".js",
    ".jsx",
    ".json",
    ".md",
    ".ts",
    ".tsx",
}

SKIP_PARTS = {
    ".git",
    ".lake",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".venv",
    ".venv_audit",
    ".venv_gpu",
    "dist",
    "external",
    "node_modules",
}

USER_FACING_JSX_HINTS = (
    "'",
    '"',
    "`",
    ">",
)


@dataclass(frozen=True)
class Rule:
    rule_id: str
    severity: str
    pattern: re.Pattern[str]
    why: str
    safer_shape: str


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    rule_id: str
    severity: str
    text: str
    why: str
    safer_shape: str


RULES = (
    Rule(
        rule_id="subjective_route_or_price_label",
        severity="high",
        pattern=re.compile(
            r"\b(best|recommended|preferred|safest|most\s+reliable|most\s+profitable)\b"
            r".{0,80}\b(route|venue|pool|path|price|slippage|execution)\b|"
            r"\b(route|venue|pool|path|price|slippage|execution)\b"
            r".{0,80}\b(best|recommended|preferred|safest|most\s+reliable|most\s+profitable)\b",
            re.IGNORECASE,
        ),
        why=(
            "Covered UI posture should avoid subjective commentary on routes, venues, "
            "prices, pools, and slippage."
        ),
        safer_shape=(
            "Use objective labels such as sorted_by_estimated_output, "
            "sorted_by_input_cost, sorted_by_gas_estimate, or user_selected_slippage."
        ),
    ),
    Rule(
        rule_id="recommendation_language",
        severity="medium",
        pattern=re.compile(
            r"\b(recommend|recommended|recommendation|suggest|suggested|suggestion)\b",
            re.IGNORECASE,
        ),
        why=(
            "Recommendation wording can blur educational/default-parameter UI into "
            "advice or solicitation when used around crypto asset securities."
        ),
        safer_shape="Prefer neutral language: default, displayed, calculated, estimated, user-selected.",
    ),
    Rule(
        rule_id="execution_or_settlement_discretion_language",
        severity="medium",
        pattern=re.compile(
            r"\b(execute\s+trade|execute\s+swap|execute\s+order|settle\b|settles\b|"
            r"finalized\s+and\s+ready\s+for\s+settlement)\b",
            re.IGNORECASE,
        ),
        why=(
            "Covered UI posture should make clear that the UI prepares wallet-signable "
            "instructions and does not execute or settle securities transactions."
        ),
        safer_shape="Use prepare, preview, sign in wallet, submitted by wallet, or track on-chain status.",
    ),
    Rule(
        rule_id="custody_or_control_language",
        severity="high",
        pattern=re.compile(
            r"\b(custody|custodial|controls?\s+funds|manages?\s+funds|"
            r"possesses?\s+funds|holds?\s+funds)\b",
            re.IGNORECASE,
        ),
        why=(
            "Covered UI posture depends on self-custody and no provider access to user "
            "funds or private keys."
        ),
        safer_shape="State self-custody precisely: users sign with their wallet; provider has no key or fund access.",
    ),
    Rule(
        rule_id="order_flow_or_affiliate_bias_language",
        severity="high",
        pattern=re.compile(
            r"\b(payment\s+for\s+order\s+flow|PFOF|preferred\s+venue|"
            r"affiliate\s+venue|venue\s+rebate)\b",
            re.IGNORECASE,
        ),
        why=(
            "Covered UI compensation should be objective, disclosed, and route-, venue-, "
            "asset-, and counterparty-agnostic."
        ),
        safer_shape="Use disclosed user-paid fixed fees and objective venue onboarding/audit criteria.",
    ),
)


def should_skip(path: Path) -> bool:
    return any(part in SKIP_PARTS for part in path.parts)


def iter_files(paths: Iterable[str]) -> Iterable[Path]:
    for raw in paths:
        path = Path(raw)
        if not path.exists():
            continue
        if path.is_file():
            if path.suffix in TEXT_SUFFIXES and not should_skip(path):
                yield path
            continue
        for child in path.rglob("*"):
            if child.is_file() and child.suffix in TEXT_SUFFIXES and not should_skip(child):
                yield child


def scan_file(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        text = path.read_text(encoding="utf-8", errors="ignore")
    for line_no, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if path.suffix == ".css" and "content:" not in stripped:
            continue
        if stripped.startswith(("//", "/*", "*", "*/")):
            continue
        if re.search(r"\b(className|class|id|key)\s*=", stripped):
            continue
        if path.suffix in {".js", ".jsx", ".ts", ".tsx"} and not any(
            hint in stripped for hint in USER_FACING_JSX_HINTS
        ):
            continue
        for rule in RULES:
            if rule.pattern.search(stripped):
                findings.append(
                    Finding(
                        path=str(path),
                        line=line_no,
                        rule_id=rule.rule_id,
                        severity=rule.severity,
                        text=stripped[:240],
                        why=rule.why,
                        safer_shape=rule.safer_shape,
                    )
                )
    return findings


def scan_paths(paths: Iterable[str]) -> tuple[list[Path], list[Finding]]:
    files = sorted(set(iter_files(paths)))
    findings: list[Finding] = []
    for path in files:
        findings.extend(scan_file(path))
    return files, findings


def result_payload(files: list[Path], findings: list[Finding]) -> dict[str, object]:
    severity_counts: dict[str, int] = {}
    rule_counts: dict[str, int] = {}
    for finding in findings:
        severity_counts[finding.severity] = severity_counts.get(finding.severity, 0) + 1
        rule_counts[finding.rule_id] = rule_counts.get(finding.rule_id, 0) + 1
    return {
        "schema": "zenodex/covered-ui-lint/v1",
        "source": (
            "SEC staff statement, April 13 2026, broker-dealer registration for "
            "covered crypto asset securities user interfaces"
        ),
        "scanned_file_count": len(files),
        "finding_count": len(findings),
        "severity_counts": severity_counts,
        "rule_counts": rule_counts,
        "findings": [asdict(finding) for finding in findings],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", default=list(DEFAULT_PATHS))
    parser.add_argument("--strict", action="store_true", help="exit non-zero when findings exist")
    args = parser.parse_args()

    files, findings = scan_paths(args.paths)
    print(json.dumps(result_payload(files, findings), indent=2, sort_keys=True))
    return 1 if args.strict and findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
