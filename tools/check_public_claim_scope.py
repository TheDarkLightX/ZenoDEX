#!/usr/bin/env python3
"""Check public-facing claim scope for selected ZenoDEX surfaces."""

from __future__ import annotations

import argparse
import json
import re
import shlex
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]

DEFAULT_PUBLIC_CLAIM_PATHS: tuple[str, ...] = (
    "README.md",
    "docs/claims_registry.yaml",
    "docs/ASSURANCE_RELEASE_SNAPSHOT.md",
    "docs/PUBLIC_ASSURANCE_REPLAY.md",
    "docs/RC1_READINESS.md",
    "docs/RC1_SCOPE.md",
    "docs/RC1_VERIFIED_SURFACE_MATRIX.md",
    "docs/zenodex_spot_state_proof_risc0_v1.md",
    "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
    "docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md",
    "docs/CONFIDENTIAL_FEATURES_USE_CASES.md",
    "docs/SPECIFICATION.md",
    "tools/dex-ui/README.md",
    "tools/dex-ui/src/lib/confidentialData.js",
    "src/integration/confidential_feature_status.py",
)

OPTIONAL_PUBLIC_CLAIM_PATHS: tuple[str, ...] = (
    "docs/UPBA_OPTIMALITY_CERTIFICATE.md",
    "docs/UPBA_V1_CERTIFICATE.md",
    "docs/UPBA_V1_EVIDENCE_BOUNDARY.md",
    "docs/UPBA_V2_CERTIFICATE.md",
    "docs/UPBA_V2_EVIDENCE_BOUNDARY.md",
    "docs/ZENOCOVER_LP_LOSS_COVER_V1.md",
)

REQUIRED_ANCHORS: dict[str, tuple[str, ...]] = {
    "README.md": (
        "The current UPBA work is scoped:",
        "UPBA reduces intra-batch ordering MEV. By itself it does not address",
        "This is current local evidence for the restricted guest path.",
        "It does not yet prove the full Python ZenoDEX runtime",
    ),
    "docs/UPBA_V2_CERTIFICATE.md": (
        "Still excluded:",
        "Completeness of the audited set remains a separate obligation",
    ),
    "docs/UPBA_V2_EVIDENCE_BOUNDARY.md": (
        "UPBA v2 does not currently claim:",
        "The v2 claim is narrower:",
    ),
    "docs/zenodex_spot_state_proof_risc0_v1.md": (
        "Transition semantics (v1 scope)",
        "Planned v2 extensions:",
    ),
    "docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md": (
        "This beta covers:",
        "It does not claim:",
    ),
    "docs/CONFIDENTIAL_FEATURES_USE_CASES.md": (
        "What this does not promise",
        "It does not make everything private on-chain.",
        "It does not eliminate all trust.",
    ),
    "tools/dex-ui/README.md": (
        "Confidential exposes live operator posture through `GET /api/confidential/status`",
        "It is not the default swap path",
    ),
    "tools/dex-ui/src/lib/confidentialData.js": (
        "No in-repo proof of TEE hardware confidentiality",
    ),
    "src/integration/confidential_feature_status.py": (
        "no in-repo proof of TEE hardware confidentiality",
    ),
    "docs/ZENOCOVER_LP_LOSS_COVER_V1.md": (
        "Legal and Regulatory Boundary",
        "This replay artifact is not a product launch",
        "Any public or production ZenoCover offering must complete counsel-led",
    ),
}

FORBIDDEN_PUBLIC_REGISTRY_PATH_PREFIXES: tuple[str, ...] = ("internal/", "runs/")


@dataclass(frozen=True)
class ClaimPattern:
    rule_id: str
    pattern: re.Pattern[str]
    message: str


@dataclass(frozen=True)
class ClaimViolation:
    path: str
    line: int
    rule_id: str
    message: str
    text: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "line": self.line,
            "rule_id": self.rule_id,
            "message": self.message,
            "text": self.text,
        }


FORBIDDEN_PATTERNS: tuple[ClaimPattern, ...] = (
    ClaimPattern(
        rule_id="upba_v2_direct_optimal_overclaim",
        pattern=re.compile(
            r"\bUPBA\s+v2\s+"
            r"(?:is|becomes|delivers|provides|guarantees|proves)\s+"
            r"(?:a\s+)?(?:globally\s+)?"
            r"(?:optimal|optimality|volume-maximizing|surplus-maximizing)\b",
            re.IGNORECASE,
        ),
        message="UPBA v2 public claims must stay conditional and bounded.",
    ),
    ClaimPattern(
        rule_id="upba_v2_optimal_title_overclaim",
        pattern=re.compile(
            r"\b(?:optimal|optimality|volume-maximizing|surplus-maximizing)\s+UPBA\s+v2\b",
            re.IGNORECASE,
        ),
        message="Do not title or summarize UPBA v2 as simply optimal.",
    ),
    ClaimPattern(
        rule_id="upba_v2_optimality_proven_overclaim",
        pattern=re.compile(
            r"\bUPBA\s+v2\b.*\b(?:optimality|optimal|volume-maximizing|surplus-maximizing)\b.*"
            r"\b(?:proved|proven|guaranteed|guarantees)\b",
            re.IGNORECASE,
        ),
        message="UPBA v2 optimality claims must stay tied to bounded candidate-completeness evidence.",
    ),
    ClaimPattern(
        rule_id="risc0_full_python_overclaim",
        pattern=re.compile(
            r"\bRisc0\b.*\b(?:proves|proved|proven|guarantees)\b.*"
            r"\b(?:full\s+Python|Python\s+runtime|full\s+runtime)\b",
            re.IGNORECASE,
        ),
        message="Risc0 claims must stay scoped to the current guest subset.",
    ),
    ClaimPattern(
        rule_id="risc0_full_python_reverse_overclaim",
        pattern=re.compile(
            r"\b(?:full\s+Python|Python\s+runtime|full\s+runtime)\b.*"
            r"\b(?:proved|proven|guaranteed)\b.*\bRisc0\b",
            re.IGNORECASE,
        ),
        message="Risc0 claims must not imply a full Python runtime proof.",
    ),
    ClaimPattern(
        rule_id="risc0_full_python_execution_proof_overclaim",
        pattern=re.compile(
            r"\bRisc0\b.*\b(?:full\s+Python|Python\s+runtime|full\s+runtime)\b.*"
            r"\b(?:execution\s+proof|proof\s+of\s+execution|proof)\b",
            re.IGNORECASE,
        ),
        message="Risc0 claims must not imply a full Python execution proof.",
    ),
    ClaimPattern(
        rule_id="tee_complete_confidential_network_overclaim",
        pattern=re.compile(
            r"\bTEE\b.*\b(?:complete|full|fully)\b.*"
            r"\b(?:confidential\s+network|private\s+network|privacy)\b",
            re.IGNORECASE,
        ),
        message="TEE claims must not imply a complete confidential network.",
    ),
    ClaimPattern(
        rule_id="tee_complete_confidential_network_reverse_overclaim",
        pattern=re.compile(
            r"\b(?:complete|full|fully)\b.*\b(?:confidential\s+network|private\s+network)\b.*\bTEE\b",
            re.IGNORECASE,
        ),
        message="TEE claims must not imply a complete confidential network.",
    ),
    ClaimPattern(
        rule_id="tee_trust_privacy_overclaim",
        pattern=re.compile(
            r"\bTEE\b.*\b(?:eliminates\s+all\s+trust|guarantees\s+privacy)\b",
            re.IGNORECASE,
        ),
        message="TEE claims must describe advisory/attestation boundaries.",
    ),
    ClaimPattern(
        rule_id="confidential_verifiable_overclaim",
        pattern=re.compile(
            r"\b(?:verifiably|provably|formally|cryptographically)\s+confidential\b",
            re.IGNORECASE,
        ),
        message="Confidentiality claims must stay scoped to attested admission and redaction evidence.",
    ),
    ClaimPattern(
        rule_id="tee_hardware_confidentiality_proof_overclaim",
        pattern=re.compile(
            r"\b(?:TEE|attestation|attested|receipt)\b.*"
            r"\b(?:proves|proved|proven|guarantees|guaranteed)\b.*"
            r"\b(?:hardware\s+confidentiality|hardware\s+privacy|confidentiality|privacy)\b",
            re.IGNORECASE,
        ),
        message="TEE evidence must not be described as a proof of hardware confidentiality.",
    ),
    ClaimPattern(
        rule_id="hardware_confidentiality_proven_overclaim",
        pattern=re.compile(
            r"\bhardware\s+(?:confidentiality|privacy)\b.*"
            r"\b(?:is\s+)?(?:proved|proven|guaranteed)\b",
            re.IGNORECASE,
        ),
        message="Hardware confidentiality remains an external assumption unless a real hardware proof is supplied.",
    ),
    ClaimPattern(
        rule_id="zenocover_insurance_product_overclaim",
        pattern=re.compile(
            r"\bZenoCover\b.*\b(?:is|offers|provides|sells|underwrites)\b.*"
            r"\b(?:insurance|insurance\s+product|policy|policies)\b",
            re.IGNORECASE,
        ),
        message="ZenoCover public claims must stay research/replay scoped until counsel-led review clears a product path.",
    ),
    ClaimPattern(
        rule_id="zenocover_regulated_launch_overclaim",
        pattern=re.compile(
            r"\bZenoCover\b.*\b(?:launched|live|available|open\s+for\s+purchase|buy\s+coverage)\b",
            re.IGNORECASE,
        ),
        message="ZenoCover must not be described as a live public offering from replay artifacts.",
    ),
    ClaimPattern(
        rule_id="zenocover_underwriting_overclaim",
        pattern=re.compile(
            r"\bZenoCover\b.*\b(?:underwrit(?:e|es|ing)|premium|policyholder|claims?\s+adjust)\b",
            re.IGNORECASE,
        ),
        message="ZenoCover underwriting, premium, policyholder, and claims-processing language needs legal clearance.",
    ),
)


def _normalize_text(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _iter_scannable_lines(text: str) -> Iterable[tuple[int, str]]:
    in_fence = False
    for line_no, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        yield line_no, line


def scan_forbidden_claims(path: str, text: str) -> list[ClaimViolation]:
    violations: list[ClaimViolation] = []
    for line_no, line in _iter_scannable_lines(text):
        for rule in FORBIDDEN_PATTERNS:
            match = rule.pattern.search(line)
            if match is None:
                continue
            if _has_scope_negation_before_match(line, match.start()):
                continue
            if match:
                violations.append(
                    ClaimViolation(
                        path=path,
                        line=line_no,
                        rule_id=rule.rule_id,
                        message=rule.message,
                        text=line.strip(),
                    )
                )
    return violations


def _has_scope_negation_before_match(line: str, match_start: int) -> bool:
    prefix = line[:match_start].lower()
    return any(
        marker in prefix
        for marker in (
            "does not ",
            "do not ",
            "must not ",
            "should not ",
            "not prove ",
            "not imply ",
            "not claim ",
            "not provide ",
        )
    )


def check_required_anchors(path: str, text: str) -> list[ClaimViolation]:
    normalized = _normalize_text(text)
    violations: list[ClaimViolation] = []
    for anchor in REQUIRED_ANCHORS.get(path, ()):
        if _normalize_text(anchor) not in normalized:
            violations.append(
                ClaimViolation(
                    path=path,
                    line=0,
                    rule_id="missing_scope_anchor",
                    message=f"Missing required scope anchor: {anchor}",
                    text="",
                )
            )
    return violations


def _normalize_registry_arg(value: str) -> str:
    normalized = value.strip().replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


def _has_forbidden_public_registry_prefix(value: str) -> bool:
    normalized = _normalize_registry_arg(value)
    return normalized.startswith(FORBIDDEN_PUBLIC_REGISTRY_PATH_PREFIXES)


def _cmd_path_args(cmd: str) -> list[str]:
    try:
        parts = shlex.split(cmd)
    except ValueError:
        parts = cmd.split()
    return [
        part
        for part in parts
        if _has_forbidden_public_registry_prefix(part)
    ]


def check_claims_registry_public_artifact_paths(path: str, text: str) -> list[ClaimViolation]:
    if path != "docs/claims_registry.yaml":
        return []

    violations: list[ClaimViolation] = []
    try:
        root = yaml.safe_load(text)
    except yaml.YAMLError as exc:
        return [
            ClaimViolation(
                path=path,
                line=0,
                rule_id="claims_registry_yaml_parse_error",
                message=f"Could not parse claims registry for public artifact path hygiene: {exc}",
                text="",
            )
        ]

    claims = root.get("claims") if isinstance(root, dict) else None
    if not isinstance(claims, list):
        return violations

    for index, claim in enumerate(claims):
        if not isinstance(claim, dict):
            continue
        claim_id = str(claim.get("id", f"claims[{index}]"))
        evidence = claim.get("evidence")
        if not isinstance(evidence, dict):
            continue
        files = evidence.get("files") or []
        if isinstance(files, list):
            for rel_path in files:
                if isinstance(rel_path, str) and _has_forbidden_public_registry_prefix(rel_path):
                    violations.append(
                        ClaimViolation(
                            path=path,
                            line=0,
                            rule_id="claims_registry_internal_or_runs_evidence_path",
                            message=(
                                "Public claims registry evidence must reference tracked public artifacts, "
                                "not ignored internal/ or runs/ paths."
                            ),
                            text=f"{claim_id}: {rel_path}",
                        )
                    )
        checks = evidence.get("check") or []
        if isinstance(checks, list):
            for check in checks:
                if not isinstance(check, dict):
                    continue
                cmd = check.get("cmd")
                if not isinstance(cmd, str):
                    continue
                for rel_path in _cmd_path_args(cmd):
                    violations.append(
                        ClaimViolation(
                            path=path,
                            line=0,
                            rule_id="claims_registry_internal_or_runs_command_path",
                            message=(
                                "Public claims registry commands must run against tracked public artifacts, "
                                "not ignored internal/ or runs/ paths."
                            ),
                            text=f"{claim_id}: {rel_path}",
                        )
                    )
    return violations


def check_public_claim_scope(
    *,
    root: Path = REPO_ROOT,
    paths: Iterable[str] = DEFAULT_PUBLIC_CLAIM_PATHS,
    optional_paths: Iterable[str] = OPTIONAL_PUBLIC_CLAIM_PATHS,
) -> list[ClaimViolation]:
    violations: list[ClaimViolation] = []
    for rel_path in paths:
        path = root / rel_path
        if not path.is_file():
            violations.append(
                ClaimViolation(
                    path=rel_path,
                    line=0,
                    rule_id="missing_public_claim_file",
                    message="Public claim file is missing.",
                    text="",
                )
            )
            continue
        text = path.read_text(encoding="utf-8")
        violations.extend(check_required_anchors(rel_path, text))
        violations.extend(scan_forbidden_claims(rel_path, text))
        violations.extend(check_claims_registry_public_artifact_paths(rel_path, text))
    for rel_path in optional_paths:
        path = root / rel_path
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        violations.extend(check_required_anchors(rel_path, text))
        violations.extend(scan_forbidden_claims(rel_path, text))
        violations.extend(check_claims_registry_public_artifact_paths(rel_path, text))
    return violations


def checked_public_claim_paths(
    *,
    root: Path = REPO_ROOT,
    paths: Iterable[str] = DEFAULT_PUBLIC_CLAIM_PATHS,
    optional_paths: Iterable[str] = OPTIONAL_PUBLIC_CLAIM_PATHS,
) -> list[str]:
    checked = list(paths)
    checked.extend(rel_path for rel_path in optional_paths if (root / rel_path).is_file())
    return checked


def _report(violations: list[ClaimViolation], *, checked_files: list[str]) -> dict[str, Any]:
    return {
        "schema": "zenodex/public_claim_scope_report/v0",
        "ok": not violations,
        "checked_files": checked_files,
        "violations": [violation.to_dict() for violation in violations],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    args = parser.parse_args(argv)

    violations = check_public_claim_scope(root=args.root)
    payload = _report(violations, checked_files=checked_public_claim_paths(root=args.root))
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    elif violations:
        for violation in violations:
            location = violation.path if violation.line == 0 else f"{violation.path}:{violation.line}"
            print(f"{location}: {violation.rule_id}: {violation.message}", file=sys.stderr)
            if violation.text:
                print(f"  {violation.text}", file=sys.stderr)
    else:
        print("public claim scope ok")
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
