#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import ROOT, extract_stream_types, normalize_spec_text
from tools.check_tau_formal_plan import DEFAULT_PLAN, validate_tau_formal_plan


DEFAULT_CENSUS_PATH = ROOT / "formal" / "tau" / "recommended_execution_census_best.json"
DEFAULT_HARD_SPECS_PATH = ROOT / "formal" / "tau" / "remaining_execution_hard_specs.json"
DEFAULT_CONFIRMED_PATH = ROOT / "formal" / "tau" / "confirmed_semantic_findings.md"
DEFAULT_CONTRACT_PATH = ROOT / "src" / "tau_specs" / "recommended" / "semantic_contracts.json"
DEFAULT_FORMAL_CONTRACTS_DIR = ROOT / "formal" / "tau" / "contracts"
DEFAULT_OUT_JSON = ROOT / "formal" / "tau" / "semantic_understanding_status.json"
DEFAULT_OUT_MD = ROOT / "formal" / "tau" / "semantic_understanding_status.md"
SCHEMA = "zenodex/tau/semantic-understanding-status/v1"


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_execution_index(path: Path) -> dict[str, dict[str, Any]]:
    raw = _load_json(path)
    entries = raw.get("entries", [])
    if not isinstance(entries, list):
        raise TypeError(f"{path}: entries must be a list")
    out: dict[str, dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        spec_id = str(entry.get("spec_id", "")).strip()
        if spec_id:
            out[spec_id] = entry
    return out


def _load_hard_specs(path: Path) -> set[str]:
    raw = _load_json(path)
    if not isinstance(raw, list):
        raise TypeError(f"{path}: expected a list")
    return {str(item).strip() for item in raw if str(item).strip()}


def _load_contract_specs(path: Path) -> set[str]:
    raw = _load_json(path)
    specs = raw.get("specs", [])
    if not isinstance(specs, list):
        raise TypeError(f"{path}: specs must be a list")
    out: set[str] = set()
    for spec in specs:
        if not isinstance(spec, dict):
            continue
        spec_path = str(spec.get("spec_path", "")).strip()
        if spec_path:
            out.add(Path(spec_path).stem)
    return out


def _load_seed_specs(plan_path: Path) -> set[str]:
    raw = _load_json(plan_path)
    seeds = raw.get("seed_artifacts", [])
    if not isinstance(seeds, list):
        raise TypeError(f"{plan_path}: seed_artifacts must be a list")
    out: set[str] = set()
    for seed in seeds:
        if not isinstance(seed, dict):
            continue
        spec_id = str(seed.get("spec_id", "")).strip()
        if spec_id:
            out.add(spec_id)
    return out


def _load_formal_contracts(path: Path) -> dict[str, dict[str, str]]:
    if not path.exists():
        return {}
    status_rank = {"draft": 0, "active": 1, "promoted": 2}
    out: dict[str, dict[str, str]] = {}
    for contract_path in sorted(path.glob("*.contract.json")):
        raw = _load_json(contract_path)
        if not isinstance(raw, dict):
            continue
        spec_id = str(raw.get("spec_id", "")).strip()
        if not spec_id:
            continue
        status = str(raw.get("contract_status", "")).strip()
        scope = str(raw.get("proof_scope", "")).strip()
        prev = out.get(spec_id)
        if prev is None or status_rank.get(status, -1) >= status_rank.get(prev["contract_status"], -1):
            out[spec_id] = {
                "contract_status": status,
                "proof_scope": scope,
                "contract_path": contract_path.relative_to(ROOT).as_posix(),
            }
    return out


def _promotion_blocker(
    *,
    formal_contract_covered: bool,
    formal_contract_status: str,
    proof_scope: str,
) -> str:
    if not formal_contract_covered:
        return "missing_formal_contract"
    if formal_contract_status == "draft":
        return "formal_contract_draft"
    if proof_scope != "full_input_domain":
        return "bounded_scope_only"
    return ""


def _load_confirmed_findings(path: Path) -> dict[str, int]:
    heading_re = re.compile(r"^### `([^`]+)`")
    current_spec = ""
    counts: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        match = heading_re.match(line)
        if match:
            current_spec = match.group(1).strip()
            counts.setdefault(current_spec, 0)
            continue
        if current_spec and line.startswith("- `"):
            counts[current_spec] = counts.get(current_spec, 0) + 1
    return counts


def _predict_style(spec_path: Path) -> tuple[str, int, int]:
    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    stream_types = extract_stream_types(spec_text)
    input_types = [ty for name, ty in stream_types.items() if name.startswith("i")]
    output_types = [ty for name, ty in stream_types.items() if name.startswith("o")]
    if input_types and all(ty == "sbf" for ty in input_types):
        return "host_projected_boolean_gate", len(input_types), len(output_types)
    return "native_tau_guard", len(input_types), len(output_types)


def _understanding_tier(
    *,
    execution_observed: bool,
    structured_hard_review: bool,
    confirmed_findings_count: int,
    semantic_contract_covered: bool,
    bounded_formal_seeded: bool,
) -> tuple[str, int]:
    if bounded_formal_seeded:
        return "bounded_formal_seeded", 5
    if semantic_contract_covered:
        return "semantic_contract_covered", 4
    if confirmed_findings_count > 0:
        return "source_backed_confirmed_review", 3
    if structured_hard_review:
        return "structured_hard_review", 2
    if execution_observed:
        return "execution_observed", 1
    return "syntax_only", 0


def build_semantic_understanding_status(
    *,
    census_path: Path = DEFAULT_CENSUS_PATH,
    hard_specs_path: Path = DEFAULT_HARD_SPECS_PATH,
    confirmed_path: Path = DEFAULT_CONFIRMED_PATH,
    contracts_path: Path = DEFAULT_CONTRACT_PATH,
    formal_contracts_dir: Path = DEFAULT_FORMAL_CONTRACTS_DIR,
    plan_path: Path = DEFAULT_PLAN,
) -> dict[str, Any]:
    plan_result = validate_tau_formal_plan(plan_path)
    if plan_result.errors:
        raise ValueError("formal plan must validate before building status map")

    execution_index = _load_execution_index(census_path)
    hard_specs = _load_hard_specs(hard_specs_path)
    confirmed_findings = _load_confirmed_findings(confirmed_path)
    semantic_contract_specs = _load_contract_specs(contracts_path)
    formal_contracts = _load_formal_contracts(formal_contracts_dir)
    bounded_seed_specs = _load_seed_specs(plan_path)

    spec_paths = sorted((ROOT / "src" / "tau_specs" / "recommended").rglob("*.tau"))
    entries: list[dict[str, Any]] = []
    for spec_path in spec_paths:
        spec_id = spec_path.stem
        relpath = spec_path.relative_to(ROOT / "src" / "tau_specs" / "recommended").as_posix()
        execution = execution_index.get(spec_id, {})
        execution_status = str(execution.get("status", "missing")).strip() or "missing"
        execution_observed = execution_status == "ok"
        predicted_style, input_count, output_count = _predict_style(spec_path)
        confirmed_count = confirmed_findings.get(spec_id, 0)
        structured_hard_review = spec_id in hard_specs
        semantic_contract_covered = spec_id in semantic_contract_specs
        formal_contract_meta = formal_contracts.get(spec_id, {})
        formal_contract_covered = bool(formal_contract_meta)
        formal_contract_status = formal_contract_meta.get("contract_status", "")
        proof_scope = formal_contract_meta.get("proof_scope", "")
        promotion_blocker = _promotion_blocker(
            formal_contract_covered=formal_contract_covered,
            formal_contract_status=formal_contract_status,
            proof_scope=proof_scope,
        )
        bounded_formal_seeded = spec_id in bounded_seed_specs
        tier, tier_rank = _understanding_tier(
            execution_observed=execution_observed,
            structured_hard_review=structured_hard_review,
            confirmed_findings_count=confirmed_count,
            semantic_contract_covered=semantic_contract_covered,
            bounded_formal_seeded=bounded_formal_seeded,
        )
        assignment = plan_result.assignments.get(relpath, {})
        errors = execution.get("errors", [])
        error_types = []
        if isinstance(errors, list):
            for error in errors:
                if isinstance(error, dict):
                    error_type = str(error.get("error_type", "")).strip()
                    if error_type:
                        error_types.append(error_type)

        entries.append(
            {
                "spec_id": spec_id,
                "spec_path": spec_path.relative_to(ROOT).as_posix(),
                "proof_profile": assignment.get("profile", ""),
                "proof_rule": assignment.get("rule", ""),
                "heuristic_style": predicted_style,
                "input_stream_count": input_count,
                "output_stream_count": output_count,
                "execution_status": execution_status,
                "execution_observed": execution_observed,
                "execution_runner": str(execution.get("runner", "")).strip(),
                "execution_error_types": sorted(set(error_types)),
                "structured_hard_review": structured_hard_review,
                "confirmed_findings_count": confirmed_count,
                "lightweight_contract_covered": semantic_contract_covered,
                "semantic_contract_covered": semantic_contract_covered,
                "formal_contract_covered": formal_contract_covered,
                "formal_contract_status": formal_contract_status,
                "proof_scope": proof_scope,
                "promotion_blocker": promotion_blocker,
                "bounded_formal_seeded": bounded_formal_seeded,
                "understanding_tier": tier,
                "understanding_tier_rank": tier_rank,
            }
        )

    tier_counts = Counter(entry["understanding_tier"] for entry in entries)
    style_counts = Counter(entry["heuristic_style"] for entry in entries)
    profile_counts = Counter(entry["proof_profile"] for entry in entries)
    summary = {
        "recommended_spec_count": len(entries),
        "execution_observed_count": sum(1 for entry in entries if entry["execution_observed"]),
        "execution_hard_count": sum(1 for entry in entries if entry["structured_hard_review"]),
        "confirmed_reviewed_spec_count": sum(1 for entry in entries if entry["confirmed_findings_count"] > 0),
        "lightweight_contract_count": sum(1 for entry in entries if entry["lightweight_contract_covered"]),
        "semantic_contract_count": sum(1 for entry in entries if entry["semantic_contract_covered"]),
        "formal_contract_count": sum(1 for entry in entries if entry["formal_contract_covered"]),
        "formal_active_or_promoted_count": sum(
            1 for entry in entries if entry["formal_contract_status"] in {"active", "promoted"}
        ),
        "bounded_formal_seed_count": sum(1 for entry in entries if entry["bounded_formal_seeded"]),
        "tier_counts": dict(sorted(tier_counts.items())),
        "heuristic_style_counts": dict(sorted(style_counts.items())),
        "proof_profile_counts": dict(sorted(profile_counts.items())),
    }

    return {
        "schema": SCHEMA,
        "source_files": {
            "execution_census": census_path.relative_to(ROOT).as_posix(),
            "hard_specs": hard_specs_path.relative_to(ROOT).as_posix(),
            "confirmed_findings": confirmed_path.relative_to(ROOT).as_posix(),
            "semantic_contracts": contracts_path.relative_to(ROOT).as_posix(),
            "formal_contracts_dir": formal_contracts_dir.relative_to(ROOT).as_posix(),
            "formal_plan": plan_path.relative_to(ROOT).as_posix(),
        },
        "summary": summary,
        "entries": entries,
    }


def render_markdown(status: dict[str, Any]) -> str:
    summary = status["summary"]
    lines = [
        "# Tau Semantic Understanding Status",
        "",
        "This artifact tracks what we currently understand about each recommended Tau spec",
        "at the semantic level, using machine-derived tiers rather than prose only.",
        "",
        "## Summary",
        "",
        f"- Recommended specs: `{summary['recommended_spec_count']}`",
        f"- Execution observed: `{summary['execution_observed_count']}`",
        f"- Structured hard-review set: `{summary['execution_hard_count']}`",
        f"- Source-backed confirmed-review specs: `{summary['confirmed_reviewed_spec_count']}`",
        f"- Lightweight semantic-contract specs: `{summary['lightweight_contract_count']}`",
        f"- Formal-contract specs: `{summary['formal_contract_count']}`",
        f"- Formal active/promoted specs: `{summary['formal_active_or_promoted_count']}`",
        f"- Semantic-contract covered specs: `{summary['semantic_contract_count']}`",
        f"- Bounded formal-seed specs: `{summary['bounded_formal_seed_count']}`",
        "",
        "## Understanding Tiers",
        "",
    ]
    for tier, count in sorted(summary["tier_counts"].items()):
        lines.append(f"- `{tier}`: `{count}`")
    lines.extend(["", "## Heuristic Styles", ""])
    for style, count in sorted(summary["heuristic_style_counts"].items()):
        lines.append(f"- `{style}`: `{count}`")
    lines.extend(["", "## Remaining Hard Specs Without Confirmed Findings", ""])
    remaining = [
        entry["spec_id"]
        for entry in status["entries"]
        if entry["structured_hard_review"] and entry["confirmed_findings_count"] == 0
    ]
    if remaining:
        for spec_id in remaining:
            lines.append(f"- `{spec_id}`")
    else:
        lines.append("- None")
    return "\n".join(lines) + "\n"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a repo-wide Tau semantic-understanding status map.")
    parser.add_argument("--out-json", default=str(DEFAULT_OUT_JSON), help="Output JSON path.")
    parser.add_argument("--out-md", default=str(DEFAULT_OUT_MD), help="Output Markdown summary path.")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    status = build_semantic_understanding_status()
    out_json = Path(args.out_json)
    out_md = Path(args.out_md)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    out_md.write_text(render_markdown(status), encoding="utf-8")
    summary = status["summary"]
    print(f"recommended specs: {summary['recommended_spec_count']}")
    print(f"execution observed: {summary['execution_observed_count']}")
    print(f"confirmed reviewed: {summary['confirmed_reviewed_spec_count']}")
    print(f"semantic contracts: {summary['semantic_contract_count']}")
    print(f"bounded formal seeds: {summary['bounded_formal_seed_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
