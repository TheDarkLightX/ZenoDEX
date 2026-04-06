#!/usr/bin/env python3
from __future__ import annotations

import argparse
import fnmatch
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PLAN = REPO_ROOT / "formal" / "tau" / "recommended_proof_plan.json"


@dataclass(frozen=True)
class TauFormalPlanResult:
    errors: list[str]
    assignments: dict[str, dict[str, str]]
    rule_hits: dict[str, list[str]]
    unmatched: list[str]


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _match_rule(relpath: str, rule: dict) -> bool:
    name = Path(relpath).name
    for exact in rule.get("include", []):
        if relpath == exact or name == exact:
            return True
    for pattern in rule.get("include_globs", []):
        if fnmatch.fnmatch(relpath, pattern) or fnmatch.fnmatch(name, pattern):
            return True
    return False


def validate_tau_formal_plan(
    plan_path: Path = DEFAULT_PLAN,
    *,
    repo_root: Path = REPO_ROOT,
) -> TauFormalPlanResult:
    raw = _load_json(plan_path)
    errors: list[str] = []

    if raw.get("schema") != "zenodex/tau/formal-proof-plan/v1":
        errors.append(f"{plan_path}: unexpected schema {raw.get('schema')!r}")

    root_value = raw.get("root")
    if not isinstance(root_value, str) or not root_value:
        errors.append(f"{plan_path}: missing root")
        return TauFormalPlanResult(errors=errors, assignments={}, rule_hits={}, unmatched=[])

    spec_root = repo_root / root_value
    if not spec_root.exists():
        errors.append(f"{plan_path}: spec root does not exist: {spec_root}")
        return TauFormalPlanResult(errors=errors, assignments={}, rule_hits={}, unmatched=[])

    profiles_obj = raw.get("profiles")
    if not isinstance(profiles_obj, list) or not profiles_obj:
        errors.append(f"{plan_path}: profiles must be a non-empty list")
        return TauFormalPlanResult(errors=errors, assignments={}, rule_hits={}, unmatched=[])

    profile_ids: set[str] = set()
    for profile in profiles_obj:
        if not isinstance(profile, dict):
            errors.append(f"{plan_path}: profile entries must be objects")
            continue
        pid = str(profile.get("id", "")).strip()
        if not pid:
            errors.append(f"{plan_path}: profile missing id")
            continue
        if pid in profile_ids:
            errors.append(f"{plan_path}: duplicate profile id {pid}")
            continue
        profile_ids.add(pid)

    rules_obj = raw.get("rules")
    if not isinstance(rules_obj, list) or not rules_obj:
        errors.append(f"{plan_path}: rules must be a non-empty list")
        return TauFormalPlanResult(errors=errors, assignments={}, rule_hits={}, unmatched=[])

    rule_ids: set[str] = set()
    rule_hits: dict[str, list[str]] = {}
    for rule in rules_obj:
        if not isinstance(rule, dict):
            errors.append(f"{plan_path}: rule entries must be objects")
            continue
        rid = str(rule.get("id", "")).strip()
        if not rid:
            errors.append(f"{plan_path}: rule missing id")
            continue
        if rid in rule_ids:
            errors.append(f"{plan_path}: duplicate rule id {rid}")
            continue
        rule_ids.add(rid)
        rule_hits[rid] = []
        profile = str(rule.get("profile", "")).strip()
        if profile not in profile_ids:
            errors.append(f"{plan_path}: rule {rid} references unknown profile {profile!r}")
        if not rule.get("include") and not rule.get("include_globs"):
            errors.append(f"{plan_path}: rule {rid} has no include/include_globs")

    spec_files = sorted(
        path.relative_to(spec_root).as_posix()
        for path in spec_root.rglob("*.tau")
        if path.is_file()
    )

    assignments: dict[str, dict[str, str]] = {}
    unmatched: list[str] = []
    for relpath in spec_files:
        assigned = False
        for rule in rules_obj:
            if not isinstance(rule, dict):
                continue
            rid = str(rule.get("id", "")).strip()
            profile = str(rule.get("profile", "")).strip()
            if not rid or not profile:
                continue
            if _match_rule(relpath, rule):
                assignments[relpath] = {"rule": rid, "profile": profile}
                rule_hits[rid].append(relpath)
                assigned = True
                break
        if not assigned:
            unmatched.append(relpath)

    if unmatched:
        errors.append(
            f"{plan_path}: {len(unmatched)} recommended Tau specs are uncovered: {', '.join(unmatched[:8])}"
        )

    for rid, hits in sorted(rule_hits.items()):
        if not hits:
            errors.append(f"{plan_path}: rule {rid} matched no Tau specs")

    for seed in raw.get("seed_artifacts", []):
        if not isinstance(seed, dict):
            errors.append(f"{plan_path}: seed_artifacts entries must be objects")
            continue
        spec_path = repo_root / str(seed.get("spec_path", ""))
        contract_path = repo_root / str(seed.get("contract_path", ""))
        atlas_path = repo_root / str(seed.get("atlas_path", ""))
        if not spec_path.exists():
            errors.append(f"{plan_path}: missing seed spec path {spec_path}")
        if not contract_path.exists():
            errors.append(f"{plan_path}: missing seed contract path {contract_path}")
        if not atlas_path.exists():
            errors.append(f"{plan_path}: missing seed atlas path {atlas_path}")

    return TauFormalPlanResult(
        errors=errors,
        assignments=assignments,
        rule_hits=rule_hits,
        unmatched=unmatched,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate Tau formal proof-plan coverage.")
    parser.add_argument(
        "--plan",
        default=str(DEFAULT_PLAN),
        help="Path to formal/tau proof-plan JSON.",
    )
    args = parser.parse_args()

    result = validate_tau_formal_plan(Path(args.plan))
    if result.errors:
        for error in result.errors:
            print(f"ERROR: {error}")
        return 1

    counts = Counter(v["profile"] for v in result.assignments.values())
    print(f"covered specs: {len(result.assignments)}")
    for profile_id, count in sorted(counts.items()):
        print(f"  {profile_id}: {count}")
    for rule_id, hits in sorted(result.rule_hits.items()):
        print(f"  rule {rule_id}: {len(hits)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
