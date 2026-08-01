"""Deterministic D06 checker for the typed C3 lineage rule manifest."""

from __future__ import annotations

import json
import sys
from dataclasses import replace
from hashlib import sha256
from itertools import permutations
from pathlib import Path
from typing import Callable, cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_lineage_closure import (  # noqa: E402
    _LINEAGE_DERIVED_KEYS_V1,
    _LINEAGE_RULE_MANIFEST_V1,
    FCISLineageClaimKeyV1,
    FCISLineageClaimSetV1,
    FCISLineageClaimV1,
    _close_claims_with_rules_v1,
    _lineage_rule_manifest_root_v1,
    _LineageRuleManifestV1,
    _LineageRuleV1,
    canonicalize_fcis_lineage_claims_v1,
)

_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_D06_RULE_MANIFEST_VECTOR.json"


def _root(label: str) -> str:
    return f"0x{sha256(label.encode('utf-8')).hexdigest()}"


def _read_vector() -> dict[str, object]:
    value = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("D06 vector must be an object")
    return cast(dict[str, object], value)


def _full_seed() -> FCISLineageClaimSetV1:
    claims = tuple(
        FCISLineageClaimV1(key, _root(key.value))
        for key in FCISLineageClaimKeyV1
        if key not in _LINEAGE_DERIVED_KEYS_V1
    )
    return canonicalize_fcis_lineage_claims_v1(claims)


def _expect_reject(label: str, callback: Callable[[], object]) -> None:
    try:
        callback()
    except (TypeError, ValueError):
        return
    raise AssertionError(f"{label} was accepted")


def run_checks() -> None:
    vector = _read_vector()
    manifest = _LINEAGE_RULE_MANIFEST_V1
    if vector.get("manifest_root") != manifest.manifest_root:
        raise AssertionError("D06 vector has the wrong manifest root")
    if vector.get("rule_count") != len(manifest.rules):
        raise AssertionError("D06 vector has the wrong rule count")
    if vector.get("derived_key_count") != len(manifest.derived_keys):
        raise AssertionError("D06 vector has the wrong derived-key count")
    if vector.get("permutation_count") != 24:
        raise AssertionError("D06 vector must cover all 4! rule permutations")
    if vector.get("acyclic") is not True:
        raise AssertionError("D06 vector does not assert acyclicity")
    if vector.get("one_writer") is not True:
        raise AssertionError("D06 vector does not assert single-writer closure")
    if vector.get("complete_coverage") is not True:
        raise AssertionError("D06 vector does not assert complete coverage")
    if vector.get("fixed_point") is not True:
        raise AssertionError("D06 vector does not assert fixed-point termination")
    if vector.get("all_permutations_same_root") is not True:
        raise AssertionError("D06 vector does not assert permutation confluence")

    expected_rules = [
        {
            "rule_id": rule.rule_id,
            "output": rule.output.value,
            "dependencies": [dependency.value for dependency in rule.dependencies],
        }
        for rule in manifest.rules
    ]
    if vector.get("rules") != expected_rules:
        raise AssertionError("D06 vector rules do not match the validated manifest")

    positions = {rule.output: index for index, rule in enumerate(manifest.rules)}
    if len(positions) != len(manifest.rules):
        raise AssertionError("D06 manifest has more than one writer for a derived key")
    if set(positions) != set(manifest.derived_keys):
        raise AssertionError("D06 manifest does not cover every derived key")
    for rule in manifest.rules:
        if rule.dependencies != tuple(
            sorted(rule.dependencies, key=lambda item: item.value.encode("utf-8"))
        ):
            raise AssertionError("D06 dependency tuple is not canonical")
        for dependency in rule.dependencies:
            if dependency in positions and positions[dependency] >= positions[rule.output]:
                raise AssertionError("D06 manifest is not topologically ordered")

    seed = _full_seed()
    results = {
        _close_claims_with_rules_v1(seed, tuple(order)) for order in permutations(manifest.rules)
    }
    if len(results) != 1:
        raise AssertionError("D06 rule permutations reached different fixed points")
    closed = next(iter(results))
    if len(closed.claims) != len(seed.claims) + len(manifest.derived_keys):
        raise AssertionError("D06 closure did not derive every output")
    if any(closed.value_for(key) is None for key in manifest.derived_keys):
        raise AssertionError("D06 closure omitted a derived claim")

    duplicate_writer = (*manifest.rules[:-1], manifest.rules[0])
    _expect_reject(
        "duplicate writer",
        lambda: _LineageRuleManifestV1(
            duplicate_writer,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(duplicate_writer, manifest.derived_keys),
        ),
    )
    missing_writer = manifest.rules[:-1]
    _expect_reject(
        "missing derived-key writer",
        lambda: _LineageRuleManifestV1(
            missing_writer,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(missing_writer, manifest.derived_keys),
        ),
    )

    evaluation = manifest.rules[0]
    cyclic_evaluation = replace(
        evaluation,
        dependencies=tuple(
            sorted(
                (
                    *evaluation.dependencies,
                    FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT,
                ),
                key=lambda item: item.value.encode("utf-8"),
            )
        ),
    )
    cyclic_rules = (cyclic_evaluation, *manifest.rules[1:])
    _expect_reject(
        "cyclic dependency",
        lambda: _LineageRuleManifestV1(
            cyclic_rules,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(cyclic_rules, manifest.derived_keys),
        ),
    )

    reversed_rules = tuple(reversed(manifest.rules))
    _expect_reject(
        "noncanonical rule order",
        lambda: _LineageRuleManifestV1(
            reversed_rules,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(reversed_rules, manifest.derived_keys),
        ),
    )
    _expect_reject(
        "manifest root substitution",
        lambda: _LineageRuleManifestV1(
            manifest.rules,
            manifest.derived_keys,
            "0x" + "0" * 64,
        ),
    )

    foreign_rule = _LineageRuleV1(
        "foreign-rule",
        FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
        tuple(
            sorted(
                (
                    FCISLineageClaimKeyV1.COMMAND_ROOT,
                    FCISLineageClaimKeyV1.EXECUTION_CONTEXT_HASH,
                ),
                key=lambda item: item.value.encode("utf-8"),
            )
        ),
    )
    foreign_rules = (foreign_rule, *manifest.rules[1:])
    _expect_reject(
        "foreign closure rule set",
        lambda: _close_claims_with_rules_v1(seed, foreign_rules),
    )


if __name__ == "__main__":
    run_checks()
    print("D06_LINEAGE_RULE_MANIFEST_MATCH")
