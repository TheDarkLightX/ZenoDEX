from __future__ import annotations

from dataclasses import replace
from hashlib import sha256
from itertools import permutations
from typing import cast

import pytest

from src.core.fcis_lineage_closure import (
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


def _root(label: str) -> str:
    return f"0x{sha256(label.encode('utf-8')).hexdigest()}"


def _full_seed() -> FCISLineageClaimSetV1:
    claims = tuple(
        FCISLineageClaimV1(key, _root(key.value))
        for key in FCISLineageClaimKeyV1
        if key not in _LINEAGE_DERIVED_KEYS_V1
    )
    return canonicalize_fcis_lineage_claims_v1(claims)


def test_manifest_is_complete_single_writer_and_topologically_canonical() -> None:
    manifest = _LINEAGE_RULE_MANIFEST_V1
    outputs = tuple(rule.output for rule in manifest.rules)
    assert outputs == (
        FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
        FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT,
        FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT,
        FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT,
    )
    assert len(outputs) == len(set(outputs))
    assert set(outputs) == set(manifest.derived_keys)
    positions = {rule.output: index for index, rule in enumerate(manifest.rules)}
    for rule in manifest.rules:
        assert rule.dependencies == tuple(
            sorted(rule.dependencies, key=lambda item: item.value.encode("utf-8"))
        )
        for dependency in rule.dependencies:
            if dependency in positions:
                assert positions[dependency] < positions[rule.output]
    assert manifest.manifest_root == _lineage_rule_manifest_root_v1(
        manifest.rules,
        manifest.derived_keys,
    )


def test_every_rule_permutation_reaches_one_fixed_point() -> None:
    seed = _full_seed()
    results = {
        _close_claims_with_rules_v1(seed, tuple(order))
        for order in permutations(_LINEAGE_RULE_MANIFEST_V1.rules)
    }
    assert len(results) == 1
    closed = next(iter(results))
    assert len(closed.claims) == len(seed.claims) + len(_LINEAGE_DERIVED_KEYS_V1)
    assert all(closed.value_for(key) is not None for key in _LINEAGE_DERIVED_KEYS_V1)


def test_duplicate_writer_and_missing_coverage_reject() -> None:
    manifest = _LINEAGE_RULE_MANIFEST_V1
    duplicate_writer = (*manifest.rules[:-1], manifest.rules[0])
    with pytest.raises(ValueError, match="one writer"):
        _LineageRuleManifestV1(
            duplicate_writer,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(duplicate_writer, manifest.derived_keys),
        )

    missing_writer = manifest.rules[:-1]
    with pytest.raises(ValueError, match="complete derived-key coverage"):
        _LineageRuleManifestV1(
            missing_writer,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(missing_writer, manifest.derived_keys),
        )


def test_cycle_and_noncanonical_order_reject() -> None:
    manifest = _LINEAGE_RULE_MANIFEST_V1
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
    with pytest.raises(ValueError, match="cycle"):
        _LineageRuleManifestV1(
            cyclic_rules,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(cyclic_rules, manifest.derived_keys),
        )

    reversed_rules = tuple(reversed(manifest.rules))
    with pytest.raises(ValueError, match="canonical dependency order"):
        _LineageRuleManifestV1(
            reversed_rules,
            manifest.derived_keys,
            _lineage_rule_manifest_root_v1(reversed_rules, manifest.derived_keys),
        )


def test_manifest_root_and_rule_boundary_reject_tampering() -> None:
    manifest = _LINEAGE_RULE_MANIFEST_V1
    with pytest.raises(ValueError, match="manifest root"):
        _LineageRuleManifestV1(
            manifest.rules,
            manifest.derived_keys,
            "0x" + "0" * 64,
        )

    with pytest.raises(TypeError, match="dependencies"):
        _LineageRuleV1(
            "invalid-dependency-container",
            FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
            cast(tuple[FCISLineageClaimKeyV1, ...], [FCISLineageClaimKeyV1.COMMAND_ROOT]),
        )


def test_closure_test_seam_rejects_another_rule_set() -> None:
    manifest = _LINEAGE_RULE_MANIFEST_V1
    seed = _full_seed()
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
    with pytest.raises(ValueError, match="differ from the validated manifest"):
        _close_claims_with_rules_v1(seed, foreign_rules)
