#!/usr/bin/env python3
"""Exact subject binding and execution premise (WholeEconomyDisasterCoverageV1).

The subject binds commit, tree, profile/release root, M6 manifest root,
whole-program requirement root, ShapeForge input root, the three registry
section roots, checker source root, toolchain manifest root, source-pins root,
and the registry SHA-256.  Nothing here is trusted from a packet; the verifier
recomputes it from its own reads.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from tools.runtime_disaster_discovery_primitives_v1 import (
    domain_root,
    require_closed_object,
    require_git_oid,
    require_root,
    require_sha256,
)
from tools.runtime_disaster_discovery_registry_v1 import RegistryV1
from tools.runtime_disaster_discovery_sources_v1 import BoundSourceV1, source_pins_root
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    PLAN_PATH_V1,
    PROFILE_RELEASE_PATH_V1,
    SHAPEFORGE_SEED_PATH_V1,
    ExecutionPremiseV1,
    HeadBindingV1,
    SourceRoleV1,
)


@dataclass(frozen=True, slots=True)
class ExactSubjectV1:
    commit: str
    tree: str
    profile_release_root: str
    m6_manifest_root: str
    whole_program_requirement_root: str
    shapeforge_input_root: str
    obligation_registry_root: str
    runner_registry_root: str
    oracle_registry_root: str
    checker_source_root: str
    toolchain_manifest_root: str
    source_pins_root: str
    registry_sha256: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "commit": self.commit,
            "tree": self.tree,
            "profile_release_root": self.profile_release_root,
            "m6_manifest_root": self.m6_manifest_root,
            "whole_program_requirement_root": self.whole_program_requirement_root,
            "shapeforge_input_root": self.shapeforge_input_root,
            "obligation_registry_root": self.obligation_registry_root,
            "runner_registry_root": self.runner_registry_root,
            "oracle_registry_root": self.oracle_registry_root,
            "checker_source_root": self.checker_source_root,
            "toolchain_manifest_root": self.toolchain_manifest_root,
            "source_pins_root": self.source_pins_root,
            "registry_sha256": self.registry_sha256,
        }

    @property
    def subject_root(self) -> str:
        return domain_root("wedc1-exact-subject", self.to_canonical())


SUBJECT_FIELDS_V1 = tuple(ExactSubjectV1.__dataclass_fields__)


def parse_subject(value: object, name: str) -> ExactSubjectV1:
    raw = require_closed_object(value, SUBJECT_FIELDS_V1, name)
    roots = {
        field: require_root(raw[field], f"{name}.{field}")
        for field in SUBJECT_FIELDS_V1
        if field not in ("commit", "tree", "registry_sha256")
    }
    return ExactSubjectV1(
        commit=require_git_oid(raw["commit"], f"{name}.commit"),
        tree=require_git_oid(raw["tree"], f"{name}.tree"),
        registry_sha256=require_sha256(raw["registry_sha256"], f"{name}.registry_sha256"),
        **roots,
    )


def _pin_root(bound: Mapping[str, BoundSourceV1], path: str) -> str:
    return domain_root("wedc1-pin-root", bound[path].pin.to_canonical())


def _role_root(bound: Mapping[str, BoundSourceV1], role: SourceRoleV1) -> str:
    pins = [source.pin.to_canonical() for source in bound.values() if source.pin.role is role]
    return domain_root(
        "wedc1-role-root",
        {"role": role.value, "pins": sorted(pins, key=lambda pin: str(pin["path"]))},
    )


def compute_subject(
    *,
    commit: str,
    tree: str,
    registry: RegistryV1,
    bound: Mapping[str, BoundSourceV1],
    m6_manifest_root: str,
) -> ExactSubjectV1:
    return ExactSubjectV1(
        commit=require_git_oid(commit, "subject.commit"),
        tree=require_git_oid(tree, "subject.tree"),
        profile_release_root=_pin_root(bound, PROFILE_RELEASE_PATH_V1),
        m6_manifest_root=m6_manifest_root,
        whole_program_requirement_root=_pin_root(bound, PLAN_PATH_V1),
        shapeforge_input_root=_pin_root(bound, SHAPEFORGE_SEED_PATH_V1),
        obligation_registry_root=registry.obligation_registry_root,
        runner_registry_root=registry.runner_registry_root,
        oracle_registry_root=registry.oracle_registry_root,
        checker_source_root=_role_root(bound, SourceRoleV1.CHECKER_SOURCE),
        toolchain_manifest_root=_role_root(bound, SourceRoleV1.TOOLCHAIN),
        source_pins_root=source_pins_root(registry.source_pins),
        registry_sha256=registry.sha256,
    )


def execution_premise(
    worktree_clean: bool | None,
    bound: Mapping[str, BoundSourceV1],
    *,
    registry_head_bound: bool,
) -> ExecutionPremiseV1:
    """Require a clean tree, every pin, and the registry to match captured HEAD."""

    if (
        worktree_clean is True
        and registry_head_bound
        and all(source.head_binding is HeadBindingV1.HEAD_BLOB_MATCH for source in bound.values())
    ):
        return ExecutionPremiseV1.CLEAN_WORKTREE_HEAD_BOUND
    return ExecutionPremiseV1.EXTERNAL_PREMISE_MUTABLE_WORKTREE
