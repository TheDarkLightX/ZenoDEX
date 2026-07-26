#!/usr/bin/env python3
"""Path-scoped AST checker for the FCIS authority snapshot contract."""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

REPORT_SCHEMA = "zenodex/fcis-authority-snapshot-contract-check/v1"
STATE_SUBSTRATE_AUTHORITY_PATHS = (
    Path("src/state/fcis_committed_state_admission.py"),
    Path("src/state/fcis_committed_state_values.py"),
    Path("src/core/fcis_step_evaluation_values.py"),
    Path("src/core/fcis_step_evaluator.py"),
    Path("src/core/fee_accumulator_transition.py"),
    Path("src/core/nonce_batch_transition.py"),
    Path("src/state/snapshot_combinators.py"),
    Path("src/state/owned_collections.py"),
    Path("src/state/perps_account_transitions.py"),
    Path("src/state/perps_collateral_transitions.py"),
    Path("src/state/perps_funding_transitions.py"),
    Path("src/state/perps_liquidation_transitions.py"),
    Path("src/state/perps_market_param_transitions.py"),
    Path("src/state/perps_aggregate_transitions.py"),
    Path("src/state/perps_settlement_transitions.py"),
    Path("src/state/perps_state_transitions.py"),
    Path("src/state/perps_transition_combinators.py"),
    Path("src/state/lp_duration_transitions.py"),
    Path("src/state/lp_duration_policy_values.py"),
    Path("src/state/lp_duration_policy_schema.py"),
    Path("src/state/lp_duration_policy_admission.py"),
    Path("src/state/lp_duration_policy_context.py"),
    Path("src/state/dex_snapshot_profile.py"),
    Path("src/state/fcis_execution_context_values.py"),
    Path("src/state/fcis_execution_context_schema.py"),
    Path("src/state/fcis_execution_context_codec.py"),
    Path("src/state/fcis_execution_context_admission.py"),
    Path("src/state/fcis_execution_context.py"),
    Path("src/state/pool_creation_transition.py"),
    Path("src/state/state_snapshot_values.py"),
    Path("src/state/state_snapshot_schema.py"),
    Path("src/state/state_admission_profile.py"),
    Path("src/state/state_snapshots.py"),
    Path("src/state/state_transitions.py"),
    Path("src/state/spot_state_transitions.py"),
    Path("src/state/committed_spot_roots.py"),
    Path("src/state/committed_dex_snapshot.py"),
)
AUTHORITY_GRAPH_AUTHORITY_PATHS = (
    Path("src/core/fcis_authority_admission.py"),
    Path("src/core/fcis_authority_dispatch.py"),
    Path("src/core/fcis_authority_schema.py"),
    Path("src/core/fcis_commit_bundle_derivation.py"),
    Path("src/core/fcis_commit_bundle_values.py"),
    Path("src/core/fcis_commit_reference.py"),
    Path("src/core/fcis_decision_values.py"),
    Path("src/core/fcis_decision_derivation.py"),
    Path("src/core/fcis_outbox_values.py"),
    Path("src/core/fcis_transition_budget.py"),
    Path("src/core/fcis_transition_values.py"),
    Path("src/state/state_admission_profile.py"),
    Path("src/state/state_snapshot_schema.py"),
    Path("src/state/owned_json.py"),
    Path("src/state/intent_field_registry.py"),
    Path("src/state/intent_schema.py"),
    Path("src/state/intent_snapshots.py"),
    Path("src/core/settlement_schema.py"),
    Path("src/core/settlement_snapshots.py"),
)
EXACT_REPLAY_AUTHORITY_PATHS = (
    Path("src/core/route_settlement.py"),
    Path("src/core/settlement_strong_validator.py"),
)
EXACT_CONSUMERS_AUTHORITY_PATHS = (
    Path("src/core/fcis_step_evaluator.py"),
    Path("src/core/fcis_commit_bundle_derivation.py"),
    Path("src/core/fcis_commit_reference.py"),
    Path("src/core/fcis_decision_derivation.py"),
    Path("src/core/fcis_state_read_trace_v5.py"),
    Path("src/core/fcis_support_profile_constants_v5.py"),
    Path("src/core/fcis_support_profile_v5.py"),
    Path("src/core/fcis_traced_reads_v5.py"),
    Path("src/core/nonce_batch_transition.py"),
    *EXACT_REPLAY_AUTHORITY_PATHS,
    Path("src/state/support_root.py"),
    Path("src/integration/fcis_spot_shadow.py"),
)
_POST_ADMISSION_MUTATION_FORBIDDEN_PATHS = frozenset(
    str(path) for path in EXACT_CONSUMERS_AUTHORITY_PATHS
)
FINAL_MOUNT_AUTHORITY_PATHS = tuple(
    dict.fromkeys(
        (
            Path("src/core/dex.py"),
            Path("src/core/settlement_strong_validator.py"),
            Path("src/state/legacy_state_snapshots.py"),
            *STATE_SUBSTRATE_AUTHORITY_PATHS,
            *AUTHORITY_GRAPH_AUTHORITY_PATHS,
            *EXACT_REPLAY_AUTHORITY_PATHS,
            *EXACT_CONSUMERS_AUTHORITY_PATHS,
        )
    )
)
DEFAULT_AUTHORITY_PATHS = FINAL_MOUNT_AUTHORITY_PATHS
_AUTHORITY_PATHS_BY_PROFILE = {
    "state-substrate": STATE_SUBSTRATE_AUTHORITY_PATHS,
    "authority-graph": AUTHORITY_GRAPH_AUTHORITY_PATHS,
    "exact-replay": EXACT_REPLAY_AUTHORITY_PATHS,
    "exact-consumers": EXACT_CONSUMERS_AUTHORITY_PATHS,
    "final-mount": FINAL_MOUNT_AUTHORITY_PATHS,
}
_PROFILE_COMPATIBILITY_ALLOWLISTS = {
    "exact-replay": frozenset(
        {
            ("src/core/route_settlement.py", 238, 11, "BROAD_ADMISSION", "str"),
            ("src/core/route_settlement.py", 262, 11, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 265, 11, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 287, 11, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 295, 15, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 304, 15, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 409, 13, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 422, 17, "BROAD_ADMISSION", "Mapping"),
            ("src/core/route_settlement.py", 514, 11, "BROAD_ADMISSION", "str"),
            (
                "src/core/settlement_strong_validator.py",
                499,
                27,
                "COERCIVE_CONTAINER_COPY",
                "tuple",
            ),
            ("src/core/settlement_strong_validator.py", 706, 15, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 710, 15, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 710, 48, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 714, 15, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 716, 15, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 861, 15, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 870, 42, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1428, 15, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1442, 19, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1442, 50, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1722, 15, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1737, 19, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1737, 52, "BROAD_ADMISSION", "str"),
            ("src/core/settlement_strong_validator.py", 1766, 23, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 1768, 23, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 1827, 23, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 1829, 23, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 1927, 20, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 1932, 19, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 2481, 16, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 2487, 16, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 2503, 16, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 2509, 16, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 2525, 16, "BROAD_ADMISSION", "int"),
            ("src/core/settlement_strong_validator.py", 2531, 16, "BROAD_ADMISSION", "int"),
        }
    ),
    "exact-consumers": frozenset(
        {
            ("src/state/support_root.py", 125, 15, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 127, 15, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 129, 15, "BROAD_ADMISSION", "int"),
            ("src/state/support_root.py", 145, 15, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 145, 43, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 148, 19, "BROAD_ADMISSION", "int"),
            ("src/state/support_root.py", 160, 11, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 165, 15, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 170, 15, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 172, 19, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 185, 15, "BROAD_ADMISSION", "str"),
            ("src/state/support_root.py", 335, 19, "BROAD_ADMISSION", "int"),
            ("src/state/support_root.py", 365, 15, "BROAD_ADMISSION", "int"),
            ("src/state/support_root.py", 400, 20, "BROAD_ADMISSION", "int"),
            ("src/state/support_root.py", 404, 16, "BROAD_ADMISSION", "int"),
        }
    ),
}
_PROFILE_COMPATIBILITY_ALLOWLISTS["exact-consumers"] = (
    _PROFILE_COMPATIBILITY_ALLOWLISTS["exact-consumers"]
    | _PROFILE_COMPATIBILITY_ALLOWLISTS["exact-replay"]
)
DEFAULT_REQUIREMENTS_PATH = Path("docs/specs/fcis_authority_snapshot_v1/requirements.json")
DEFAULT_TEST_MATRIX_PATHS = (
    Path("docs/specs/fcis_authority_snapshot_v1/TEST_MATRIX.md"),
    Path("docs/specs/fcis_authority_snapshot_v1/TEST_MATRIX_PR477_PR478.md"),
)
TEST_ID_PATTERN = re.compile(r"FCIS-(?:T-[A-Z0-9-]+|PROP-[0-9]{3})")
_MUTABLE_BUFFER_FREE_MARKER = "FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN"

_BROAD_ISINSTANCE_TARGETS = {
    "Mapping",
    "Sequence",
    "Iterable",
    "int",
    "str",
    "bytes",
    "Enum",
}
_MUTABLE_BASE_NAMES = {
    "dict",
    "list",
    "set",
    "MutableMapping",
    "MutableSequence",
    "MutableSet",
    "BalanceTable",
    "LPTable",
    "NonceTable",
    "PoolState",
    "Intent",
    "Settlement",
    "Fill",
}
_RECONSTRUCTION_METHODS = {
    "__copy__",
    "__deepcopy__",
    "__reduce__",
    "__reduce_ex__",
}
_COERCIVE_CONTAINER_NAMES = {"dict", "list", "tuple"}
_UNTRUSTED_VALUE_NAMES = {
    "command",
    "input",
    "payload",
    "raw",
    "source",
    "state",
    "value",
}
_PROFILE_PATHS = (
    "src/state/state_admission_profile.py",
    "src/state/lp_duration_policy_admission.py",
    "src/state/fcis_execution_context_admission.py",
)
_SHADOW_AUTHORITY_MODULE = "src.integration.fcis_spot_shadow"
_SHADOW_AUTHORITY_PATH = "src/integration/fcis_spot_shadow.py"
_SHADOW_AUTHORITY_RESERVED_TOKENS = (
    "fcis_spot_shadow",
    "evaluate_fcis_spot_candidate_shadow_v1",
    "evaluate_fcis_step_shadow_v1",
)
_UNMOUNTED_EVALUATOR_MODULE = "src.core.fcis_step_evaluator"
_UNMOUNTED_EVALUATOR_ALLOWED_PATHS = (
    "src/core/fcis_step_evaluator.py",
    "src/core/fcis_decision_derivation.py",
    "src/integration/fcis_spot_shadow.py",
)
_UNMOUNTED_EVALUATOR_RESERVED_TOKENS = (
    "fcis_step_evaluator",
    "evaluate_fcis_spot_candidate_v1",
    "evaluate_fcis_step_candidate_v1",
)
_PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST = {
    "_compute_support_state_root_for_batch_owned_admitted_v1": (
        "src/core/fcis_step_evaluator.py",
        "src/state/support_root.py",
    ),
    "_evaluate_settlement_strong_admitted_v1": (
        "src/core/fcis_step_evaluator.py",
        "src/core/settlement_strong_validator.py",
    ),
    "_evaluate_settlement_strong_admitted_observed_v5": (
        "src/core/fcis_step_evaluator.py",
        "src/core/settlement_strong_validator.py",
    ),
    "_validate_and_apply_intent_nonce_batch_admitted_v1": (
        "src/core/fcis_step_evaluator.py",
        "src/core/nonce_batch_transition.py",
    ),
    "_validate_and_apply_intent_nonce_batch_admitted_observed_v5": (
        "src/core/fcis_step_evaluator.py",
        "src/core/nonce_batch_transition.py",
    ),
    "_compute_fcis_support_root_v5_admitted": (
        "src/core/fcis_step_evaluator.py",
        "src/core/fcis_support_profile_v5.py",
    ),
    "_FCISStepEvaluationBoundRejectV1": (
        "src/core/fcis_step_evaluator.py",
        "src/core/fcis_decision_derivation.py",
    ),
    "_evaluate_fcis_step_candidate_bound_v1": (
        "src/core/fcis_step_evaluator.py",
        "src/core/fcis_decision_derivation.py",
    ),
    "_admit_with_registry_v1": _PROFILE_PATHS,
    "_encode_admitted": (
        "src/core/fcis_authority_admission.py",
        "src/state/state_admission_profile.py",
    ),
    "_canonical_authority_claim_bytes_from_encoder_v1": ("src/core/fcis_authority_admission.py",),
    "_CANONICAL_AUTHORITY_CLAIM_BYTES_TOKEN_V1": ("src/core/fcis_authority_admission.py",),
    "_COMMIT_BUNDLE_CONSTRUCTION_TOKEN_V1": ("src/core/fcis_commit_bundle_derivation.py",),
    "_DECISION_CONSTRUCTION_TOKEN_V1": (
        "src/core/fcis_decision_derivation.py",
        "src/core/fcis_commit_bundle_derivation.py",
    ),
    "_claim_root_v1": (
        "src/core/fcis_decision_derivation.py",
        "src/core/fcis_commit_bundle_derivation.py",
    ),
    "_initial_reference_commit_store_v1": ("src/core/fcis_commit_reference.py",),
    "_owned_enum_from_admitted": ("src/state/snapshot_combinators.py",),
    "_owned_enum_from_canonical_transition_v1": ("src/state/pool_creation_transition.py",),
    "_owned_map_from_admitted": ("src/state/snapshot_combinators.py",),
    "_owned_map_from_canonical_transition_v1": ("src/state/state_transitions.py",),
    "_OWNED_ENUM_CONSTRUCTION_TOKEN": ("src/state/owned_collections.py",),
    "_OWNED_MAP_CONSTRUCTION_TOKEN": ("src/state/owned_collections.py",),
    "_ADMISSION_REGISTRY_TOKEN": ("src/state/snapshot_combinators.py",),
    "_VALIDATED_LIMITS_TOKEN": ("src/state/snapshot_combinators.py",),
}

# Unresolved reflection into a module that exports a private authority
# capability is fail-closed.  Direct imports remain governed by the symbol
# allowlist above; dynamic lookup cannot provide equivalent provenance.
_PRIVATE_AUTHORITY_REFLECTION_MODULES = frozenset(
    {
        "src.core.fcis_authority_admission",
        "src.core.fcis_commit_bundle_derivation",
        "src.core.fcis_commit_reference",
        "src.core.fcis_support_profile_v5",
        "src.core.nonce_batch_transition",
        "src.core.settlement_strong_validator",
        "src.state.owned_collections",
        "src.state.pool_creation_transition",
        "src.state.snapshot_combinators",
        "src.state.state_transitions",
        "src.state.support_root",
    }
)
_PRIVATE_AUTHORITY_MODULE_OBJECT_ALLOWLIST = {
    "src.state.snapshot_combinators": ("src/state/state_admission_profile.py",),
}
_PROFILE_ENGINE_NAMES = {
    "snapshot_combinators._admit_with_registry_v1",
    "src.state.snapshot_combinators._admit_with_registry_v1",
}
_LEGACY_MUTABLE_CONSTRUCTORS = {
    "BalanceTable",
    "FeeAccumulatorState",
    "LPTable",
    "NonceTable",
    "OracleState",
    "PerpsState",
    "PoolState",
    "VaultState",
}
_STRUCTURAL_CORE_VIEW_NAMES = {
    "BalanceView",
    "LPView",
    "NonceView",
    "PoolView",
}


def _matches_allowed_path(relative_path: str, allowed_paths: tuple[str, ...]) -> bool:
    return relative_path in allowed_paths


def _is_profile_path(relative_path: str) -> bool:
    return _matches_allowed_path(relative_path, _PROFILE_PATHS)


def _shadow_import_detail(
    relative_path: str,
    module: str,
    imported_name: str | None = None,
    *,
    level: int = 0,
) -> str | None:
    if level:
        package_parts = relative_path.removesuffix(".py").split("/")[:-1]
        retained_parts = len(package_parts) - level + 1
        if retained_parts < 0:
            return None
        module_parts = module.split(".") if module else []
        absolute_module = ".".join((*package_parts[:retained_parts], *module_parts))
    else:
        absolute_module = module
    if absolute_module == _SHADOW_AUTHORITY_MODULE:
        return (
            f"{absolute_module}.{imported_name}" if imported_name is not None else absolute_module
        )
    if absolute_module == "src.integration" and imported_name == "fcis_spot_shadow":
        return f"{absolute_module}.{imported_name}"
    return None


def _unmounted_evaluator_import_detail(
    relative_path: str,
    module: str,
    imported_name: str | None = None,
    *,
    level: int = 0,
) -> str | None:
    if level:
        package_parts = relative_path.removesuffix(".py").split("/")[:-1]
        retained_parts = len(package_parts) - level + 1
        if retained_parts < 0:
            return None
        module_parts = module.split(".") if module else []
        absolute_module = ".".join((*package_parts[:retained_parts], *module_parts))
    else:
        absolute_module = module
    if absolute_module == _UNMOUNTED_EVALUATOR_MODULE:
        return (
            f"{absolute_module}.{imported_name}" if imported_name is not None else absolute_module
        )
    if absolute_module == "src.core" and imported_name == "fcis_step_evaluator":
        return f"{absolute_module}.{imported_name}"
    return None


@dataclass(frozen=True, order=True, slots=True)
class _Violation:
    path: str
    line: int
    column: int
    code: str
    detail: str

    def as_json(self) -> dict[str, object]:
        return {
            "code": self.code,
            "column": self.column,
            "detail": self.detail,
            "line": self.line,
            "path": self.path,
        }


def _node_name(node: ast.AST) -> str | None:
    if type(node) is ast.Name:
        return node.id
    if type(node) is ast.Attribute:
        prefix = _node_name(node.value)
        return node.attr if prefix is None else f"{prefix}.{node.attr}"
    return None


def _last_name(node: ast.AST) -> str | None:
    qualified = _node_name(node)
    if qualified is None:
        return None
    return qualified.rsplit(".", 1)[-1]


class _AuthorityVisitor(ast.NodeVisitor):
    def __init__(self, relative_path: str) -> None:
        self.relative_path = relative_path
        self.violations: list[_Violation] = []
        self.module_aliases: dict[str, str] = {}
        self.name_aliases: dict[str, str] = {}
        self.module_string_constants: dict[str, str] = {}
        self.function_names: list[str] = []
        self.function_parameters: list[set[str]] = []
        self.profile_admit_count = 0
        self.profile_engine_call_count = 0
        self.profile_engine_bound_names: tuple[str, str, str] | None = None

    def _add(self, node: ast.AST, code: str, detail: str) -> None:
        self.violations.append(
            _Violation(
                path=self.relative_path,
                line=getattr(node, "lineno", 0),
                column=getattr(node, "col_offset", 0),
                code=code,
                detail=detail,
            )
        )

    def _resolve(self, node: ast.AST) -> str | None:
        qualified = _node_name(node)
        if qualified is None:
            return None
        head, separator, tail = qualified.partition(".")
        if head in self.name_aliases and not separator:
            return self.name_aliases[head]
        if head in self.module_aliases:
            module = self.module_aliases[head]
            return module if not separator else f"{module}.{tail}"
        return qualified

    def _bounded_static_string(self, node: ast.AST) -> str | None:
        if type(node) is ast.Constant and type(node.value) is str:
            return node.value if len(node.value) <= 256 else None
        if type(node) is ast.Name:
            return self.module_string_constants.get(node.id)
        if type(node) is ast.BinOp and type(node.op) is ast.Add:
            left = self._bounded_static_string(node.left)
            right = self._bounded_static_string(node.right)
            if left is None or right is None or len(left) + len(right) > 256:
                return None
            return left + right
        return None

    def visit_Assign(self, node: ast.Assign) -> None:
        if not self.function_names:
            value = self._bounded_static_string(node.value)
            for target in node.targets:
                if type(target) is not ast.Name:
                    continue
                if value is None:
                    self.module_string_constants.pop(target.id, None)
                else:
                    self.module_string_constants[target.id] = value
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if not self.function_names and type(node.target) is ast.Name:
            value = self._bounded_static_string(node.value) if node.value is not None else None
            if value is None:
                self.module_string_constants.pop(node.target.id, None)
            else:
                self.module_string_constants[node.target.id] = value
        self.generic_visit(node)

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            local_name = alias.asname or alias.name.split(".", 1)[0]
            self.module_aliases[local_name] = alias.name
            module_object_paths = _PRIVATE_AUTHORITY_MODULE_OBJECT_ALLOWLIST.get(
                alias.name,
                (),
            )
            if alias.name in _PRIVATE_AUTHORITY_REFLECTION_MODULES and not _matches_allowed_path(
                self.relative_path,
                module_object_paths,
            ):
                self._add(
                    node,
                    "PRIVATE_AUTHORITY_IMPORT",
                    f"module-object:{alias.name}",
                )
            if alias.name in {"pickle", "copyreg"}:
                self._add(node, "FORBIDDEN_RECONSTRUCTION", alias.name)
            shadow_detail = _shadow_import_detail(self.relative_path, alias.name)
            if shadow_detail is not None and self.relative_path != _SHADOW_AUTHORITY_PATH:
                self._add(node, "SHADOW_AUTHORITY_IMPORT", shadow_detail)
            evaluator_detail = _unmounted_evaluator_import_detail(
                self.relative_path,
                alias.name,
            )
            if evaluator_detail is not None and not _matches_allowed_path(
                self.relative_path,
                _UNMOUNTED_EVALUATOR_ALLOWED_PATHS,
            ):
                self._add(node, "UNMOUNTED_EVALUATOR_IMPORT", evaluator_detail)
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        module = node.module or ""
        for alias in node.names:
            local_name = alias.asname or alias.name
            qualified = f"{module}.{alias.name}" if module else alias.name
            self.name_aliases[local_name] = qualified
            module_object_paths = _PRIVATE_AUTHORITY_MODULE_OBJECT_ALLOWLIST.get(
                qualified,
                (),
            )
            if qualified in _PRIVATE_AUTHORITY_REFLECTION_MODULES and not _matches_allowed_path(
                self.relative_path,
                module_object_paths,
            ):
                self._add(
                    node,
                    "PRIVATE_AUTHORITY_IMPORT",
                    f"module-object:{qualified}",
                )
            if module == "copy" and alias.name in {"copy", "deepcopy"}:
                self._add(node, "FORBIDDEN_COPY", qualified)
            if module in {"pickle", "copyreg"}:
                self._add(node, "FORBIDDEN_RECONSTRUCTION", qualified)
            if alias.name == "deep_freeze":
                self._add(node, "GENERIC_DEEP_FREEZE", qualified)
            if module == "typing" and alias.name == "Any":
                self._add(node, "OPEN_AUTHORITY_TYPE", qualified)
            if module == "dataclasses" and alias.name == "is_dataclass":
                self._add(node, "REFLECTIVE_ADMISSION", qualified)
            shadow_detail = _shadow_import_detail(
                self.relative_path,
                module,
                alias.name,
                level=node.level,
            )
            if shadow_detail is not None and self.relative_path != _SHADOW_AUTHORITY_PATH:
                self._add(node, "SHADOW_AUTHORITY_IMPORT", shadow_detail)
            evaluator_detail = _unmounted_evaluator_import_detail(
                self.relative_path,
                module,
                alias.name,
                level=node.level,
            )
            if evaluator_detail is not None and not _matches_allowed_path(
                self.relative_path,
                _UNMOUNTED_EVALUATOR_ALLOWED_PATHS,
            ):
                self._add(node, "UNMOUNTED_EVALUATOR_IMPORT", evaluator_detail)
            allowed_paths = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(alias.name)
            if allowed_paths is not None and not _matches_allowed_path(
                self.relative_path,
                allowed_paths,
            ):
                self._add(node, "PRIVATE_AUTHORITY_IMPORT", qualified)
        self.generic_visit(node)

    def visit_Name(self, node: ast.Name) -> None:
        resolved = self._resolve(node)
        if resolved == "typing.Any" or node.id == "Any":
            self._add(node, "OPEN_AUTHORITY_TYPE", resolved or node.id)
        if node.id == "_snapshot_sealed":
            self._add(node, "SNAPSHOT_SEAL_FLAG", node.id)
        if (
            self.relative_path != _SHADOW_AUTHORITY_PATH
            and node.id in _SHADOW_AUTHORITY_RESERVED_TOKENS
        ):
            self._add(node, "SHADOW_AUTHORITY_IMPORT", node.id)
        if (
            not _matches_allowed_path(
                self.relative_path,
                _UNMOUNTED_EVALUATOR_ALLOWED_PATHS,
            )
            and node.id in _UNMOUNTED_EVALUATOR_RESERVED_TOKENS
        ):
            self._add(node, "UNMOUNTED_EVALUATOR_IMPORT", node.id)
        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if self._resolve(node) == "typing.Any":
            self._add(node, "OPEN_AUTHORITY_TYPE", "typing.Any")
        if node.attr == "_snapshot_sealed":
            self._add(node, "SNAPSHOT_SEAL_FLAG", node.attr)
        allowed_paths = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(node.attr)
        if allowed_paths is not None and not _matches_allowed_path(
            self.relative_path,
            allowed_paths,
        ):
            # Attribute capture is equivalent to importing the private capability.
            self._add(node, "PRIVATE_AUTHORITY_IMPORT", self._resolve(node) or node.attr)
        reflected_base = self._resolve(node.value)
        if node.attr == "__dict__" and reflected_base in _PRIVATE_AUTHORITY_REFLECTION_MODULES:
            self._add(
                node,
                "PRIVATE_AUTHORITY_IMPORT",
                f"module-dict:{reflected_base}",
            )
        if (
            self.relative_path != _SHADOW_AUTHORITY_PATH
            and node.attr in _SHADOW_AUTHORITY_RESERVED_TOKENS
        ):
            self._add(node, "SHADOW_AUTHORITY_IMPORT", node.attr)
        if (
            not _matches_allowed_path(
                self.relative_path,
                _UNMOUNTED_EVALUATOR_ALLOWED_PATHS,
            )
            and node.attr in _UNMOUNTED_EVALUATOR_RESERVED_TOKENS
        ):
            self._add(node, "UNMOUNTED_EVALUATOR_IMPORT", node.attr)
        self.generic_visit(node)

    def visit_Constant(self, node: ast.Constant) -> None:
        if (
            self.relative_path != _SHADOW_AUTHORITY_PATH
            and type(node.value) is str
            and any(token in node.value for token in _SHADOW_AUTHORITY_RESERVED_TOKENS)
        ):
            # A reserved lexical token closes ordinary dynamic-import aliases,
            # local bindings, and forward declarations without attempting to
            # execute caller-controlled Python during the static check.
            self._add(node, "SHADOW_AUTHORITY_IMPORT", node.value)
        if (
            not _matches_allowed_path(
                self.relative_path,
                _UNMOUNTED_EVALUATOR_ALLOWED_PATHS,
            )
            and type(node.value) is str
            and any(token in node.value for token in _UNMOUNTED_EVALUATOR_RESERVED_TOKENS)
        ):
            self._add(node, "UNMOUNTED_EVALUATOR_IMPORT", node.value)
        if type(node.value) is str and node.value == "_snapshot_sealed":
            self._add(node, "SNAPSHOT_SEAL_FLAG", node.value)
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        symbol = (
            node.slice.value
            if type(node.slice) is ast.Constant and type(node.slice.value) is str
            else None
        )
        allowed_paths = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(symbol or "")
        if allowed_paths is not None and not _matches_allowed_path(
            self.relative_path,
            allowed_paths,
        ):
            # Reflective dictionary lookup imports the same private capability as
            # direct attribute access; spelling must not weaken the boundary.
            self._add(node, "PRIVATE_AUTHORITY_IMPORT", symbol or "")
        if self._resolve(node.value) == "sys.modules":
            module_name = self._bounded_static_string(node.slice)
            if module_name in _PRIVATE_AUTHORITY_REFLECTION_MODULES:
                self._add(
                    node,
                    "PRIVATE_AUTHORITY_IMPORT",
                    f"sys.modules:{module_name}",
                )
        self.generic_visit(node)

    def _claim_typed_parameter_names(
        self,
        node: ast.FunctionDef | ast.AsyncFunctionDef,
    ) -> frozenset[str]:
        names: set[str] = set()
        for argument in (
            *node.args.posonlyargs,
            *node.args.args,
            *node.args.kwonlyargs,
        ):
            if argument.annotation is None:
                continue
            annotation_names = {
                resolved.rsplit(".", maxsplit=1)[-1]
                for part in ast.walk(argument.annotation)
                if (resolved := self._resolve(part)) is not None
            }
            if any(name.endswith("ClaimV1") for name in annotation_names):
                names.add(argument.arg)
        return frozenset(names)

    @staticmethod
    def _expression_uses_names(
        expression: ast.AST,
        names: frozenset[str] | set[str],
    ) -> bool:
        return any(type(part) is ast.Name and part.id in names for part in ast.walk(expression))

    @staticmethod
    def _assigned_names(node: ast.AST) -> tuple[str, ...]:
        if type(node) is ast.Assign:
            return tuple(
                name for target in node.targets for name in _assignment_target_names(target)
            )
        if type(node) is ast.AnnAssign:
            return _assignment_target_names(node.target)
        if type(node) is ast.NamedExpr:
            return _assignment_target_names(node.target)
        return ()

    @staticmethod
    def _assigned_value(node: ast.AST) -> ast.AST | None:
        if type(node) in {ast.Assign, ast.AnnAssign, ast.NamedExpr}:
            return node.value
        return None

    @staticmethod
    def _sink_tokens() -> tuple[str, ...]:
        return ("commit", "publish", "persist", "deliver", "apply", "write")

    @classmethod
    def _is_direct_tainted_value(
        cls,
        expression: ast.AST,
        tainted_names: set[str],
    ) -> bool:
        if type(expression) is ast.Name:
            return expression.id in tainted_names
        if type(expression) in {ast.Attribute, ast.Starred, ast.Subscript}:
            return cls._is_direct_tainted_value(expression.value, tainted_names)
        if type(expression) in {ast.List, ast.Set, ast.Tuple}:
            return any(
                cls._is_direct_tainted_value(element, tainted_names) for element in expression.elts
            )
        if type(expression) is ast.Dict:
            return any(
                cls._is_direct_tainted_value(value, tainted_names) for value in expression.values
            )
        if type(expression) is ast.Lambda:
            return cls._expression_uses_names(expression, tainted_names)
        return False

    def _record_tainted_assignment_escape(
        self,
        expression: ast.AST,
        tainted_names: set[str],
        escaping_names: set[str],
    ) -> bool:
        assigned_value = self._assigned_value(expression)
        if assigned_value is None or not self._expression_uses_names(
            assigned_value,
            tainted_names,
        ):
            return False
        assigned_names = self._assigned_names(expression)
        targets = expression.targets if type(expression) is ast.Assign else (expression.target,)
        if any(type(target) in {ast.Attribute, ast.Subscript} for target in targets):
            self._add(expression, "CLAIM_AUTHORITY_ESCAPE", "nonlocal storage")
        if escaping_names.intersection(assigned_names):
            self._add(expression, "CLAIM_AUTHORITY_ESCAPE", "global/nonlocal storage")
        previous_size = len(tainted_names)
        tainted_names.update(assigned_names)
        return len(tainted_names) != previous_size

    def _propagate_claim_taint(
        self,
        expressions: tuple[ast.AST, ...],
        tainted_names: set[str],
        escaping_names: set[str],
    ) -> None:
        changed = True
        while changed:
            changed = False
            for expression in expressions:
                changed = (
                    self._record_tainted_assignment_escape(
                        expression,
                        tainted_names,
                        escaping_names,
                    )
                    or changed
                )

    def _record_tainted_call_escape(
        self,
        expression: ast.AST,
        tainted_names: set[str],
    ) -> None:
        if type(expression) is not ast.Call:
            return
        call_values = (
            *expression.args,
            *(keyword.value for keyword in expression.keywords),
        )
        tainted_argument = any(
            self._expression_uses_names(value, tainted_names) for value in call_values
        )
        tainted_callable = type(expression.func) is ast.Name and expression.func.id in tainted_names
        if tainted_argument or tainted_callable:
            self._add(
                expression,
                "CLAIM_AUTHORITY_ESCAPE",
                self._resolve(expression.func) or "<dynamic call>",
            )

    def _record_direct_claim_escape(
        self,
        expression: ast.AST,
        tainted_names: set[str],
    ) -> None:
        if (
            type(expression) in {ast.Return, ast.Yield, ast.YieldFrom}
            and expression.value is not None
            and self._is_direct_tainted_value(expression.value, tainted_names)
        ):
            self._add(expression, "CLAIM_AUTHORITY_ESCAPE", "returned/yielded claim")

    def _check_claim_authority_escape(
        self,
        node: ast.FunctionDef | ast.AsyncFunctionDef,
    ) -> None:
        claim_parameters = self._claim_typed_parameter_names(node)
        if not claim_parameters:
            return
        if any(token in node.name.lower() for token in self._sink_tokens()):
            self._add(node, "CLAIM_AUTHORITY_ESCAPE", node.name)
            return
        expressions = tuple(ast.walk(node))
        escaping_names = {
            name
            for expression in expressions
            if type(expression) in {ast.Global, ast.Nonlocal}
            for name in expression.names
        }
        tainted_names = set(claim_parameters)
        self._propagate_claim_taint(expressions, tainted_names, escaping_names)
        for expression in expressions:
            self._record_tainted_call_escape(expression, tainted_names)
            self._record_direct_claim_escape(expression, tainted_names)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._check_claim_authority_escape(node)
        if node.name in _RECONSTRUCTION_METHODS:
            self._add(node, "FORBIDDEN_RECONSTRUCTION", node.name)
        if node.name.startswith("to_scratch_") and self.relative_path.startswith(
            ("src/core/", "src/state/")
        ):
            self._add(node, "MUTABLE_CORE_BOUNDARY", node.name)
        if self.relative_path == "src/state/intent_snapshots.py" and node.name in {
            "snapshot_intent",
            "admit_intent_batch",
        }:
            body = node.body
            if (
                body
                and type(body[0]) is ast.Expr
                and type(body[0].value) is ast.Constant
                and type(body[0].value.value) is str
            ):
                body = body[1:]
            while body and type(body[0]) in {ast.Import, ast.ImportFrom}:
                body = body[1:]
            first_statement = body[0] if body else None
            direct_admission = (
                type(first_statement) is ast.Assign
                and len(first_statement.targets) == 1
                and type(first_statement.targets[0]) is ast.Name
                and first_statement.targets[0].id == "admitted"
                and type(first_statement.value) is ast.Call
                and _last_name(first_statement.value.func) == "_admit_graph_value"
                and len(first_statement.value.args) == 2
                and type(first_statement.value.args[1]) is ast.Name
                and first_statement.value.args[1].id == "source"
                and not first_statement.value.keywords
            )
            guard_statement = body[1] if len(body) > 1 else None
            guard_calls = (
                tuple(
                    expression
                    for expression in ast.walk(guard_statement.test)
                    if type(expression) is ast.Call
                )
                if type(guard_statement) is ast.If
                else ()
            )
            exact_guard = (
                type(guard_statement) is ast.If
                and len(guard_statement.body) == 1
                and type(guard_statement.body[0]) is ast.Raise
                and not guard_statement.orelse
                and bool(guard_calls)
                and all(_last_name(call.func) in {"any", "type"} for call in guard_calls)
                and not any(
                    type(expression) in {ast.Assign, ast.AnnAssign, ast.NamedExpr}
                    for expression in ast.walk(guard_statement.test)
                )
            )
            return_statement = body[2] if len(body) > 2 else None
            exact_return = type(return_statement) is ast.Return and (
                (
                    type(return_statement.value) is ast.Name
                    and return_statement.value.id == "admitted"
                )
                or (
                    type(return_statement.value) is ast.Call
                    and _last_name(return_statement.value.func) == "cast"
                    and len(return_statement.value.args) == 2
                    and type(return_statement.value.args[1]) is ast.Name
                    and return_statement.value.args[1].id == "admitted"
                    and not return_statement.value.keywords
                )
            )
            source_reused = any(
                type(expression) is ast.Name
                and expression.id == "source"
                and type(expression.ctx) is ast.Load
                for statement in body[1:]
                for expression in ast.walk(statement)
            )
            if not (
                len(body) == 3
                and not node.decorator_list
                and direct_admission
                and exact_guard
                and exact_return
                and not source_reused
            ):
                self._add(node, "MANUAL_SOURCE_PROJECTION", node.name)
        if not node.name.startswith("_"):
            annotations = tuple(
                annotation
                for annotation in (
                    node.returns,
                    *(argument.annotation for argument in node.args.posonlyargs),
                    *(argument.annotation for argument in node.args.args),
                    *(argument.annotation for argument in node.args.kwonlyargs),
                )
                if annotation is not None
            )
            for annotation in annotations:
                for annotation_node in ast.walk(annotation):
                    annotation_name = _last_name(annotation_node)
                    if annotation_name in _STRUCTURAL_CORE_VIEW_NAMES:
                        self._add(
                            annotation_node,
                            "STRUCTURAL_CORE_BOUNDARY",
                            annotation_name,
                        )
        if (
            _is_profile_path(self.relative_path)
            and not self.function_names
            and not node.name.startswith("_")
            and node.name != "admit"
        ):
            self._add(node, "PROFILE_FACADE_SHAPE", f"extra public function:{node.name}")
        if (
            _is_profile_path(self.relative_path)
            and not self.function_names
            and node.name == "admit"
        ):
            self.profile_admit_count += 1
            positional_names = tuple(argument.arg for argument in node.args.args)
            if (
                node.args.posonlyargs
                or positional_names
                != ("schema_revision", "schema_id", "validated_limits", "source")
                or node.args.vararg is not None
                or node.args.kwonlyargs
                or node.args.kwarg is not None
                or node.args.defaults
                or node.args.kw_defaults
            ):
                self._add(node, "PROFILE_FACADE_SHAPE", "admit signature")
            body = node.body
            if (
                body
                and type(body[0]) is ast.Expr
                and type(body[0].value) is ast.Constant
                and type(body[0].value.value) is str
            ):
                body = body[1:]
            direct_engine_return = (
                len(body) == 1
                and type(body[0]) is ast.Return
                and type(body[0].value) is ast.Call
                and self._resolve(body[0].value.func) in _PROFILE_ENGINE_NAMES
            )
            if node.decorator_list or not direct_engine_return:
                # Authority invariant: the facade cannot discard, wrap, or replace
                # the closed interpreter result with caller-controlled output.
                self._add(node, "PROFILE_FACADE_SHAPE", "admit direct return")
        self.function_names.append(node.name)
        self.function_parameters.append(self._parameter_names(node.args))
        try:
            self.generic_visit(node)
        finally:
            self.function_parameters.pop()
            self.function_names.pop()

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._check_claim_authority_escape(node)
        if node.name in _RECONSTRUCTION_METHODS:
            self._add(node, "FORBIDDEN_RECONSTRUCTION", node.name)
        if _is_profile_path(self.relative_path) and not self.function_names:
            self._add(node, "PROFILE_FACADE_SHAPE", f"async function:{node.name}")
        self.function_names.append(node.name)
        self.function_parameters.append(self._parameter_names(node.args))
        try:
            self.generic_visit(node)
        finally:
            self.function_parameters.pop()
            self.function_names.pop()

    @staticmethod
    def _parameter_names(arguments: ast.arguments) -> set[str]:
        names = {
            argument.arg
            for argument in (
                *arguments.posonlyargs,
                *arguments.args,
                *arguments.kwonlyargs,
            )
        }
        if arguments.vararg is not None:
            names.add(arguments.vararg.arg)
        if arguments.kwarg is not None:
            names.add(arguments.kwarg.arg)
        return names

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        if (
            self.relative_path == "src/state/intent_snapshots.py"
            and node.name == "_IntentAdmissionSourceV1"
        ):
            self._add(node, "MANUAL_SOURCE_PROJECTION", node.name)
        if _is_profile_path(self.relative_path) and not node.name.startswith("_"):
            self._add(node, "PROFILE_FACADE_SHAPE", f"public class:{node.name}")
        for base in node.bases:
            base_name = _last_name(base)
            if base_name in _MUTABLE_BASE_NAMES:
                self._add(node, "MUTABLE_BASE", base_name)
        dataclass_decorator = next(
            (
                decorator
                for decorator in node.decorator_list
                if (
                    _last_name(decorator) == "dataclass"
                    or (type(decorator) is ast.Call and _last_name(decorator.func) == "dataclass")
                )
            ),
            None,
        )
        frozen_dataclass = type(dataclass_decorator) is ast.Call and any(
            keyword.arg == "frozen"
            and type(keyword.value) is ast.Constant
            and keyword.value.value is True
            for keyword in dataclass_decorator.keywords
        )
        if dataclass_decorator is not None and not frozen_dataclass:
            self._add(node, "MUTABLE_CORE_STATE", node.name)
        frozen_dataclass = any(
            type(decorator) is ast.Call
            and _last_name(decorator.func) == "dataclass"
            and any(
                keyword.arg == "frozen"
                and type(keyword.value) is ast.Constant
                and keyword.value.value is True
                for keyword in decorator.keywords
            )
            for decorator in node.decorator_list
        )
        if frozen_dataclass:
            for statement in node.body:
                if type(statement) is not ast.AnnAssign:
                    continue
                for annotation_node in ast.walk(statement.annotation):
                    if _last_name(annotation_node) in {"set", "frozenset"}:
                        self._add(
                            statement,
                            "OPEN_AUTHORITY_SCHEMA",
                            _last_name(annotation_node) or "set",
                        )
                        break
        if node.name in {
            "EnumRegistrationV1",
            "RecordRegistrationV1",
            "SchemaRegistrationV1",
        }:
            for statement in node.body:
                if type(statement) is not ast.AnnAssign:
                    continue
                if any(
                    _last_name(annotation_node) == "Callable"
                    for annotation_node in ast.walk(statement.annotation)
                ):
                    self._add(
                        statement,
                        "REGISTRY_BEHAVIOR_FIELD",
                        node.name,
                    )
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        called = self._resolve(node.func)
        called_tail = called.rsplit(".", 1)[-1] if called is not None else None
        if called_tail == "deep_freeze":
            self._add(node, "GENERIC_DEEP_FREEZE", called or called_tail)
        if _is_profile_path(self.relative_path) and called_tail in _LEGACY_MUTABLE_CONSTRUCTORS:
            self._add(
                node,
                "LEGACY_MUTABLE_CONSTRUCTION",
                called or called_tail or "",
            )
        if (
            called
            in {
                "getattr",
                "builtins.getattr",
                "setattr",
                "builtins.setattr",
                "delattr",
                "builtins.delattr",
            }
            and len(node.args) >= 2
        ):
            symbol = self._bounded_static_string(node.args[1])
            allowed_paths = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(symbol or "")
            if allowed_paths is not None and not _matches_allowed_path(
                self.relative_path,
                allowed_paths,
            ):
                # Statically resolvable reflection is authority import by
                # another spelling.
                self._add(node, "PRIVATE_AUTHORITY_IMPORT", symbol or "")
            reflected_base = self._resolve(node.args[0])
            if symbol is None and reflected_base in _PRIVATE_AUTHORITY_REFLECTION_MODULES:
                self._add(
                    node,
                    "PRIVATE_AUTHORITY_IMPORT",
                    f"dynamic:{reflected_base}",
                )
        if called_tail == "vars" and node.args:
            reflected_base = self._resolve(node.args[0])
            if reflected_base in _PRIVATE_AUTHORITY_REFLECTION_MODULES:
                self._add(
                    node,
                    "PRIVATE_AUTHORITY_IMPORT",
                    f"module-vars:{reflected_base}",
                )
        if called in {"copy.copy", "copy.deepcopy"}:
            self._add(node, "FORBIDDEN_COPY", called)
        if (
            called
            in {
                "__import__",
                "builtins.__import__",
                "importlib.import_module",
            }
            and node.args
            and self._bounded_static_string(node.args[0]) in _PRIVATE_AUTHORITY_REFLECTION_MODULES
        ):
            self._add(
                node,
                "PRIVATE_AUTHORITY_IMPORT",
                f"dynamic-module:{self._bounded_static_string(node.args[0])}",
            )
        if (
            called
            in {
                "__import__",
                "builtins.__import__",
                "importlib.import_module",
            }
            and node.args
            and self._bounded_static_string(node.args[0]) == _SHADOW_AUTHORITY_MODULE
            and self.relative_path != _SHADOW_AUTHORITY_PATH
        ):
            self._add(node, "SHADOW_AUTHORITY_IMPORT", _SHADOW_AUTHORITY_MODULE)
        if (
            called
            in {
                "__import__",
                "builtins.__import__",
                "importlib.import_module",
            }
            and node.args
            and self._bounded_static_string(node.args[0]) == _UNMOUNTED_EVALUATOR_MODULE
            and not _matches_allowed_path(
                self.relative_path,
                _UNMOUNTED_EVALUATOR_ALLOWED_PATHS,
            )
        ):
            self._add(
                node,
                "UNMOUNTED_EVALUATOR_IMPORT",
                _UNMOUNTED_EVALUATOR_MODULE,
            )
        if called is not None and called.split(".", 1)[0] in {"pickle", "copyreg"}:
            self._add(node, "FORBIDDEN_RECONSTRUCTION", called)
        if called in {"dataclasses.is_dataclass", "is_dataclass"}:
            self._add(node, "REFLECTIVE_ADMISSION", called)
        if called == "object.__new__":
            self._add(node, "CONSTRUCTOR_BYPASS", called)
        if self.relative_path in _POST_ADMISSION_MUTATION_FORBIDDEN_PATHS and called in {
            "object.__delattr__",
            "object.__setattr__",
            "type.__delattr__",
            "type.__setattr__",
        }:
            self._add(node, "OWNED_VALUE_MUTATION_BYPASS", called)
        if called in {"isinstance", "builtins.isinstance"} and len(node.args) >= 2:
            targets = node.args[1].elts if type(node.args[1]) is ast.Tuple else (node.args[1],)
            broad = sorted(
                target_name
                for target in targets
                if (target_name := _last_name(target)) in _BROAD_ISINSTANCE_TARGETS
            )
            if broad:
                self._add(node, "BROAD_ADMISSION", ",".join(broad))
        if called_tail in _COERCIVE_CONTAINER_NAMES and node.args:
            first_argument = node.args[0]
            current_parameters = self.function_parameters[-1] if self.function_parameters else set()
            if (
                called in _COERCIVE_CONTAINER_NAMES
                or called in {f"builtins.{name}" for name in _COERCIVE_CONTAINER_NAMES}
            ) and (
                type(first_argument) is ast.Name
                and (
                    first_argument.id in _UNTRUSTED_VALUE_NAMES
                    or first_argument.id in current_parameters
                )
            ):
                self._add(node, "COERCIVE_CONTAINER_COPY", called or called_tail)
        if called_tail in {
            "_owned_enum_from_admitted",
            "_owned_enum_from_canonical_transition_v1",
            "_owned_map_from_admitted",
            "_owned_map_from_canonical_transition_v1",
        } and not (
            called_tail in {"_owned_enum_from_admitted", "_owned_map_from_admitted"}
            and self.relative_path == "src/state/snapshot_combinators.py"
            or called_tail == "_owned_enum_from_canonical_transition_v1"
            and self.relative_path == "src/state/pool_creation_transition.py"
            or called_tail == "_owned_map_from_canonical_transition_v1"
            and self.relative_path == "src/state/state_transitions.py"
        ):
            self._add(node, "OWNED_CONSTRUCTION_ESCAPE", called or called_tail)
        if called_tail == "_admit_with_registry_v1":
            if not _is_profile_path(self.relative_path):
                self._add(node, "PROFILE_BINDING_ESCAPE", called or called_tail)
            elif called not in _PROFILE_ENGINE_NAMES:
                self._add(node, "PROFILE_FACADE_SHAPE", "noncanonical engine binding")
            else:
                self.profile_engine_call_count += 1
                parameter_names = (
                    self.function_parameters[-1] if self.function_parameters else set()
                )
                bound_names = (
                    (node.args[0], node.args[5], node.args[6]) if len(node.args) == 7 else ()
                )
                bound_name_values = tuple(
                    argument.id if type(argument) is ast.Name else None for argument in bound_names
                )
                bound_inputs_are_private = bool(bound_name_values) and all(
                    name is not None and name.startswith("_") and name not in parameter_names
                    for name in bound_name_values
                )
                forwarded_names = tuple(
                    argument.id if type(argument) is ast.Name else None
                    for argument in node.args[1:5]
                )
                if (
                    not self.function_names
                    or self.function_names[-1] != "admit"
                    or len(node.args) != 7
                    or node.keywords
                    or not bound_inputs_are_private
                    or forwarded_names
                    != ("schema_revision", "schema_id", "validated_limits", "source")
                ):
                    self._add(node, "PROFILE_FACADE_SHAPE", "engine binding")
                elif self.profile_engine_bound_names is None:
                    registry_name, constructor_name, encoder_name = bound_name_values
                    if (
                        registry_name is not None
                        and constructor_name is not None
                        and encoder_name is not None
                    ):
                        self.profile_engine_bound_names = (
                            registry_name,
                            constructor_name,
                            encoder_name,
                        )
        if called_tail == "build_admission_registry_v1" and not _is_profile_path(
            self.relative_path
        ):
            self._add(node, "REGISTRY_BINDING_ESCAPE", called or called_tail)
        construction_allowlist = {
            "AdmissionRegistryV1": (
                (
                    "src/state/snapshot_combinators.py",
                    "build_admission_registry_v1",
                ),
            ),
            "OwnedMapV1": (
                (
                    "src/state/owned_collections.py",
                    "_owned_map_from_admitted",
                ),
                (
                    "src/state/owned_collections.py",
                    "_owned_map_from_canonical_transition_v1",
                ),
            ),
            "OwnedEnumV1": (
                (
                    "src/state/owned_collections.py",
                    "_owned_enum_from_admitted",
                ),
                (
                    "src/state/owned_collections.py",
                    "_owned_enum_from_canonical_transition_v1",
                ),
            ),
            "ValidatedAdmissionLimitsV1": (
                (
                    "src/state/snapshot_combinators.py",
                    "build_admission_limits_v1",
                ),
            ),
            "CanonicalAuthorityClaimBytesV1": (
                (
                    "src/core/fcis_authority_admission.py",
                    "_canonical_authority_claim_bytes_from_encoder_v1",
                ),
            ),
            "CommitBundleV1": (
                (
                    "src/core/fcis_commit_bundle_derivation.py",
                    "_build_bundle_v1",
                ),
            ),
        }
        required_sites = construction_allowlist.get(called_tail or "")
        current_function = self.function_names[-1] if self.function_names else None
        if required_sites is not None and not any(
            self.relative_path == required_path and current_function == required_function
            for required_path, required_function in required_sites
        ):
            required_text = "|".join(
                f"{required_path}:{required_function}"
                for required_path, required_function in required_sites
            )
            self._add(
                node,
                "CONSTRUCTION_CALLSITE",
                (f"{called_tail}:{current_function or '<module>'}:required={required_text}"),
            )
        if called_tail in {"owned_type", "source_type"}:
            self._add(node, "DECLARATIVE_REGISTRY_EXECUTION", called or called_tail)
        if called == "issubclass" and len(node.args) >= 2:
            if _last_name(node.args[1]) == "Enum":
                self._add(node, "REFLECTIVE_ADMISSION", "issubclass(..., Enum)")
        self.generic_visit(node)

    def finalize(self, module: ast.Module) -> list[_Violation]:
        if not _is_profile_path(self.relative_path):
            return []
        if self.profile_admit_count != 1:
            self._add(module, "PROFILE_FACADE_SHAPE", "exactly one module admit")
        if self.profile_engine_call_count != 1:
            self._add(module, "PROFILE_FACADE_SHAPE", "exactly one engine call")
        if self.profile_engine_bound_names is not None:
            registry_name, constructor_name, encoder_name = self.profile_engine_bound_names
            assignments, functions = self._module_bindings(module)
            if assignments.get(registry_name, 0) != 1 or functions.get(registry_name):
                self._add(module, "PROFILE_FACADE_SHAPE", "module-owned registry binding")
            if not _has_registry_manifest_binding(module, registry_name):
                self._add(
                    module,
                    "PROFILE_REGISTRY_BINDING",
                    f"{registry_name}.schema_ids",
                )
            for resolver_name in (constructor_name, encoder_name):
                resolver_functions = functions.get(resolver_name, ())
                if assignments.get(resolver_name, 0) or len(resolver_functions) != 1:
                    self._add(
                        module,
                        "PROFILE_FACADE_SHAPE",
                        f"module-owned resolver binding:{resolver_name}",
                    )
                    continue
                if resolver_functions[0].decorator_list:
                    self._add(
                        resolver_functions[0],
                        "PROFILE_FACADE_SHAPE",
                        f"decorated resolver:{resolver_name}",
                    )
        return self.violations

    @staticmethod
    def _module_bindings(
        module: ast.Module,
    ) -> tuple[dict[str, int], dict[str, tuple[ast.FunctionDef, ...]]]:
        assignments: dict[str, int] = {}
        functions_mutable: dict[str, list[ast.FunctionDef]] = {}
        for statement in module.body:
            targets: tuple[ast.AST, ...] = ()
            if type(statement) is ast.Assign:
                targets = tuple(statement.targets)
            elif type(statement) is ast.AnnAssign:
                targets = (statement.target,)
            elif type(statement) is ast.AugAssign:
                targets = (statement.target,)
            for target in targets:
                if type(target) is ast.Name:
                    assignments[target.id] = assignments.get(target.id, 0) + 1
            if type(statement) is ast.FunctionDef:
                functions_mutable.setdefault(statement.name, []).append(statement)
            elif type(statement) is ast.AsyncFunctionDef:
                # An async resolver is behavior-bearing but cannot satisfy the
                # synchronous exact-function profile contract.
                assignments[statement.name] = assignments.get(statement.name, 0) + 1
        functions = {name: tuple(declarations) for name, declarations in functions_mutable.items()}
        return assignments, functions


def _has_registry_manifest_binding(module: ast.Module, registry_name: str) -> bool:
    matches = 0
    for statement in module.body:
        if type(statement) is not ast.If or statement.orelse:
            continue
        comparison = statement.test
        if (
            type(comparison) is not ast.Compare
            or len(comparison.ops) != 1
            or type(comparison.ops[0]) is not ast.NotEq
            or len(comparison.comparators) != 1
        ):
            continue
        left = comparison.left
        right = comparison.comparators[0]
        if not (
            type(left) is ast.Attribute
            and left.attr == "schema_ids"
            and type(left.value) is ast.Name
            and left.value.id == registry_name
            and type(right) is ast.Name
            and right.id == "FCIS_REGISTERED_REGISTRY_IDS"
        ):
            continue
        if len(statement.body) != 1 or type(statement.body[0]) is not ast.Raise:
            continue
        exception = statement.body[0].exc
        if (
            type(exception) is not ast.Call
            or type(exception.func) is not ast.Name
            or exception.func.id != "RuntimeError"
            or len(exception.args) != 1
            or exception.keywords
            or type(exception.args[0]) is not ast.Constant
            or type(exception.args[0].value) is not str
            or not exception.args[0].value
        ):
            continue
        matches += 1
    return matches == 1


def _assignment_string_tuple(module: ast.Module, name: str) -> tuple[str, ...] | None:
    for statement in module.body:
        target: ast.AST | None = None
        value: ast.AST | None = None
        if type(statement) is ast.Assign and len(statement.targets) == 1:
            target = statement.targets[0]
            value = statement.value
        elif type(statement) is ast.AnnAssign:
            target = statement.target
            value = statement.value
        if type(target) is not ast.Name or target.id != name or type(value) is not ast.Tuple:
            continue
        strings: list[str] = []
        for element in value.elts:
            if type(element) is not ast.Constant or type(element.value) is not str:
                return None
            strings.append(element.value)
        return tuple(strings)
    return None


def _module_exact_true(module: ast.Module, name: str) -> bool:
    for statement in module.body:
        target: ast.AST | None = None
        value: ast.AST | None = None
        if type(statement) is ast.Assign and len(statement.targets) == 1:
            target = statement.targets[0]
            value = statement.value
        elif type(statement) is ast.AnnAssign:
            target = statement.target
            value = statement.value
        if type(target) is not ast.Name or target.id != name:
            continue
        return type(value) is ast.Constant and type(value.value) is bool and value.value is True
    return False


def _mutable_buffer_kind(node: ast.AST) -> str | None:
    if type(node) in {ast.List, ast.ListComp}:
        return "list"
    if type(node) in {ast.Dict, ast.DictComp}:
        return "dict"
    if type(node) in {ast.Set, ast.SetComp}:
        return "set"
    if type(node) is ast.Call and _last_name(node.func) in {"dict", "list", "set"}:
        return _last_name(node.func)
    return None


def _check_mutable_local_buffers(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    if not _module_exact_true(module, _MUTABLE_BUFFER_FREE_MARKER):
        return []
    violations: list[_Violation] = []
    for node in ast.walk(module):
        detail = _mutable_buffer_kind(node)
        if detail is not None:
            violations.append(
                _Violation(
                    relative_path,
                    getattr(node, "lineno", 0),
                    getattr(node, "col_offset", 0),
                    "MUTABLE_LOCAL_BUFFER",
                    detail,
                )
            )
    return violations


def _check_registry_constants(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    is_profile = _is_profile_path(relative_path)
    drift_code = "PROFILE_REGISTRY_DRIFT" if is_profile else "REGISTRY_DRIFT"
    required = _assignment_string_tuple(module, "FCIS_REQUIRED_REGISTRY_IDS")
    registered = _assignment_string_tuple(module, "FCIS_REGISTERED_REGISTRY_IDS")
    if required is None and registered is None:
        return (
            [_Violation(relative_path, 0, 0, drift_code, "missing registry tuples")]
            if is_profile
            else []
        )
    if required is None or registered is None:
        return [_Violation(relative_path, 0, 0, drift_code, "missing registry tuple")]
    if is_profile and not required:
        return [_Violation(relative_path, 0, 0, drift_code, "empty production registry")]
    if len(required) != len(set(required)) or len(registered) != len(set(registered)):
        return [_Violation(relative_path, 0, 0, drift_code, "duplicate registry ID")]
    missing = sorted(set(required) - set(registered))
    extra = sorted(set(registered) - set(required))
    violations: list[_Violation] = []
    for registry_id in missing:
        violations.append(_Violation(relative_path, 0, 0, drift_code, f"missing:{registry_id}"))
    for registry_id in extra:
        violations.append(_Violation(relative_path, 0, 0, drift_code, f"extra:{registry_id}"))
    return violations


def _scoped_path(repo_root: Path, relative_path: Path) -> Path | None:
    root = repo_root.resolve()
    candidate = (
        relative_path.resolve() if relative_path.is_absolute() else (root / relative_path).resolve()
    )
    if candidate != root and root not in candidate.parents:
        return None
    return candidate


def _function_calls(function: ast.FunctionDef) -> tuple[ast.Call, ...]:
    return tuple(node for node in ast.walk(function) if type(node) is ast.Call)


def _normalized_annotation(annotation: ast.expr | None) -> str:
    return "" if annotation is None else ast.unparse(annotation).replace(" ", "")


def _assignment_target_names(target: ast.AST) -> tuple[str, ...]:
    if type(target) is ast.Name:
        return (target.id,)
    if type(target) is ast.Starred:
        return _assignment_target_names(target.value)
    if type(target) in {ast.List, ast.Tuple}:
        return tuple(name for element in target.elts for name in _assignment_target_names(element))
    return ()


class _FunctionBindingCollector(ast.NodeVisitor):
    """Collect local binding sites without entering nested execution scopes."""

    def __init__(self, protected_names: frozenset[str]) -> None:
        self._protected_names = protected_names
        self.sites: dict[str, list[ast.AST]] = {name: [] for name in sorted(protected_names)}

    def _record_name(self, name: str | None, node: ast.AST) -> None:
        if name in self._protected_names:
            self.sites[name].append(node)

    def _record_target(self, target: ast.AST, node: ast.AST) -> None:
        for name in _assignment_target_names(target):
            self._record_name(name, node)

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self._record_target(target, node)
        self.visit(node.value)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self._record_target(node.target, node)
        self.visit(node.annotation)
        if node.value is not None:
            self.visit(node.value)

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self._record_target(node.target, node)
        self.visit(node.value)

    def visit_NamedExpr(self, node: ast.NamedExpr) -> None:
        self._record_target(node.target, node)
        self.visit(node.value)

    def visit_For(self, node: ast.For) -> None:
        self._record_target(node.target, node)
        self.visit(node.iter)
        for statement in (*node.body, *node.orelse):
            self.visit(statement)

    def visit_AsyncFor(self, node: ast.AsyncFor) -> None:
        self.visit_For(node)

    def visit_comprehension(self, node: ast.comprehension) -> None:
        self._record_target(node.target, node)
        self.visit(node.iter)
        for condition in node.ifs:
            self.visit(condition)

    def visit_With(self, node: ast.With) -> None:
        for item in node.items:
            self.visit(item.context_expr)
            if item.optional_vars is not None:
                self._record_target(item.optional_vars, node)
        for statement in node.body:
            self.visit(statement)

    def visit_AsyncWith(self, node: ast.AsyncWith) -> None:
        self.visit_With(node)

    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        self._record_name(node.name, node)
        if node.type is not None:
            self.visit(node.type)
        for statement in node.body:
            self.visit(statement)

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            self._record_name(alias.asname or alias.name.split(".", maxsplit=1)[0], node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        for alias in node.names:
            self._record_name(alias.asname or alias.name, node)

    def visit_Delete(self, node: ast.Delete) -> None:
        for target in node.targets:
            self._record_target(target, node)

    def visit_Global(self, node: ast.Global) -> None:
        for name in node.names:
            self._record_name(name, node)

    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        for name in node.names:
            self._record_name(name, node)

    def visit_MatchAs(self, node: ast.MatchAs) -> None:
        self._record_name(node.name, node)
        if node.pattern is not None:
            self.visit(node.pattern)

    def visit_MatchStar(self, node: ast.MatchStar) -> None:
        self._record_name(node.name, node)

    def visit_MatchMapping(self, node: ast.MatchMapping) -> None:
        self._record_name(node.rest, node)
        for key in node.keys:
            self.visit(key)
        for pattern in node.patterns:
            self.visit(pattern)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._record_name(node.name, node)
        self._visit_nested_definition_expressions(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._record_name(node.name, node)
        self._visit_nested_definition_expressions(node)

    def _visit_nested_definition_expressions(
        self,
        node: ast.FunctionDef | ast.AsyncFunctionDef,
    ) -> None:
        for expression in (
            *node.decorator_list,
            *node.args.defaults,
            *(default for default in node.args.kw_defaults if default is not None),
        ):
            self.visit(expression)

    def visit_Lambda(self, node: ast.Lambda) -> None:
        for expression in (
            *node.args.defaults,
            *(default for default in node.args.kw_defaults if default is not None),
        ):
            self.visit(expression)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._record_name(node.name, node)
        for expression in (
            *node.decorator_list,
            *node.bases,
            *(keyword.value for keyword in node.keywords),
        ):
            self.visit(expression)


def _function_binding_sites(
    function: ast.FunctionDef,
    protected_names: tuple[str, ...],
) -> dict[str, tuple[ast.AST, ...]]:
    collector = _FunctionBindingCollector(frozenset(protected_names))
    for argument in (
        *function.args.posonlyargs,
        *function.args.args,
        *function.args.kwonlyargs,
    ):
        collector._record_name(argument.arg, argument)
    if function.args.vararg is not None:
        collector._record_name(function.args.vararg.arg, function.args.vararg)
    if function.args.kwarg is not None:
        collector._record_name(function.args.kwarg.arg, function.args.kwarg)
    for statement in function.body:
        collector.visit(statement)
    return {name: tuple(collector.sites[name]) for name in sorted(collector.sites)}


def _has_single_bindings(
    function: ast.FunctionDef,
    protected_names: tuple[str, ...],
) -> bool:
    sites = _function_binding_sites(function, protected_names)
    return all(len(sites[name]) == 1 for name in protected_names)


def _has_named_call_assignment(
    function: ast.FunctionDef,
    *,
    target_name: str,
    call_name: str,
    positional_names: tuple[str, ...],
) -> bool:
    for node in ast.walk(function):
        if type(node) is not ast.Assign or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if type(target) is not ast.Name or target.id != target_name:
            continue
        if type(node.value) is not ast.Call or _last_name(node.value.func) != call_name:
            continue
        actual_names = tuple(
            argument.id if type(argument) is ast.Name else "" for argument in node.value.args
        )
        if actual_names == positional_names and not node.value.keywords:
            return True
    return False


def _has_named_tuple_assignment(
    function: ast.FunctionDef,
    *,
    target_names: tuple[str, ...],
    source_name: str,
) -> bool:
    for node in ast.walk(function):
        if type(node) is not ast.Assign or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if type(target) is not ast.Tuple or type(node.value) is not ast.Name:
            continue
        actual_names = tuple(item.id if type(item) is ast.Name else "" for item in target.elts)
        if actual_names == target_names and node.value.id == source_name:
            return True
    return False


def _has_named_tuple_return(function: ast.FunctionDef, names: tuple[str, ...]) -> bool:
    for node in ast.walk(function):
        if type(node) is not ast.Return or type(node.value) is not ast.Tuple:
            continue
        actual_names = tuple(item.id if type(item) is ast.Name else "" for item in node.value.elts)
        if actual_names == names:
            return True
    return False


def _is_named_tuple_return(node: ast.Return, names: tuple[str, ...]) -> bool:
    if type(node.value) is not ast.Tuple:
        return False
    actual_names = tuple(item.id if type(item) is ast.Name else "" for item in node.value.elts)
    return actual_names == names


def _is_named_reject_return(node: ast.Return, call_name: str) -> bool:
    return type(node.value) is ast.Call and _last_name(node.value.func) == call_name


def _call_has_named_keywords(call: ast.Call, expected: dict[str, str]) -> bool:
    actual = {
        keyword.arg: keyword.value.id
        for keyword in call.keywords
        if keyword.arg is not None and type(keyword.value) is ast.Name
    }
    return all(actual.get(keyword) == value_name for keyword, value_name in expected.items())


def _check_exact_replay_shape(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    if relative_path != "src/core/settlement_strong_validator.py":
        return []
    functions = {
        statement.name: statement for statement in module.body if type(statement) is ast.FunctionDef
    }
    required_names = (
        "_admit_exact_commands_v1",
        "evaluate_settlement_strong_committed_v1",
        "_evaluate_settlement_strong_admitted_v1",
        "_evaluate_settlement_strong_replay_committed_v1",
        "_validate_settlement_strong_impl",
    )
    missing = tuple(name for name in required_names if name not in functions)
    if missing:
        return [
            _Violation(
                relative_path,
                0,
                0,
                "EXACT_REPLAY_ENTRY_SHAPE",
                f"missing:{','.join(missing)}",
            )
        ]

    entry = functions["evaluate_settlement_strong_committed_v1"]
    annotations = {argument.arg: argument.annotation for argument in entry.args.kwonlyargs}
    expected_annotations = {
        "settlement": "OwnedSettlementV1",
        "intents": "tuple[OwnedIntentV1,...]",
        "pre_balances": "CommittedBalanceTableV1",
        "pre_pools": "OwnedMapV1[str,CommittedPoolStateV1]",
        "pre_lp_balances": "CommittedLPTableV1",
    }
    violations: list[_Violation] = []
    for field, expected in expected_annotations.items():
        actual = _normalized_annotation(annotations.get(field))
        if actual != expected:
            violations.append(
                _Violation(
                    relative_path,
                    entry.lineno,
                    entry.col_offset,
                    "EXACT_REPLAY_ENTRY_SHAPE",
                    f"annotation:{field}:{actual or '<missing>'}",
                )
            )

    entry_calls = {_last_name(call.func) for call in _function_calls(entry)}
    for required_call in (
        "_admit_exact_commands_v1",
        "_evaluate_settlement_strong_admitted_v1",
    ):
        if required_call not in entry_calls:
            violations.append(
                _Violation(
                    relative_path,
                    entry.lineno,
                    entry.col_offset,
                    "EXACT_REPLAY_ENTRY_SHAPE",
                    f"missing-call:{required_call}",
                )
            )

    admission = functions["_admit_exact_commands_v1"]
    admission_calls = {_last_name(call.func) for call in _function_calls(admission)}
    for required_call in ("snapshot_settlement", "admit_intent_batch"):
        if required_call not in admission_calls:
            violations.append(
                _Violation(
                    relative_path,
                    admission.lineno,
                    admission.col_offset,
                    "EXACT_REPLAY_ENTRY_SHAPE",
                    f"missing-admission:{required_call}",
                )
            )

    if not _has_named_call_assignment(
        admission,
        target_name="exact_settlement",
        call_name="snapshot_settlement",
        positional_names=("settlement",),
    ) or not _has_named_call_assignment(
        admission,
        target_name="exact_intents",
        call_name="admit_intent_batch",
        positional_names=("intents",),
    ):
        violations.append(
            _Violation(
                relative_path,
                admission.lineno,
                admission.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "admission-results-not-bound",
            )
        )
    if not _has_single_bindings(
        admission,
        ("exact_settlement", "exact_intents"),
    ):
        violations.append(
            _Violation(
                relative_path,
                admission.lineno,
                admission.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "admission-exact-values-rebound",
            )
        )
    if not _has_named_tuple_return(admission, ("exact_settlement", "exact_intents")):
        violations.append(
            _Violation(
                relative_path,
                admission.lineno,
                admission.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "admission-results-not-returned",
            )
        )
    admission_returns = tuple(node for node in ast.walk(admission) if type(node) is ast.Return)
    invalid_admission_returns = tuple(
        node
        for node in admission_returns
        if not _is_named_tuple_return(node, ("exact_settlement", "exact_intents"))
        and not _is_named_reject_return(node, "_strong_reject_v1")
    )
    for invalid_return in invalid_admission_returns:
        violations.append(
            _Violation(
                relative_path,
                invalid_return.lineno,
                invalid_return.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "admission-has-raw-or-unknown-return",
            )
        )

    if not _has_named_call_assignment(
        entry,
        target_name="command",
        call_name="_admit_exact_commands_v1",
        positional_names=("settlement", "intents"),
    ) or not _has_named_tuple_assignment(
        entry,
        target_names=("exact_settlement", "exact_intents"),
        source_name="command",
    ):
        violations.append(
            _Violation(
                relative_path,
                entry.lineno,
                entry.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "entry-does-not-destructure-admitted-command",
            )
        )
    if not _has_single_bindings(
        entry,
        ("command", "exact_settlement", "exact_intents"),
    ):
        violations.append(
            _Violation(
                relative_path,
                entry.lineno,
                entry.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "entry-exact-values-rebound",
            )
        )

    common_arguments = {
        "settlement": "exact_settlement",
        "intents": "exact_intents",
        "pre_balances": "pre_balances",
        "pre_pools": "pre_pools",
        "pre_lp_balances": "pre_lp_balances",
        "now": "now",
        "min_lp_position_age_seconds": "min_lp_position_age_seconds",
        "lp_duration_policy": "lp_duration_policy",
        "mode": "mode",
        "allow_cow_netting": "allow_cow_netting",
        "allow_snapshot_bound_quote_bindings": "allow_snapshot_bound_quote_bindings",
        "protocol_fee_share_bps": "protocol_fee_share_bps",
        "protocol_fee_recipient_pubkey": "protocol_fee_recipient_pubkey",
    }
    if not _single_exact_call_v1(
        entry,
        call_name="_evaluate_settlement_strong_admitted_v1",
        keywords=common_arguments,
    ):
        violations.append(
            _Violation(
                relative_path,
                entry.lineno,
                entry.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "private-sink-does-not-consume-admitted-command",
            )
        )

    admitted_sink = functions["_evaluate_settlement_strong_admitted_v1"]
    replay_arguments = dict(common_arguments)
    replay_arguments["settlement"] = "settlement"
    replay_arguments["intents"] = "intents"
    observed_name = "_evaluate_settlement_strong_admitted_observed_v5"
    private_sink_name = (
        observed_name
        if observed_name in functions
        else "_evaluate_settlement_strong_replay_committed_v1"
    )
    if not _single_exact_call_v1(
        admitted_sink,
        call_name=private_sink_name,
        keywords=replay_arguments,
    ):
        violations.append(
            _Violation(
                relative_path,
                admitted_sink.lineno,
                admitted_sink.col_offset,
                "EXACT_REPLAY_DATAFLOW",
                "private-replay-sink-does-not-consume-admitted-command",
            )
        )
    if observed_name in functions:
        observed_sink = functions[observed_name]
        implementation_calls = tuple(
            call
            for call in _function_calls(observed_sink)
            if _last_name(call.func) == "_validate_settlement_strong_impl"
        )
        if len(implementation_calls) != 1:
            violations.append(
                _Violation(
                    relative_path,
                    observed_sink.lineno,
                    observed_sink.col_offset,
                    "EXACT_REPLAY_DATAFLOW",
                    "observed-sink-does-not-call-exact-replay-once",
                )
            )
        if any(
            (_last_name(call.func) or "").startswith("admit_")
            for call in _function_calls(observed_sink)
        ):
            violations.append(
                _Violation(
                    relative_path,
                    observed_sink.lineno,
                    observed_sink.col_offset,
                    "EXACT_REPLAY_DATAFLOW",
                    "observed-sink-readmits-command-or-state",
                )
            )

    forbidden_calls = {
        "BalanceTable",
        "Intent",
        "LPTable",
        "PoolState",
        "Settlement",
        "deep_freeze",
        "deepcopy",
        "project_owned_json",
        "_project_owned_json_unchecked",
    }
    for function_name in required_names:
        function = functions[function_name]
        for call in _function_calls(function):
            called = _last_name(call.func) or ""
            if called in forbidden_calls or called.startswith("admit_legacy_"):
                violations.append(
                    _Violation(
                        relative_path,
                        call.lineno,
                        call.col_offset,
                        "EXACT_REPLAY_MUTABLE_PROJECTION",
                        f"{function_name}:{called}",
                    )
                )
    return violations


def _add_exact_consumer_violation(
    violations: list[_Violation],
    *,
    relative_path: str,
    node: ast.AST,
    detail: str,
) -> None:
    violations.append(
        _Violation(
            relative_path,
            getattr(node, "lineno", 0),
            getattr(node, "col_offset", 0),
            "EXACT_CONSUMER_DATAFLOW",
            detail,
        )
    )


def _check_exact_command_admission_v1(
    admission: ast.FunctionDef,
    relative_path: str,
) -> list[_Violation]:
    violations: list[_Violation] = []
    if not _has_named_call_assignment(
        admission,
        target_name="exact_settlement",
        call_name="snapshot_settlement",
        positional_names=("settlement",),
    ) or not _has_named_call_assignment(
        admission,
        target_name="exact_intents",
        call_name="admit_intent_batch",
        positional_names=("intents",),
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admission,
            detail="admission-results-not-bound",
        )
    if not _has_single_bindings(admission, ("exact_settlement", "exact_intents")):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admission,
            detail="admission-exact-values-rebound",
        )
    if not _has_named_tuple_return(admission, ("exact_settlement", "exact_intents")):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admission,
            detail="admission-results-not-returned",
        )
    admission_returns = tuple(node for node in ast.walk(admission) if type(node) is ast.Return)
    for invalid_return in (
        node
        for node in admission_returns
        if not _is_named_tuple_return(node, ("exact_settlement", "exact_intents"))
        and not _is_named_reject_return(node, "_reject")
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=invalid_return,
            detail="admission-has-raw-or-unknown-return",
        )
    return violations


def _check_exact_command_sinks_v1(
    entry: ast.FunctionDef,
    relative_path: str,
) -> list[_Violation]:
    violations: list[_Violation] = []
    if _function_parameter_names_v1(entry) != (
        "state_source",
        "settlement",
        "intents",
        "context",
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=entry,
            detail="entry-does-not-accept-one-state-aggregate",
        )
    if not _single_exact_assigned_call_v1(
        entry,
        target_name="state",
        call_name="_admit_exact_state_v1",
        positional=("state_source",),
    ) or not _single_exact_call_v1(
        entry,
        call_name="_admit_exact_state_v1",
        positional=("state_source",),
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=entry,
            detail="entry-state-aggregate-admission-bypassed",
        )
    if (
        not _has_named_call_assignment(
            entry,
            target_name="command",
            call_name="_admit_exact_command_v1",
            positional_names=("settlement", "intents"),
        )
        or not _single_exact_call_v1(
            entry,
            call_name="_admit_exact_command_v1",
            positional=("settlement", "intents"),
        )
        or not _has_named_tuple_assignment(
            entry,
            target_names=("exact_settlement", "exact_intents"),
            source_name="command",
        )
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=entry,
            detail="entry-does-not-destructure-admitted-command",
        )
    protected_results = (
        "command",
        "exact_context",
        "state",
        "pre_binding",
        "exact_settlement",
        "exact_intents",
        "nonce",
        "spot",
        "fee",
        "successor",
        "candidate",
        "evidence",
        "material",
    )
    if not _has_single_bindings(entry, protected_results):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=entry,
            detail="entry-authoritative-value-rebound",
        )

    required_sink_arguments: dict[str, tuple[str | tuple[str, ...], dict[str, str]]] = {
        "_nonce_candidate_v1": (
            "nonce",
            {
                "state": "state",
                "intents": "exact_intents",
                "context": "exact_context",
            },
        ),
        "_spot_candidate_v1": (
            "spot",
            {
                "state": "state",
                "settlement": "exact_settlement",
                "intents": "exact_intents",
                "context": "exact_context",
            },
        ),
        "_fee_candidate_v1": (
            "fee",
            {
                "state": "state",
                "settlement": "exact_settlement",
                "context": "exact_context",
            },
        ),
        "_candidate_evidence_v1": (
            "evidence",
            {
                "pre_state": "state",
                "candidate": "candidate",
                "context": "exact_context",
                "intents": "exact_intents",
                "pre_binding": "pre_binding",
            },
        ),
    }
    entry_calls = {_last_name(call.func) for call in _function_calls(entry)}
    if "_nonce_candidate_observed_v5" in entry_calls:
        required_sink_arguments = {
            "_nonce_candidate_observed_v5": (
                ("nonce", "nonce_read_trace"),
                {"state": "state", "intents": "exact_intents", "context": "exact_context"},
            ),
            "_spot_candidate_observed_v5": (
                ("spot", "spot_read_trace"),
                {
                    "state": "state",
                    "settlement": "exact_settlement",
                    "intents": "exact_intents",
                    "context": "exact_context",
                },
            ),
            "_fee_candidate_observed_v5": (
                ("fee", "complete_read_trace"),
                {
                    "state": "state",
                    "settlement": "exact_settlement",
                    "context": "exact_context",
                    "state_read_trace": "combined_read_trace",
                },
            ),
            "_candidate_evidence_v1": (
                "evidence",
                {
                    "pre_state": "state",
                    "candidate": "candidate",
                    "settlement": "exact_settlement",
                    "context": "exact_context",
                    "intents": "exact_intents",
                    "pre_binding": "pre_binding",
                    "state_read_trace": "complete_read_trace",
                    "context_read_trace": "context_read_trace",
                },
            ),
        }
    for sink_name, (target_spec, expected_arguments) in required_sink_arguments.items():
        target_names: tuple[str, ...] = (
            (target_spec,) if isinstance(target_spec, str) else target_spec
        )
        call_is_exact = _single_exact_call_v1(
            entry,
            call_name=sink_name,
            keywords=expected_arguments,
        )
        if len(target_names) == 1:
            assignment_is_exact = _single_exact_assigned_call_v1(
                entry,
                target_name=target_names[0],
                call_name=sink_name,
                keywords=expected_arguments,
            )
        else:
            assignment_is_exact = _single_exact_tuple_assigned_call_v1(
                entry,
                target_names=target_names,
                call_name=sink_name,
                keywords=expected_arguments,
            )
        if not call_is_exact or not assignment_is_exact:
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=entry,
                detail=(f"sink-result-not-authoritative:{','.join(target_names)}:{sink_name}"),
            )

    violations.extend(_check_exact_lineage_assignments_v1(entry, relative_path))
    violations.extend(_check_exact_lineage_result_v1(entry, relative_path))

    admission_calls = tuple(
        call
        for call in _function_calls(entry)
        if _last_name(call.func) in {"_admit_exact_command_v1", "_admit_exact_state_v1"}
    )
    allowed_raw_loads = {
        id(argument)
        for call in admission_calls
        for argument in call.args
        if type(argument) is ast.Name and argument.id in {"state_source", "settlement", "intents"}
    }
    for node in ast.walk(entry):
        if (
            type(node) is ast.Name
            and type(node.ctx) is ast.Load
            and node.id in {"state_source", "settlement", "intents"}
            and id(node) not in allowed_raw_loads
        ):
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=node,
                detail=f"entry-raw-authority-load-outside-admission:{node.id}",
            )
    return violations


def _check_exact_lineage_assignments_v1(
    entry: ast.FunctionDef,
    relative_path: str,
) -> list[_Violation]:
    exact_constructions = (
        (
            "successor",
            "FCISCommittedStateV1",
            {
                "balances": "spot.balances",
                "pools": "spot.pools",
                "lp_balances": "spot.lp_balances",
                "nonces": "nonce.state",
                "vault": "state.vault",
                "oracle": "state.oracle",
                "fee_accumulator": "fee[0]",
                "perps": "state.perps",
            },
        ),
        (
            "candidate",
            "FCISStepCandidateV1",
            {
                "state": "successor",
                "balance_patch": "spot.balance_patch",
                "pool_patch": "spot.pool_patch",
                "lp_patch": "spot.lp_patch",
                "nonce_patch": "nonce.patch",
                "fee_allocation": "fee[1]",
            },
        ),
        (
            "material",
            "FCISEvaluatedMaterialV1",
            {
                "pre_state": "state",
                "settlement": "exact_settlement",
                "intents": "exact_intents",
                "context": "exact_context",
            },
        ),
    )
    violations: list[_Violation] = []
    for target_name, constructor_name, expected_arguments in exact_constructions:
        if _single_exact_assigned_call_v1(
            entry,
            target_name=target_name,
            call_name=constructor_name,
            keywords=expected_arguments,
        ):
            continue
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=entry,
            detail=f"lineage-construction:{target_name}:{constructor_name}",
        )
    return violations


def _check_exact_lineage_result_v1(
    entry: ast.FunctionDef,
    relative_path: str,
) -> list[_Violation]:
    direct_construction = any(
        _last_name(call.func) == "FCISStepEvaluationOkV1" for call in _function_calls(entry)
    )
    result_returns = tuple(
        node
        for node in ast.walk(entry)
        if type(node) is ast.Return
        and type(node.value) is ast.Call
        and _last_name(node.value.func) == "_evaluation_ok_from_evaluator_v1"
    )
    if (
        not direct_construction
        and len(result_returns) == 1
        and _call_matches_exact_expressions_v1(
            result_returns[0].value,
            positional=("material", "candidate", "evidence"),
        )
    ):
        return []
    return [
        _Violation(
            relative_path,
            entry.lineno,
            entry.col_offset,
            "EXACT_CONSUMER_DATAFLOW",
            "lineage-result-not-exact",
        )
    ]


def _check_exact_consumer_annotations_v1(
    functions: dict[str, ast.FunctionDef],
    relative_path: str,
) -> list[_Violation]:
    violations: list[_Violation] = []
    exact_annotations = {
        "_canonical_state_root_binding_v1": {
            "state": "FCISCommittedStateV1",
            "snapshot_version": "int",
        },
        "_pre_state_binding_v1": {
            "state": "FCISCommittedStateV1",
            "context": "FCISStepExecutionContextV1",
        },
        "_evaluate_spot_v1": {
            "settlement": "OwnedSettlementV1",
            "intents": "tuple[OwnedIntentV1,...]",
        },
        "_nonce_candidate_v1": {
            "state": "FCISCommittedStateV1",
            "intents": "tuple[OwnedIntentV1,...]",
        },
        "_spot_candidate_v1": {
            "state": "FCISCommittedStateV1",
            "settlement": "OwnedSettlementV1",
            "intents": "tuple[OwnedIntentV1,...]",
        },
        "_fee_candidate_v1": {
            "state": "FCISCommittedStateV1",
            "settlement": "OwnedSettlementV1",
        },
        "_candidate_evidence_v1": {
            "pre_state": "FCISCommittedStateV1",
            "intents": "tuple[OwnedIntentV1,...]",
        },
    }
    exact_parameters = {
        "_canonical_state_root_binding_v1": ("state", "snapshot_version"),
        "_pre_state_binding_v1": ("state", "context"),
        "_evaluate_spot_v1": (
            "balances",
            "pools",
            "lp_balances",
            "settlement",
            "intents",
            "context",
        ),
        "_nonce_candidate_v1": ("state", "intents", "context"),
        "_spot_candidate_v1": ("state", "settlement", "intents", "context"),
        "_fee_candidate_v1": ("state", "settlement", "context"),
        "_candidate_evidence_v1": (
            "pre_state",
            "candidate",
            "settlement",
            "context",
            "intents",
            "pre_binding",
            "state_read_trace",
            "context_read_trace",
        ),
    }
    for function_name, expected in exact_annotations.items():
        function = functions[function_name]
        annotations = {
            argument.arg: argument.annotation
            for argument in (*function.args.args, *function.args.kwonlyargs)
        }
        for field, expected_annotation in expected.items():
            actual = _normalized_annotation(annotations.get(field))
            if actual != expected_annotation:
                _add_exact_consumer_violation(
                    violations,
                    relative_path=relative_path,
                    node=function,
                    detail=(f"annotation:{function_name}:{field}:{actual or '<missing>'}"),
                )
        actual_parameters = _function_parameter_names_v1(function)
        if actual_parameters != exact_parameters[function_name]:
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=function,
                detail=(
                    f"parameters:{function_name}:"
                    f"{','.join(actual_parameters) or '<none>'}:expected:"
                    f"{','.join(exact_parameters[function_name])}"
                ),
            )
    return violations


def _check_exact_consumer_sink_forwarding_v1(
    functions: dict[str, ast.FunctionDef],
    relative_path: str,
) -> list[_Violation]:
    """Require every evaluator helper to forward only its declared exact graph."""

    expected_calls = {
        "_evaluate_spot_v1": (
            "_evaluate_settlement_strong_admitted_v1",
            (),
            {
                "settlement": "settlement",
                "intents": "intents",
                "pre_balances": "balances",
                "pre_pools": "pools",
                "pre_lp_balances": "lp_balances",
                "now": "settlement_context.now",
                "min_lp_position_age_seconds": "settlement_context.min_lp_position_age_seconds",
                "lp_duration_policy": "context.lp_duration_policy",
                "mode": "settlement_mode_label_v1(settlement_context.mode)",
                "allow_cow_netting": "settlement_context.allow_cow_netting",
                "allow_snapshot_bound_quote_bindings": "settlement_context.allow_snapshot_bound_quote_bindings",
                "protocol_fee_share_bps": "settlement_context.protocol_fee_share_bps",
                "protocol_fee_recipient_pubkey": "settlement_context.protocol_fee_recipient_pubkey",
            },
        ),
        "_nonce_candidate_v1": (
            "_validate_and_apply_intent_nonce_batch_admitted_v1",
            (),
            {
                "nonces": "state.nonces",
                "intents": "intents",
                "require_all_nonces": "context.require_all_nonces",
            },
        ),
        "_spot_candidate_v1": (
            "_evaluate_spot_v1",
            (),
            {
                "balances": "state.balances",
                "pools": "state.pools",
                "lp_balances": "state.lp_balances",
                "settlement": "settlement",
                "intents": "intents",
                "context": "context",
            },
        ),
        "_fee_candidate_v1": (
            "_total_settlement_fees_v1",
            ("settlement",),
            {},
        ),
        "_candidate_evidence_v1": (
            "_compute_support_state_root_for_batch_owned_admitted_v1",
            (),
            {
                "intents": "intents",
                "balances": "pre_state.balances",
                "pools": "pre_state.pools",
                "lp_balances": "pre_state.lp_balances",
                "nonces": "pre_state.nonces",
            },
        ),
    }
    if "_nonce_candidate_observed_v5" in functions:
        expected_calls = {
            "_evaluate_spot_v1": (
                "_evaluate_spot_observed_v5",
                (),
                {
                    "balances": "balances",
                    "pools": "pools",
                    "lp_balances": "lp_balances",
                    "settlement": "settlement",
                    "intents": "intents",
                    "context": "context",
                },
            ),
            "_nonce_candidate_v1": (
                "_nonce_candidate_observed_v5",
                (),
                {"state": "state", "intents": "intents", "context": "context"},
            ),
            "_spot_candidate_v1": (
                "_spot_candidate_observed_v5",
                (),
                {
                    "state": "state",
                    "settlement": "settlement",
                    "intents": "intents",
                    "context": "context",
                },
            ),
            "_fee_candidate_v1": (
                "_fee_candidate_observed_v5",
                (),
                {
                    "state": "state",
                    "settlement": "settlement",
                    "context": "context",
                    "state_read_trace": "FCISStateReadTraceV5()",
                },
            ),
            "_candidate_evidence_v1": (
                "_compute_fcis_support_root_v5_admitted",
                (),
                {
                    "settlement": "settlement",
                    "intents": "intents",
                    "context": "context",
                    "balances": "pre_state.balances",
                    "pools": "pre_state.pools",
                    "lp_balances": "pre_state.lp_balances",
                    "nonces": "pre_state.nonces",
                    "fee_accumulator": "pre_state.fee_accumulator",
                    "state_read_trace": "state_read_trace",
                    "context_read_trace": "context_read_trace",
                },
            ),
        }
    violations: list[_Violation] = []
    for function_name, (call_name, positional, keywords) in expected_calls.items():
        function = functions[function_name]
        if not _single_exact_call_v1(
            function,
            call_name=call_name,
            positional=positional,
            keywords=keywords,
        ):
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=function,
                detail=f"sink-forwarding:{function_name}:{call_name}",
            )
    return violations


def _check_exact_consumer_projection_v1(
    functions: dict[str, ast.FunctionDef],
    required_names: tuple[str, ...],
    relative_path: str,
) -> list[_Violation]:
    violations: list[_Violation] = []
    forbidden_calls = {
        "BalanceTable",
        "Intent",
        "LPTable",
        "PoolState",
        "Settlement",
        "deep_freeze",
        "deepcopy",
        "project_owned_json",
        "_project_owned_json_unchecked",
    }
    for function_name in required_names:
        function = functions[function_name]
        for call in _function_calls(function):
            called = _last_name(call.func) or ""
            if called in forbidden_calls or "legacy" in called.lower():
                _add_exact_consumer_violation(
                    violations,
                    relative_path=relative_path,
                    node=call,
                    detail=f"legacy-or-mutable-call:{function_name}:{called}",
                )
        for node in ast.walk(function):
            if type(node) is ast.Attribute and node.attr == "get_field":
                _add_exact_consumer_violation(
                    violations,
                    relative_path=relative_path,
                    node=node,
                    detail=f"reflective-intent-read:{function_name}",
                )
    return violations


def _top_level_functions_v1(module: ast.Module) -> dict[str, ast.FunctionDef]:
    return {
        statement.name: statement for statement in module.body if type(statement) is ast.FunctionDef
    }


def _call_uses_names_v1(
    call: ast.Call,
    *,
    positional: tuple[str, ...] = (),
    keywords: dict[str, str] | None = None,
) -> bool:
    actual_positional = tuple(
        argument.id if type(argument) is ast.Name else "" for argument in call.args
    )
    return actual_positional == positional and _call_has_named_keywords(
        call,
        {} if keywords is None else keywords,
    )


def _function_parameter_names_v1(function: ast.FunctionDef) -> tuple[str, ...]:
    names = tuple(
        argument.arg
        for argument in (
            *function.args.posonlyargs,
            *function.args.args,
            *function.args.kwonlyargs,
        )
    )
    if function.args.vararg is not None:
        names += (f"*{function.args.vararg.arg}",)
    if function.args.kwarg is not None:
        names += (f"**{function.args.kwarg.arg}",)
    return names


def _call_matches_exact_expressions_v1(
    call: ast.Call,
    *,
    positional: tuple[str, ...] = (),
    keywords: dict[str, str] | None = None,
) -> bool:
    expected_keywords = {} if keywords is None else keywords
    if any(keyword.arg is None for keyword in call.keywords):
        return False
    actual_positional = tuple(ast.unparse(argument).replace(" ", "") for argument in call.args)
    actual_keywords = {
        keyword.arg: ast.unparse(keyword.value).replace(" ", "")
        for keyword in call.keywords
        if keyword.arg is not None
    }
    normalized_keywords = {key: value.replace(" ", "") for key, value in expected_keywords.items()}
    return actual_positional == positional and actual_keywords == normalized_keywords


def _single_exact_call_v1(
    function: ast.FunctionDef,
    *,
    call_name: str,
    positional: tuple[str, ...] = (),
    keywords: dict[str, str] | None = None,
) -> bool:
    calls = tuple(call for call in _function_calls(function) if _last_name(call.func) == call_name)
    return len(calls) == 1 and _call_matches_exact_expressions_v1(
        calls[0],
        positional=positional,
        keywords=keywords,
    )


def _single_exact_assigned_call_v1(
    function: ast.FunctionDef,
    *,
    target_name: str,
    call_name: str,
    positional: tuple[str, ...] = (),
    keywords: dict[str, str] | None = None,
) -> bool:
    assignments = tuple(
        node
        for node in ast.walk(function)
        if type(node) is ast.Assign
        and len(node.targets) == 1
        and type(node.targets[0]) is ast.Name
        and node.targets[0].id == target_name
        and type(node.value) is ast.Call
        and _last_name(node.value.func) == call_name
    )
    return len(assignments) == 1 and _call_matches_exact_expressions_v1(
        assignments[0].value,
        positional=positional,
        keywords=keywords,
    )


def _single_exact_tuple_assigned_call_v1(
    function: ast.FunctionDef,
    *,
    target_names: tuple[str, ...],
    call_name: str,
    keywords: dict[str, str],
) -> bool:
    assignments = tuple(
        node
        for node in ast.walk(function)
        if type(node) is ast.Assign
        and len(node.targets) == 1
        and type(node.targets[0]) is ast.Tuple
        and tuple(
            element.id if type(element) is ast.Name else "" for element in node.targets[0].elts
        )
        == target_names
        and type(node.value) is ast.Call
        and _last_name(node.value.func) == call_name
    )
    return len(assignments) == 1 and _call_matches_exact_expressions_v1(
        assignments[0].value,
        keywords=keywords,
    )


def _check_exact_nonce_consumer_shape_v1(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    if relative_path != "src/core/nonce_batch_transition.py":
        return []
    functions = _top_level_functions_v1(module)
    required = (
        "validate_and_apply_intent_nonce_batch_committed_v1",
        "_validate_and_apply_intent_nonce_batch_admitted_v1",
        "_validate_and_apply_intent_nonce_batch_admitted_observed_v5",
    )
    missing = tuple(name for name in required if name not in functions)
    if missing:
        return [
            _Violation(
                relative_path,
                0,
                0,
                "EXACT_CONSUMER_DATAFLOW",
                f"missing:{','.join(missing)}",
            )
        ]
    function = functions["validate_and_apply_intent_nonce_batch_committed_v1"]
    admitted_sink = functions["_validate_and_apply_intent_nonce_batch_admitted_v1"]
    observed_sink = functions["_validate_and_apply_intent_nonce_batch_admitted_observed_v5"]
    violations: list[_Violation] = []
    annotations = {
        argument.arg: _normalized_annotation(argument.annotation)
        for argument in (*function.args.args, *function.args.kwonlyargs)
    }
    if annotations.get("intents") != "tuple[OwnedIntentV1,...]":
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=function,
            detail=f"nonce-intents-annotation:{annotations.get('intents') or '<missing>'}",
        )
    if not _has_named_call_assignment(
        function,
        target_name="exact_intents",
        call_name="admit_intent_batch",
        positional_names=("intents",),
    ) or not _has_single_bindings(function, ("exact_intents",)):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=function,
            detail="nonce-admission-result-not-single-bound",
        )
    expected_parameters = ("nonces", "intents", "require_all_nonces")
    for candidate in (function, admitted_sink, observed_sink):
        if _function_parameter_names_v1(candidate) != expected_parameters:
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=candidate,
                detail=f"nonce-parameters:{candidate.name}",
            )
    if not _single_exact_call_v1(
        function,
        call_name="_validate_and_apply_intent_nonce_batch_admitted_v1",
        keywords={
            "nonces": "nonces",
            "intents": "exact_intents",
            "require_all_nonces": "require_all_nonces",
        },
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=function,
            detail="nonce-public-wrapper-does-not-forward-admitted-command",
        )
    if not _single_exact_call_v1(
        admitted_sink,
        call_name="_validate_and_apply_intent_nonce_batch_admitted_observed_v5",
        keywords={
            "nonces": "nonces",
            "intents": "intents",
            "require_all_nonces": "require_all_nonces",
        },
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admitted_sink,
            detail="nonce-admitted-wrapper-bypasses-observed-sink",
        )
    if any(
        _last_name(call.func) == "admit_intent_batch"
        for sink in (admitted_sink, observed_sink)
        for call in _function_calls(sink)
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=observed_sink,
            detail="nonce-private-sink-readmits-command",
        )
    admitted_loops = tuple(
        node
        for node in ast.walk(observed_sink)
        if type(node) is ast.For and type(node.iter) is ast.Name and node.iter.id == "intents"
    )
    if len(admitted_loops) != 1:
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=observed_sink,
            detail="nonce-private-sink-does-not-consume-exact-intents-once",
        )
    admission_lines = tuple(
        node.lineno
        for node in ast.walk(function)
        if type(node) is ast.Assign
        and any(
            type(target) is ast.Name and target.id == "exact_intents" for target in node.targets
        )
        and type(node.value) is ast.Call
        and _last_name(node.value.func) == "admit_intent_batch"
    )
    if admission_lines:
        admission_line = admission_lines[0]
        for loop in (
            node
            for node in ast.walk(function)
            if type(node) is ast.For and node.lineno > admission_line
        ):
            if type(loop.iter) is ast.Name and loop.iter.id == "intents":
                _add_exact_consumer_violation(
                    violations,
                    relative_path=relative_path,
                    node=loop,
                    detail="nonce-raw-intents-used-after-admission",
                )
    return violations + _check_exact_consumer_projection_v1(
        functions,
        required,
        relative_path,
    )


def _check_exact_support_consumer_shape_v1(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    if relative_path != "src/state/support_root.py":
        return []
    functions = _top_level_functions_v1(module)
    required = (
        "_derive_batch_state_support_owned_v1",
        "derive_batch_state_support_owned_committed_v1",
        "_compute_support_state_root_for_batch_owned_admitted_v1",
        "compute_support_state_root_for_batch_owned_committed_v1",
    )
    missing = tuple(name for name in required if name not in functions)
    if missing:
        return [
            _Violation(
                relative_path,
                0,
                0,
                "EXACT_CONSUMER_DATAFLOW",
                f"missing:{','.join(missing)}",
            )
        ]
    violations: list[_Violation] = []
    admission = functions["derive_batch_state_support_owned_committed_v1"]
    if not _has_named_call_assignment(
        admission,
        target_name="exact_intents",
        call_name="admit_intent_batch",
        positional_names=("intents",),
    ) or not _has_single_bindings(admission, ("exact_intents",)):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admission,
            detail="support-admission-result-not-single-bound",
        )
    if not _has_named_call_assignment(
        admission,
        target_name="exact_pools",
        call_name="snapshot_pool_map",
        positional_names=("pools",),
    ) or not _has_single_bindings(admission, ("exact_intents", "exact_pools")):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admission,
            detail="support-state-admission-result-not-single-bound",
        )
    if not _single_exact_call_v1(
        admission,
        call_name="_derive_batch_state_support_owned_v1",
        positional=("exact_intents",),
        keywords={"pools": "exact_pools"},
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admission,
            detail="support-private-derive-does-not-consume-admitted-intents",
        )

    expected_parameters = {
        "_derive_batch_state_support_owned_v1": ("intents", "pools"),
        "derive_batch_state_support_owned_committed_v1": ("intents", "pools"),
        "_compute_support_state_root_for_batch_owned_admitted_v1": (
            "intents",
            "balances",
            "pools",
            "lp_balances",
            "nonces",
        ),
        "compute_support_state_root_for_batch_owned_committed_v1": (
            "intents",
            "balances",
            "pools",
            "lp_balances",
            "nonces",
        ),
    }
    for function_name, parameters in expected_parameters.items():
        if _function_parameter_names_v1(functions[function_name]) != parameters:
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=functions[function_name],
                detail=f"support-parameters:{function_name}",
            )

    admitted_root = functions["_compute_support_state_root_for_batch_owned_admitted_v1"]
    if not _single_exact_call_v1(
        admitted_root,
        call_name="_derive_batch_state_support_owned_v1",
        positional=("intents",),
        keywords={"pools": "pools"},
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=admitted_root,
            detail="support-private-root-readmits-or-bypasses-command",
        )
    for call in _function_calls(admitted_root):
        if _last_name(call.func) in {"admit_intent_batch", "snapshot_pool_map"}:
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=call,
                detail="support-private-root-readmits-command-or-state",
            )

    root = functions["compute_support_state_root_for_batch_owned_committed_v1"]
    root_calls = _function_calls(root)
    derive_calls = tuple(
        call
        for call in root_calls
        if _last_name(call.func) == "derive_batch_state_support_owned_committed_v1"
    )
    encoder_calls = tuple(
        call
        for call in root_calls
        if _last_name(call.func) == "compute_support_state_root_v5_with_committed_spot_state_v1"
    )
    if len(derive_calls) != 1 or not _call_uses_names_v1(
        derive_calls[0],
        positional=("intents",),
        keywords={"pools": "pools"},
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=root,
            detail="support-root-does-not-use-readmitted-support",
        )
    if len(encoder_calls) != 1:
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=root,
            detail="support-root-does-not-use-unmounted-v5-encoder",
        )
    return violations + _check_exact_consumer_projection_v1(
        functions,
        required,
        relative_path,
    )


def _check_shared_committed_root_binding_v1(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    if relative_path != "src/state/committed_dex_snapshot.py":
        return []
    functions = _top_level_functions_v1(module)
    root = functions.get("canonical_committed_state_root_binding_v1")
    if root is None:
        return [
            _Violation(
                relative_path,
                0,
                0,
                "EXACT_CONSUMER_DATAFLOW",
                "missing:canonical_committed_state_root_binding_v1",
            )
        ]
    expected_snapshot_fields = {
        "version": "snapshot_version",
        "balances": "state.balances",
        "pools": "state.pools",
        "lp_balances": "state.lp_balances",
        "nonces": "state.nonces",
        "fee_accumulator": "state.fee_accumulator",
        "vault": "state.vault",
        "oracle": "state.oracle",
        "perps": "state.perps",
    }
    if _function_parameter_names_v1(root) != (
        "state",
        "snapshot_version",
    ) or not _single_exact_call_v1(
        root,
        call_name="canonical_snapshot_bytes_from_committed_state_v1",
        keywords=expected_snapshot_fields,
    ):
        return [
            _Violation(
                relative_path,
                root.lineno,
                root.col_offset,
                "EXACT_CONSUMER_DATAFLOW",
                "shared-state-root-does-not-bind-eight-fields",
            )
        ]
    if not _single_exact_call_v1(
        root,
        call_name="sha256_hex",
        positional=("root_preimage",),
    ):
        return [
            _Violation(
                relative_path,
                root.lineno,
                root.col_offset,
                "EXACT_CONSUMER_DATAFLOW",
                "shared-state-root-does-not-hash-one-preimage",
            )
        ]
    return []


def _check_full_state_root_binding_v1(
    functions: dict[str, ast.FunctionDef],
    relative_path: str,
) -> list[_Violation]:
    violations: list[_Violation] = []
    root = functions["_canonical_state_root_binding_v1"]
    pre = functions["_pre_state_binding_v1"]
    evidence = functions["_candidate_evidence_v1"]
    if _function_parameter_names_v1(root) != (
        "state",
        "snapshot_version",
    ) or not _single_exact_call_v1(
        root,
        call_name="canonical_committed_state_root_binding_v1",
        positional=("state", "snapshot_version"),
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=root,
            detail="full-state-root-bypasses-shared-binding",
        )
    if not _single_exact_call_v1(
        pre,
        call_name="_canonical_state_root_binding_v1",
        positional=("state", "context.snapshot_version"),
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=pre,
            detail="pre-state-root-bypasses-full-state-binding",
        )
    if not _single_exact_call_v1(
        evidence,
        call_name="_canonical_state_root_binding_v1",
        positional=("candidate.state", "context.snapshot_version"),
    ):
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=evidence,
            detail="post-state-root-bypasses-full-state-binding",
        )
    for function in (root, pre, evidence):
        if any(
            _last_name(call.func) == "state_root_preimage_with_committed_spot_state_v1"
            for call in _function_calls(function)
        ):
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=function,
                detail="legacy-five-field-root-used",
            )
    evidence_calls = tuple(
        call
        for call in _function_calls(evidence)
        if _last_name(call.func) == "FCISStepEvaluationEvidenceV1"
    )
    if len(evidence_calls) != 1:
        _add_exact_consumer_violation(
            violations,
            relative_path=relative_path,
            node=evidence,
            detail="candidate-evidence-construction-count",
        )
    else:
        bindings = {
            keyword.arg: ast.unparse(keyword.value).replace(" ", "")
            for keyword in evidence_calls[0].keywords
            if keyword.arg is not None
        }
        if (
            bindings.get("post_state_root") != "post_root"
            or bindings.get("snapshot_commitment") != "post_root"
        ):
            _add_exact_consumer_violation(
                violations,
                relative_path=relative_path,
                node=evidence_calls[0],
                detail="post-root-and-snapshot-commitment-diverge",
            )
    return violations


def _check_exact_consumer_shape(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    """Prove that the M4 evaluator consumes only its admitted command graph."""

    if relative_path != "src/core/fcis_step_evaluator.py":
        return []
    functions = {
        statement.name: statement for statement in module.body if type(statement) is ast.FunctionDef
    }
    required_names = (
        "_admit_exact_state_v1",
        "_canonical_state_root_binding_v1",
        "_pre_state_binding_v1",
        "_admit_exact_command_v1",
        "_evaluate_spot_v1",
        "_evaluate_spot_observed_v5",
        "_nonce_candidate_v1",
        "_nonce_candidate_observed_v5",
        "_spot_candidate_v1",
        "_spot_candidate_observed_v5",
        "_fee_candidate_v1",
        "_fee_candidate_observed_v5",
        "_candidate_evidence_v1",
        "_reject_after_trace_containment_v5",
        "_evaluate_fcis_step_candidate_bound_v1",
        "evaluate_fcis_step_candidate_v1",
    )
    missing = tuple(name for name in required_names if name not in functions)
    if missing:
        return [
            _Violation(
                relative_path,
                0,
                0,
                "EXACT_CONSUMER_DATAFLOW",
                f"missing:{','.join(missing)}",
            )
        ]
    return (
        _check_exact_command_admission_v1(functions["_admit_exact_command_v1"], relative_path)
        + _check_full_state_root_binding_v1(functions, relative_path)
        + _check_exact_command_sinks_v1(
            functions["_evaluate_fcis_step_candidate_bound_v1"], relative_path
        )
        + _check_exact_consumer_annotations_v1(functions, relative_path)
        + _check_exact_consumer_sink_forwarding_v1(functions, relative_path)
        + _check_exact_consumer_projection_v1(functions, required_names, relative_path)
    )


def _m5_support_violation_v5(
    relative_path: str,
    node: ast.AST,
    detail: str,
) -> _Violation:
    return _Violation(
        relative_path,
        getattr(node, "lineno", 0),
        getattr(node, "col_offset", 0),
        "FCIS_SUPPORT_TRACE_V5",
        detail,
    )


def _top_level_class_fields_v5(
    module: ast.Module,
    class_name: str,
) -> tuple[str, ...] | None:
    for statement in module.body:
        if type(statement) is not ast.ClassDef or statement.name != class_name:
            continue
        return tuple(
            field.target.id
            for field in statement.body
            if type(field) is ast.AnnAssign and type(field.target) is ast.Name
        )
    return None


def _reachable_calls_v5(
    functions: dict[str, ast.FunctionDef],
    entry_name: str,
) -> tuple[set[str], set[str]]:
    pending = [entry_name]
    visited: set[str] = set()
    calls: set[str] = set()
    while pending:
        function_name = pending.pop()
        if function_name in visited or function_name not in functions:
            continue
        visited.add(function_name)
        for call in _function_calls(functions[function_name]):
            called = _last_name(call.func)
            if called is None:
                continue
            calls.add(called)
            if called in functions and called not in visited:
                pending.append(called)
    return visited, calls


def _has_broad_exception_handler_v5(function: ast.FunctionDef) -> bool:
    for handler in (node for node in ast.walk(function) if type(node) is ast.ExceptHandler):
        if handler.type is None:
            return True
        if any(
            type(node) is ast.Name and node.id == "Exception" for node in ast.walk(handler.type)
        ):
            return True
    return False


def _is_direct_state_lookup_v5(node: ast.AST) -> bool:
    roots = (
        "pre_balances",
        "pre_pools",
        "pre_lp_balances",
        "replay_state.balances",
        "replay_state.pools",
        "replay_state.lp_balances",
    )
    if type(node) is ast.Subscript:
        expression = ast.unparse(node.value).replace(" ", "")
        return expression.startswith(roots)
    if type(node) is ast.Call and type(node.func) is ast.Attribute:
        if node.func.attr not in {"get", "get_last", "__getitem__"}:
            return False
        expression = ast.unparse(node.func.value).replace(" ", "")
        return expression.startswith(roots)
    return False


def _check_m5_support_trace_contract_v5(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    violations: list[_Violation] = []
    public_fields: dict[str, dict[str, tuple[str, ...]]] = {
        "src/core/fcis_decision_derivation.py": {
            "AcceptV1": (
                "next_state",
                "commit_plan",
                "receipt",
                "_construction_token",
            ),
            "RejectV1": ("receipt", "_construction_token"),
            "CommittedFailureV1": (
                "next_state",
                "commit_plan",
                "receipt",
                "_construction_token",
            ),
        },
        "src/core/fcis_commit_bundle_derivation.py": {
            "CommitBundleV1": (
                "decision",
                "outbox_plan",
                "_canonical_bundle_bytes",
                "_bundle_root",
                "_construction_token",
            ),
        },
        "src/core/fcis_commit_reference.py": {
            "ReferencePublicationV1": ("bundle",),
            "ReferenceCommitStoreV1": ("current_state", "publications"),
        },
        "src/core/fcis_step_evaluation_values.py": {
            "FCISStepEvaluationRejectV1": ("phase", "code", "path", "public_reason"),
        },
        "src/core/nonce_batch_transition.py": {
            "IntentNonceBatchRejectV1": ("code", "public_reason"),
            "IntentNonceBatchOkV1": ("state", "patch"),
        },
        "src/core/settlement_strong_validator.py": {
            "StrongSettlementRejectV1": ("reason",),
        },
    }
    for class_name, expected in public_fields.get(relative_path, {}).items():
        actual = _top_level_class_fields_v5(module, class_name)
        if actual != expected:
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    f"public-result-shape:{class_name}:{actual or '<missing>'}",
                )
            )

    functions = _top_level_functions_v1(module)
    if relative_path == "src/core/fcis_decision_derivation.py":
        required_functions = {
            "_admit_budget_v1",
            "_authoritative_reject_v1",
            "_derive_accept_v1",
            "_derive_patch_v1",
            "_derive_plan_v1",
            "_derive_replay_v1",
            "_revalidate_evaluation_v1",
            "evaluate_fcis_decision_v1",
        }
        for missing_function in sorted(required_functions - functions.keys()):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    f"decision-missing:{missing_function}",
                )
            )
        decision_aliases = tuple(
            statement
            for statement in module.body
            if type(statement) is ast.AnnAssign
            and type(statement.target) is ast.Name
            and statement.target.id == "DecisionV1"
        )
        if (
            len(decision_aliases) != 1
            or decision_aliases[0].value is None
            or ast.unparse(decision_aliases[0].value).replace(" ", "")
            != "AcceptV1|RejectV1|CommittedFailureV1"
        ):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    "decision-union-not-exhaustive",
                )
            )
        token_assignments = tuple(
            statement
            for statement in module.body
            if type(statement) is ast.Assign
            and len(statement.targets) == 1
            and type(statement.targets[0]) is ast.Name
            and statement.targets[0].id == "_DECISION_CONSTRUCTION_TOKEN_V1"
            and type(statement.value) is ast.Call
            and _last_name(statement.value.func) == "object"
            and not statement.value.args
            and not statement.value.keywords
        )
        if len(token_assignments) != 1:
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    "decision-construction-token-not-private-exact",
                )
            )
        constructor_sites: dict[str, list[str]] = {
            "AcceptV1": [],
            "RejectV1": [],
            "CommittedFailureV1": [],
        }
        for function_name, function in functions.items():
            for call in _function_calls(function):
                called = _last_name(call.func)
                if called in constructor_sites:
                    constructor_sites[called].append(function_name)
        expected_sites = {
            "AcceptV1": ["_derive_accept_v1"],
            "RejectV1": ["_authoritative_reject_v1"],
            "CommittedFailureV1": [],
        }
        for constructor, expected_construction_sites in expected_sites.items():
            if constructor_sites[constructor] != expected_construction_sites:
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        module,
                        f"decision-construction-sites:{constructor}",
                    )
                )
        if required_functions <= functions.keys():
            entry = functions["evaluate_fcis_decision_v1"]
            _visited, reachable_calls = _reachable_calls_v5(
                functions,
                "evaluate_fcis_decision_v1",
            )
            required_calls = {
                "_admit_budget_v1",
                "_evaluate_fcis_step_candidate_bound_v1",
                "_derive_accept_v1",
            }
            for missing_call in sorted(required_calls - reachable_calls):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        entry,
                        f"decision-unreachable:{missing_call}",
                    )
                )
            derive_accept = functions["_derive_accept_v1"]
            if not _single_exact_call_v1(
                derive_accept,
                call_name="_revalidate_evaluation_v1",
                positional=("evaluation",),
            ):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        derive_accept,
                        "accept-bypasses-lineage-revalidation",
                    )
                )
            if not _single_exact_call_v1(
                derive_accept,
                call_name="AcceptV1",
                positional=(
                    "evaluation.candidate.state",
                    "plan",
                    "receipt",
                    "_DECISION_CONSTRUCTION_TOKEN_V1",
                ),
            ):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        derive_accept,
                        "accept-not-derived-from-one-candidate",
                    )
                )
            derive_plan = functions["_derive_plan_v1"]
            if not _single_exact_call_v1(
                derive_plan,
                call_name="CommitPlanV1",
                positional=(
                    "_derive_patch_v1(evaluation)",
                    "effects",
                    "_derive_replay_v1(evaluation)",
                ),
            ):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        derive_plan,
                        "plan-not-derived-from-one-evaluation",
                    )
                )
            revalidate = functions["_revalidate_evaluation_v1"]
            calls = tuple(_last_name(call.func) for call in _function_calls(revalidate))
            expected_counts = {
                "canonical_committed_state_root_binding_v1": 2,
                "encode_fcis_execution_context_v1": 1,
                "_command_preimage_v5": 1,
            }
            for call_name, expected_count in expected_counts.items():
                if calls.count(call_name) != expected_count:
                    violations.append(
                        _m5_support_violation_v5(
                            relative_path,
                            revalidate,
                            f"decision-lineage-revalidation:{call_name}",
                        )
                    )

    if relative_path == "src/core/fcis_step_evaluator.py":
        visited, reachable_calls = _reachable_calls_v5(
            functions,
            "evaluate_fcis_step_candidate_v1",
        )
        required_calls = {
            "read_step_execution_context_v5",
            "_validate_and_apply_intent_nonce_batch_admitted_observed_v5",
            "_evaluate_settlement_strong_admitted_observed_v5",
            "_compute_fcis_support_root_v5_admitted",
        }
        for missing_call in sorted(required_calls - reachable_calls):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    functions["evaluate_fcis_step_candidate_v1"],
                    f"unreachable-observed-sink:{missing_call}",
                )
            )
        expected_support_keywords = {
            "settlement": "settlement",
            "intents": "intents",
            "context": "context",
            "balances": "pre_state.balances",
            "pools": "pre_state.pools",
            "lp_balances": "pre_state.lp_balances",
            "nonces": "pre_state.nonces",
            "fee_accumulator": "pre_state.fee_accumulator",
            "state_read_trace": "state_read_trace",
            "context_read_trace": "context_read_trace",
        }
        for function_name in ("_candidate_evidence_v1", "_reject_after_trace_containment_v5"):
            support_function = functions.get(function_name)
            if support_function is None or not _single_exact_call_v1(
                support_function,
                call_name="_compute_fcis_support_root_v5_admitted",
                keywords=expected_support_keywords,
            ):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        module if support_function is None else support_function,
                        f"support-root-not-bound-to-pre-state:{function_name}",
                    )
                )
        for function_name in visited:
            function = functions[function_name]
            if _has_broad_exception_handler_v5(function):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        function,
                        f"broad-exception-on-exact-path:{function_name}",
                    )
                )

    if relative_path == "src/core/settlement_strong_validator.py":
        implementation = functions.get("_validate_settlement_strong_impl")
        if implementation is not None:
            for node in ast.walk(implementation):
                if _is_direct_state_lookup_v5(node):
                    violations.append(
                        _m5_support_violation_v5(
                            relative_path,
                            node,
                            "untraced-direct-state-lookup",
                        )
                    )
            if _has_broad_exception_handler_v5(implementation):
                violations.append(
                    _m5_support_violation_v5(
                        relative_path,
                        implementation,
                        "broad-exception-in-exact-replay",
                    )
                )

    imported_modules = {node.module or "" for node in module.body if type(node) is ast.ImportFrom}
    if relative_path == "src/core/fcis_traced_reads_v5.py":
        if any(name.endswith("fcis_support_profile_v5") for name in imported_modules):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    "observed-reads-import-declared-support",
                )
            )
        if any(
            _last_name(call.func) == "_derive_fcis_support_set_v5_admitted"
            for function in functions.values()
            for call in _function_calls(function)
        ):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    "observed-reads-derived-from-declared-support",
                )
            )
    if relative_path == "src/core/fcis_support_profile_v5.py":
        if any(name.endswith("fcis_traced_reads_v5") for name in imported_modules):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module,
                    "declared-support-imports-observed-reader",
                )
            )
        support_root = functions.get("_compute_fcis_support_root_v5_admitted")
        required = {"_sequential_read_trace_v5", "support_contains_trace_v5"}
        actual_calls = (
            set()
            if support_root is None
            else {_last_name(call.func) or "" for call in _function_calls(support_root)}
        )
        for missing_call in sorted(required - actual_calls):
            violations.append(
                _m5_support_violation_v5(
                    relative_path,
                    module if support_root is None else support_root,
                    f"support-containment-missing:{missing_call}",
                )
            )
    return violations


def _check_authority_path(
    repo_root: Path,
    relative_path: Path,
) -> tuple[str, list[_Violation]]:
    resolved = _scoped_path(repo_root, relative_path)
    display = relative_path.as_posix()
    if resolved is None:
        return display, [_Violation(display, 0, 0, "PATH_OUTSIDE_SCOPE", display)]
    try:
        display = resolved.relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return display, [_Violation(display, 0, 0, "PATH_OUTSIDE_SCOPE", display)]
    try:
        source = resolved.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return display, [_Violation(display, 0, 0, "PATH_READ_ERROR", type(exc).__name__)]
    try:
        module = ast.parse(source, filename=display)
    except SyntaxError as exc:
        return display, [
            _Violation(
                display,
                exc.lineno or 0,
                exc.offset or 0,
                "SYNTAX_ERROR",
                exc.msg,
            )
        ]
    visitor = _AuthorityVisitor(display)
    visitor.visit(module)
    visitor.finalize(module)
    return (
        display,
        visitor.violations
        + _check_registry_constants(module, display)
        + _check_mutable_local_buffers(module, display)
        + _check_exact_replay_shape(module, display)
        + _check_shared_committed_root_binding_v1(module, display)
        + _check_exact_consumer_shape(module, display)
        + _check_exact_nonce_consumer_shape_v1(module, display)
        + _check_exact_support_consumer_shape_v1(module, display)
        + _check_m5_support_trace_contract_v5(module, display),
    )


_SENSITIVE_SOURCE_CODES = {
    "CLAIM_AUTHORITY_ESCAPE",
    "CONSTRUCTION_CALLSITE",
    "DECLARATIVE_REGISTRY_EXECUTION",
    "OWNED_CONSTRUCTION_ESCAPE",
    "PATH_READ_ERROR",
    "PRIVATE_AUTHORITY_IMPORT",
    "PROFILE_FACADE_SHAPE",
    "PROFILE_REGISTRY_BINDING",
    "PROFILE_REGISTRY_DRIFT",
    "PROFILE_BINDING_ESCAPE",
    "REGISTRY_BEHAVIOR_FIELD",
    "REGISTRY_BINDING_ESCAPE",
    "LEGACY_MUTABLE_CONSTRUCTION",
    "MUTABLE_CORE_BOUNDARY",
    "MUTABLE_LOCAL_BUFFER",
    "STRUCTURAL_CORE_BOUNDARY",
    "SHADOW_AUTHORITY_IMPORT",
    "UNMOUNTED_EVALUATOR_IMPORT",
    "SYNTAX_ERROR",
}


def _check_sensitive_source_tree(repo_root: Path) -> list[_Violation]:
    source_root = _scoped_path(repo_root, Path("src"))
    if source_root is None or not source_root.is_dir():
        return []
    violations: list[_Violation] = []
    for source_path in sorted(source_root.rglob("*.py")):
        relative_path = source_path.relative_to(repo_root.resolve())
        _display, path_violations = _check_authority_path(repo_root, relative_path)
        violations.extend(
            violation for violation in path_violations if violation.code in _SENSITIVE_SOURCE_CODES
        )
    return violations


def _declared_test_ids(
    repo_root: Path,
    paths: tuple[Path, ...],
) -> tuple[set[str], list[_Violation]]:
    declared: set[str] = set()
    violations: list[_Violation] = []
    for relative_path in paths:
        resolved = _scoped_path(repo_root, relative_path)
        display = relative_path.as_posix()
        if resolved is None:
            violations.append(_Violation(display, 0, 0, "PATH_OUTSIDE_SCOPE", display))
            continue
        try:
            text = resolved.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            violations.append(
                _Violation(display, 0, 0, "TEST_MATRIX_READ_ERROR", type(exc).__name__)
            )
            continue
        declared.update(TEST_ID_PATTERN.findall(text))
    return declared, violations


def _exact_string_list(value: object) -> list[str] | None:
    if type(value) is not list:
        return None
    strings: list[str] = []
    for item in value:
        if type(item) is not str:
            return None
        strings.append(item)
    return strings


def _check_requirement_coverage(
    repo_root: Path,
    requirements_path: Path,
    test_matrix_paths: tuple[Path, ...],
) -> list[_Violation]:
    resolved = _scoped_path(repo_root, requirements_path)
    display = requirements_path.as_posix()
    if resolved is None:
        return [_Violation(display, 0, 0, "PATH_OUTSIDE_SCOPE", display)]
    try:
        data = json.loads(resolved.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        return [_Violation(display, 0, 0, "REQUIREMENTS_READ_ERROR", type(exc).__name__)]
    declared_tests, violations = _declared_test_ids(repo_root, test_matrix_paths)
    if type(data) is not dict or type(data.get("requirements")) is not list:
        violations.append(_Violation(display, 0, 0, "REQUIREMENTS_SHAPE", "requirements"))
        return violations
    for index, requirement in enumerate(data["requirements"]):
        if type(requirement) is not dict:
            violations.append(
                _Violation(display, 0, 0, "REQUIREMENTS_SHAPE", f"requirements[{index}]")
            )
            continue
        requirement_id = requirement.get("id")
        if type(requirement_id) is not str or requirement.get("pr") != 477:
            continue
        test_ids = _exact_string_list(requirement.get("tests"))
        evidence_items = _exact_string_list(requirement.get("evidence"))
        if test_ids is None or evidence_items is None:
            violations.append(_Violation(display, 0, 0, "REQUIREMENTS_SHAPE", requirement_id))
            continue
        if not test_ids and not evidence_items:
            violations.append(_Violation(display, 0, 0, "UNCOVERED_REQUIREMENT", requirement_id))
            continue
        for test_id in sorted(test_ids):
            if test_matrix_paths and test_id not in declared_tests:
                violations.append(
                    _Violation(
                        display,
                        0,
                        0,
                        "UNDECLARED_REQUIREMENT_TEST",
                        f"{requirement_id}:{test_id}",
                    )
                )
    return violations


def check_contract(
    *,
    repo_root: Path,
    authority_paths: tuple[Path, ...],
    requirements_path: Path | None,
    test_matrix_paths: tuple[Path, ...],
    profile: str = "custom",
) -> dict[str, object]:
    """Check supplied authority paths plus sensitive call sites across ``src``."""

    checked_paths: list[str] = []
    violations: list[_Violation] = []
    for authority_path in authority_paths:
        display, path_violations = _check_authority_path(repo_root, authority_path)
        checked_paths.append(display)
        violations.extend(path_violations)
    violations.extend(_check_sensitive_source_tree(repo_root))
    if requirements_path is not None:
        violations.extend(
            _check_requirement_coverage(repo_root, requirements_path, test_matrix_paths)
        )
    unique_findings = sorted(set(violations))
    compatibility_allowlist = _PROFILE_COMPATIBILITY_ALLOWLISTS.get(profile, frozenset())
    compatibility_mutable: list[_Violation] = []
    blocking_mutable: list[_Violation] = []
    for finding in unique_findings:
        key = (finding.path, finding.line, finding.column, finding.code, finding.detail)
        if key in compatibility_allowlist:
            compatibility_mutable.append(finding)
        else:
            blocking_mutable.append(finding)
    compatibility_findings = tuple(compatibility_mutable)
    blocking_violations = tuple(blocking_mutable)
    return {
        "checked_paths": sorted(checked_paths),
        "compatibility_findings": [finding.as_json() for finding in compatibility_findings],
        "ok": not blocking_violations,
        "profile": profile,
        "schema": REPORT_SCHEMA,
        "sensitive_source_glob": "src/**/*.py",
        "violations": [violation.as_json() for violation in blocking_violations],
    }


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--authority-path", type=Path, action="append")
    parser.add_argument(
        "--profile",
        choices=tuple(_AUTHORITY_PATHS_BY_PROFILE),
        default="final-mount",
    )
    parser.add_argument("--requirements", type=Path, default=DEFAULT_REQUIREMENTS_PATH)
    parser.add_argument("--test-matrix", type=Path, action="append")
    parser.add_argument("--skip-requirements", action="store_true")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    profile = "custom" if args.authority_path else args.profile
    authority_paths = tuple(args.authority_path or _AUTHORITY_PATHS_BY_PROFILE[args.profile])
    test_matrix_paths = tuple(args.test_matrix or DEFAULT_TEST_MATRIX_PATHS)
    requirements_path = None if args.skip_requirements else args.requirements
    report = check_contract(
        repo_root=args.root,
        authority_paths=authority_paths,
        requirements_path=requirements_path,
        test_matrix_paths=test_matrix_paths,
        profile=profile,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
