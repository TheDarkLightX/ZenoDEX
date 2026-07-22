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
DEFAULT_AUTHORITY_PATHS = (
    Path("src/state/snapshot_combinators.py"),
    Path("src/state/owned_collections.py"),
    Path("src/state/state_snapshot_values.py"),
    Path("src/state/state_snapshot_schema.py"),
    Path("src/state/state_admission_profile.py"),
    Path("src/state/state_transitions.py"),
)
DEFAULT_REQUIREMENTS_PATH = Path("docs/specs/fcis_authority_snapshot_v1/requirements.json")
DEFAULT_TEST_MATRIX_PATHS = (
    Path("docs/specs/fcis_authority_snapshot_v1/TEST_MATRIX.md"),
    Path("docs/specs/fcis_authority_snapshot_v1/TEST_MATRIX_PR477_PR478.md"),
)
TEST_ID_PATTERN = re.compile(r"FCIS-(?:T-[A-Z0-9-]+|PROP-[0-9]{3})")

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
_PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST = {
    "_admit_with_registry_v1": "src/state/state_admission_profile.py",
    "_owned_enum_from_admitted": "src/state/snapshot_combinators.py",
    "_owned_map_from_admitted": "src/state/snapshot_combinators.py",
    "_owned_map_from_canonical_transition_v1": "src/state/state_transitions.py",
    "_OWNED_ENUM_CONSTRUCTION_TOKEN": "src/state/owned_collections.py",
    "_OWNED_MAP_CONSTRUCTION_TOKEN": "src/state/owned_collections.py",
    "_ADMISSION_REGISTRY_TOKEN": "src/state/snapshot_combinators.py",
    "_VALIDATED_LIMITS_TOKEN": "src/state/snapshot_combinators.py",
}
_PROFILE_PATH_SUFFIX = "src/state/state_admission_profile.py"
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

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            local_name = alias.asname or alias.name.split(".", 1)[0]
            self.module_aliases[local_name] = alias.name
            if alias.name in {"pickle", "copyreg"}:
                self._add(node, "FORBIDDEN_RECONSTRUCTION", alias.name)
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        module = node.module or ""
        for alias in node.names:
            local_name = alias.asname or alias.name
            qualified = f"{module}.{alias.name}" if module else alias.name
            self.name_aliases[local_name] = qualified
            if module == "copy" and alias.name in {"copy", "deepcopy"}:
                self._add(node, "FORBIDDEN_COPY", qualified)
            if module in {"pickle", "copyreg"}:
                self._add(node, "FORBIDDEN_RECONSTRUCTION", qualified)
            if module == "typing" and alias.name == "Any":
                self._add(node, "OPEN_AUTHORITY_TYPE", qualified)
            if module == "dataclasses" and alias.name == "is_dataclass":
                self._add(node, "REFLECTIVE_ADMISSION", qualified)
            allowed_path = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(alias.name)
            if allowed_path is not None and not self.relative_path.endswith(allowed_path):
                self._add(node, "PRIVATE_AUTHORITY_IMPORT", qualified)
        self.generic_visit(node)

    def visit_Name(self, node: ast.Name) -> None:
        resolved = self._resolve(node)
        if resolved == "typing.Any" or node.id == "Any":
            self._add(node, "OPEN_AUTHORITY_TYPE", resolved or node.id)
        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if self._resolve(node) == "typing.Any":
            self._add(node, "OPEN_AUTHORITY_TYPE", "typing.Any")
        allowed_path = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(node.attr)
        if allowed_path is not None and not self.relative_path.endswith(allowed_path):
            # Attribute capture is equivalent to importing the private capability.
            self._add(node, "PRIVATE_AUTHORITY_IMPORT", self._resolve(node) or node.attr)
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        symbol = (
            node.slice.value
            if type(node.slice) is ast.Constant and type(node.slice.value) is str
            else None
        )
        allowed_path = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(symbol or "")
        if allowed_path is not None and not self.relative_path.endswith(allowed_path):
            # Reflective dictionary lookup imports the same private capability as
            # direct attribute access; spelling must not weaken the boundary.
            self._add(node, "PRIVATE_AUTHORITY_IMPORT", symbol or "")
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if node.name in _RECONSTRUCTION_METHODS:
            self._add(node, "FORBIDDEN_RECONSTRUCTION", node.name)
        if node.name.startswith("to_scratch_") and self.relative_path.startswith(
            ("src/core/", "src/state/")
        ):
            self._add(node, "MUTABLE_CORE_BOUNDARY", node.name)
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
            self.relative_path.endswith(_PROFILE_PATH_SUFFIX)
            and not self.function_names
            and not node.name.startswith("_")
            and node.name != "admit"
        ):
            self._add(node, "PROFILE_FACADE_SHAPE", f"extra public function:{node.name}")
        if (
            self.relative_path.endswith(_PROFILE_PATH_SUFFIX)
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
        if node.name in _RECONSTRUCTION_METHODS:
            self._add(node, "FORBIDDEN_RECONSTRUCTION", node.name)
        if self.relative_path.endswith(_PROFILE_PATH_SUFFIX) and not self.function_names:
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
        if self.relative_path.endswith(_PROFILE_PATH_SUFFIX) and not node.name.startswith("_"):
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
        if (
            self.relative_path.endswith(_PROFILE_PATH_SUFFIX)
            and called_tail in _LEGACY_MUTABLE_CONSTRUCTORS
        ):
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
            symbol_node = node.args[1]
            symbol = (
                symbol_node.value
                if type(symbol_node) is ast.Constant and type(symbol_node.value) is str
                else None
            )
            allowed_path = _PRIVATE_AUTHORITY_SYMBOL_ALLOWLIST.get(symbol or "")
            if allowed_path is not None and not self.relative_path.endswith(allowed_path):
                # Literal reflection is authority import by another spelling.
                self._add(node, "PRIVATE_AUTHORITY_IMPORT", symbol or "")
        if called in {"copy.copy", "copy.deepcopy"}:
            self._add(node, "FORBIDDEN_COPY", called)
        if called is not None and called.split(".", 1)[0] in {"pickle", "copyreg"}:
            self._add(node, "FORBIDDEN_RECONSTRUCTION", called)
        if called in {"dataclasses.is_dataclass", "is_dataclass"}:
            self._add(node, "REFLECTIVE_ADMISSION", called)
        if called == "object.__new__":
            self._add(node, "CONSTRUCTOR_BYPASS", called)
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
            "_owned_map_from_admitted",
            "_owned_map_from_canonical_transition_v1",
        } and not (
            called_tail in {"_owned_enum_from_admitted", "_owned_map_from_admitted"}
            and self.relative_path.endswith("src/state/snapshot_combinators.py")
            or called_tail == "_owned_map_from_canonical_transition_v1"
            and self.relative_path.endswith("src/state/state_transitions.py")
        ):
            self._add(node, "OWNED_CONSTRUCTION_ESCAPE", called or called_tail)
        if called_tail == "_admit_with_registry_v1":
            if not self.relative_path.endswith(_PROFILE_PATH_SUFFIX):
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
        if called_tail == "build_admission_registry_v1" and not self.relative_path.endswith(
            _PROFILE_PATH_SUFFIX
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
            ),
            "ValidatedAdmissionLimitsV1": (
                (
                    "src/state/snapshot_combinators.py",
                    "build_admission_limits_v1",
                ),
            ),
        }
        required_sites = construction_allowlist.get(called_tail or "")
        current_function = self.function_names[-1] if self.function_names else None
        if required_sites is not None and not any(
            self.relative_path.endswith(required_path) and current_function == required_function
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
        if not self.relative_path.endswith(_PROFILE_PATH_SUFFIX):
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


def _check_registry_constants(
    module: ast.Module,
    relative_path: str,
) -> list[_Violation]:
    is_profile = relative_path.endswith("src/state/state_admission_profile.py")
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
    return display, visitor.violations + _check_registry_constants(module, display)


_SENSITIVE_SOURCE_CODES = {
    "CONSTRUCTION_CALLSITE",
    "DECLARATIVE_REGISTRY_EXECUTION",
    "OWNED_CONSTRUCTION_ESCAPE",
    "PATH_READ_ERROR",
    "PRIVATE_AUTHORITY_IMPORT",
    "PROFILE_FACADE_SHAPE",
    "PROFILE_REGISTRY_DRIFT",
    "PROFILE_BINDING_ESCAPE",
    "REGISTRY_BEHAVIOR_FIELD",
    "REGISTRY_BINDING_ESCAPE",
    "LEGACY_MUTABLE_CONSTRUCTION",
    "MUTABLE_CORE_BOUNDARY",
    "STRUCTURAL_CORE_BOUNDARY",
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
    unique_violations = sorted(set(violations))
    return {
        "checked_paths": sorted(checked_paths),
        "ok": not unique_violations,
        "schema": REPORT_SCHEMA,
        "sensitive_source_glob": "src/**/*.py",
        "violations": [violation.as_json() for violation in unique_violations],
    }


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--authority-path", type=Path, action="append")
    parser.add_argument("--requirements", type=Path, default=DEFAULT_REQUIREMENTS_PATH)
    parser.add_argument("--test-matrix", type=Path, action="append")
    parser.add_argument("--skip-requirements", action="store_true")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    authority_paths = tuple(args.authority_path or DEFAULT_AUTHORITY_PATHS)
    test_matrix_paths = tuple(args.test_matrix or DEFAULT_TEST_MATRIX_PATHS)
    requirements_path = None if args.skip_requirements else args.requirements
    report = check_contract(
        repo_root=args.root,
        authority_paths=authority_paths,
        requirements_path=requirements_path,
        test_matrix_paths=test_matrix_paths,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
