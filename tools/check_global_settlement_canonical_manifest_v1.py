#!/usr/bin/env python3
"""Check the closed Python canonical-admission surface for Settlement ABI V1.

The checker is intentionally static.  It does not import domain modules, run
module initializers, or discover types at runtime.  Its source-closure digest
binds the reviewed manifest to every defining module and every current source
caller of the canonical byte/hash entry points.  A digest change requires a
fresh audit and an explicit checker update.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Final, Iterable, Sequence

MANIFEST_PATH_V1: Final = Path(
    "src/core/global_settlement_canonical_manifest_v1.py"
)
DISPATCHER_PATH_V1: Final = Path("src/core/global_settlement_types_v1.py")

SERIALIZER_TUPLE_V1: Final = "GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1"
ENUM_TUPLE_V1: Final = "GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1"
SERIALIZER_SET_V1: Final = "GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPE_SET_V1"
ENUM_SET_V1: Final = "GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPE_SET_V1"

EXPECTED_SERIALIZER_COUNT_V1: Final = 104
EXPECTED_ENUM_COUNT_V1: Final = 35
EXPECTED_CALL_COUNTS_V1: Final[dict[str, int]] = {
    "canonical_economic_command_body_bytes_v1": 1,
    "canonical_global_bytes_v1": 48,
    "hash_economic_command_body_v1": 4,
    "hash_global_v1": 219,
}
EXPECTED_CALL_FILE_COUNT_V1: Final = 93
EXPECTED_SOURCE_CLOSURE_SHA256_V1: Final = (
    "76b200564f8f5a48b78579c8dfab137c27c76475f42c0c5503f013fdd1c0c830"
)


class CanonicalManifestCheckError(ValueError):
    """A deterministic static admission check could not be completed."""


def _parse_python(path: Path) -> ast.Module:
    try:
        return ast.parse(path.read_text(encoding="utf-8"), filename=path.as_posix())
    except (OSError, SyntaxError, UnicodeError) as exc:
        raise CanonicalManifestCheckError(f"cannot parse {path.as_posix()}: {exc}") from exc


def _annotated_assignment(tree: ast.Module, name: str) -> ast.expr:
    matches = [
        node.value
        for node in tree.body
        if isinstance(node, ast.AnnAssign)
        and isinstance(node.target, ast.Name)
        and node.target.id == name
        and node.value is not None
    ]
    if len(matches) != 1:
        raise CanonicalManifestCheckError(
            f"manifest must define exactly one annotated assignment for {name}"
        )
    return matches[0]


def _literal_string_tuple(tree: ast.Module, name: str) -> tuple[str, ...]:
    expression = _annotated_assignment(tree, name)
    try:
        value = ast.literal_eval(expression)
    except (ValueError, TypeError, SyntaxError) as exc:
        raise CanonicalManifestCheckError(f"{name} must be a literal tuple") from exc
    if type(value) is not tuple or any(type(item) is not str for item in value):
        raise CanonicalManifestCheckError(f"{name} must be a literal tuple of strings")
    return value


def _dotted_name(expression: ast.expr) -> str | None:
    if isinstance(expression, ast.Name):
        return expression.id
    if isinstance(expression, ast.Attribute):
        prefix = _dotted_name(expression.value)
        if prefix is not None:
            return f"{prefix}.{expression.attr}"
    return None


def _check_data_only_manifest(tree: ast.Module) -> list[str]:
    errors: list[str] = []
    expected_assignments = {
        SERIALIZER_TUPLE_V1,
        ENUM_TUPLE_V1,
        SERIALIZER_SET_V1,
        ENUM_SET_V1,
    }
    seen_assignments: set[str] = set()
    for node in tree.body:
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant):
            continue
        if isinstance(node, ast.ImportFrom):
            imported = {alias.name for alias in node.names}
            if node.module == "__future__" and imported == {"annotations"}:
                continue
            if node.module == "typing" and imported == {"Final"}:
                continue
            errors.append(f"manifest imports forbidden module {node.module!r}")
            continue
        if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            seen_assignments.add(node.target.id)
            continue
        errors.append(f"manifest contains forbidden top-level {type(node).__name__}")

    if seen_assignments != expected_assignments:
        errors.append(
            "manifest assignments differ from the four frozen admission constants: "
            f"{sorted(seen_assignments)}"
        )
    calls = [node for node in ast.walk(tree) if isinstance(node, ast.Call)]
    if any(_dotted_name(node.func) != "frozenset" for node in calls):
        errors.append("manifest may call only the built-in frozenset constructor")
    expected_set_sources = {
        SERIALIZER_SET_V1: SERIALIZER_TUPLE_V1,
        ENUM_SET_V1: ENUM_TUPLE_V1,
    }
    for set_name, tuple_name in expected_set_sources.items():
        expression = _annotated_assignment(tree, set_name)
        if not (
            isinstance(expression, ast.Call)
            and _dotted_name(expression.func) == "frozenset"
            and len(expression.args) == 1
            and not expression.keywords
            and isinstance(expression.args[0], ast.Name)
            and expression.args[0].id == tuple_name
        ):
            errors.append(f"{set_name} must freeze exactly {tuple_name}")
    return errors


def _check_manifest_shape(
    serializers: tuple[str, ...],
    enums: tuple[str, ...],
) -> list[str]:
    errors: list[str] = []
    for label, values, expected_count in (
        ("serializer", serializers, EXPECTED_SERIALIZER_COUNT_V1),
        ("enum", enums, EXPECTED_ENUM_COUNT_V1),
    ):
        if len(values) != expected_count:
            errors.append(
                f"{label} manifest count is {len(values)}; expected {expected_count}"
            )
        if values != tuple(sorted(values)):
            errors.append(f"{label} manifest must be sorted")
        if len(values) != len(set(values)):
            errors.append(f"{label} manifest contains duplicates")
        for value in values:
            module_name, separator, type_name = value.rpartition(".")
            if (
                not separator
                or not module_name.startswith("src.")
                or not all(part.isidentifier() for part in module_name.split("."))
                or not type_name.isidentifier()
            ):
                errors.append(f"invalid {label} fully-qualified type name: {value!r}")
    overlap = sorted(set(serializers).intersection(enums))
    if overlap:
        errors.append(f"types appear in both admission classes: {overlap}")
    return errors


def _source_path_for_fqn(repo_root: Path, qualified_name: str) -> tuple[Path, str]:
    module_name, _, type_name = qualified_name.rpartition(".")
    return repo_root.joinpath(*module_name.split(".")).with_suffix(".py"), type_name


def _top_level_class(tree: ast.Module, name: str) -> ast.ClassDef | None:
    matches = [
        node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == name
    ]
    return matches[0] if len(matches) == 1 else None


def _check_declared_types(
    repo_root: Path,
    serializers: tuple[str, ...],
    enums: tuple[str, ...],
) -> tuple[list[str], set[Path]]:
    errors: list[str] = []
    defining_paths: set[Path] = set()
    for kind, values in (("serializer", serializers), ("enum", enums)):
        for qualified_name in values:
            path, type_name = _source_path_for_fqn(repo_root, qualified_name)
            relative_path = path.relative_to(repo_root).as_posix()
            if not path.is_file():
                errors.append(f"{qualified_name} has no defining file {relative_path}")
                continue
            defining_paths.add(path)
            tree = _parse_python(path)
            class_node = _top_level_class(tree, type_name)
            if class_node is None:
                errors.append(
                    f"{qualified_name} must be exactly one top-level class in {relative_path}"
                )
                continue
            owned_serializers = [
                node
                for node in class_node.body
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name == "to_canonical"
            ]
            if kind == "serializer":
                if len(owned_serializers) != 1 or not isinstance(
                    owned_serializers[0], ast.FunctionDef
                ):
                    errors.append(
                        f"{qualified_name} must own one synchronous to_canonical function"
                    )
            else:
                bases = {_dotted_name(base) for base in class_node.bases}
                if not {"str", "Enum"}.issubset(bases):
                    errors.append(f"{qualified_name} must be a declared str, Enum class")
                if owned_serializers:
                    errors.append(f"{qualified_name} must not own to_canonical")
    return errors, defining_paths


def _function_node(tree: ast.Module, name: str) -> ast.FunctionDef | None:
    matches = [
        node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == name
    ]
    return matches[0] if len(matches) == 1 else None


def _check_dispatcher(tree: ast.Module) -> list[str]:
    errors: list[str] = []
    all_names = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}
    forbidden_names = {
        "Protocol",
        "runtime_checkable",
        "_Canonicalizable",
        "importlib",
        "pkgutil",
        "__import__",
    }
    present_forbidden = sorted(all_names.intersection(forbidden_names))
    if present_forbidden:
        errors.append(f"dispatcher contains forbidden dynamic admission names: {present_forbidden}")

    projection = _function_node(tree, "_canonical_registered_projection_v1")
    canonical_value = _function_node(tree, "_canonical_value")
    identity_check = _function_node(tree, "_require_loaded_canonical_type_v1")
    for name, function_node in (
        ("_canonical_registered_projection_v1", projection),
        ("_canonical_value", canonical_value),
        ("_require_loaded_canonical_type_v1", identity_check),
    ):
        if function_node is None:
            errors.append(f"dispatcher must define exactly one top-level {name}")
    if projection is None or canonical_value is None or identity_check is None:
        return errors

    guarded_nodes: Iterable[ast.AST] = (projection, canonical_value, identity_check)
    guarded_calls = [
        node
        for root in guarded_nodes
        for node in ast.walk(root)
        if isinstance(node, ast.Call)
    ]
    dotted_calls = {_dotted_name(node.func) for node in guarded_calls}
    required_calls = {
        "ModuleType.__getattribute__",
        "object.__getattribute__",
        "sys.modules.get",
        "type.__getattribute__",
    }
    missing_calls = sorted(required_calls.difference(dotted_calls))
    if missing_calls:
        errors.append(f"dispatcher lacks authority-closed identity calls: {missing_calls}")
    identity_compares = [
        node for node in ast.walk(identity_check) if isinstance(node, ast.Compare)
    ]
    if not any(
        isinstance(compare.left, ast.Call)
        and _dotted_name(compare.left.func) == "namespace.get"
        and len(compare.left.args) == 1
        and isinstance(compare.left.args[0], ast.Name)
        and compare.left.args[0].id == "type_name"
        and len(compare.ops) == 1
        and isinstance(compare.ops[0], ast.IsNot)
        and len(compare.comparators) == 1
        and isinstance(compare.comparators[0], ast.Name)
        and compare.comparators[0].id == "candidate_type"
        for compare in identity_compares
    ):
        errors.append("loaded-module binding must be the exact candidate type identity")
    required_exact_type_checks = {("module", "ModuleType"), ("namespace", "dict")}
    observed_exact_type_checks: set[tuple[str, str]] = set()
    for compare in identity_compares:
        if not (
            isinstance(compare.left, ast.Call)
            and isinstance(compare.left.func, ast.Name)
            and compare.left.func.id == "type"
            and len(compare.left.args) == 1
            and isinstance(compare.left.args[0], ast.Name)
            and len(compare.ops) == 1
            and isinstance(compare.ops[0], ast.IsNot)
            and len(compare.comparators) == 1
            and isinstance(compare.comparators[0], ast.Name)
        ):
            continue
        observed_exact_type_checks.add(
            (compare.left.args[0].id, compare.comparators[0].id)
        )
    if not required_exact_type_checks.issubset(observed_exact_type_checks):
        errors.append("module and namespace identity must use exact built-in type checks")
    projection_compares = [
        node for node in ast.walk(projection) if isinstance(node, ast.Compare)
    ]
    if not any(
        isinstance(compare.left, ast.Call)
        and isinstance(compare.left.func, ast.Name)
        and compare.left.func.id == "type"
        and len(compare.left.args) == 1
        and isinstance(compare.left.args[0], ast.Name)
        and compare.left.args[0].id == "serializer"
        and len(compare.ops) == 1
        and isinstance(compare.ops[0], ast.IsNot)
        and len(compare.comparators) == 1
        and isinstance(compare.comparators[0], ast.Name)
        and compare.comparators[0].id == "FunctionType"
        for compare in projection_compares
    ):
        errors.append("admitted serializer must be an exact class-owned Python function")
    if not any(
        isinstance(call.func, ast.Name)
        and call.func.id == "serializer"
        and len(call.args) == 1
        and isinstance(call.args[0], ast.Name)
        and call.args[0].id == "value"
        and not call.keywords
        for call in guarded_calls
    ):
        errors.append("dispatcher must call the admitted class serializer unbound")
    if not any(
        isinstance(node.func, ast.Name)
        and node.func.id == "_canonical_registered_projection_v1"
        for node in ast.walk(canonical_value)
        if isinstance(node, ast.Call)
    ):
        errors.append("_canonical_value must delegate typed values to the closed projection")
    for call in guarded_calls:
        if isinstance(call.func, ast.Attribute) and call.func.attr == "to_canonical":
            errors.append("dispatcher must never invoke an instance-bound to_canonical hook")
        call_name = _dotted_name(call.func)
        if call_name in {"importlib.import_module", "__import__"}:
            errors.append("dispatcher must not import or discover admitted types")
        if isinstance(call.func, ast.Name) and call.func.id == "isinstance":
            if len(call.args) >= 2 and any(
                isinstance(descendant, ast.Name) and descendant.id == "Enum"
                for descendant in ast.walk(call.args[1])
            ):
                errors.append("dispatcher must not structurally admit generic Enum instances")
    for syntax_node in ast.walk(projection):
        if isinstance(syntax_node, (ast.Import, ast.ImportFrom)):
            errors.append("projection must not import types at call time")
        if isinstance(syntax_node, ast.Call) and isinstance(
            syntax_node.func, ast.Attribute
        ):
            if syntax_node.func.attr in {"register", "add", "update", "setdefault"}:
                errors.append("projection must not mutate its admission registry")
    for manifest_name in (SERIALIZER_SET_V1, ENUM_SET_V1):
        if manifest_name not in all_names:
            errors.append(f"dispatcher does not consult {manifest_name}")
    return errors


def _call_inventory(repo_root: Path) -> tuple[Counter[str], set[Path]]:
    target_names = set(EXPECTED_CALL_COUNTS_V1)
    counts: Counter[str] = Counter()
    call_paths: set[Path] = set()
    for path in sorted((repo_root / "src").rglob("*.py")):
        tree = _parse_python(path)
        matched = False
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            call_name = _dotted_name(node.func)
            leaf_name = call_name.rsplit(".", 1)[-1] if call_name else None
            if leaf_name in target_names:
                counts[leaf_name] += 1
                matched = True
        if matched:
            call_paths.add(path)
    return counts, call_paths


def _source_closure_sha256(repo_root: Path, paths: Iterable[Path]) -> str:
    digest = hashlib.sha256()
    for path in sorted(set(paths), key=lambda item: item.relative_to(repo_root).as_posix()):
        relative_path = path.relative_to(repo_root).as_posix().encode("utf-8")
        file_digest = hashlib.sha256(path.read_bytes()).hexdigest().encode("ascii")
        digest.update(relative_path)
        digest.update(b"\0")
        digest.update(file_digest)
        digest.update(b"\n")
    return digest.hexdigest()


def check_repository(repo_root: Path) -> dict[str, object]:
    repo_root = repo_root.resolve()
    manifest_path = repo_root / MANIFEST_PATH_V1
    dispatcher_path = repo_root / DISPATCHER_PATH_V1
    manifest_tree = _parse_python(manifest_path)
    dispatcher_tree = _parse_python(dispatcher_path)

    serializers = _literal_string_tuple(manifest_tree, SERIALIZER_TUPLE_V1)
    enums = _literal_string_tuple(manifest_tree, ENUM_TUPLE_V1)
    errors = _check_data_only_manifest(manifest_tree)
    errors.extend(_check_manifest_shape(serializers, enums))
    type_errors, defining_paths = _check_declared_types(repo_root, serializers, enums)
    errors.extend(type_errors)
    errors.extend(_check_dispatcher(dispatcher_tree))

    call_counts, call_paths = _call_inventory(repo_root)
    if dict(sorted(call_counts.items())) != EXPECTED_CALL_COUNTS_V1:
        errors.append(
            "canonical helper call inventory changed: "
            f"{dict(sorted(call_counts.items()))}; expected {EXPECTED_CALL_COUNTS_V1}"
        )
    if len(call_paths) != EXPECTED_CALL_FILE_COUNT_V1:
        errors.append(
            f"canonical helper call-file count is {len(call_paths)}; "
            f"expected {EXPECTED_CALL_FILE_COUNT_V1}"
        )

    closure_paths = defining_paths.union(call_paths)
    closure_paths.update({manifest_path, dispatcher_path})
    closure_digest = _source_closure_sha256(repo_root, closure_paths)
    if closure_digest != EXPECTED_SOURCE_CLOSURE_SHA256_V1:
        errors.append(
            f"canonical source closure digest is {closure_digest}; "
            f"expected {EXPECTED_SOURCE_CLOSURE_SHA256_V1}"
        )
    return {
        "ok": not errors,
        "schema": "zenodex/global-settlement-canonical-manifest-check/v1",
        "serializer_type_count": len(serializers),
        "enum_type_count": len(enums),
        "canonical_helper_call_counts": dict(sorted(call_counts.items())),
        "canonical_helper_call_file_count": len(call_paths),
        "source_closure_file_count": len(closure_paths),
        "source_closure_sha256": closure_digest,
        "errors": errors,
        "nonclaims": [
            "Static source closure is not a proof of semantic call-graph completeness.",
            "Python process and loaded-module namespace integrity remain trusted premises.",
            "Registered class-owned serializer implementations remain trusted reviewed source.",
        ],
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        report = check_repository(args.repo_root)
    except CanonicalManifestCheckError as exc:
        report = {
            "ok": False,
            "schema": "zenodex/global-settlement-canonical-manifest-check/v1",
            "errors": [str(exc)],
        }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        status = "PASS" if report["ok"] else "FAIL"
        print(f"global-settlement canonical manifest: {status}")
        report_errors = report.get("errors")
        if isinstance(report_errors, list):
            for error in report_errors:
                print(f"- {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
