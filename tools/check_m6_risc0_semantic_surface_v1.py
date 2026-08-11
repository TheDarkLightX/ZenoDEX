#!/usr/bin/env python3
"""Fail closed on an unsupported claim of full-M6 Rust/RISC0 equivalence.

This source-level gate checks two necessary preconditions for the launch-plan
claim that a RISC0 guest runs the same M6 transition semantics as the Python
reference: the Rust state declaration must bind every non-derived Python
execution-state and state-root field, the command declaration must bind every
Python command field, and the visible state-root codec must be canonical-JSON
rather than postcard.
It deliberately cannot establish execution equivalence, receipt validity, or
RISC0 image provenance.  Consequently it remains non-activating even if both
static preconditions hold; an independently checked direct/RISC0 trace suite
and real receipt verifier are still required.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_V1 = "zenodex/m6-risc0-semantic-surface/v1"
_RUST_FIELD_RE = re.compile(r"^\s*pub\s+([A-Za-z_][A-Za-z0-9_]*)\s*:", re.MULTILINE)
_PYTHON_CANONICAL_CODEC_MARKER = "canonical_bytes_v1("
_RUST_CANONICAL_CODEC_MARKER = "canonical_json_bytes_v1("
_RUST_POSTCARD_CODEC_MARKER = "hash_postcard_v1("

NONCLAIMS: tuple[str, ...] = (
    "this is a static source-surface inspection, not a Rust or Python transition proof",
    "matching field names or codec markers do not establish byte-level canonical encoding parity",
    "no RISC0 receipt, image binding, recursive proof, validator finality, data availability, or publication authority is verified",
    "a source inspection cannot provide independent direct/RISC0 execution parity evidence",
    "M6 remains research-only and unmounted regardless of this report",
)
REQUIRED_NEXT_EVIDENCE: tuple[str, ...] = (
    "a versioned full-state Python-to-Rust projection with exact canonical byte vectors",
    "per-command direct Python/Rust outcome, state, delta, history, nullifier, and outbox differential traces",
    "real pinned-image RISC0 receipts whose journals bind those full transition outputs",
    "a verifier-owned activation gate that rejects missing, stale, foreign-image, foreign-profile, and crossed-journal receipts before publication",
)


@dataclass(frozen=True, slots=True)
class _SurfaceInspectionV1:
    python_fields: tuple[str, ...]
    python_execution_fields: tuple[str, ...]
    python_command_fields: tuple[str, ...]
    rust_fields: tuple[str, ...]
    rust_command_fields: tuple[str, ...]
    python_canonical_codec_visible: bool
    rust_canonical_codec_visible: bool
    rust_postcard_state_codec_visible: bool
    rust_transition_function_visible: bool
    errors: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class _SurfaceComparisonV1:
    missing_state_root_fields: tuple[str, ...]
    missing_execution_state_fields: tuple[str, ...]
    missing_command_fields: tuple[str, ...]
    extra_rust_state_fields: tuple[str, ...]
    extra_rust_command_fields: tuple[str, ...]
    canonical_state_codec_match: bool


def _read_source_or_error(path: Path, *, label: str) -> tuple[str, str | None]:
    try:
        return path.read_text(encoding="utf-8"), None
    except (OSError, UnicodeError) as exc:
        return "", f"cannot read {label}: {exc}"


def _class_named(tree: ast.Module, *, name: str) -> ast.ClassDef:
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == name:
            return node
    raise ValueError(f"Python {name} is missing")


def _method_named(class_node: ast.ClassDef, *, name: str) -> ast.FunctionDef | ast.AsyncFunctionDef:
    for member in class_node.body:
        if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)) and member.name == name:
            return member
    raise ValueError(f"Python {class_node.name}.{name} is missing")


def _returned_dictionary(method: ast.FunctionDef | ast.AsyncFunctionDef) -> ast.Dict:
    for statement in ast.walk(method):
        if isinstance(statement, ast.Return) and isinstance(statement.value, ast.Dict):
            return statement.value
    raise ValueError(f"Python {method.name} does not return a dictionary")


def _direct_self_fields(root_dictionary: ast.Dict) -> tuple[str, ...]:
    fields: list[str] = []
    for key, value in zip(root_dictionary.keys, root_dictionary.values, strict=True):
        is_self_field = (
            isinstance(value, ast.Attribute)
            and isinstance(value.value, ast.Name)
            and value.value.id == "self"
        )
        if isinstance(key, ast.Constant) and isinstance(key.value, str) and is_self_field:
            fields.append(key.value)
    if not fields:
        raise ValueError("Python M6 state root has no direct state fields")
    if len(fields) != len(set(fields)):
        raise ValueError("Python M6 state root contains duplicate fields")
    return tuple(fields)


def _annotated_fields(
    class_node: ast.ClassDef,
    *,
    label: str,
) -> tuple[str, ...]:
    """Return source-order declared dataclass fields."""

    fields: list[str] = []
    for member in class_node.body:
        if not isinstance(member, ast.AnnAssign) or not isinstance(member.target, ast.Name):
            continue
        field_name = member.target.id
        fields.append(field_name)
    if not fields:
        raise ValueError(f"Python {label} has no annotated fields")
    if len(fields) != len(set(fields)):
        raise ValueError(f"Python {label} contains duplicate fields")
    return tuple(fields)


def _non_derived_state_fields(state_class: ast.ClassDef) -> tuple[str, ...]:
    """Remove deterministic archive-root caches from the execution surface."""

    declared_fields = _annotated_fields(
        state_class,
        label="M6ApplicationStateV1 execution state",
    )
    # These are deterministic caches of archives committed through separate
    # roots.  They carry no independent transition authority.
    return tuple(field_name for field_name in declared_fields if not field_name.endswith("_cache"))


def _python_state_surface(source: str) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    """Return Python execution-state, state-root, and command fields in source order."""

    try:
        tree = ast.parse(source, filename="m6_safe_mount_types_v1.py")
    except SyntaxError as exc:
        raise ValueError(f"cannot parse Python M6 types: {exc.msg}") from exc
    state_class = _class_named(tree, name="M6ApplicationStateV1")
    command_class = _class_named(tree, name="GlobalCommandV1")
    state_root_method = _method_named(state_class, name="_state_root_canonical")
    return (
        _non_derived_state_fields(state_class),
        _direct_self_fields(_returned_dictionary(state_root_method)),
        _annotated_fields(command_class, label="GlobalCommandV1"),
    )


def _balanced_block(source: str, marker: str, *, label: str) -> str:
    start = source.find(marker)
    if start < 0:
        raise ValueError(f"{label} is missing")
    opening = source.find("{", start)
    if opening < 0:
        raise ValueError(f"{label} has no opening brace")
    depth = 0
    for index in range(opening, len(source)):
        character = source[index]
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return source[opening + 1 : index]
    raise ValueError(f"{label} has unbalanced braces")


def _rust_struct_fields(source: str, *, name: str) -> tuple[str, ...]:
    state_struct = _balanced_block(source, f"pub struct {name}", label=f"Rust {name} declaration")
    fields = tuple(_RUST_FIELD_RE.findall(state_struct))
    if not fields:
        raise ValueError(f"Rust {name} has no public fields")
    if len(fields) != len(set(fields)):
        raise ValueError(f"Rust {name} contains duplicate public fields")
    return fields


def _rust_state_surface(source: str) -> tuple[tuple[str, ...], tuple[str, ...], bool, bool, bool]:
    """Extract the closed Rust state declaration and visible root-codec markers."""

    fields = _rust_struct_fields(source, name="M6ApplicationStateV1")
    command_fields = _rust_struct_fields(source, name="GlobalCommandV1")
    implementation = _balanced_block(
        source,
        "impl M6ApplicationStateV1",
        label="Rust M6ApplicationStateV1 implementation",
    )
    state_root = _balanced_block(
        implementation,
        "pub fn state_root",
        label="Rust M6ApplicationStateV1.state_root",
    )
    return (
        fields,
        command_fields,
        _RUST_CANONICAL_CODEC_MARKER in state_root,
        _RUST_POSTCARD_CODEC_MARKER in state_root,
        "pub fn run_m6_transition_v1" in source,
    )


def _inspect_sources(
    python_source: str,
    rust_source: str,
    *,
    initial_errors: tuple[str, ...] = (),
) -> _SurfaceInspectionV1:
    errors = list(initial_errors)
    try:
        python_execution_fields, python_fields, python_command_fields = _python_state_surface(
            python_source
        )
    except ValueError as exc:
        python_fields = ()
        python_execution_fields = ()
        python_command_fields = ()
        errors.append(str(exc))
    try:
        (
            rust_fields,
            rust_command_fields,
            rust_canonical_codec_visible,
            rust_postcard_state_codec_visible,
            rust_transition_function_visible,
        ) = _rust_state_surface(rust_source)
    except ValueError as exc:
        rust_fields = ()
        rust_command_fields = ()
        rust_canonical_codec_visible = False
        rust_postcard_state_codec_visible = False
        rust_transition_function_visible = False
        errors.append(str(exc))
    return _SurfaceInspectionV1(
        python_fields=python_fields,
        python_execution_fields=python_execution_fields,
        python_command_fields=python_command_fields,
        rust_fields=rust_fields,
        rust_command_fields=rust_command_fields,
        python_canonical_codec_visible=_PYTHON_CANONICAL_CODEC_MARKER in python_source,
        rust_canonical_codec_visible=rust_canonical_codec_visible,
        rust_postcard_state_codec_visible=rust_postcard_state_codec_visible,
        rust_transition_function_visible=rust_transition_function_visible,
        errors=tuple(errors),
    )


def _canonical_codec_match(inspection: _SurfaceInspectionV1) -> bool:
    return (
        inspection.python_canonical_codec_visible
        and inspection.rust_canonical_codec_visible
        and not inspection.rust_postcard_state_codec_visible
    )


def _compare_surfaces(inspection: _SurfaceInspectionV1) -> _SurfaceComparisonV1:
    required_root_fields = set(inspection.python_fields)
    required_execution_fields = set(inspection.python_execution_fields)
    declared_state_fields = set(inspection.rust_fields)
    required_command_fields = set(inspection.python_command_fields)
    declared_command_fields = set(inspection.rust_command_fields)
    return _SurfaceComparisonV1(
        missing_state_root_fields=tuple(sorted(required_root_fields - declared_state_fields)),
        missing_execution_state_fields=tuple(
            sorted(required_execution_fields - declared_state_fields)
        ),
        missing_command_fields=tuple(sorted(required_command_fields - declared_command_fields)),
        extra_rust_state_fields=tuple(sorted(declared_state_fields - required_root_fields)),
        extra_rust_command_fields=tuple(sorted(declared_command_fields - required_command_fields)),
        canonical_state_codec_match=_canonical_codec_match(inspection),
    )


def _semantic_blockers(
    inspection: _SurfaceInspectionV1,
    comparison: _SurfaceComparisonV1,
) -> list[str]:
    errors = list(inspection.errors)
    if comparison.missing_state_root_fields:
        errors.append(
            "Rust M6 state omits Python state-root fields: "
            + ", ".join(comparison.missing_state_root_fields)
        )
    if comparison.missing_execution_state_fields:
        errors.append(
            "Rust M6 state omits Python execution fields: "
            + ", ".join(comparison.missing_execution_state_fields)
        )
    if comparison.missing_command_fields:
        errors.append(
            "Rust M6 command omits Python fields: " + ", ".join(comparison.missing_command_fields)
        )
    if not inspection.rust_transition_function_visible:
        errors.append("Rust run_m6_transition_v1 is missing")
    if not comparison.canonical_state_codec_match:
        errors.append(
            "Python/Rust canonical state-root codec parity is not statically visible "
            "or Rust state_root still uses postcard"
        )
    errors.append("independent direct/RISC0 execution parity evidence is absent")
    return errors


def _semantic_surface_status(
    inspection: _SurfaceInspectionV1,
    comparison: _SurfaceComparisonV1,
) -> str:
    if (
        inspection.errors
        or comparison.missing_state_root_fields
        or comparison.missing_execution_state_fields
        or comparison.missing_command_fields
        or not comparison.canonical_state_codec_match
        or not inspection.rust_transition_function_visible
    ):
        return "BLOCKED_SEMANTIC_SURFACE"
    return "BLOCKED_EXECUTABLE_PARITY_EVIDENCE"


def _report_from_inspection(inspection: _SurfaceInspectionV1) -> dict[str, object]:
    comparison = _compare_surfaces(inspection)
    errors = _semantic_blockers(inspection, comparison)
    status = _semantic_surface_status(inspection, comparison)
    return {
        "activation_eligible": False,
        "canonical_state_codec_match": comparison.canonical_state_codec_match,
        "errors": errors,
        "extra_rust_state_fields": list(comparison.extra_rust_state_fields),
        "extra_rust_command_fields": list(comparison.extra_rust_command_fields),
        "independent_execution_parity_evidence": False,
        "missing_state_root_fields": list(comparison.missing_state_root_fields),
        "missing_execution_state_fields": list(comparison.missing_execution_state_fields),
        "missing_command_fields": list(comparison.missing_command_fields),
        "nonclaims": list(NONCLAIMS),
        "ok": False,
        "python_canonical_codec_visible": inspection.python_canonical_codec_visible,
        "python_execution_state_fields": list(inspection.python_execution_fields),
        "python_command_fields": list(inspection.python_command_fields),
        "python_to_rust_command_surface_match": bool(inspection.python_command_fields)
        and not comparison.missing_command_fields,
        "python_to_rust_execution_state_surface_match": bool(
            inspection.python_execution_fields
        )
        and not comparison.missing_execution_state_fields,
        "python_state_root_fields": list(inspection.python_fields),
        "python_to_rust_state_surface_match": bool(inspection.python_fields)
        and not comparison.missing_state_root_fields,
        "required_next_evidence": list(REQUIRED_NEXT_EVIDENCE),
        "rust_canonical_codec_visible": inspection.rust_canonical_codec_visible,
        "rust_postcard_state_codec_visible": inspection.rust_postcard_state_codec_visible,
        "rust_state_fields": list(inspection.rust_fields),
        "rust_command_fields": list(inspection.rust_command_fields),
        "rust_transition_function_visible": inspection.rust_transition_function_visible,
        "schema": SCHEMA_V1,
        "status": status,
    }


def inspect_m6_risc0_semantic_surface(
    python_types_path: Path,
    rust_core_path: Path,
) -> dict[str, object]:
    """Inspect explicit source paths without assigning any execution authority."""

    python_source, python_error = _read_source_or_error(
        python_types_path,
        label="Python M6 types",
    )
    rust_source, rust_error = _read_source_or_error(
        rust_core_path,
        label="Rust M6 core",
    )
    initial_errors = tuple(error for error in (python_error, rust_error) if error is not None)
    inspection = _inspect_sources(
        python_source,
        rust_source,
        initial_errors=initial_errors,
    )
    return _report_from_inspection(inspection)


def check_m6_risc0_semantic_surface(root: Path = REPO_ROOT) -> dict[str, object]:
    """Inspect the repository M6 Python and RISC0 sources with a closed report."""

    root = root.resolve()
    return inspect_m6_risc0_semantic_surface(
        root / "src" / "core" / "m6_safe_mount_types_v1.py",
        root / "zk" / "recursive_stark_v2_risc0" / "shared" / "src" / "m6_core_v1.rs",
    )


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = check_m6_risc0_semantic_surface(args.root)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
