from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from src.fire.pathing_v1 import fire_stdlib_objects_dir, resolve_fire_spec_path
from src.fire.registry.object_manifest_v1 import FireContractProvenance, FireWitnessRequirement
from src.fire.verifier.cert_v1 import FireCertEnv, FireInterval, verify_interval_certificate

from .fmos_v1 import FireImportedInterfaceRef, FireMathObjectSpec, FireTermFieldSpec
from .object_compiler_v1 import (
    FireExpr,
    add_expr,
    cap_expr,
    clamp_expr,
    compile_interval_expression_certificate,
    const_expr,
    exact_param_expr,
    infer_fire_expr_unit,
    max_expr,
    min_expr,
    mul_expr,
    parse_fire_unit,
    positive_part_expr,
    source_bound_expr,
    sub_expr,
)


FIRE_FMOS_FILE_SCHEMA = "zenodex/fire-math-object-spec/v1"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _require_mapping(name: str, value: object) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


@dataclass(frozen=True)
class FireValueRef:
    kind: str
    value: int | None = None
    term: str | None = None

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireValueRef":
        if not isinstance(payload, Mapping):
            raise TypeError("value ref must be a mapping")
        kind = _require_nonempty_str("value ref kind", payload["kind"])
        value = payload.get("value")
        term = payload.get("term")
        if kind == "const":
            if not isinstance(value, int) or isinstance(value, bool):
                raise TypeError("const value ref requires int value")
            return cls(kind=kind, value=value)
        if kind == "term":
            if not isinstance(term, str) or not term:
                raise TypeError("term value ref requires non-empty term")
            return cls(kind=kind, term=term)
        raise ValueError(f"unsupported value ref kind: {kind}")


@dataclass(frozen=True)
class FireContractSpec:
    name: str
    role: str

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireContractSpec":
        if not isinstance(payload, Mapping):
            raise TypeError("contract spec must be a mapping")
        name = payload.get("name")
        role = payload.get("role")
        if not isinstance(name, str) or not name:
            raise TypeError("contract spec requires non-empty name")
        if not isinstance(role, str) or not role:
            raise TypeError("contract spec requires non-empty role")
        return cls(name=name, role=role)


@dataclass(frozen=True)
class FireSourceBoundSpec:
    name: str
    unit: str
    lower: FireValueRef
    upper: FireValueRef
    contract: FireContractSpec | None = None

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireSourceBoundSpec":
        if not isinstance(payload, Mapping):
            raise TypeError("source bound spec must be a mapping")
        name = payload.get("name")
        if not isinstance(name, str) or not name:
            raise TypeError("source bound spec requires non-empty name")
        return cls(
            name=name,
            unit=_require_nonempty_str("source bound unit", payload["unit"]),
            lower=FireValueRef.from_dict(payload["lower"]),
            upper=FireValueRef.from_dict(payload["upper"]),
            contract=None if payload.get("contract") is None else FireContractSpec.from_dict(payload["contract"]),
        )


@dataclass(frozen=True)
class FireImportSpec:
    name: str
    interface_object_id: str
    interface_output: str
    unit: str
    lower: FireValueRef
    upper: FireValueRef
    contract: FireContractSpec | None = None

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireImportSpec":
        if not isinstance(payload, Mapping):
            raise TypeError("import spec must be a mapping")
        name = payload.get("name")
        interface_object_id = payload.get("interface_object_id")
        interface_output = payload.get("interface_output")
        if not isinstance(name, str) or not name:
            raise TypeError("import spec requires non-empty name")
        if not isinstance(interface_object_id, str) or not interface_object_id:
            raise TypeError("import spec requires non-empty interface_object_id")
        if not isinstance(interface_output, str) or not interface_output:
            raise TypeError("import spec requires non-empty interface_output")
        return cls(
            name=name,
            interface_object_id=interface_object_id,
            interface_output=interface_output,
            unit=_require_nonempty_str("import unit", payload["unit"]),
            lower=FireValueRef.from_dict(payload["lower"]),
            upper=FireValueRef.from_dict(payload["upper"]),
            contract=None if payload.get("contract") is None else FireContractSpec.from_dict(payload["contract"]),
        )


@dataclass(frozen=True)
class FireWitnessSpec:
    name: str
    freshness: str
    unit: str
    lower: FireValueRef
    upper: FireValueRef
    contract: FireContractSpec | None = None

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireWitnessSpec":
        if not isinstance(payload, Mapping):
            raise TypeError("witness spec must be a mapping")
        name = payload.get("name")
        freshness = payload.get("freshness")
        if not isinstance(name, str) or not name:
            raise TypeError("witness spec requires non-empty name")
        if not isinstance(freshness, str) or not freshness:
            raise TypeError("witness spec requires non-empty freshness")
        return cls(
            name=name,
            freshness=freshness,
            unit=_require_nonempty_str("witness unit", payload["unit"]),
            lower=FireValueRef.from_dict(payload["lower"]),
            upper=FireValueRef.from_dict(payload["upper"]),
            contract=None if payload.get("contract") is None else FireContractSpec.from_dict(payload["contract"]),
        )


@dataclass(frozen=True)
class FireExprFile:
    kind: str
    value: int | None = None
    name: str | None = None
    left: "FireExprFile | None" = None
    right: "FireExprFile | None" = None
    inner: "FireExprFile | None" = None
    lower: "FireExprFile | None" = None
    upper: "FireExprFile | None" = None

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireExprFile":
        if not isinstance(payload, Mapping):
            raise TypeError("expression payload must be a mapping")
        kind = _require_nonempty_str("expression kind", payload["kind"])
        value = payload.get("value")
        if "value" in payload and (not isinstance(value, int) or isinstance(value, bool)):
            raise TypeError("expression value must be an int")
        name = payload.get("name")
        if "name" in payload and (not isinstance(name, str) or not name):
            raise TypeError("expression name must be a non-empty string")
        return cls(
            kind=kind,
            value=value,
            name=name,
            left=None if "left" not in payload else cls.from_dict(payload["left"]),
            right=None if "right" not in payload else cls.from_dict(payload["right"]),
            inner=None if "inner" not in payload else cls.from_dict(payload["inner"]),
            lower=None if "lower" not in payload else cls.from_dict(payload["lower"]),
            upper=None if "upper" not in payload else cls.from_dict(payload["upper"]),
        )


@dataclass(frozen=True)
class FireOutputSpec:
    name: str
    description: str
    unit: str
    expression: FireExprFile

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireOutputSpec":
        if not isinstance(payload, Mapping):
            raise TypeError("output spec must be a mapping")
        name = payload.get("name")
        description = payload.get("description")
        if not isinstance(name, str) or not name:
            raise TypeError("output spec requires non-empty name")
        if not isinstance(description, str) or not description:
            raise TypeError("output spec requires non-empty description")
        return cls(
            name=name,
            description=description,
            unit=_require_nonempty_str("output unit", payload["unit"]),
            expression=FireExprFile.from_dict(payload["expression"]),
        )


@dataclass(frozen=True)
class FireMathObjectSpecFile:
    schema: str
    object_id: str
    object_name: str
    cli_help: str
    object_version: str
    object_family: str
    settlement_asset: str
    payoff_summary: str
    ir_hash: str
    term_fields: tuple[FireTermFieldSpec, ...]
    source_bounds: tuple[FireSourceBoundSpec, ...]
    imports: tuple[FireImportSpec, ...]
    witnesses: tuple[FireWitnessSpec, ...]
    outputs: tuple[FireOutputSpec, ...]
    expression: FireExprFile

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireMathObjectSpecFile":
        if not isinstance(payload, Mapping):
            raise TypeError("spec payload must be a mapping")
        schema = _require_nonempty_str("schema", payload["schema"])
        if schema != FIRE_FMOS_FILE_SCHEMA:
            raise ValueError(f"unsupported FIRE FMOS file schema: {schema}")
        term_fields_payload = payload.get("term_fields")
        source_bounds_payload = payload.get("source_bounds", [])
        imports_payload = payload.get("imports", [])
        witnesses_payload = payload.get("witnesses")
        outputs_payload = payload.get("outputs")
        if not isinstance(term_fields_payload, list):
            raise TypeError("term_fields must be a list")
        if not isinstance(source_bounds_payload, list):
            raise TypeError("source_bounds must be a list")
        if not isinstance(imports_payload, list):
            raise TypeError("imports must be a list")
        if not isinstance(witnesses_payload, list):
            raise TypeError("witnesses must be a list")
        if not isinstance(outputs_payload, list):
            raise TypeError("outputs must be a list")
        return cls(
            schema=schema,
            object_id=_require_nonempty_str("object_id", payload["object_id"]),
            object_name=_require_nonempty_str("object_name", payload["object_name"]),
            cli_help=_require_nonempty_str("cli_help", payload["cli_help"]),
            object_version=_require_nonempty_str("object_version", payload["object_version"]),
            object_family=_require_nonempty_str("object_family", payload["object_family"]),
            settlement_asset=_require_nonempty_str("settlement_asset", payload["settlement_asset"]),
            payoff_summary=_require_nonempty_str("payoff_summary", payload["payoff_summary"]),
            ir_hash=_require_nonempty_str("ir_hash", payload["ir_hash"]),
            term_fields=tuple(
                FireTermFieldSpec(
                    name=_require_nonempty_str(
                        "term field name",
                        _require_mapping("term field", item)["name"],
                    ),
                    description=_require_nonempty_str("term field description", item["description"]),
                    unit=_require_nonempty_str("term field unit", item["unit"]),
                    minimum=item["minimum"],
                    maximum=item["maximum"],
                )
                for item in term_fields_payload
            ),
            source_bounds=tuple(FireSourceBoundSpec.from_dict(item) for item in source_bounds_payload),
            imports=tuple(FireImportSpec.from_dict(item) for item in imports_payload),
            witnesses=tuple(FireWitnessSpec.from_dict(item) for item in witnesses_payload),
            outputs=tuple(FireOutputSpec.from_dict(item) for item in outputs_payload),
            expression=FireExprFile.from_dict(payload["expression"]),
        )


def load_fire_math_object_spec_file(path: str | Path) -> FireMathObjectSpecFile:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    if not ok:
        raise ValueError(f"invalid FIRE FMOS spec file: {err}")
    return spec_file


def _resolve_value_ref(value_ref: FireValueRef, terms: Any) -> int:
    if value_ref.kind == "const":
        assert value_ref.value is not None
        return value_ref.value
    if value_ref.kind == "term":
        assert value_ref.term is not None
        value = getattr(terms, value_ref.term)
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"term field {value_ref.term} must resolve to int")
        return value
    raise ValueError(f"unsupported value ref kind: {value_ref.kind}")


def _fire_spec_dir() -> Path:
    return fire_stdlib_objects_dir()


def _load_imported_spec_file(interface_object_id: str) -> FireMathObjectSpecFile:
    direct_path = resolve_fire_spec_path(interface_object_id)
    if direct_path.exists():
        payload = json.loads(direct_path.read_text(encoding="utf-8"))
        return FireMathObjectSpecFile.from_dict(payload)
    for candidate in sorted(_fire_spec_dir().glob("*.json")):
        payload = json.loads(candidate.read_text(encoding="utf-8"))
        spec_file = FireMathObjectSpecFile.from_dict(payload)
        if spec_file.object_id == interface_object_id:
            return spec_file
    raise ValueError(f"unknown_import_interface:{interface_object_id}")


def build_source_intervals_from_spec_file(spec_file: FireMathObjectSpecFile, terms: Any) -> Mapping[str, FireInterval]:
    source_bounds = {
        bound.name: FireInterval(
            lower=_resolve_value_ref(bound.lower, terms),
            upper=_resolve_value_ref(bound.upper, terms),
        )
        for bound in spec_file.source_bounds
    }
    source_bounds.update(
        {
            imported.name: FireInterval(
                lower=_resolve_value_ref(imported.lower, terms),
                upper=_resolve_value_ref(imported.upper, terms),
            )
            for imported in spec_file.imports
        }
    )
    return source_bounds


def _build_source_unit_map(spec_file: FireMathObjectSpecFile) -> Mapping[str, str]:
    return {
        bound.name: bound.unit for bound in spec_file.source_bounds
    } | {
        imported.name: imported.unit for imported in spec_file.imports
    }


def build_certificate_env_from_spec_file(spec_file: FireMathObjectSpecFile, terms: Any) -> FireCertEnv:
    exact_values = {field.name: getattr(terms, field.name) for field in spec_file.term_fields}
    return FireCertEnv(
        exact_values=exact_values,
        source_bounds=build_source_intervals_from_spec_file(spec_file, terms),
    )


def build_witnesses_from_spec_file(spec_file: FireMathObjectSpecFile, terms: Any) -> tuple[FireWitnessRequirement, ...]:
    return tuple(
        FireWitnessRequirement(
            name=witness.name,
            freshness=witness.freshness,
            lower=_resolve_value_ref(witness.lower, terms),
            upper=_resolve_value_ref(witness.upper, terms),
            contract=(
                None
                if witness.contract is None
                else FireContractProvenance(name=witness.contract.name, role=witness.contract.role)
            ),
        )
        for witness in spec_file.witnesses
    )


def build_output_intervals_from_spec_file(spec_file: FireMathObjectSpecFile, terms: Any) -> Mapping[str, FireInterval]:
    env = build_certificate_env_from_spec_file(spec_file, terms)
    outputs: dict[str, FireInterval] = {}
    for output in spec_file.outputs:
        certificate = compile_interval_expression_certificate(_build_expr(output.expression), env)
        ok, err, interval = verify_interval_certificate(certificate, env)
        if not ok or interval is None:
            raise ValueError(f"invalid FIRE output certificate for {output.name}: {err or 'unknown error'}")
        outputs[output.name] = interval
    return outputs


def _require_child(child: FireExprFile | None, name: str) -> FireExprFile:
    if child is None:
        raise TypeError(f"expression missing child: {name}")
    return child


def _build_expr(expr_file: FireExprFile) -> FireExpr:
    kind = expr_file.kind
    if kind == "const":
        if not isinstance(expr_file.value, int) or isinstance(expr_file.value, bool):
            raise TypeError("const expression requires int value")
        return const_expr(expr_file.value)
    if kind == "exact_param":
        if not isinstance(expr_file.name, str) or not expr_file.name:
            raise TypeError("exact_param expression requires non-empty name")
        return exact_param_expr(expr_file.name)
    if kind == "source_bound":
        if not isinstance(expr_file.name, str) or not expr_file.name:
            raise TypeError("source_bound expression requires non-empty name")
        return source_bound_expr(expr_file.name)
    if kind == "add":
        return add_expr(_build_expr(_require_child(expr_file.left, "left")), _build_expr(_require_child(expr_file.right, "right")))
    if kind == "sub":
        return sub_expr(_build_expr(_require_child(expr_file.left, "left")), _build_expr(_require_child(expr_file.right, "right")))
    if kind == "mul":
        return mul_expr(_build_expr(_require_child(expr_file.left, "left")), _build_expr(_require_child(expr_file.right, "right")))
    if kind == "min":
        return min_expr(_build_expr(_require_child(expr_file.left, "left")), _build_expr(_require_child(expr_file.right, "right")))
    if kind == "max":
        return max_expr(_build_expr(_require_child(expr_file.left, "left")), _build_expr(_require_child(expr_file.right, "right")))
    if kind == "positive_part":
        return positive_part_expr(_build_expr(_require_child(expr_file.inner, "inner")))
    if kind == "cap":
        return cap_expr(_build_expr(_require_child(expr_file.inner, "inner")), _build_expr(_require_child(expr_file.upper, "upper")))
    if kind == "clamp":
        return clamp_expr(
            _build_expr(_require_child(expr_file.inner, "inner")),
            _build_expr(_require_child(expr_file.lower, "lower")),
            _build_expr(_require_child(expr_file.upper, "upper")),
        )
    raise ValueError(f"unsupported FIRE expression file kind: {kind}")


def build_expression_from_spec_file(spec_file: FireMathObjectSpecFile) -> FireExpr:
    return _build_expr(spec_file.expression)


def _collect_expr_refs(expr_file: FireExprFile, *, exact_params: set[str], source_bounds: set[str]) -> None:
    kind = expr_file.kind
    if kind == "exact_param":
        if not isinstance(expr_file.name, str) or not expr_file.name:
            raise ValueError("exact_param expression requires non-empty name")
        exact_params.add(expr_file.name)
        return
    if kind == "source_bound":
        if not isinstance(expr_file.name, str) or not expr_file.name:
            raise ValueError("source_bound expression requires non-empty name")
        source_bounds.add(expr_file.name)
        return
    if expr_file.left is not None:
        _collect_expr_refs(expr_file.left, exact_params=exact_params, source_bounds=source_bounds)
    if expr_file.right is not None:
        _collect_expr_refs(expr_file.right, exact_params=exact_params, source_bounds=source_bounds)
    if expr_file.inner is not None:
        _collect_expr_refs(expr_file.inner, exact_params=exact_params, source_bounds=source_bounds)
    if expr_file.lower is not None:
        _collect_expr_refs(expr_file.lower, exact_params=exact_params, source_bounds=source_bounds)
    if expr_file.upper is not None:
        _collect_expr_refs(expr_file.upper, exact_params=exact_params, source_bounds=source_bounds)


def verify_fire_math_object_spec_file(spec_file: FireMathObjectSpecFile) -> tuple[bool, str | None]:
    return _verify_fire_math_object_spec_file(spec_file, visited=frozenset())


def _names(items: tuple[Any, ...]) -> list[str]:
    return [item.name for item in items]


def _has_duplicates(names: list[str]) -> bool:
    return len(names) != len(set(names))


def _check_duplicate_names(spec_file: FireMathObjectSpecFile) -> str | None:
    """Reject duplicate or colliding declared names.

    Note: this covers term/source/import/witness duplicates only. The
    ``duplicate_output`` check deliberately lives later (after the witness
    loop); do not move it here -- that would change reject precedence.
    """

    source_names = _names(spec_file.source_bounds)
    import_names = _names(spec_file.imports)

    # Ordered: each per-collection duplicate check, then the source/import name
    # collision, then the witness duplicate (matching the original sequence).
    ordered_checks = (
        (_has_duplicates(_names(spec_file.term_fields)), "duplicate_term_field"),
        (_has_duplicates(source_names), "duplicate_source_bound"),
        (_has_duplicates(import_names), "duplicate_import"),
        (bool(set(source_names) & set(import_names)), "duplicate_source_interface_name"),
        (_has_duplicates(_names(spec_file.witnesses)), "duplicate_witness"),
    )
    for failed, code in ordered_checks:
        if failed:
            return code
    return None


def _check_term_fields(spec_file: FireMathObjectSpecFile) -> str | None:
    for field in spec_file.term_fields:
        try:
            parse_fire_unit(field.unit)
        except ValueError as exc:
            return f"term_field_unit_invalid:{field.name}:{exc}"
        if field.minimum > field.maximum:
            return f"term_field_bounds_invalid:{field.name}"
    return None


@dataclass(frozen=True)
class _BoundRefLabels:
    """Reject-code prefixes for a section that declares a [lower, upper] bound.

    The source-bound, import, and witness loops share an identical
    unit-and-term-ref validation pattern that differs only in these labels.
    Factoring it here removes the triplicated logic while preserving the exact
    reject codes and their ordering.
    """

    unit_invalid: str
    unknown_ref: str
    unit_mismatch: str


_SOURCE_BOUND_LABELS = _BoundRefLabels(
    unit_invalid="source_bound_unit_invalid",
    unknown_ref="unknown_term_ref_in_source_bound",
    unit_mismatch="source_bound_unit_mismatch",
)
_IMPORT_LABELS = _BoundRefLabels(
    unit_invalid="import_unit_invalid",
    unknown_ref="unknown_term_ref_in_import",
    unit_mismatch="import_unit_mismatch",
)
_WITNESS_LABELS = _BoundRefLabels(
    unit_invalid="witness_unit_invalid",
    unknown_ref="unknown_term_ref_in_witness",
    unit_mismatch="witness_unit_mismatch",
)


def _term_field_unit(spec_file: FireMathObjectSpecFile, term: str | None) -> str:
    return next(field for field in spec_file.term_fields if field.name == term).unit


def _check_ref_exists(value_ref: FireValueRef, term_name_set: set[str], name: str, labels: _BoundRefLabels) -> str | None:
    if value_ref.kind == "term" and value_ref.term not in term_name_set:
        return f"{labels.unknown_ref}:{name}:{value_ref.term}"
    return None


def _check_ref_unit(
    value_ref: FireValueRef,
    spec_file: FireMathObjectSpecFile,
    unit: str,
    name: str,
    labels: _BoundRefLabels,
) -> str | None:
    if value_ref.kind == "term" and _term_field_unit(spec_file, value_ref.term) != unit:
        return f"{labels.unit_mismatch}:{name}:{value_ref.term}"
    return None


def _check_bound_unit_and_refs(
    name: str,
    unit: str,
    lower: FireValueRef,
    upper: FireValueRef,
    spec_file: FireMathObjectSpecFile,
    term_name_set: set[str],
    labels: _BoundRefLabels,
) -> str | None:
    """Validate one [lower, upper]-bounded declaration's unit and term refs.

    Order is load-bearing: the declared unit is parsed first, then BOTH
    existence checks (lower, upper) run before EITHER unit-mismatch check. The
    characterization corpus locks this two-phase interleave.
    """

    try:
        parse_fire_unit(unit)
    except ValueError as exc:
        return f"{labels.unit_invalid}:{name}:{exc}"
    return (
        _check_ref_exists(lower, term_name_set, name, labels)
        or _check_ref_exists(upper, term_name_set, name, labels)
        or _check_ref_unit(lower, spec_file, unit, name, labels)
        or _check_ref_unit(upper, spec_file, unit, name, labels)
    )


def _check_source_bounds(spec_file: FireMathObjectSpecFile, term_name_set: set[str]) -> str | None:
    for bound in spec_file.source_bounds:
        error = _check_bound_unit_and_refs(
            bound.name, bound.unit, bound.lower, bound.upper, spec_file, term_name_set, _SOURCE_BOUND_LABELS
        )
        if error is not None:
            return error
    return None


def _check_imported_output(imported: FireImportSpec, imported_spec: FireMathObjectSpecFile) -> str | None:
    """Confirm the declared imported output exists and matches the declared unit."""

    imported_outputs = {output.name: output for output in imported_spec.outputs}
    if imported.interface_output not in imported_outputs:
        return f"unknown_import_output:{imported.interface_object_id}:{imported.interface_output}"
    if imported_outputs[imported.interface_output].unit != imported.unit:
        return (
            f"import_output_unit_mismatch:{imported.name}:"
            f"{imported.interface_object_id}:{imported.interface_output}"
        )
    return None


def _check_import_interface(
    imported: FireImportSpec,
    visited: frozenset[str],
) -> str | None:
    """Resolve, recursively verify, and unit-check one imported interface."""

    try:
        imported_spec = _load_imported_spec_file(imported.interface_object_id)
    except ValueError as exc:
        return str(exc)
    ok, err = _verify_fire_math_object_spec_file(imported_spec, visited=visited)
    if not ok:
        return f"import_invalid:{imported.interface_object_id}:{err}"
    return _check_imported_output(imported, imported_spec)


def _check_imports(
    spec_file: FireMathObjectSpecFile,
    term_name_set: set[str],
    visited: frozenset[str],
) -> str | None:
    """Validate imported interface bindings (the dependency-digest check).

    Per import: validate the local unit/term-ref binding (shared pattern), then
    resolve and recursively verify the dependency, confirming the imported
    output exists and matches the declared unit.
    """

    for imported in spec_file.imports:
        error = _check_bound_unit_and_refs(
            imported.name, imported.unit, imported.lower, imported.upper, spec_file, term_name_set, _IMPORT_LABELS
        ) or _check_import_interface(imported, visited)
        if error is not None:
            return error
    return None


def _check_witnesses(spec_file: FireMathObjectSpecFile, term_name_set: set[str]) -> str | None:
    for witness in spec_file.witnesses:
        error = _check_bound_unit_and_refs(
            witness.name, witness.unit, witness.lower, witness.upper, spec_file, term_name_set, _WITNESS_LABELS
        )
        if error is not None:
            return error
    return None


def _check_duplicate_outputs(spec_file: FireMathObjectSpecFile) -> str | None:
    output_names = [output.name for output in spec_file.outputs]
    if len(output_names) != len(set(output_names)):
        return "duplicate_output"
    return None


@dataclass(frozen=True)
class _ExprRefLabels:
    """Reject-code prefixes for the shared expression-reference checks.

    Prefixes already include any per-output name segment, so the helper appends
    only the trailing detail. Global checks pass bare prefixes; per-output checks
    pass ``f"...:{output.name}"`` prefixes.
    """

    invalid: str
    unknown_params: str
    unknown_bounds: str


def _check_expr_refs(
    expr: FireExprFile,
    term_name_set: set[str],
    source_name_set: set[str],
    labels: _ExprRefLabels,
) -> str | None:
    """Collect an expression's refs and reject unknown params / source bounds."""

    exact_params: set[str] = set()
    source_bounds: set[str] = set()
    try:
        _collect_expr_refs(expr, exact_params=exact_params, source_bounds=source_bounds)
    except (TypeError, ValueError) as exc:
        return f"{labels.invalid}:{exc}"
    unknown_params = sorted(exact_params - term_name_set)
    if unknown_params:
        return f"{labels.unknown_params}:{','.join(unknown_params)}"
    unknown_bounds = sorted(source_bounds - source_name_set)
    if unknown_bounds:
        return f"{labels.unknown_bounds}:{','.join(unknown_bounds)}"
    return None


def _infer_unit_or_error(expr: FireExpr, spec_file: FireMathObjectSpecFile, invalid_prefix: str) -> tuple[str | None, str | None]:
    """Infer an expression's unit, returning ``(unit, None)`` or ``(None, error)``."""

    try:
        inferred = infer_fire_expr_unit(
            expr,
            exact_units={field.name: field.unit for field in spec_file.term_fields},
            source_units=_build_source_unit_map(spec_file),
        )
    except (KeyError, ValueError) as exc:
        return None, f"{invalid_prefix}:{exc}"
    return inferred, None


_GLOBAL_EXPR_LABELS = _ExprRefLabels(
    invalid="expression_invalid",
    unknown_params="unknown_exact_params",
    unknown_bounds="unknown_source_bounds",
)


def _check_global_expression(
    spec_file: FireMathObjectSpecFile,
    term_name_set: set[str],
    source_name_set: set[str],
) -> str | None:
    """Validate the top-level payoff expression's refs and inferred unit."""

    ref_error = _check_expr_refs(spec_file.expression, term_name_set, source_name_set, _GLOBAL_EXPR_LABELS)
    if ref_error is not None:
        return ref_error
    inferred_unit, unit_error = _infer_unit_or_error(
        build_expression_from_spec_file(spec_file), spec_file, "expression_unit_invalid"
    )
    if unit_error is not None:
        return unit_error
    expected_unit = spec_file.outputs[0].unit
    if inferred_unit != expected_unit:
        return f"expression_unit_mismatch:expected_{expected_unit}:got_{inferred_unit}"
    return None


def _check_one_output(
    output: FireOutputSpec,
    spec_file: FireMathObjectSpecFile,
    term_name_set: set[str],
    source_name_set: set[str],
) -> str | None:
    """Validate one declared output's unit, expression refs, and inferred unit."""

    try:
        parse_fire_unit(output.unit)
    except ValueError as exc:
        return f"output_unit_invalid:{output.name}:{exc}"
    ref_error = _check_expr_refs(
        output.expression,
        term_name_set,
        source_name_set,
        _ExprRefLabels(
            invalid=f"output_expression_invalid:{output.name}",
            unknown_params=f"unknown_output_exact_params:{output.name}",
            unknown_bounds=f"unknown_output_source_bounds:{output.name}",
        ),
    )
    if ref_error is not None:
        return ref_error
    output_inferred, unit_error = _infer_unit_or_error(
        _build_expr(output.expression), spec_file, f"output_expression_unit_invalid:{output.name}"
    )
    if unit_error is not None:
        return unit_error
    if output_inferred != output.unit:
        return f"output_expression_unit_mismatch:{output.name}:expected_{output.unit}:got_{output_inferred}"
    return None


def _check_outputs(
    spec_file: FireMathObjectSpecFile,
    term_name_set: set[str],
    source_name_set: set[str],
) -> str | None:
    for output in spec_file.outputs:
        error = _check_one_output(output, spec_file, term_name_set, source_name_set)
        if error is not None:
            return error
    return None


def _verify_fire_math_object_spec_file(
    spec_file: FireMathObjectSpecFile,
    *,
    visited: frozenset[str],
) -> tuple[bool, str | None]:
    if not isinstance(spec_file, FireMathObjectSpecFile):
        raise TypeError("spec_file must be a FireMathObjectSpecFile")
    if spec_file.object_id in visited:
        return False, f"import_cycle:{spec_file.object_id}"
    visited = visited | {spec_file.object_id}

    term_name_set = {field.name for field in spec_file.term_fields}
    source_name_set = (
        {bound.name for bound in spec_file.source_bounds}
        | {imported.name for imported in spec_file.imports}
    )

    # Ordered, short-circuiting checks. The sequence below is the consensus
    # reject precedence and must not be reordered (see characterization corpus
    # tests/kernels/test_fmos_file_v1_characterization.py, which locks it).
    error = (
        _check_duplicate_names(spec_file)
        or _check_term_fields(spec_file)
        or _check_source_bounds(spec_file, term_name_set)
        or _check_imports(spec_file, term_name_set, visited)
        or _check_witnesses(spec_file, term_name_set)
        or _check_duplicate_outputs(spec_file)
        or _check_global_expression(spec_file, term_name_set, source_name_set)
        or _check_outputs(spec_file, term_name_set, source_name_set)
    )
    if error is not None:
        return False, error
    return True, None


def bind_fire_math_object_spec_file(
    spec_file_path: str | Path,
    *,
    terms_type: type,
    artifact_type: type,
    compile_state: Any,
    compiled_state_from_artifact: Any,
) -> FireMathObjectSpec:
    spec_file = load_fire_math_object_spec_file(spec_file_path)
    return bind_fire_math_object_spec(
        spec_file,
        terms_type=terms_type,
        artifact_type=artifact_type,
        compile_state=compile_state,
        compiled_state_from_artifact=compiled_state_from_artifact,
    )


def bind_fire_math_object_spec(
    spec_file: FireMathObjectSpecFile,
    *,
    terms_type: type,
    artifact_type: type,
    compile_state: Any,
    compiled_state_from_artifact: Any,
) -> FireMathObjectSpec:
    return FireMathObjectSpec(
        object_id=spec_file.object_id,
        object_name=spec_file.object_name,
        cli_help=spec_file.cli_help,
        object_version=spec_file.object_version,
        object_family=spec_file.object_family,
        settlement_asset=spec_file.settlement_asset,
        payoff_summary=spec_file.payoff_summary,
        ir_hash=spec_file.ir_hash,
        term_fields=spec_file.term_fields,
        source_units=_build_source_unit_map(spec_file),
        source_interfaces={
            imported.name: FireImportedInterfaceRef(
                name=imported.name,
                interface_object_id=imported.interface_object_id,
                interface_output=imported.interface_output,
                unit=imported.unit,
                contract=(
                    None
                    if imported.contract is None
                    else FireContractProvenance(name=imported.contract.name, role=imported.contract.role)
                ),
            )
            for imported in spec_file.imports
        },
        source_contracts={
            bound.name: FireContractProvenance(name=bound.contract.name, role=bound.contract.role)
            for bound in spec_file.source_bounds
            if bound.contract is not None
        }
        | {
            imported.name: FireContractProvenance(name=imported.contract.name, role=imported.contract.role)
            for imported in spec_file.imports
            if imported.contract is not None
        },
        output_units={output.name: output.unit for output in spec_file.outputs},
        primary_output_unit=spec_file.outputs[0].unit,
        terms_type=terms_type,
        artifact_type=artifact_type,
        expression_builder=lambda terms: build_expression_from_spec_file(spec_file),
        certificate_env_builder=lambda terms: build_certificate_env_from_spec_file(spec_file, terms),
        source_interval_builder=lambda terms: build_source_intervals_from_spec_file(spec_file, terms),
        output_interval_builder=lambda terms: build_output_intervals_from_spec_file(spec_file, terms),
        compile_state=compile_state,
        compiled_state_from_artifact=compiled_state_from_artifact,
        witness_builder=lambda artifact: build_witnesses_from_spec_file(spec_file, artifact.terms),
        witness_contracts={
            witness.name: FireContractProvenance(name=witness.contract.name, role=witness.contract.role)
            for witness in spec_file.witnesses
            if witness.contract is not None
        },
    )


__all__ = [
    "FIRE_FMOS_FILE_SCHEMA",
    "FireContractSpec",
    "FireExprFile",
    "FireImportSpec",
    "FireMathObjectSpecFile",
    "FireOutputSpec",
    "FireSourceBoundSpec",
    "FireValueRef",
    "FireWitnessSpec",
    "bind_fire_math_object_spec",
    "bind_fire_math_object_spec_file",
    "build_certificate_env_from_spec_file",
    "build_expression_from_spec_file",
    "build_output_intervals_from_spec_file",
    "build_source_intervals_from_spec_file",
    "build_witnesses_from_spec_file",
    "load_fire_math_object_spec_file",
    "verify_fire_math_object_spec_file",
]
