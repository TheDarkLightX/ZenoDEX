from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Mapping

from src.fire.registry.object_manifest_v1 import (
    FireContractProvenance,
    FireImportedInterfaceRequirement,
)
from src.fire.runtime.burn_boost_call_v1 import SPEC as BURN_BOOST_CALL_SPEC
from src.fire.runtime.fee_note_v1 import SPEC as FEE_NOTE_SPEC
from src.fire.runtime.lp_loss_cover_v1 import SPEC as LP_LOSS_COVER_SPEC

from .fmos_file_v1 import FireMathObjectSpecFile, bind_fire_math_object_spec
from .fmos_v1 import (
    FireInterfaceInterval,
    FireMathObjectSpec,
    compile_fmos_object,
    verify_fmos_composition,
)
from .zpl_v1 import (
    FireZplDiagnosticError,
    FireZplProgram,
    _contract_detail_for_name,
    _first_contract_detail,
    compile_fire_zpl_program_to_fmos_payload,
    parse_fire_zpl_source,
)


@dataclass(frozen=True)
class FireCompiledObject:
    spec: FireMathObjectSpec
    artifact: object

    @property
    def object_id(self) -> str:
        return self.spec.object_id

    @property
    def object_name(self) -> str:
        return self.spec.object_name

    @property
    def output_guarantees(self) -> tuple[FireInterfaceInterval, ...]:
        return self.spec.build_output_guarantees(self.artifact.terms)

    @property
    def source_requirements(self) -> tuple[FireInterfaceInterval, ...]:
        return self.spec.build_source_requirements(self.artifact.terms)


FIRE_COMPILER_SPECS: tuple[FireMathObjectSpec, ...] = (
    BURN_BOOST_CALL_SPEC,
    FEE_NOTE_SPEC,
    LP_LOSS_COVER_SPEC,
)


_FIRE_COMPILER_SPEC_MAP = {spec.object_id: spec for spec in FIRE_COMPILER_SPECS}
_FIRE_COMPILER_SPEC_BY_RUNTIME_ID = {
    (spec.object_name, spec.object_version, spec.object_family): spec for spec in FIRE_COMPILER_SPECS
}


def list_fire_compiler_entries() -> tuple[FireMathObjectSpec, ...]:
    return FIRE_COMPILER_SPECS


def get_fire_compiler_entry(object_id: str) -> FireMathObjectSpec:
    if object_id not in _FIRE_COMPILER_SPEC_MAP:
        raise KeyError(f"unsupported FIRE object_id: {object_id}")
    return _FIRE_COMPILER_SPEC_MAP[object_id]


def resolve_fire_compiler_entry(object_name: str, object_version: str, object_family: str) -> FireMathObjectSpec:
    key = (object_name, object_version, object_family)
    if key not in _FIRE_COMPILER_SPEC_BY_RUNTIME_ID:
        raise KeyError(
            "unsupported FIRE runtime identity: "
            f"{object_name}@{object_version} family {object_family}"
        )
    return _FIRE_COMPILER_SPEC_BY_RUNTIME_ID[key]


def compile_fire_object(object_id: str, raw_terms: Mapping[str, object]) -> FireCompiledObject:
    spec = get_fire_compiler_entry(object_id)
    artifact = compile_fmos_object(spec, raw_terms)
    return FireCompiledObject(spec=spec, artifact=artifact)


def _manifest_runtime_signature(compiled: FireCompiledObject) -> tuple[object, ...]:
    import_requirements: tuple[FireImportedInterfaceRequirement, ...] = compiled.spec.build_import_requirements(
        compiled.artifact.terms
    )
    witnesses = compiled.spec.witness_builder(compiled.artifact)
    return (
        compiled.spec.object_name,
        compiled.spec.object_version,
        compiled.spec.object_family,
        compiled.spec.settlement_asset,
        compiled.spec.payoff_summary,
        compiled.artifact.artifact_lower,
        compiled.artifact.artifact_upper,
        max(0, -compiled.artifact.artifact_lower),
        max(0, compiled.artifact.artifact_upper),
        import_requirements,
        witnesses,
        compiled.spec.evidence,
    )


def _strip_import_contracts(
    requirements: tuple[FireImportedInterfaceRequirement, ...],
) -> tuple[FireImportedInterfaceRequirement, ...]:
    return tuple(
        FireImportedInterfaceRequirement(
            name=item.name,
            interface_object_id=item.interface_object_id,
            interface_output=item.interface_output,
            unit=item.unit,
            lower=item.lower,
            upper=item.upper,
            contract=None,
        )
        for item in requirements
    )


def _strip_source_interface_contracts(
    interfaces: Mapping[str, object],
) -> tuple[tuple[str, object], ...]:
    normalized: list[tuple[str, object]] = []
    for name, item in interfaces.items():
        normalized.append(
            (
                name,
                (
                    item.name,
                    item.interface_object_id,
                    item.interface_output,
                    item.unit,
                ),
            )
        )
    return tuple(normalized)


def _normalize_term_fields(term_fields: tuple[object, ...]) -> tuple[tuple[object, ...], ...]:
    return tuple(
        (
            getattr(item, "name"),
            getattr(item, "description"),
            getattr(item, "unit"),
            getattr(item, "minimum"),
            getattr(item, "maximum"),
        )
        for item in term_fields
    )


def _normalize_interval_items(items: tuple[object, ...]) -> tuple[tuple[object, ...], ...]:
    return tuple(
        (
            getattr(item, "name"),
            getattr(item, "unit"),
            getattr(item, "lower"),
            getattr(item, "upper"),
        )
        for item in items
    )


def _strip_witness_contracts(requirements: tuple[object, ...]) -> tuple[object, ...]:
    return tuple(
        type(item)(
            name=item.name,
            freshness=item.freshness,
            lower=item.lower,
            upper=item.upper,
            contract=None,
        )
        for item in requirements
    )


def _contract_maps_comparable(
    source_contracts: Mapping[str, FireContractProvenance],
    canonical_contracts: Mapping[str, FireContractProvenance],
) -> bool:
    return bool(source_contracts) and bool(canonical_contracts)


def _first_contract_provenance_mismatch(
    source_contracts: Mapping[str, FireContractProvenance],
    canonical_contracts: Mapping[str, FireContractProvenance],
) -> tuple[str | None, FireContractProvenance | None, FireContractProvenance | None]:
    canonical_names = set()
    for name, expected in canonical_contracts.items():
        canonical_names.add(name)
        current = source_contracts.get(name)
        if current != expected:
            return name, current, expected
    for name, current in source_contracts.items():
        if name not in canonical_names:
            return name, current, None
    return None, None, None


def _format_contract_provenance_obligation(
    *,
    binding_name: str,
    expected: FireContractProvenance | None,
) -> str | None:
    if expected is None:
        return None
    return f"expected contract provenance {expected.name} role {expected.role} for {binding_name}"


def _verify_fire_spec_runtime_compatibility(
    *,
    source_spec: FireMathObjectSpec,
    source_artifact: object,
    canonical_spec: FireMathObjectSpec,
    canonical_artifact: object,
) -> tuple[bool, str | None]:
    source_static = (
        source_spec.object_id,
        source_spec.object_name,
        source_spec.cli_help,
        source_spec.object_version,
        source_spec.object_family,
        source_spec.settlement_asset,
        source_spec.payoff_summary,
        source_spec.ir_hash,
        _normalize_term_fields(source_spec.term_fields),
        source_spec.source_units,
        _strip_source_interface_contracts(source_spec.source_interfaces),
        source_spec.output_units,
        source_spec.primary_output_unit,
    )
    canonical_static = (
        canonical_spec.object_id,
        canonical_spec.object_name,
        canonical_spec.cli_help,
        canonical_spec.object_version,
        canonical_spec.object_family,
        canonical_spec.settlement_asset,
        canonical_spec.payoff_summary,
        canonical_spec.ir_hash,
        _normalize_term_fields(canonical_spec.term_fields),
        canonical_spec.source_units,
        _strip_source_interface_contracts(canonical_spec.source_interfaces),
        canonical_spec.output_units,
        canonical_spec.primary_output_unit,
    )
    if source_static != canonical_static:
        return False, "static_spec_mismatch"
    if _contract_maps_comparable(source_spec.source_contracts, canonical_spec.source_contracts):
        if source_spec.source_contracts != canonical_spec.source_contracts:
            return False, "source_contract_provenance_mismatch"
    if _contract_maps_comparable(source_spec.witness_contracts, canonical_spec.witness_contracts):
        if source_spec.witness_contracts != canonical_spec.witness_contracts:
            return False, "witness_contract_provenance_mismatch"
    if _normalize_interval_items(source_spec.build_source_requirements(source_artifact.terms)) != _normalize_interval_items(
        canonical_spec.build_source_requirements(canonical_artifact.terms)
    ):
        return False, "source_requirements_mismatch"
    if _normalize_interval_items(source_spec.build_output_guarantees(source_artifact.terms)) != _normalize_interval_items(
        canonical_spec.build_output_guarantees(canonical_artifact.terms)
    ):
        return False, "output_guarantees_mismatch"
    if _strip_import_contracts(source_spec.build_import_requirements(source_artifact.terms)) != _strip_import_contracts(
        canonical_spec.build_import_requirements(canonical_artifact.terms)
    ):
        return False, "import_requirements_mismatch"
    source_signature = _manifest_runtime_signature(FireCompiledObject(spec=source_spec, artifact=source_artifact))
    canonical_signature = _manifest_runtime_signature(FireCompiledObject(spec=canonical_spec, artifact=canonical_artifact))
    normalized_source_signature = source_signature[:-3] + (
        _strip_import_contracts(source_signature[-3]),
        _strip_witness_contracts(source_signature[-2]),
        source_signature[-1],
    )
    normalized_canonical_signature = canonical_signature[:-3] + (
        _strip_import_contracts(canonical_signature[-3]),
        _strip_witness_contracts(canonical_signature[-2]),
        canonical_signature[-1],
    )
    if normalized_source_signature != normalized_canonical_signature:
        return False, "manifest_runtime_signature_mismatch"
    return True, None


def _first_named_mismatch(
    source_items: tuple[object, ...],
    canonical_items: tuple[object, ...],
    *,
    normalize=lambda item: item,
) -> tuple[str | None, object | None, object | None]:
    source_by_name = {getattr(item, "name"): (item, normalize(item)) for item in source_items}
    canonical_names = set()
    for canonical in canonical_items:
        name = getattr(canonical, "name")
        canonical_names.add(name)
        current_pair = source_by_name.get(name)
        current_item = None if current_pair is None else current_pair[0]
        current_norm = None if current_pair is None else current_pair[1]
        if current_norm != normalize(canonical):
            return name, current_item, canonical
    for name, current_pair in source_by_name.items():
        if name not in canonical_names:
            return name, current_pair[0], None
    return None, None, None


def _format_interval_obligation(spec: FireMathObjectSpec, interval: FireInterfaceInterval) -> str:
    if interval.name in spec.source_interfaces:
        interface = spec.source_interfaces[interval.name]
        return (
            f"expected producer guarantee {interface.interface_object_id}.{interface.interface_output} "
            f"for {interval.name}: {interval.unit} in [{interval.lower}, {interval.upper}]"
        )
    return f"expected source envelope {interval.name}: {interval.unit} in [{interval.lower}, {interval.upper}]"


def _format_import_obligation(requirement: FireImportedInterfaceRequirement) -> str:
    return (
        f"expected producer guarantee {requirement.interface_object_id}.{requirement.interface_output} "
        f"for import {requirement.name}: {requirement.unit} in [{requirement.lower}, {requirement.upper}]"
    )


def _format_witness_obligation(requirement: object) -> str:
    name = getattr(requirement, "name")
    freshness = getattr(requirement, "freshness")
    lower = getattr(requirement, "lower")
    upper = getattr(requirement, "upper")
    return f"expected witness policy {name} freshness {freshness} in [{lower}, {upper}]"


def _append_obligation_detail(message: str, contract_detail: str | None, obligation_detail: str | None) -> str:
    details: list[str] = []
    if contract_detail is not None:
        details.append(contract_detail)
    if obligation_detail is not None:
        details.append(obligation_detail)
    if not details:
        return message
    return f"{message} [{' -> '.join(details)}]"


def _decorate_runtime_compatibility_error(
    *,
    program: FireZplProgram,
    object_id: str,
    source_spec: FireMathObjectSpec,
    source_artifact: object,
    canonical_spec: FireMathObjectSpec,
    canonical_artifact: object,
    err: str,
) -> tuple[object | None, str]:
    prefix = f"compiled ZPL source is runtime-incompatible for {object_id}"
    statement_spans = program.statement_spans or {}

    if err == "static_spec_mismatch":
        scalar_fields = (
            ("object_name", source_spec.object_name, canonical_spec.object_name, "name"),
            ("cli_help", source_spec.cli_help, canonical_spec.cli_help, "cli_help"),
            ("object_version", source_spec.object_version, canonical_spec.object_version, "version"),
            ("object_family", source_spec.object_family, canonical_spec.object_family, "family"),
            ("settlement_asset", source_spec.settlement_asset, canonical_spec.settlement_asset, "settlement"),
            ("payoff_summary", source_spec.payoff_summary, canonical_spec.payoff_summary, "summary"),
            ("ir_hash", source_spec.ir_hash, canonical_spec.ir_hash, "ir_hash"),
        )
        for field_name, source_value, canonical_value, statement_name in scalar_fields:
            if source_value != canonical_value:
                return statement_spans.get(statement_name), f"{prefix}: static_spec_mismatch:{field_name}"
        if _normalize_term_fields(source_spec.term_fields) != _normalize_term_fields(canonical_spec.term_fields):
            return (program.term_fields[0].span if program.term_fields else None), f"{prefix}: static_spec_mismatch:term_fields"
        if source_spec.source_units != canonical_spec.source_units or _strip_source_interface_contracts(
            source_spec.source_interfaces
        ) != _strip_source_interface_contracts(canonical_spec.source_interfaces):
            canonical_requirements = canonical_spec.build_source_requirements(canonical_artifact.terms)
            mismatch_name, _, mismatch_required = _first_named_mismatch(
                source_spec.build_source_requirements(source_artifact.terms),
                canonical_requirements,
                normalize=lambda item: (
                    getattr(item, "name"),
                    getattr(item, "unit"),
                    getattr(item, "lower"),
                    getattr(item, "upper"),
                ),
            )
            obligation_detail = (
                None
                if mismatch_required is None
                else _format_interval_obligation(canonical_spec, mismatch_required)
            )
            contract_span = None
            contract_detail = None
            if mismatch_name is not None:
                contract_span, contract_detail = _contract_detail_for_name(program.source_bounds, name=mismatch_name, program=program)
                if contract_span is None:
                    contract_span, contract_detail = _contract_detail_for_name(program.imports, name=mismatch_name, program=program)
            if contract_span is None:
                contract_span, contract_detail = _first_contract_detail(program.source_bounds, program)
            if contract_span is None:
                contract_span, contract_detail = _first_contract_detail(program.imports, program)
            if contract_span is not None:
                return contract_span, _append_obligation_detail(
                    f"{prefix}: static_spec_mismatch:source_contract",
                    contract_detail,
                    obligation_detail,
                )
            if program.source_bounds:
                return program.source_bounds[0].span, f"{prefix}: static_spec_mismatch:source_contract"
            if program.imports:
                return program.imports[0].span, f"{prefix}: static_spec_mismatch:source_contract"
            return None, f"{prefix}: static_spec_mismatch:source_contract"
        if source_spec.output_units != canonical_spec.output_units or source_spec.primary_output_unit != canonical_spec.primary_output_unit:
            return (program.outputs[0].span if program.outputs else None), f"{prefix}: static_spec_mismatch:output_contract"
        return None, f"{prefix}: static_spec_mismatch"

    if err == "source_requirements_mismatch":
        mismatch_name, _, mismatch_required = _first_named_mismatch(
            source_spec.build_source_requirements(source_artifact.terms),
            canonical_spec.build_source_requirements(canonical_artifact.terms),
            normalize=lambda item: (
                getattr(item, "name"),
                getattr(item, "unit"),
                getattr(item, "lower"),
                getattr(item, "upper"),
            ),
        )
        obligation_detail = (
            None
            if mismatch_required is None
            else _format_interval_obligation(canonical_spec, mismatch_required)
        )
        contract_span = None
        contract_detail = None
        if mismatch_name is not None:
            contract_span, contract_detail = _contract_detail_for_name(program.source_bounds, name=mismatch_name, program=program)
            if contract_span is None:
                contract_span, contract_detail = _contract_detail_for_name(program.imports, name=mismatch_name, program=program)
        if contract_span is None:
            contract_span, contract_detail = _first_contract_detail(program.source_bounds, program)
        if contract_span is None:
            contract_span, contract_detail = _first_contract_detail(program.imports, program)
        if contract_span is not None:
            return contract_span, _append_obligation_detail(
                f"{prefix}: {err}:contract",
                contract_detail,
                obligation_detail,
            )
        if program.source_bounds:
            return program.source_bounds[0].span, f"{prefix}: {err}"
        if program.imports:
            return program.imports[0].span, f"{prefix}: {err}"
        return statement_spans.get("expression"), f"{prefix}: {err}"

    if err == "output_guarantees_mismatch":
        return (program.outputs[0].span if program.outputs else statement_spans.get("expression")), f"{prefix}: {err}"

    if err == "import_requirements_mismatch":
        mismatch_name, _, mismatch_required = _first_named_mismatch(
            source_spec.build_import_requirements(source_artifact.terms),
            canonical_spec.build_import_requirements(canonical_artifact.terms),
        )
        obligation_detail = (
            _format_import_obligation(mismatch_required)
            if isinstance(mismatch_required, FireImportedInterfaceRequirement)
            else None
        )
        contract_span = None
        contract_detail = None
        if mismatch_name is not None:
            contract_span, contract_detail = _contract_detail_for_name(program.imports, name=mismatch_name, program=program)
        if contract_span is None:
            contract_span, contract_detail = _first_contract_detail(program.imports, program)
        if contract_span is not None:
            return contract_span, _append_obligation_detail(
                f"{prefix}: {err}:contract",
                contract_detail,
                obligation_detail,
            )
        return (program.imports[0].span if program.imports else None), f"{prefix}: {err}"

    if err == "source_contract_provenance_mismatch":
        mismatch_name, _, mismatch_expected = _first_contract_provenance_mismatch(
            source_spec.source_contracts,
            canonical_spec.source_contracts,
        )
        contract_span = None
        contract_detail = None
        if mismatch_name is not None:
            contract_span, contract_detail = _contract_detail_for_name(program.source_bounds, name=mismatch_name, program=program)
            if contract_span is None:
                contract_span, contract_detail = _contract_detail_for_name(program.imports, name=mismatch_name, program=program)
        if contract_span is None:
            contract_span, contract_detail = _first_contract_detail(program.source_bounds, program)
        if contract_span is None:
            contract_span, contract_detail = _first_contract_detail(program.imports, program)
        obligation_detail = (
            _format_contract_provenance_obligation(binding_name=mismatch_name or "source", expected=mismatch_expected)
            if mismatch_name is not None
            else None
        )
        if contract_span is not None:
            return contract_span, _append_obligation_detail(
                f"{prefix}: {err}",
                contract_detail,
                obligation_detail,
            )
        return None, _append_obligation_detail(f"{prefix}: {err}", contract_detail, obligation_detail)

    if err == "witness_contract_provenance_mismatch":
        mismatch_name, _, mismatch_expected = _first_contract_provenance_mismatch(
            source_spec.witness_contracts,
            canonical_spec.witness_contracts,
        )
        contract_span = None
        contract_detail = None
        if mismatch_name is not None:
            contract_span, contract_detail = _contract_detail_for_name(program.witnesses, name=mismatch_name, program=program)
        if contract_span is None:
            contract_span, contract_detail = _first_contract_detail(program.witnesses, program)
        obligation_detail = (
            _format_contract_provenance_obligation(binding_name=mismatch_name or "witness", expected=mismatch_expected)
            if mismatch_name is not None
            else None
        )
        if contract_span is not None:
            return contract_span, _append_obligation_detail(
                f"{prefix}: {err}",
                contract_detail,
                obligation_detail,
            )
        return None, _append_obligation_detail(f"{prefix}: {err}", contract_detail, obligation_detail)

    if err == "manifest_runtime_signature_mismatch":
        source_witnesses = source_spec.witness_builder(source_artifact)
        canonical_witnesses = canonical_spec.witness_builder(canonical_artifact)
        if source_witnesses != canonical_witnesses and program.witnesses:
            mismatch_name, _, mismatch_required = _first_named_mismatch(source_witnesses, canonical_witnesses)
            obligation_detail = _format_witness_obligation(mismatch_required) if mismatch_required is not None else None
            contract_span = None
            contract_detail = None
            if mismatch_name is not None:
                contract_span, contract_detail = _contract_detail_for_name(program.witnesses, name=mismatch_name, program=program)
            if contract_span is None:
                contract_span, contract_detail = _first_contract_detail(program.witnesses, program)
            if contract_span is not None:
                return contract_span, _append_obligation_detail(
                    f"{prefix}: {err}:witness_contract",
                    contract_detail,
                    obligation_detail,
                )
            return program.witnesses[0].span, f"{prefix}: {err}:witnesses"
        return (program.outputs[0].span if program.outputs else statement_spans.get("expression")), f"{prefix}: {err}"

    return None, f"{prefix}: {err}"


def compile_fire_zpl_object(source_file: str | Path, raw_terms: Mapping[str, object]) -> FireCompiledObject:
    program = parse_fire_zpl_source(Path(source_file).read_text(encoding="utf-8"))
    compiled_payload = compile_fire_zpl_program_to_fmos_payload(program)
    object_id = str(compiled_payload["object_id"])
    canonical_spec = get_fire_compiler_entry(object_id)
    spec_file = FireMathObjectSpecFile.from_dict(compiled_payload)
    source_spec = bind_fire_math_object_spec(
        spec_file,
        terms_type=canonical_spec.terms_type,
        artifact_type=canonical_spec.artifact_type,
        compile_state=canonical_spec.compile_state,
        compiled_state_from_artifact=canonical_spec.compiled_state_from_artifact,
    )
    source_artifact = compile_fmos_object(source_spec, raw_terms)
    canonical_artifact = compile_fmos_object(canonical_spec, raw_terms)
    ok, err = _verify_fire_spec_runtime_compatibility(
        source_spec=source_spec,
        source_artifact=source_artifact,
        canonical_spec=canonical_spec,
        canonical_artifact=canonical_artifact,
    )
    if not ok:
        span, message = _decorate_runtime_compatibility_error(
            program=program,
            object_id=object_id,
            source_spec=source_spec,
            source_artifact=source_artifact,
            canonical_spec=canonical_spec,
            canonical_artifact=canonical_artifact,
            err=err or "unknown_runtime_compatibility_error",
        )
        raise FireZplDiagnosticError(message, span=span)
    return FireCompiledObject(spec=source_spec, artifact=source_artifact)


def verify_fire_object_composition(
    *,
    producer: FireCompiledObject,
    consumer_object_id: str,
    consumer_raw_terms: Mapping[str, object],
    bindings: Mapping[str, str],
) -> tuple[bool, str | None]:
    if not isinstance(producer, FireCompiledObject):
        raise TypeError("producer must be a FireCompiledObject")
    consumer_spec = get_fire_compiler_entry(consumer_object_id)
    consumer_terms = consumer_spec.build_terms(consumer_raw_terms)
    return verify_fmos_composition(
        producer_spec=producer.spec,
        producer_terms=producer.artifact.terms,
        consumer_spec=consumer_spec,
        consumer_terms=consumer_terms,
        bindings=bindings,
    )


__all__ = [
    "FIRE_COMPILER_SPECS",
    "FireCompiledObject",
    "_verify_fire_spec_runtime_compatibility",
    "compile_fire_object",
    "compile_fire_zpl_object",
    "get_fire_compiler_entry",
    "list_fire_compiler_entries",
    "resolve_fire_compiler_entry",
    "verify_fire_object_composition",
]
