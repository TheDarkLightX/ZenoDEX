from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, Mapping

from src.fire.registry.object_manifest_v1 import (
    DEFAULT_FIRE_EVIDENCE,
    FireContractProvenance,
    FireImportedInterfaceRequirement,
    FireInstancePolicy,
    FireObjectManifest,
    FireParameterRequirement,
    FireWitnessRequirement,
    default_fire_instance_gate_claims,
    fire_manifest_file_sha256,
    render_fire_object_card,
)
from src.fire.runtime.common_v1 import compile_certified_artifact
from src.fire.verifier.cert_v1 import FireCertEnv, FireInterval, FireIntervalCertificate

from .object_compiler_v1 import FireExpr, compile_interval_expression_certificate, infer_fire_expr_unit


@dataclass(frozen=True)
class FireTermFieldSpec:
    name: str
    description: str
    unit: str
    minimum: int
    maximum: int

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("term field name must be non-empty")
        if not self.description:
            raise ValueError(f"term field {self.name} description must be non-empty")
        if not self.unit:
            raise ValueError(f"term field {self.name} unit must be non-empty")
        if not isinstance(self.minimum, int) or isinstance(self.minimum, bool):
            raise TypeError(f"term field {self.name} minimum must be int")
        if not isinstance(self.maximum, int) or isinstance(self.maximum, bool):
            raise TypeError(f"term field {self.name} maximum must be int")
        if self.minimum > self.maximum:
            raise ValueError(f"term field {self.name} has inverted bounds")

    @property
    def cli_flag(self) -> str:
        return "--" + self.name.replace("_", "-")

    def validate_value(self, value: object) -> int:
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"{self.name} must be int for FIRE unit {self.unit}")
        if value < self.minimum or value > self.maximum:
            raise ValueError(
                f"{self.name} outside FIRE FMOS bound [{self.minimum}, {self.maximum}] for unit {self.unit}"
            )
        return value


@dataclass(frozen=True)
class FireInterfaceInterval:
    name: str
    unit: str
    lower: int
    upper: int

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("interface interval name must be non-empty")
        if not self.unit:
            raise ValueError(f"interface interval {self.name} unit must be non-empty")
        if not isinstance(self.lower, int) or isinstance(self.lower, bool):
            raise TypeError(f"interface interval {self.name} lower must be int")
        if not isinstance(self.upper, int) or isinstance(self.upper, bool):
            raise TypeError(f"interface interval {self.name} upper must be int")
        if self.lower > self.upper:
            raise ValueError(f"interface interval {self.name} has inverted bounds")


@dataclass(frozen=True)
class FireImportedInterfaceRef:
    name: str
    interface_object_id: str
    interface_output: str
    unit: str
    contract: FireContractProvenance | None = None

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("imported interface name must be non-empty")
        if not self.interface_object_id:
            raise ValueError(f"imported interface {self.name} object id must be non-empty")
        if not self.interface_output:
            raise ValueError(f"imported interface {self.name} output must be non-empty")
        if not self.unit:
            raise ValueError(f"imported interface {self.name} unit must be non-empty")
        if self.contract is not None and not isinstance(self.contract, FireContractProvenance):
            raise TypeError(f"imported interface {self.name} contract must be FireContractProvenance")


@dataclass(frozen=True)
class FireMathObjectSpec:
    object_id: str
    object_name: str
    cli_help: str
    object_version: str
    object_family: str
    settlement_asset: str
    payoff_summary: str
    ir_hash: str
    term_fields: tuple[FireTermFieldSpec, ...]
    source_units: Mapping[str, str]
    source_interfaces: Mapping[str, FireImportedInterfaceRef]
    source_contracts: Mapping[str, FireContractProvenance]
    output_units: Mapping[str, str]
    primary_output_unit: str
    terms_type: type
    artifact_type: type
    expression_builder: Callable[[Any], FireExpr]
    certificate_env_builder: Callable[[Any], FireCertEnv]
    source_interval_builder: Callable[[Any], Mapping[str, FireInterval]]
    output_interval_builder: Callable[[Any], Mapping[str, FireInterval]]
    compile_state: Callable[[Any], Any]
    compiled_state_from_artifact: Callable[[Any], Any]
    witness_builder: Callable[[Any], tuple[FireWitnessRequirement, ...]]
    witness_contracts: Mapping[str, FireContractProvenance]
    evidence: tuple[str, ...] = DEFAULT_FIRE_EVIDENCE

    def build_terms(self, raw_terms: Mapping[str, object]) -> Any:
        if not isinstance(raw_terms, Mapping):
            raise TypeError("raw_terms must be a mapping")
        expected_names = tuple(field.name for field in self.term_fields)
        missing = [name for name in expected_names if name not in raw_terms]
        extras = [name for name in raw_terms.keys() if name not in expected_names]
        if missing:
            raise ValueError(f"missing FIRE term fields for {self.object_id}: {', '.join(sorted(missing))}")
        if extras:
            raise ValueError(
                f"unexpected FIRE term fields for {self.object_id}: {', '.join(sorted(str(x) for x in extras))}"
            )
        terms = self.terms_type(**{name: raw_terms[name] for name in expected_names})
        return self.validate_terms(terms)

    def validate_terms(self, terms: Any) -> Any:
        if not isinstance(terms, self.terms_type):
            raise TypeError(f"terms must be a {self.terms_type.__name__}")
        for field in self.term_fields:
            if not hasattr(terms, field.name):
                raise TypeError(f"terms missing FIRE field {field.name}")
            field.validate_value(getattr(terms, field.name))
        return terms

    @property
    def expected_output_unit(self) -> str:
        return self.primary_output_unit

    def validate_expression_unit(self, terms: Any) -> str:
        inferred = infer_fire_expr_unit(
            self.expression_builder(terms),
            exact_units={field.name: field.unit for field in self.term_fields},
            source_units=self.source_units,
        )
        if inferred != self.expected_output_unit:
            raise ValueError(
                f"FIRE expression unit mismatch for {self.object_id}: expected {self.expected_output_unit}, got {inferred}"
            )
        return inferred

    def build_source_requirements(self, terms: Any) -> tuple[FireInterfaceInterval, ...]:
        terms = self.validate_terms(terms)
        return tuple(
            FireInterfaceInterval(
                name=name,
                unit=self.source_units[name],
                lower=interval.lower,
                upper=interval.upper,
            )
            for name, interval in self.source_interval_builder(terms).items()
        )

    def build_output_guarantees(self, terms: Any) -> tuple[FireInterfaceInterval, ...]:
        terms = self.validate_terms(terms)
        return tuple(
            FireInterfaceInterval(
                name=name,
                unit=self.output_units[name],
                lower=interval.lower,
                upper=interval.upper,
            )
            for name, interval in self.output_interval_builder(terms).items()
        )

    def build_import_requirements(self, terms: Any) -> tuple[FireImportedInterfaceRequirement, ...]:
        source_requirements = {item.name: item for item in self.build_source_requirements(terms)}
        return tuple(
            FireImportedInterfaceRequirement(
                name=name,
                interface_object_id=interface.interface_object_id,
                interface_output=interface.interface_output,
                unit=interface.unit,
                lower=source_requirements[name].lower,
                upper=source_requirements[name].upper,
                contract=interface.contract,
            )
            for name, interface in self.source_interfaces.items()
        )


def verify_fmos_composition(
    *,
    producer_spec: FireMathObjectSpec,
    producer_terms: Any,
    consumer_spec: FireMathObjectSpec,
    consumer_terms: Any,
    bindings: Mapping[str, str],
) -> tuple[bool, str | None]:
    producer_outputs = {item.name: item for item in producer_spec.build_output_guarantees(producer_terms)}
    consumer_sources = {item.name: item for item in consumer_spec.build_source_requirements(consumer_terms)}
    if not bindings:
        return False, "composition_bindings_empty"
    for producer_output, consumer_source in bindings.items():
        if producer_output not in producer_outputs:
            return False, f"composition_missing_producer_output:{producer_output}"
        if consumer_source not in consumer_sources:
            return False, f"composition_missing_consumer_source:{consumer_source}"
        provided = producer_outputs[producer_output]
        required = consumer_sources[consumer_source]
        if provided.unit != required.unit:
            return False, f"composition_unit_mismatch:{producer_output}:{consumer_source}"
        if provided.lower < required.lower or provided.upper > required.upper:
            return False, f"composition_bound_mismatch:{producer_output}:{consumer_source}"
    return True, None


def compile_fmos_certificate(spec: FireMathObjectSpec, terms: Any) -> FireIntervalCertificate:
    spec.validate_expression_unit(terms)
    certificate = compile_interval_expression_certificate(
        spec.expression_builder(terms),
        spec.certificate_env_builder(terms),
    )
    return replace(certificate, instance_gate_claims=default_fire_instance_gate_claims())


def compile_fmos_artifact(spec: FireMathObjectSpec, terms: Any) -> Any:
    terms = spec.validate_terms(terms)
    artifact = compile_certified_artifact(
        terms,
        build_certificate=lambda local_terms: compile_fmos_certificate(spec, local_terms),
        certificate_env=spec.certificate_env_builder,
        compile_state=spec.compile_state,
        artifact_factory=spec.artifact_type,
    )
    manifest = build_fmos_manifest(spec, artifact)
    return replace(
        artifact,
        manifest_sha256=manifest.manifest_hash,
        manifest_file_sha256=fire_manifest_file_sha256(manifest),
    )


def compile_fmos_object(spec: FireMathObjectSpec, raw_terms: Mapping[str, object]) -> Any:
    return compile_fmos_artifact(spec, spec.build_terms(raw_terms))


def holder_collateral_required(artifact: Any) -> int:
    return max(0, -artifact.artifact_lower)


def writer_collateral_required(artifact: Any) -> int:
    return max(0, artifact.artifact_upper)


def build_fmos_manifest(spec: FireMathObjectSpec, artifact: Any) -> FireObjectManifest:
    return FireObjectManifest.build(
        object_name=spec.object_name,
        object_version=spec.object_version,
        object_family=spec.object_family,
        settlement_asset=spec.settlement_asset,
        payoff_summary=spec.payoff_summary,
        artifact_lower=artifact.artifact_lower,
        artifact_upper=artifact.artifact_upper,
        holder_collateral_required=holder_collateral_required(artifact),
        writer_collateral_required=writer_collateral_required(artifact),
        ir_hash=artifact.ir_hash,
        cert_sha256=artifact.cert_sha256,
        parameters=tuple(
            FireParameterRequirement(
                name=field.name,
                unit=field.unit,
                minimum=field.minimum,
                maximum=field.maximum,
                description=field.description,
            )
            for field in spec.term_fields
        ),
        imported_interfaces=spec.build_import_requirements(artifact.terms),
        witnesses=spec.witness_builder(artifact),
        evidence=spec.evidence,
        instance_policy=FireInstancePolicy(required_party_roles=("holder", "writer")),
    )


def render_fmos_object_card(spec: FireMathObjectSpec, artifact: Any) -> str:
    card = render_fire_object_card(build_fmos_manifest(spec, artifact))
    certificate = getattr(artifact, "certificate", None)
    claims = None if certificate is None else getattr(certificate, "instance_gate_claims", None)
    if claims is None:
        return card
    return "\n".join(
        [
            card,
            "",
            "Instance gate claim evidence:",
            f"  ParamOK: {claims.param_ok}",
            f"  AuthorizationOK: {claims.authorization_ok}",
            f"  NonceOK: {claims.nonce_ok}",
            f"  MaturityOK: {claims.maturity_ok}",
            f"  WindowOK: {claims.window_ok}",
        ]
    )


__all__ = [
    "FireImportedInterfaceRef",
    "FireInterfaceInterval",
    "FireMathObjectSpec",
    "FireTermFieldSpec",
    "build_fmos_manifest",
    "compile_fmos_artifact",
    "compile_fmos_certificate",
    "compile_fmos_object",
    "holder_collateral_required",
    "render_fmos_object_card",
    "verify_fmos_composition",
    "writer_collateral_required",
]
