#!/usr/bin/env python3
"""Replay the Tau envelope for tight-argmax m-source certificates."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from docs.research.discrete_argmax_proximity_test import (  # noqa: E402
    INTERVAL_M_CERTIFICATE_SCHEMA,
    M_SOURCE_ENDPOINT,
    M_SOURCE_INTERVAL_CERTIFICATE,
    M_SOURCE_STATIONARY_CERTIFICATE,
    STATIONARY_M_CERTIFICATE_SCHEMA,
    _build_tight_argmax_certificate_payload,
    _canonical_json_bytes,
    _curvature_module,
    _decoded_certificate,
    _sample_certificate_case,
    best_continuous_integer_anchor,
    build_hybrid_tight_argmax_certificate,
    build_interval_m_backed_tight_argmax_certificate,
    build_stationary_m_backed_tight_argmax_certificate,
    continuous_optimum,
    discrete_optimum_prod,
    verify_tight_argmax_certificate_bytes,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.check_nonendpoint_hybrid_root_guard_20260630 import (  # noqa: E402
    AcceptedGuard as AcceptedHybridRootGuard,
)
from tools.check_nonendpoint_hybrid_root_guard_20260630 import (  # noqa: E402
    build_nonendpoint_hybrid_root_guard_certificate,
    verify_nonendpoint_hybrid_root_guard_certificate_bytes,
)
from tools.check_tau_host_projection_contracts import lint_host_projection_contracts  # noqa: E402

OUT_DIR = REPO_ROOT / "generated" / "tight_argmax_m_source_certificate_20260630"
REPORT_JSON = OUT_DIR / "report.json"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "tight_argmax_m_source_certificate_v1.tau"
BOUND_PROJECTION_RECEIPT_SCHEMA = "zenodex.tight_argmax.bound_projection_receipt.v1"
BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA = "zenodex.tight_argmax.bound_projection_receipt_manifest.v1"
CLAIM_PROMOTION_BUNDLE_SCHEMA = "zenodex.tight_argmax.claim_promotion_bundle.v1"
NO_AUTHORITY_BOUNDARY = "research_only_no_routing_settlement_consensus"
TIGHT_ARGMAX_REPLAY_COMMAND = "python3 tools/check_tight_argmax_m_source_certificate_20260630.py"
SOURCE_ROLE_TIGHT_ARGMAX_CERTIFICATE = "tight_argmax_certificate"
SOURCE_ROLE_RESOLVER_ARTIFACT = "resolver_artifact"
SOURCE_ROLE_ROOT_GUARD_CERTIFICATE = "hybrid_root_guard_certificate"
SOURCE_ROLE_ROOT_GUARD_RESOLVER_ARTIFACT = "hybrid_root_guard_resolver_artifact"
SOURCE_ROLE_THEOREMSEARCH_PRIOR_ART = "theoremsearch_prior_art"
PROOF_INPUT_ROLE = "proof_input"
RETRIEVAL_ONLY_ROLE = "retrieval_only"
MANIFEST_SOURCE_ROLES = {
    SOURCE_ROLE_TIGHT_ARGMAX_CERTIFICATE,
    SOURCE_ROLE_RESOLVER_ARTIFACT,
    SOURCE_ROLE_ROOT_GUARD_CERTIFICATE,
    SOURCE_ROLE_ROOT_GUARD_RESOLVER_ARTIFACT,
    SOURCE_ROLE_THEOREMSEARCH_PRIOR_ART,
}
PROMOTION_TARGETS = {"claims_registry", "research_kernel"}

SLOTS: dict[str, str] = {
    "certificate_requested": "i1",
    "canonical_packet_ok": "i2",
    "schema_ok": "i3",
    "transcript_binding_ok": "i4",
    "research_scope_only": "i5",
    "domain_hash_ok": "i6",
    "argmax_anchor_membership_ok": "i7",
    "b_star_in_domain_ok": "i8",
    "production_dominance_ok": "i9",
    "one_sided_perturbation_ok": "i10",
    "metrics_recomputed": "i11",
    "radius_hierarchy_ok": "i12",
    "m_positive": "i13",
    "endpoint_source": "i14",
    "endpoint_m_recomputed": "i15",
    "interval_source": "i16",
    "interval_artifact_present": "i17",
    "interval_schema_ok": "i18",
    "interval_sha256_ok": "i19",
    "interval_domain_ok": "i20",
    "interval_certificate_accepted": "i21",
    "stationary_source": "i22",
    "stationary_artifact_present": "i23",
    "stationary_schema_ok": "i24",
    "stationary_sha256_ok": "i25",
    "stationary_domain_ok": "i26",
    "stationary_certificate_accepted": "i27",
    "no_production_routing_authority": "i28",
    "no_settlement_authority": "i29",
    "no_consensus_authority": "i30",
    "hybrid_radius_absent": "i31",
    "hybrid_radius_present": "i32",
    "hybrid_lipschitz_pair_ok": "i33",
    "hybrid_radius_recomputed": "i34",
    "hybrid_radius_certificate_ok": "i35",
    "hybrid_radius_hierarchy_ok": "i36",
}

PACKET_FLAGS = (
    "canonical_packet_ok",
    "schema_ok",
    "transcript_binding_ok",
    "research_scope_only",
    "domain_hash_ok",
    "argmax_anchor_membership_ok",
    "b_star_in_domain_ok",
)
ARGMAX_FLAGS = (
    "production_dominance_ok",
    "one_sided_perturbation_ok",
    "metrics_recomputed",
    "radius_hierarchy_ok",
)
AUTHORITY_FLAGS = (
    "no_production_routing_authority",
    "no_settlement_authority",
    "no_consensus_authority",
)
HYBRID_PRESENT_FLAGS = (
    "hybrid_radius_present",
    "hybrid_lipschitz_pair_ok",
    "hybrid_radius_recomputed",
    "hybrid_radius_certificate_ok",
    "hybrid_radius_hierarchy_ok",
)
SOURCE_FLAGS: dict[str, tuple[str, ...]] = {
    "endpoint": ("endpoint_source", "endpoint_m_recomputed"),
    "interval": (
        "interval_source",
        "interval_artifact_present",
        "interval_schema_ok",
        "interval_sha256_ok",
        "interval_domain_ok",
        "interval_certificate_accepted",
    ),
    "stationary": (
        "stationary_source",
        "stationary_artifact_present",
        "stationary_schema_ok",
        "stationary_sha256_ok",
        "stationary_domain_ok",
        "stationary_certificate_accepted",
    ),
}
OUTPUTS = tuple(f"o{idx}" for idx in range(1, 11))


@dataclass(frozen=True)
class TauCase:
    case_id: str
    flags: Mapping[str, int]
    expected: Mapping[str, int]
    rationale: str


@dataclass(frozen=True)
class EndpointSourceProjection:
    def apply(self, flags: dict[str, int]) -> None:
        flags["endpoint_source"] = 1
        flags["endpoint_m_recomputed"] = 1


@dataclass(frozen=True)
class IntervalSourceProjection:
    artifact_sha256: str

    def apply(self, flags: dict[str, int]) -> None:
        flags["interval_source"] = 1
        flags["interval_artifact_present"] = 1
        flags["interval_schema_ok"] = 1
        flags["interval_sha256_ok"] = 1
        flags["interval_domain_ok"] = 1
        flags["interval_certificate_accepted"] = 1


@dataclass(frozen=True)
class StationarySourceProjection:
    artifact_sha256: str

    def apply(self, flags: dict[str, int]) -> None:
        flags["stationary_source"] = 1
        flags["stationary_artifact_present"] = 1
        flags["stationary_schema_ok"] = 1
        flags["stationary_sha256_ok"] = 1
        flags["stationary_domain_ok"] = 1
        flags["stationary_certificate_accepted"] = 1


SourceProjection = EndpointSourceProjection | IntervalSourceProjection | StationarySourceProjection
CERTIFICATE_M_SOURCES = (
    M_SOURCE_ENDPOINT,
    M_SOURCE_INTERVAL_CERTIFICATE,
    M_SOURCE_STATIONARY_CERTIFICATE,
)


class HybridRadiusProjection(Enum):
    ABSENT = "absent"
    INLINE_CERTIFICATE = "inline_certificate"
    ROOT_GUARD = "root_guard"


@dataclass(frozen=True)
class BoundTightArgmaxProjection:
    source: SourceProjection
    m_source: str
    m_certificate_sha256: str | None
    anchor: int
    argmax: int
    hybrid_radius: HybridRadiusProjection

    def __post_init__(self) -> None:
        if self.m_source not in CERTIFICATE_M_SOURCES:
            raise ValueError(f"unsupported m_source: {self.m_source}")
        if not isinstance(self.hybrid_radius, HybridRadiusProjection):
            raise ValueError("hybrid_radius must be a HybridRadiusProjection")
        source_type_ok = (
            (self.m_source == M_SOURCE_ENDPOINT and isinstance(self.source, EndpointSourceProjection))
            or (self.m_source == M_SOURCE_INTERVAL_CERTIFICATE and isinstance(self.source, IntervalSourceProjection))
            or (
                self.m_source == M_SOURCE_STATIONARY_CERTIFICATE
                and isinstance(self.source, StationarySourceProjection)
            )
        )
        if not source_type_ok:
            raise ValueError("source projection type does not match m_source")
        if self.m_source == M_SOURCE_ENDPOINT:
            if self.m_certificate_sha256 is not None:
                raise ValueError("endpoint m-source cannot carry an artifact hash")
        elif not self.m_certificate_sha256:
            raise ValueError("non-endpoint m-source must carry an artifact hash")
        if self.m_source != M_SOURCE_ENDPOINT and self.hybrid_radius is HybridRadiusProjection.INLINE_CERTIFICATE:
            raise ValueError("inline hybrid radius is endpoint-only")


@dataclass(frozen=True)
class BoundProjectionReceipt:
    schema: str
    case_id: str
    certificate_sha256: str
    root_guard_sha256: str | None
    resolver_artifacts: tuple[tuple[str, int], ...]
    root_guard_resolver_artifacts: tuple[tuple[str, int], ...]
    m_source: str
    m_certificate_sha256: str | None
    anchor: int
    argmax: int
    hybrid_radius: HybridRadiusProjection
    tau_flags: tuple[tuple[str, int], ...]
    tau_step_facts: tuple[tuple[str, int], ...]

    def __post_init__(self) -> None:
        if self.schema != BOUND_PROJECTION_RECEIPT_SCHEMA:
            raise ValueError("unsupported bound projection receipt schema")
        if self.hybrid_radius is HybridRadiusProjection.ROOT_GUARD:
            if self.root_guard_sha256 is None:
                raise ValueError("root-guard receipt requires root guard bytes")
        elif self.root_guard_sha256 is not None:
            raise ValueError("non-root receipt cannot carry root guard bytes")
        artifact_hashes = {sha256 for sha256, _byte_len in self.resolver_artifacts}
        root_artifact_hashes = {sha256 for sha256, _byte_len in self.root_guard_resolver_artifacts}
        all_artifact_hashes = artifact_hashes | root_artifact_hashes
        if self.m_source == M_SOURCE_ENDPOINT:
            if self.m_certificate_sha256 is not None:
                raise ValueError("endpoint receipt cannot carry an m artifact hash")
            if all_artifact_hashes:
                raise ValueError("endpoint receipt cannot depend on resolver artifacts")
        elif self.m_certificate_sha256 not in all_artifact_hashes:
            raise ValueError("non-endpoint receipt missing selected m artifact hash")
        if {name for name, _value in self.tau_flags} != set(SLOTS):
            raise ValueError("receipt tau flags must cover every named host fact")
        if {slot for slot, _value in self.tau_step_facts} != set(SLOTS.values()):
            raise ValueError("receipt tau step facts must cover every Tau slot")
        if any(value not in (0, 1) for _name, value in (*self.tau_flags, *self.tau_step_facts)):
            raise ValueError("receipt facts must be boolean integers")

    def payload(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "case_id": self.case_id,
            "certificate_sha256": self.certificate_sha256,
            "root_guard_sha256": self.root_guard_sha256,
            "resolver_artifacts": [
                {"sha256": sha256, "byte_len": byte_len}
                for sha256, byte_len in self.resolver_artifacts
            ],
            "root_guard_resolver_artifacts": [
                {"sha256": sha256, "byte_len": byte_len}
                for sha256, byte_len in self.root_guard_resolver_artifacts
            ],
            "bound": {
                "m_source": self.m_source,
                "m_certificate_sha256": self.m_certificate_sha256,
                "anchor": self.anchor,
                "argmax": self.argmax,
                "hybrid_radius": self.hybrid_radius.value,
            },
            "tau_flags": dict(self.tau_flags),
            "tau_step_facts": dict(self.tau_step_facts),
        }

    @property
    def receipt_sha256(self) -> str:
        return hashlib.sha256(_canonical_json_bytes(self.payload())).hexdigest()

    def report_row(self) -> dict[str, object]:
        payload = self.payload()
        payload["receipt_sha256"] = self.receipt_sha256
        return payload


@dataclass(frozen=True)
class ManifestSourceRef:
    role: str
    sha256: str
    byte_len: int
    evidence_role: str

    def __post_init__(self) -> None:
        if self.role not in MANIFEST_SOURCE_ROLES:
            raise ValueError(f"unsupported manifest source role: {self.role}")
        if len(self.sha256) != 64 or any(ch not in "0123456789abcdef" for ch in self.sha256):
            raise ValueError("manifest source ref requires lowercase SHA-256")
        if self.byte_len < 0:
            raise ValueError("manifest source ref byte_len must be nonnegative")
        if self.role == SOURCE_ROLE_THEOREMSEARCH_PRIOR_ART:
            if self.evidence_role != RETRIEVAL_ONLY_ROLE:
                raise ValueError("TheoremSearch prior art must be retrieval-only")
        elif self.evidence_role != PROOF_INPUT_ROLE:
            raise ValueError("manifest proof source refs must be proof inputs")

    def payload(self) -> dict[str, object]:
        return {
            "role": self.role,
            "sha256": self.sha256,
            "byte_len": self.byte_len,
            "evidence_role": self.evidence_role,
        }


@dataclass(frozen=True)
class BoundProjectionReceiptManifest:
    schema: str
    manifest_id: str
    case_id: str
    receipt_sha256: str
    source_refs: tuple[ManifestSourceRef, ...]
    no_authority_boundary: str

    def __post_init__(self) -> None:
        if self.schema != BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA:
            raise ValueError("unsupported bound projection receipt manifest schema")
        if not self.manifest_id or not self.case_id:
            raise ValueError("manifest id and case id must be non-empty")
        if len(self.receipt_sha256) != 64 or any(ch not in "0123456789abcdef" for ch in self.receipt_sha256):
            raise ValueError("manifest receipt hash must be lowercase SHA-256")
        if self.no_authority_boundary != NO_AUTHORITY_BOUNDARY:
            raise ValueError("manifest missing no-authority boundary")
        ref_keys = tuple(
            (ref.role, ref.sha256, ref.byte_len, ref.evidence_role)
            for ref in self.source_refs
        )
        if len(set(ref_keys)) != len(ref_keys):
            raise ValueError("duplicate manifest source ref")
        cert_refs = [ref for ref in self.source_refs if ref.role == SOURCE_ROLE_TIGHT_ARGMAX_CERTIFICATE]
        if len(cert_refs) != 1:
            raise ValueError("manifest requires exactly one tight-argmax certificate ref")

    def payload(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "manifest_id": self.manifest_id,
            "case_id": self.case_id,
            "receipt_sha256": self.receipt_sha256,
            "source_refs": [ref.payload() for ref in self.source_refs],
            "no_authority_boundary": self.no_authority_boundary,
        }

    @property
    def manifest_sha256(self) -> str:
        return hashlib.sha256(_canonical_json_bytes(self.payload())).hexdigest()

    def report_row(self) -> dict[str, object]:
        payload = self.payload()
        payload["manifest_sha256"] = self.manifest_sha256
        return payload


@dataclass(frozen=True)
class ClaimPromotionBundle:
    schema: str
    bundle_id: str
    promotion_target: str
    manifest_sha256: str
    replay_command: str
    source_refs: tuple[ManifestSourceRef, ...]
    no_authority_boundary: str
    production_security_claim: bool

    def __post_init__(self) -> None:
        if self.schema != CLAIM_PROMOTION_BUNDLE_SCHEMA:
            raise ValueError("unsupported claim promotion bundle schema")
        if not self.bundle_id:
            raise ValueError("promotion bundle id must be non-empty")
        if self.promotion_target not in PROMOTION_TARGETS:
            raise ValueError("unsupported promotion target")
        if len(self.manifest_sha256) != 64 or any(ch not in "0123456789abcdef" for ch in self.manifest_sha256):
            raise ValueError("promotion bundle manifest hash must be lowercase SHA-256")
        if self.replay_command != TIGHT_ARGMAX_REPLAY_COMMAND:
            raise ValueError("promotion bundle replay command mismatch")
        if self.no_authority_boundary != NO_AUTHORITY_BOUNDARY:
            raise ValueError("promotion missing no-authority boundary")
        if self.production_security_claim:
            raise ValueError("promotion bundle cannot claim production security")
        ref_keys = tuple(
            (ref.role, ref.sha256, ref.byte_len, ref.evidence_role)
            for ref in self.source_refs
        )
        if len(set(ref_keys)) != len(ref_keys):
            raise ValueError("duplicate promotion source ref")
        if not self.source_refs:
            raise ValueError("promotion bundle requires source refs")

    def payload(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "bundle_id": self.bundle_id,
            "promotion_target": self.promotion_target,
            "manifest_sha256": self.manifest_sha256,
            "replay_command": self.replay_command,
            "source_refs": [ref.payload() for ref in self.source_refs],
            "no_authority_boundary": self.no_authority_boundary,
            "production_security_claim": self.production_security_claim,
        }

    @property
    def bundle_sha256(self) -> str:
        return hashlib.sha256(_canonical_json_bytes(self.payload())).hexdigest()

    def report_row(self) -> dict[str, object]:
        payload = self.payload()
        payload["bundle_sha256"] = self.bundle_sha256
        return payload


@dataclass(frozen=True)
class AcceptedProjection:
    bound: BoundTightArgmaxProjection
    flags: Mapping[str, int]
    verifier_rejects: tuple[str, ...] = ()

    @property
    def source(self) -> SourceProjection:
        return self.bound.source


@dataclass(frozen=True)
class RejectedProjection:
    verifier_rejects: tuple[str, ...]
    flags: Mapping[str, int]


Projection = AcceptedProjection | RejectedProjection


@dataclass(frozen=True)
class ActualProjectionCase:
    case_id: str
    p0: Any
    p1: Any
    amount_out_total: int
    raw_certificate: bytes
    resolver: Mapping[str, bytes] | None
    expected_accepted: bool
    rationale: str
    hybrid_root_guard_raw: bytes | None = None
    hybrid_root_guard_resolver: Mapping[str, bytes] | None = None
    expected_rejects: tuple[str, ...] = ()


def _require_accepted_projection_case(
    case_id: str,
    p0: Any,
    p1: Any,
    amount_out_total: int,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
) -> bytes:
    verification = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        int(amount_out_total),
        raw_certificate,
        resolver,
    )
    if not verification.ok:
        rejects = tuple(reject.value for reject in verification.rejects)
        raise AssertionError(f"{case_id} fixture rejected: {rejects}")
    return raw_certificate


def _first_accepted_interval_binding_variant(
    p0: Any,
    p1: Any,
    amount_out_total: int,
    b_star: float,
    interval_m_raw: bytes,
    *,
    anchor_values: tuple[int, ...],
    argmax_values: tuple[int, ...],
    case_id: str,
) -> bytes:
    cert_hash = hashlib.sha256(interval_m_raw).hexdigest()
    resolver = {cert_hash: interval_m_raw}
    for anchor in anchor_values:
        for argmax in argmax_values:
            try:
                raw = build_interval_m_backed_tight_argmax_certificate(
                    p0,
                    p1,
                    amount_out_total,
                    anchor,
                    argmax,
                    b_star,
                    interval_m_raw,
                )
            except ValueError:
                continue
            verification = verify_tight_argmax_certificate_bytes(
                p0,
                p1,
                int(amount_out_total),
                raw,
                resolver,
            )
            if verification.ok:
                return raw
    raise AssertionError(f"{case_id} has no accepted tight-argmax binding variant")


def _is1(flags: Mapping[str, int], name: str) -> bool:
    return int(flags.get(name, 0)) == 1


def _all1(flags: Mapping[str, int], names: tuple[str, ...]) -> bool:
    return all(_is1(flags, name) for name in names)


def _all0(flags: Mapping[str, int], names: tuple[str, ...]) -> bool:
    return all(not _is1(flags, name) for name in names)


def hybrid_radius_surface_ok(flags: Mapping[str, int]) -> bool:
    absent = _is1(flags, "hybrid_radius_absent")
    present = _is1(flags, "hybrid_radius_present")
    absent_ok = absent and not present and _all0(flags, HYBRID_PRESENT_FLAGS[1:])
    present_ok = (not absent) and present and _all1(flags, HYBRID_PRESENT_FLAGS[1:])
    return absent_ok or present_ok


def evaluate_outputs(flags: Mapping[str, int]) -> dict[str, int]:
    packet_ok = _all1(flags, PACKET_FLAGS)
    argmax_ok = _all1(flags, ARGMAX_FLAGS)
    hybrid_ok = hybrid_radius_surface_ok(flags)
    endpoint_ok = _all1(flags, SOURCE_FLAGS["endpoint"])
    interval_ok = _all1(flags, SOURCE_FLAGS["interval"])
    stationary_ok = _all1(flags, SOURCE_FLAGS["stationary"])
    source_bits = (
        _is1(flags, "endpoint_source"),
        _is1(flags, "interval_source"),
        _is1(flags, "stationary_source"),
    )
    source_one_hot = sum(1 for value in source_bits if value) == 1
    m_source_ok = source_one_hot and (endpoint_ok or interval_ok or stationary_ok)
    no_authority_ok = _all1(flags, AUTHORITY_FLAGS)
    admitted = (
        _is1(flags, "certificate_requested")
        and packet_ok
        and argmax_ok
        and hybrid_ok
        and _is1(flags, "m_positive")
        and m_source_ok
        and no_authority_ok
    )
    inactive_safe = not _is1(flags, "certificate_requested") and no_authority_ok
    return {
        "o1": int(packet_ok),
        "o2": int(argmax_ok),
        "o3": int(endpoint_ok),
        "o4": int(interval_ok),
        "o5": int(stationary_ok),
        "o6": int(m_source_ok),
        "o7": int(no_authority_ok),
        "o8": int(admitted),
        "o9": int(inactive_safe),
        "o10": int(hybrid_ok),
    }


def base_flags(source: str) -> dict[str, int]:
    if source not in SOURCE_FLAGS:
        raise ValueError(f"unsupported source: {source}")
    flags = {name: 0 for name in SLOTS}
    for name in ("certificate_requested", "m_positive", *PACKET_FLAGS, *ARGMAX_FLAGS, *AUTHORITY_FLAGS):
        flags[name] = 1
    flags["hybrid_radius_absent"] = 1
    for name in SOURCE_FLAGS[source]:
        flags[name] = 1
    return flags


def tau_step(flags: Mapping[str, int]) -> dict[str, int]:
    return {slot: int(flags.get(name, 0)) for name, slot in SLOTS.items()}


def _fail_closed_flags() -> dict[str, int]:
    return {name: 0 for name in SLOTS}


def _accepted_common_flags() -> dict[str, int]:
    flags = _fail_closed_flags()
    for name in ("certificate_requested", "m_positive", *PACKET_FLAGS, *ARGMAX_FLAGS, *AUTHORITY_FLAGS):
        flags[name] = 1
    return flags


def _apply_hybrid_present_projection(flags: dict[str, int]) -> None:
    flags["hybrid_radius_absent"] = 0
    for name in HYBRID_PRESENT_FLAGS:
        flags[name] = 1


def _sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _resolver_artifact_refs(resolver: Mapping[str, bytes] | None) -> tuple[tuple[str, int], ...]:
    rows: list[tuple[str, int]] = []
    for key, raw in (resolver or {}).items():
        if not isinstance(key, str):
            raise ValueError("resolver key must be a SHA-256 string")
        content_hash = _sha256_bytes(raw)
        if key != content_hash:
            raise ValueError("resolver key/content hash mismatch")
        rows.append((key, len(raw)))
    return tuple(sorted(rows))


def _verified_int_field(cert: Mapping[str, object], field_name: str) -> int:
    value = cert.get(field_name)
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"verified certificate has non-integer {field_name}")
    return value


def _verified_source_name(cert: Mapping[str, object]) -> str:
    source = cert.get("m_source")
    if not isinstance(source, str):
        raise ValueError("verified certificate has non-string m_source")
    return source


def _verified_certificate_hash(cert: Mapping[str, object]) -> str | None:
    cert_hash = cert.get("m_certificate_sha256")
    if cert_hash is None:
        return None
    if not isinstance(cert_hash, str):
        raise ValueError("verified certificate has non-string m_certificate_sha256")
    return cert_hash


def _flags_from_bound_tight_argmax(bound: BoundTightArgmaxProjection) -> dict[str, int]:
    flags = _accepted_common_flags()
    bound.source.apply(flags)
    if bound.hybrid_radius is HybridRadiusProjection.ABSENT:
        flags["hybrid_radius_absent"] = 1
        return flags
    _apply_hybrid_present_projection(flags)
    return flags


def _verify_receipt_matches_certificate(bound: BoundTightArgmaxProjection, raw_certificate: bytes) -> None:
    cert = _decoded_certificate(raw_certificate)
    if cert.get("m_source") != bound.m_source:
        raise ValueError("receipt certificate m_source mismatch")
    if cert.get("m_certificate_sha256") != bound.m_certificate_sha256:
        raise ValueError("receipt certificate m artifact mismatch")
    if cert.get("anchor") != bound.anchor or cert.get("argmax") != bound.argmax:
        raise ValueError("receipt certificate anchor/argmax mismatch")
    inline_present = "hybrid_radius" in cert
    if bound.hybrid_radius is HybridRadiusProjection.INLINE_CERTIFICATE and not inline_present:
        raise ValueError("receipt inline hybrid certificate missing")
    if bound.hybrid_radius is not HybridRadiusProjection.INLINE_CERTIFICATE and inline_present:
        raise ValueError("receipt unexpected inline hybrid certificate")


def build_bound_projection_receipt(
    case_id: str,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
    hybrid_root_guard_raw: bytes | None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None,
    bound: BoundTightArgmaxProjection,
) -> BoundProjectionReceipt:
    _verify_receipt_matches_certificate(bound, raw_certificate)
    resolver_refs = _resolver_artifact_refs(resolver)
    if bound.hybrid_radius is HybridRadiusProjection.ROOT_GUARD:
        if hybrid_root_guard_raw is None:
            raise ValueError("root-guard receipt requires root guard bytes")
        root_guard_sha256 = _sha256_bytes(hybrid_root_guard_raw)
        effective_root_resolver = hybrid_root_guard_resolver if hybrid_root_guard_resolver is not None else resolver
        root_guard_resolver_refs = _resolver_artifact_refs(effective_root_resolver)
    else:
        if hybrid_root_guard_raw is not None:
            raise ValueError("non-root receipt cannot carry root guard bytes")
        root_guard_sha256 = None
        root_guard_resolver_refs = ()

    projection = project_bound_tight_argmax_to_tau_flags(bound)
    tau_flags = tuple(sorted((name, int(value)) for name, value in projection.flags.items()))
    tau_step_facts = tuple(sorted((slot, int(value)) for slot, value in tau_step(projection.flags).items()))
    return BoundProjectionReceipt(
        schema=BOUND_PROJECTION_RECEIPT_SCHEMA,
        case_id=case_id,
        certificate_sha256=_sha256_bytes(raw_certificate),
        root_guard_sha256=root_guard_sha256,
        resolver_artifacts=resolver_refs,
        root_guard_resolver_artifacts=root_guard_resolver_refs,
        m_source=bound.m_source,
        m_certificate_sha256=bound.m_certificate_sha256,
        anchor=bound.anchor,
        argmax=bound.argmax,
        hybrid_radius=bound.hybrid_radius,
        tau_flags=tau_flags,
        tau_step_facts=tau_step_facts,
    )


def verify_bound_projection_receipt(
    case_id: str,
    p0: Any,
    p1: Any,
    amount_out_total: int,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
    hybrid_root_guard_raw: bytes | None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None,
    receipt_row: Mapping[str, object],
) -> BoundProjectionReceipt:
    if not isinstance(receipt_row, Mapping):
        raise ValueError("receipt row must be an object")
    expected_row = dict(receipt_row)
    embedded_hash = expected_row.pop("receipt_sha256", None)
    if not isinstance(embedded_hash, str) or not embedded_hash:
        raise ValueError("receipt row missing receipt_sha256")
    bound_payload = expected_row.get("bound")
    if not isinstance(bound_payload, Mapping):
        raise ValueError("receipt row missing bound payload")
    receipt_hybrid_radius = bound_payload.get("hybrid_radius")
    if receipt_hybrid_radius == HybridRadiusProjection.ROOT_GUARD.value:
        if hybrid_root_guard_raw is None:
            raise ValueError("root-guard receipt requires root guard bytes")
    elif hybrid_root_guard_raw is not None:
        raise ValueError("non-root receipt cannot carry root guard bytes")
    _resolver_artifact_refs(resolver)
    if hybrid_root_guard_resolver is not None:
        _resolver_artifact_refs(hybrid_root_guard_resolver)

    binding = bind_tight_argmax_projection(
        p0,
        p1,
        amount_out_total,
        raw_certificate,
        resolver,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
    )
    if not isinstance(binding, BoundTightArgmaxProjection):
        raise ValueError("receipt consumer requires accepted bound projection")

    reconstructed = build_bound_projection_receipt(
        case_id,
        raw_certificate,
        resolver,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
        binding,
    )
    if embedded_hash != reconstructed.receipt_sha256:
        raise ValueError("receipt hash mismatch")
    if expected_row != reconstructed.payload():
        raise ValueError("receipt payload mismatch")
    return reconstructed


def _manifest_source_ref(role: str, raw: bytes, evidence_role: str = PROOF_INPUT_ROLE) -> ManifestSourceRef:
    return ManifestSourceRef(
        role=role,
        sha256=_sha256_bytes(raw),
        byte_len=len(raw),
        evidence_role=evidence_role,
    )


def _manifest_resolver_refs(
    role: str,
    resolver: Mapping[str, bytes] | None,
) -> tuple[ManifestSourceRef, ...]:
    refs = []
    for sha256, byte_len in _resolver_artifact_refs(resolver):
        raw = (resolver or {})[sha256]
        refs.append(ManifestSourceRef(role=role, sha256=sha256, byte_len=byte_len, evidence_role=PROOF_INPUT_ROLE))
        if _sha256_bytes(raw) != sha256:
            raise ValueError("resolver key/content hash mismatch")
    return tuple(sorted(refs, key=lambda ref: (ref.role, ref.sha256, ref.byte_len, ref.evidence_role)))


def _receipt_manifest_source_refs(
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
    hybrid_root_guard_raw: bytes | None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None,
    theoremsearch_prior_art_raw: bytes | None = None,
) -> tuple[ManifestSourceRef, ...]:
    refs: list[ManifestSourceRef] = [
        _manifest_source_ref(SOURCE_ROLE_TIGHT_ARGMAX_CERTIFICATE, raw_certificate),
    ]
    refs.extend(_manifest_resolver_refs(SOURCE_ROLE_RESOLVER_ARTIFACT, resolver))
    if hybrid_root_guard_raw is not None:
        refs.append(_manifest_source_ref(SOURCE_ROLE_ROOT_GUARD_CERTIFICATE, hybrid_root_guard_raw))
        effective_root_resolver = hybrid_root_guard_resolver if hybrid_root_guard_resolver is not None else resolver
        refs.extend(_manifest_resolver_refs(SOURCE_ROLE_ROOT_GUARD_RESOLVER_ARTIFACT, effective_root_resolver))
    if theoremsearch_prior_art_raw is not None:
        refs.append(
            _manifest_source_ref(
                SOURCE_ROLE_THEOREMSEARCH_PRIOR_ART,
                theoremsearch_prior_art_raw,
                RETRIEVAL_ONLY_ROLE,
            )
        )
    return tuple(sorted(refs, key=lambda ref: (ref.role, ref.sha256, ref.byte_len, ref.evidence_role)))


def build_bound_projection_receipt_manifest(
    manifest_id: str,
    case_id: str,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
    hybrid_root_guard_raw: bytes | None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None,
    receipt_row: Mapping[str, object],
    theoremsearch_prior_art_raw: bytes | None = None,
) -> BoundProjectionReceiptManifest:
    receipt_sha256 = receipt_row.get("receipt_sha256")
    if not isinstance(receipt_sha256, str):
        raise ValueError("manifest receipt row missing receipt hash")
    return BoundProjectionReceiptManifest(
        schema=BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
        manifest_id=manifest_id,
        case_id=case_id,
        receipt_sha256=receipt_sha256,
        source_refs=_receipt_manifest_source_refs(
            raw_certificate,
            resolver,
            hybrid_root_guard_raw,
            hybrid_root_guard_resolver,
            theoremsearch_prior_art_raw,
        ),
        no_authority_boundary=NO_AUTHORITY_BOUNDARY,
    )


def verify_bound_projection_receipt_manifest(
    manifest: BoundProjectionReceiptManifest,
    p0: Any,
    p1: Any,
    amount_out_total: int,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
    hybrid_root_guard_raw: bytes | None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None,
    receipt_row: Mapping[str, object],
    theoremsearch_prior_art_raw: bytes | None = None,
) -> BoundProjectionReceiptManifest:
    if receipt_row.get("receipt_sha256") != manifest.receipt_sha256:
        raise ValueError("manifest receipt hash mismatch")
    expected_refs = set(_receipt_manifest_source_refs(
        raw_certificate,
        resolver,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
        theoremsearch_prior_art_raw,
    ))
    declared_refs = set(manifest.source_refs)
    if expected_refs - declared_refs:
        raise ValueError("manifest missing source ref")
    if declared_refs - expected_refs:
        raise ValueError("manifest undeclared source ref")
    verify_bound_projection_receipt(
        manifest.case_id,
        p0,
        p1,
        amount_out_total,
        raw_certificate,
        resolver,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
        receipt_row,
    )
    return manifest


def build_claim_promotion_bundle(
    bundle_id: str,
    promotion_target: str,
    manifest: BoundProjectionReceiptManifest,
) -> ClaimPromotionBundle:
    return ClaimPromotionBundle(
        schema=CLAIM_PROMOTION_BUNDLE_SCHEMA,
        bundle_id=bundle_id,
        promotion_target=promotion_target,
        manifest_sha256=manifest.manifest_sha256,
        replay_command=TIGHT_ARGMAX_REPLAY_COMMAND,
        source_refs=manifest.source_refs,
        no_authority_boundary=NO_AUTHORITY_BOUNDARY,
        production_security_claim=False,
    )


def verify_claim_promotion_bundle(
    bundle: ClaimPromotionBundle,
    manifest: BoundProjectionReceiptManifest | None,
    p0: Any,
    p1: Any,
    amount_out_total: int,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None,
    hybrid_root_guard_raw: bytes | None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None,
    receipt_row: Mapping[str, object],
    theoremsearch_prior_art_raw: bytes | None = None,
) -> ClaimPromotionBundle:
    if manifest is None:
        raise ValueError("promotion manifest required")
    if bundle.manifest_sha256 != manifest.manifest_sha256:
        raise ValueError("promotion manifest hash mismatch")
    if set(bundle.source_refs) != set(manifest.source_refs):
        raise ValueError("promotion source refs mismatch")
    verify_bound_projection_receipt_manifest(
        manifest,
        p0,
        p1,
        amount_out_total,
        raw_certificate,
        resolver,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
        receipt_row,
        theoremsearch_prior_art_raw,
    )
    return bundle


def _verify_optional_nonendpoint_hybrid_root_guard(
    p0: Any,
    p1: Any,
    amount_out_total: int,
    cert: Mapping[str, object],
    root_guard_raw: bytes | None,
    root_guard_resolver: Mapping[str, bytes] | None,
    fallback_resolver: Mapping[str, bytes] | None,
) -> tuple[bool, tuple[str, ...]]:
    if root_guard_raw is None:
        return False, ()

    resolver = root_guard_resolver if root_guard_resolver is not None else fallback_resolver
    guard = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        int(amount_out_total),
        root_guard_raw,
        resolver,
    )
    if not isinstance(guard, AcceptedHybridRootGuard):
        rejects = tuple(getattr(reject, "value", str(reject)) for reject in getattr(guard, "rejects", ()))
        return False, tuple(f"hybrid_root_guard:{reject}" for reject in rejects)

    if guard.m_source != cert.get("m_source"):
        return False, ("hybrid_root_guard:m_source_mismatch",)
    if guard.m_certificate_sha256 != cert.get("m_certificate_sha256"):
        return False, ("hybrid_root_guard:m_certificate_hash_mismatch",)
    if guard.anchor != cert.get("anchor") or guard.argmax != cert.get("argmax"):
        return False, ("hybrid_root_guard:argmax_anchor_mismatch",)
    return True, ()


def _source_projection_from_verified_cert(cert: Mapping[str, object]) -> SourceProjection:
    source = cert.get("m_source")
    if source == M_SOURCE_ENDPOINT:
        return EndpointSourceProjection()
    if source == M_SOURCE_INTERVAL_CERTIFICATE:
        cert_hash = cert.get("m_certificate_sha256")
        if not isinstance(cert_hash, str):
            raise ValueError("verified interval source missing artifact hash")
        return IntervalSourceProjection(cert_hash)
    if source == M_SOURCE_STATIONARY_CERTIFICATE:
        cert_hash = cert.get("m_certificate_sha256")
        if not isinstance(cert_hash, str):
            raise ValueError("verified stationary source missing artifact hash")
        return StationarySourceProjection(cert_hash)
    raise ValueError(f"verified certificate has unsupported m_source: {source!r}")


def bind_tight_argmax_projection(
    p0: Any,
    p1: Any,
    amount_out_total: int,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None = None,
    hybrid_root_guard_raw: bytes | None = None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None = None,
) -> BoundTightArgmaxProjection | RejectedProjection:
    verification = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        int(amount_out_total),
        raw_certificate,
        resolver,
    )
    if not verification.ok:
        return RejectedProjection(
            verifier_rejects=tuple(reject.value for reject in verification.rejects),
            flags=_fail_closed_flags(),
        )

    cert = _decoded_certificate(raw_certificate)
    try:
        source = _source_projection_from_verified_cert(cert)
        m_source = _verified_source_name(cert)
        cert_hash = _verified_certificate_hash(cert)
        anchor = _verified_int_field(cert, "anchor")
        argmax = _verified_int_field(cert, "argmax")
    except ValueError as exc:
        return RejectedProjection(
            verifier_rejects=(f"projection_binding:{exc}",),
            flags=_fail_closed_flags(),
        )
    root_guard_present, root_guard_rejects = _verify_optional_nonendpoint_hybrid_root_guard(
        p0,
        p1,
        amount_out_total,
        cert,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
        resolver,
    )
    if root_guard_rejects:
        return RejectedProjection(verifier_rejects=root_guard_rejects, flags=_fail_closed_flags())

    if root_guard_present:
        hybrid_radius = HybridRadiusProjection.ROOT_GUARD
    elif "hybrid_radius" in cert:
        hybrid_radius = HybridRadiusProjection.INLINE_CERTIFICATE
    else:
        hybrid_radius = HybridRadiusProjection.ABSENT

    try:
        return BoundTightArgmaxProjection(
            source=source,
            m_source=m_source,
            m_certificate_sha256=cert_hash,
            anchor=anchor,
            argmax=argmax,
            hybrid_radius=hybrid_radius,
        )
    except ValueError as exc:
        return RejectedProjection(
            verifier_rejects=(f"projection_binding:{exc}",),
            flags=_fail_closed_flags(),
        )


def project_bound_tight_argmax_to_tau_flags(bound: BoundTightArgmaxProjection) -> AcceptedProjection:
    return AcceptedProjection(bound=bound, flags=_flags_from_bound_tight_argmax(bound))


def project_certificate_to_tau_flags(
    p0: Any,
    p1: Any,
    amount_out_total: int,
    raw_certificate: bytes,
    resolver: Mapping[str, bytes] | None = None,
    hybrid_root_guard_raw: bytes | None = None,
    hybrid_root_guard_resolver: Mapping[str, bytes] | None = None,
) -> Projection:
    bound = bind_tight_argmax_projection(
        p0,
        p1,
        amount_out_total,
        raw_certificate,
        resolver,
        hybrid_root_guard_raw,
        hybrid_root_guard_resolver,
    )
    if isinstance(bound, RejectedProjection):
        return bound
    return project_bound_tight_argmax_to_tau_flags(bound)


def tau_cases() -> tuple[TauCase, ...]:
    endpoint = base_flags("endpoint")
    interval = base_flags("interval")
    stationary = base_flags("stationary")
    endpoint_hybrid = dict(endpoint, hybrid_radius_absent=0)
    for name in HYBRID_PRESENT_FLAGS:
        endpoint_hybrid[name] = 1

    default_reject = {name: 0 for name in SLOTS}
    missing_radius = dict(endpoint, radius_hierarchy_ok=0)
    mixed_sources = dict(interval, endpoint_source=1, endpoint_m_recomputed=1)
    bad_interval_hash = dict(interval, interval_sha256_ok=0)
    bad_stationary_domain = dict(stationary, stationary_domain_ok=0)
    mixed_hybrid = dict(endpoint_hybrid, hybrid_radius_absent=1)
    missing_hybrid_certificate = dict(endpoint_hybrid, hybrid_radius_certificate_ok=0)
    stray_hybrid_fact = dict(endpoint, hybrid_lipschitz_pair_ok=1)
    authority_reject = dict(endpoint, no_settlement_authority=0)
    inactive_safe = dict(endpoint, certificate_requested=0)

    raw_cases = (
        ("endpoint_admit", endpoint, "Endpoint m is accepted when it is recomputed from pool parameters."),
        ("interval_admit", interval, "Interval m is accepted when the referenced interval certificate is bound and accepted."),
        ("stationary_admit", stationary, "Stationary m is accepted when the exact-rational stationary certificate is bound and accepted."),
        ("endpoint_hybrid_admit", endpoint_hybrid, "Hybrid radius is accepted only when every host-recomputed hybrid fact is present."),
        ("default_reject", default_reject, "All missing host facts fail closed."),
        ("missing_radius_reject", missing_radius, "Radius hierarchy must be recomputed and checked by the host."),
        ("mixed_sources_reject", mixed_sources, "Two active source bits are rejected even if both source surfaces look valid."),
        ("bad_interval_hash_reject", bad_interval_hash, "A missing interval artifact hash binding rejects."),
        ("bad_stationary_domain_reject", bad_stationary_domain, "A stationary artifact must match the tight-argmax domain."),
        ("mixed_hybrid_reject", mixed_hybrid, "Hybrid absent and hybrid present cannot both be active."),
        ("missing_hybrid_certificate_reject", missing_hybrid_certificate, "Hybrid-present packets require the quadratic radius certificate fact."),
        ("stray_hybrid_fact_reject", stray_hybrid_fact, "Hybrid-absent packets reject stray hybrid facts."),
        ("authority_reject", authority_reject, "Settlement authority leakage rejects the certificate lane."),
        ("inactive_safe", inactive_safe, "Inactive requests do not admit while the no-authority rail stays true."),
    )
    return tuple(TauCase(case_id, flags, evaluate_outputs(flags), rationale) for case_id, flags, rationale in raw_cases)


def actual_projection_cases() -> tuple[ActualProjectionCase, ...]:
    p0, p1, D, anchor, argmax, b_star, _endpoint_m, endpoint_raw = _sample_certificate_case()
    curvature = _curvature_module()
    endpoint_m = _decoded_certificate(endpoint_raw)["m"]
    hybrid_endpoint_raw = build_hybrid_tight_argmax_certificate(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        float(endpoint_m),
    )

    build_interval = curvature.build_refined_interval_curvature_m_certificate
    verify_interval = curvature.verify_interval_curvature_m_certificate_bytes
    interval_m_raw = build_interval(p0, p1, D, 16, 64)
    interval_m_result = verify_interval(p0, p1, D, interval_m_raw)
    if not interval_m_result.accepted or interval_m_result.m is None:
        raise AssertionError("interval m fixture rejected")
    interval_hash = hashlib.sha256(interval_m_raw).hexdigest()
    interval_raw = build_interval_m_backed_tight_argmax_certificate(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        interval_m_raw,
    )
    interval_root_guard_raw = build_nonendpoint_hybrid_root_guard_certificate(
        p0,
        p1,
        D,
        M_SOURCE_INTERVAL_CERTIFICATE,
        interval_m_raw,
    )
    interval_root_guard = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        p0,
        p1,
        D,
        interval_root_guard_raw,
        {interval_hash: interval_m_raw},
    )
    if not isinstance(interval_root_guard, AcceptedHybridRootGuard):
        raise AssertionError("interval root guard fixture rejected")
    alt_interval_m_raw = build_interval(p0, p1, D, 8, 64)
    alt_interval_hash = hashlib.sha256(alt_interval_m_raw).hexdigest()
    if alt_interval_hash == interval_hash:
        raise AssertionError("alternate interval fixture did not change hash")
    alt_interval_root_guard_raw = build_nonendpoint_hybrid_root_guard_certificate(
        p0,
        p1,
        D,
        M_SOURCE_INTERVAL_CERTIFICATE,
        alt_interval_m_raw,
    )
    interval_anchor_mismatch_raw = _first_accepted_interval_binding_variant(
        p0,
        p1,
        D,
        b_star,
        interval_m_raw,
        anchor_values=tuple(value for value in range(D + 1) if value != interval_root_guard.anchor),
        argmax_values=(interval_root_guard.argmax,),
        case_id="actual_interval_root_guard_anchor_mismatch_reject",
    )
    interval_argmax_mismatch_raw = _first_accepted_interval_binding_variant(
        p0,
        p1,
        D,
        b_star,
        interval_m_raw,
        anchor_values=(interval_root_guard.anchor,),
        argmax_values=tuple(value for value in range(D + 1) if value != interval_root_guard.argmax),
        case_id="actual_interval_root_guard_argmax_mismatch_reject",
    )
    interval_hybrid_unsupported_raw = _canonical_json_bytes(
        _build_tight_argmax_certificate_payload(
            p0,
            p1,
            D,
            anchor,
            argmax,
            b_star,
            float(interval_m_result.m),
            M_SOURCE_INTERVAL_CERTIFICATE,
            {
                "m_certificate_schema": INTERVAL_M_CERTIFICATE_SCHEMA,
                "m_certificate_sha256": interval_hash,
            },
            include_hybrid_radius=True,
        )
    )

    construct_stationary = curvature._construct_fee_free_stationary_case
    build_stationary = curvature.build_stationary_curvature_m_certificate
    verify_stationary = curvature.verify_stationary_curvature_m_certificate_bytes
    sp0, sp1, sD, minimizer_a = construct_stationary(467, 437, 104, 56)
    stationary_m_raw = build_stationary(sp0, sp1, sD, minimizer_a)
    stationary_m_result = verify_stationary(sp0, sp1, sD, stationary_m_raw)
    if not stationary_m_result.accepted or stationary_m_result.m is None:
        raise AssertionError("stationary m fixture rejected")
    stationary_hash = hashlib.sha256(stationary_m_raw).hexdigest()
    sb_star = continuous_optimum(sp0, sp1, sD)
    sargmax, _ = discrete_optimum_prod(sp0, sp1, sD)
    sanchor = best_continuous_integer_anchor(sp0, sp1, sD)
    stationary_raw = build_stationary_m_backed_tight_argmax_certificate(
        sp0,
        sp1,
        sD,
        sanchor,
        sargmax,
        sb_star,
        stationary_m_raw,
    )
    stationary_domain_interval_m_raw = build_interval(sp0, sp1, sD, 8, 64)
    stationary_domain_interval_hash = hashlib.sha256(stationary_domain_interval_m_raw).hexdigest()
    stationary_domain_interval_root_guard_raw = build_nonendpoint_hybrid_root_guard_certificate(
        sp0,
        sp1,
        sD,
        M_SOURCE_INTERVAL_CERTIFICATE,
        stationary_domain_interval_m_raw,
    )
    stationary_domain_interval_root_guard = verify_nonendpoint_hybrid_root_guard_certificate_bytes(
        sp0,
        sp1,
        sD,
        stationary_domain_interval_root_guard_raw,
        {stationary_domain_interval_hash: stationary_domain_interval_m_raw},
    )
    if not isinstance(stationary_domain_interval_root_guard, AcceptedHybridRootGuard):
        raise AssertionError("stationary-domain interval root guard fixture rejected")
    up0, up1, uD, unsafe_minimizer = construct_stationary(315, 351, 126, 83)
    unsafe_stationary_m_raw = build_stationary(up0, up1, uD, unsafe_minimizer)
    unsafe_stationary_m_result = verify_stationary(up0, up1, uD, unsafe_stationary_m_raw)
    if not unsafe_stationary_m_result.accepted or unsafe_stationary_m_result.m is None:
        raise AssertionError("unsafe stationary hybrid fixture rejected")
    unsafe_stationary_hash = hashlib.sha256(unsafe_stationary_m_raw).hexdigest()
    ub_star = continuous_optimum(up0, up1, uD)
    uargmax, _ = discrete_optimum_prod(up0, up1, uD)
    uanchor = best_continuous_integer_anchor(up0, up1, uD)
    unsafe_stationary_raw = build_stationary_m_backed_tight_argmax_certificate(
        up0,
        up1,
        uD,
        uanchor,
        uargmax,
        ub_star,
        unsafe_stationary_m_raw,
    )
    unsafe_stationary_root_guard_raw = build_nonendpoint_hybrid_root_guard_certificate(
        up0,
        up1,
        uD,
        M_SOURCE_STATIONARY_CERTIFICATE,
        unsafe_stationary_m_raw,
    )
    stationary_hybrid_unsupported_raw = _canonical_json_bytes(
        _build_tight_argmax_certificate_payload(
            up0,
            up1,
            uD,
            uanchor,
            uargmax,
            ub_star,
            float(unsafe_stationary_m_result.m),
            M_SOURCE_STATIONARY_CERTIFICATE,
            {
                "m_certificate_schema": STATIONARY_M_CERTIFICATE_SCHEMA,
                "m_certificate_sha256": unsafe_stationary_hash,
            },
            include_hybrid_radius=True,
        )
    )

    bad_authority = _decoded_certificate(endpoint_raw)
    bad_authority["authority_effects"] = True

    stale_metric = _decoded_certificate(endpoint_raw)
    stale_metric["anchor_radius"] = 0.0
    stale_hybrid_metric = _decoded_certificate(hybrid_endpoint_raw)
    stale_hybrid_metric["hybrid_radius"] = 0.0

    return (
        ActualProjectionCase(
            "actual_endpoint_accept",
            p0,
            p1,
            D,
            endpoint_raw,
            None,
            True,
            "Endpoint certificate accepted by the actual tight-argmax verifier projects to endpoint Tau facts.",
        ),
        ActualProjectionCase(
            "actual_hybrid_endpoint_accept",
            p0,
            p1,
            D,
            hybrid_endpoint_raw,
            None,
            True,
            "Hybrid endpoint certificate accepted by the actual verifier projects to hybrid-present Tau facts.",
        ),
        ActualProjectionCase(
            "actual_interval_accept",
            p0,
            p1,
            D,
            interval_raw,
            {interval_hash: interval_m_raw},
            True,
            "Interval-backed certificate accepted by the actual verifier projects to interval Tau facts.",
        ),
        ActualProjectionCase(
            "actual_interval_root_guard_hybrid_accept",
            p0,
            p1,
            D,
            interval_raw,
            {interval_hash: interval_m_raw},
            True,
            "Interval-backed certificate plus accepted exact root guard projects to hybrid-present Tau facts.",
            interval_root_guard_raw,
            {interval_hash: interval_m_raw},
        ),
        ActualProjectionCase(
            "actual_stationary_accept",
            sp0,
            sp1,
            sD,
            stationary_raw,
            {stationary_hash: stationary_m_raw},
            True,
            "Stationary-backed certificate accepted by the actual verifier projects to stationary Tau facts.",
        ),
        ActualProjectionCase(
            "actual_stationary_root_guard_hybrid_accept",
            up0,
            up1,
            uD,
            unsafe_stationary_raw,
            {unsafe_stationary_hash: unsafe_stationary_m_raw},
            True,
            "Stationary-backed certificate plus accepted exact root guard repairs the under-radius fixture before Tau projection.",
            unsafe_stationary_root_guard_raw,
            {unsafe_stationary_hash: unsafe_stationary_m_raw},
        ),
        ActualProjectionCase(
            "actual_authority_reject",
            p0,
            p1,
            D,
            _canonical_json_bytes(bad_authority),
            None,
            False,
            "Authority effects in actual certificate bytes fail closed before Tau admission.",
        ),
        ActualProjectionCase(
            "actual_stale_metric_reject",
            p0,
            p1,
            D,
            _canonical_json_bytes(stale_metric),
            None,
            False,
            "Stale radius metrics fail closed before Tau admission.",
        ),
        ActualProjectionCase(
            "actual_stale_hybrid_metric_reject",
            p0,
            p1,
            D,
            _canonical_json_bytes(stale_hybrid_metric),
            None,
            False,
            "Stale hybrid radius metrics fail closed before Tau admission.",
        ),
        ActualProjectionCase(
            "actual_interval_hybrid_unsupported_reject",
            p0,
            p1,
            D,
            interval_hybrid_unsupported_raw,
            {interval_hash: interval_m_raw},
            False,
            "Interval m plus hybrid radius is unsupported and fails closed before Tau admission.",
        ),
        ActualProjectionCase(
            "actual_stationary_hybrid_unsupported_reject",
            up0,
            up1,
            uD,
            stationary_hybrid_unsupported_raw,
            {unsafe_stationary_hash: unsafe_stationary_m_raw},
            False,
            "Stationary m plus hybrid radius is unsupported and fails closed before Tau admission.",
        ),
        ActualProjectionCase(
            "actual_interval_root_guard_hash_mismatch_reject",
            p0,
            p1,
            D,
            interval_raw,
            {interval_hash: interval_m_raw},
            False,
            "A valid root guard for a different interval certificate hash cannot bind to the accepted tight-argmax certificate.",
            alt_interval_root_guard_raw,
            {alt_interval_hash: alt_interval_m_raw},
            ("hybrid_root_guard:m_certificate_hash_mismatch",),
        ),
        ActualProjectionCase(
            "actual_stationary_root_guard_source_mismatch_reject",
            sp0,
            sp1,
            sD,
            stationary_raw,
            {stationary_hash: stationary_m_raw},
            False,
            "A valid interval-source root guard cannot bind to a stationary-source tight-argmax certificate on the same domain.",
            stationary_domain_interval_root_guard_raw,
            {stationary_domain_interval_hash: stationary_domain_interval_m_raw},
            ("hybrid_root_guard:m_source_mismatch",),
        ),
        ActualProjectionCase(
            "actual_interval_root_guard_anchor_mismatch_reject",
            p0,
            p1,
            D,
            interval_anchor_mismatch_raw,
            {interval_hash: interval_m_raw},
            False,
            "A tight-argmax certificate with a different accepted anchor cannot reuse a root guard for the canonical anchor.",
            interval_root_guard_raw,
            {interval_hash: interval_m_raw},
            ("hybrid_root_guard:argmax_anchor_mismatch",),
        ),
        ActualProjectionCase(
            "actual_interval_root_guard_argmax_mismatch_reject",
            p0,
            p1,
            D,
            interval_argmax_mismatch_raw,
            {interval_hash: interval_m_raw},
            False,
            "A tight-argmax certificate with a different accepted argmax cannot reuse a root guard for the canonical argmax.",
            interval_root_guard_raw,
            {interval_hash: interval_m_raw},
            ("hybrid_root_guard:argmax_anchor_mismatch",),
        ),
        ActualProjectionCase(
            "actual_interval_root_guard_domain_mismatch_reject",
            sp0,
            sp1,
            sD,
            stationary_raw,
            {stationary_hash: stationary_m_raw},
            False,
            "A root guard from a different domain fails closed before cross-binding checks.",
            interval_root_guard_raw,
            {interval_hash: interval_m_raw},
            ("hybrid_root_guard:domain_hash_mismatch",),
        ),
        ActualProjectionCase(
            "actual_interval_root_guard_missing_resolver_reject",
            p0,
            p1,
            D,
            interval_raw,
            {interval_hash: interval_m_raw},
            False,
            "Supplying a non-endpoint hybrid root guard without its referenced artifact bytes fails closed.",
            interval_root_guard_raw,
            {},
        ),
        ActualProjectionCase(
            "actual_interval_missing_resolver_reject",
            p0,
            p1,
            D,
            interval_raw,
            None,
            False,
            "Missing referenced interval certificate bytes fail closed before Tau admission.",
        ),
        ActualProjectionCase(
            "actual_stationary_tampered_resolver_reject",
            sp0,
            sp1,
            sD,
            stationary_raw,
            {stationary_hash: stationary_m_raw + b"\n"},
            False,
            "Tampered stationary artifact bytes fail closed before Tau admission.",
        ),
    )


def mutation_checks() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source, source_flags in SOURCE_FLAGS.items():
        required = (
            "certificate_requested",
            "m_positive",
            *PACKET_FLAGS,
            *ARGMAX_FLAGS,
            *AUTHORITY_FLAGS,
            "hybrid_radius_absent",
            *source_flags,
        )
        for flag in required:
            mutated = base_flags(source)
            mutated[flag] = 0
            outputs = evaluate_outputs(mutated)
            rows.append(
                {
                    "mutation_id": f"{source}:clear:{flag}",
                    "source": source,
                    "accepted": outputs["o8"] == 1,
                    "expected_reject": True,
                    "outputs": outputs,
                }
            )

    endpoint_hybrid = base_flags("endpoint")
    endpoint_hybrid["hybrid_radius_absent"] = 0
    for name in HYBRID_PRESENT_FLAGS:
        endpoint_hybrid[name] = 1
    for flag in ("certificate_requested", "m_positive", *PACKET_FLAGS, *ARGMAX_FLAGS,
                 *AUTHORITY_FLAGS, *HYBRID_PRESENT_FLAGS, *SOURCE_FLAGS["endpoint"]):
        mutated = dict(endpoint_hybrid)
        mutated[flag] = 0
        outputs = evaluate_outputs(mutated)
        rows.append(
            {
                "mutation_id": f"endpoint_hybrid:clear:{flag}",
                "source": "endpoint_hybrid",
                "accepted": outputs["o8"] == 1,
                "expected_reject": True,
                "outputs": outputs,
            }
        )

    hybrid_mixed = dict(endpoint_hybrid, hybrid_radius_absent=1)
    rows.append(
        {
            "mutation_id": "endpoint_hybrid_plus_absent",
            "source": "endpoint_hybrid",
            "accepted": evaluate_outputs(hybrid_mixed)["o8"] == 1,
            "expected_reject": True,
            "outputs": evaluate_outputs(hybrid_mixed),
        }
    )

    mixed = base_flags("stationary")
    mixed.update({"endpoint_source": 1, "endpoint_m_recomputed": 1})
    rows.append(
        {
            "mutation_id": "stationary_plus_endpoint_source",
            "source": "stationary",
            "accepted": evaluate_outputs(mixed)["o8"] == 1,
            "expected_reject": True,
            "outputs": evaluate_outputs(mixed),
        }
    )
    return rows


def _structural_checks() -> list[dict[str, Any]]:
    text = TAU_SPEC.read_text(encoding="utf-8") if TAU_SPEC.exists() else ""
    used_slots = {slot for slot in SLOTS.values() if f"{slot}[t]" in text}
    host_contract_errors = lint_host_projection_contracts(REPO_ROOT / "src" / "tau_specs" / "recommended" / "host_projection_contracts.json")
    return [
        {"check_id": "spec_exists", "ok": TAU_SPEC.is_file(), "detail": str(TAU_SPEC.relative_to(REPO_ROOT))},
        {"check_id": "no_bitvector_inputs", "ok": "bv[" not in text, "detail": "Tau envelope uses sbf host facts only"},
        {"check_id": "all_slots_used", "ok": used_slots == set(SLOTS.values()), "missing": sorted(set(SLOTS.values()) - used_slots)},
        {
            "check_id": "bound_projection_type_exposed",
            "ok": BoundTightArgmaxProjection.__name__ == "BoundTightArgmaxProjection",
            "detail": "Tau fact emission for actual certificates is routed through a validated bound projection object.",
        },
        {
            "check_id": "bound_projection_receipt_schema_exposed",
            "ok": BOUND_PROJECTION_RECEIPT_SCHEMA.endswith(".v1"),
            "detail": BOUND_PROJECTION_RECEIPT_SCHEMA,
        },
        {
            "check_id": "bound_projection_receipt_consumer_exposed",
            "ok": verify_bound_projection_receipt.__name__ == "verify_bound_projection_receipt",
            "detail": "Receipt consumers reconstruct and compare canonical receipt payloads before accepting cited hashes.",
        },
        {
            "check_id": "bound_projection_receipt_manifest_schema_exposed",
            "ok": BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA.endswith(".v1"),
            "detail": BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
        },
        {
            "check_id": "claim_promotion_bundle_schema_exposed",
            "ok": CLAIM_PROMOTION_BUNDLE_SCHEMA.endswith(".v1"),
            "detail": CLAIM_PROMOTION_BUNDLE_SCHEMA,
        },
        {"check_id": "host_projection_contracts_lint", "ok": not host_contract_errors, "errors": host_contract_errors},
    ]


def _run_tau_cases() -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "cases": []}

    cases = tau_cases()
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[tau_step(case.flags) for case in cases],
        timeout_s=20.0,
    )

    rows: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(cases):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": int(case.expected[key]), "got": got.get(key)}
            for key in OUTPUTS
            if got.get(key) != int(case.expected[key])
        }
        ok = ok and not mismatches
        rows.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": dict(case.expected),
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    return {
        "ok": ok,
        "tau_bin": tau_bin,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "case_count": len(rows),
        "cases": rows,
    }


def _run_actual_projection_tau_cases() -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "cases": []}

    cases = actual_projection_cases()
    bindings = [
        bind_tight_argmax_projection(
            case.p0,
            case.p1,
            case.amount_out_total,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
        )
        for case in cases
    ]
    projections: list[Projection] = [
        project_bound_tight_argmax_to_tau_flags(binding)
        if isinstance(binding, BoundTightArgmaxProjection)
        else binding
        for binding in bindings
    ]
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[tau_step(projection.flags) for projection in projections],
        timeout_s=20.0,
    )

    rows: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(cases):
        binding = bindings[idx]
        projection = projections[idx]
        bound_accepted = isinstance(binding, BoundTightArgmaxProjection)
        projection_accepted = isinstance(projection, AcceptedProjection)
        receipt: BoundProjectionReceipt | None = None
        receipt_error: str | None = None
        if isinstance(binding, BoundTightArgmaxProjection):
            try:
                receipt = build_bound_projection_receipt(
                    case.case_id,
                    case.raw_certificate,
                    case.resolver,
                    case.hybrid_root_guard_raw,
                    case.hybrid_root_guard_resolver,
                    binding,
                )
            except ValueError as exc:
                receipt_error = str(exc)
        expected = evaluate_outputs(projection.flags)
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": int(expected[key]), "got": got.get(key)}
            for key in OUTPUTS
            if got.get(key) != int(expected[key])
        }
        accepted_mismatch = projection_accepted != case.expected_accepted
        tau_admit_mismatch = (got.get("o8") == 1) != case.expected_accepted
        receipt_mismatch = (receipt is not None) != case.expected_accepted or receipt_error is not None
        case_ok = not mismatches and not accepted_mismatch and not tau_admit_mismatch and not receipt_mismatch
        ok = ok and case_ok
        rows.append(
            {
                "case_id": case.case_id,
                "ok": case_ok,
                "expected_accepted": case.expected_accepted,
                "expected_rejects": case.expected_rejects,
                "binding_accepted": bound_accepted,
                "bound_type": binding.__class__.__name__,
                "hybrid_radius_projection": (
                    binding.hybrid_radius.value if isinstance(binding, BoundTightArgmaxProjection) else None
                ),
                "receipt_sha256": receipt.receipt_sha256 if receipt is not None else None,
                "receipt": receipt.report_row() if receipt is not None else None,
                "receipt_error": receipt_error,
                "projection_accepted": projection_accepted,
                "verifier_rejects": tuple(getattr(projection, "verifier_rejects", ())),
                "expected": expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    accepted_count = sum(1 for row in rows if row["projection_accepted"] is True)
    rejected_count = sum(1 for row in rows if row["projection_accepted"] is False)
    receipt_count = sum(1 for row in rows if row["receipt"] is not None)
    return {
        "ok": ok,
        "tau_bin": tau_bin,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "case_count": len(rows),
        "accepted_count": accepted_count,
        "rejected_count": rejected_count,
        "receipt_count": receipt_count,
        "receipt_schema": BOUND_PROJECTION_RECEIPT_SCHEMA,
        "cases": rows,
    }


def receipt_consumer_checks() -> dict[str, Any]:
    cases = {case.case_id: case for case in actual_projection_cases()}
    receipt_rows: dict[str, dict[str, object]] = {}
    positive_rows: list[dict[str, object]] = []

    for case in cases.values():
        if not case.expected_accepted:
            continue
        binding = bind_tight_argmax_projection(
            case.p0,
            case.p1,
            case.amount_out_total,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
        )
        if not isinstance(binding, BoundTightArgmaxProjection):
            positive_rows.append({
                "case_id": case.case_id,
                "ok": False,
                "reason": "accepted fixture did not bind",
            })
            continue
        receipt = build_bound_projection_receipt(
            case.case_id,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
            binding,
        )
        receipt_rows[case.case_id] = receipt.report_row()
        try:
            consumed = verify_bound_projection_receipt(
                case.case_id,
                case.p0,
                case.p1,
                case.amount_out_total,
                case.raw_certificate,
                case.resolver,
                case.hybrid_root_guard_raw,
                case.hybrid_root_guard_resolver,
                receipt.report_row(),
            )
            positive_rows.append({
                "case_id": case.case_id,
                "ok": consumed.receipt_sha256 == receipt.receipt_sha256,
                "receipt_sha256": receipt.receipt_sha256,
            })
        except ValueError as exc:
            positive_rows.append({
                "case_id": case.case_id,
                "ok": False,
                "reason": str(exc),
            })

    def expect_reject(
        mutation_id: str,
        expected_reason: str,
        case: ActualProjectionCase,
        receipt_row: Mapping[str, object],
        resolver: Mapping[str, bytes] | None = None,
        hybrid_root_guard_raw: bytes | None = None,
        hybrid_root_guard_resolver: Mapping[str, bytes] | None = None,
    ) -> dict[str, object]:
        try:
            verify_bound_projection_receipt(
                case.case_id,
                case.p0,
                case.p1,
                case.amount_out_total,
                case.raw_certificate,
                case.resolver if resolver is None else resolver,
                case.hybrid_root_guard_raw if hybrid_root_guard_raw is None else hybrid_root_guard_raw,
                (
                    case.hybrid_root_guard_resolver
                    if hybrid_root_guard_resolver is None
                    else hybrid_root_guard_resolver
                ),
                receipt_row,
            )
        except ValueError as exc:
            reason = str(exc)
            return {
                "mutation_id": mutation_id,
                "expected_reason": expected_reason,
                "reason": reason,
                "ok": expected_reason in reason,
            }
        return {
            "mutation_id": mutation_id,
            "expected_reason": expected_reason,
            "reason": "accepted",
            "ok": False,
        }

    endpoint = cases["actual_endpoint_accept"]
    hybrid_endpoint = cases["actual_hybrid_endpoint_accept"]
    interval = cases["actual_interval_accept"]
    root_guard = cases["actual_interval_root_guard_hybrid_accept"]
    extra = b"unreferenced resolver bytes"
    interval_key = next(iter(interval.resolver or {}))
    tampered_row = json.loads(json.dumps(receipt_rows[endpoint.case_id]))
    tampered_row["tau_flags"]["certificate_requested"] = 0

    negative_rows = [
        expect_reject(
            "stale_receipt_replayed_with_new_certificate",
            "receipt hash mismatch",
            hybrid_endpoint,
            receipt_rows[endpoint.case_id],
        ),
        expect_reject(
            "swapped_resolver_artifact",
            "resolver key/content hash mismatch",
            interval,
            receipt_rows[interval.case_id],
            resolver={interval_key: b"tampered"},
        ),
        expect_reject(
            "root_guard_replayed_against_non_root_projection",
            "non-root receipt cannot carry root guard bytes",
            endpoint,
            receipt_rows[endpoint.case_id],
            hybrid_root_guard_raw=root_guard.hybrid_root_guard_raw,
            hybrid_root_guard_resolver=root_guard.hybrid_root_guard_resolver,
        ),
        expect_reject(
            "endpoint_receipt_with_injected_resolver_dependency",
            "endpoint receipt cannot depend on resolver artifacts",
            endpoint,
            receipt_rows[endpoint.case_id],
            resolver={_sha256_bytes(extra): extra},
        ),
        expect_reject(
            "report_row_payload_hash_mismatch",
            "receipt payload mismatch",
            endpoint,
            tampered_row,
        ),
    ]
    return {
        "ok": all(row["ok"] for row in positive_rows) and all(row["ok"] for row in negative_rows),
        "positive_count": len(positive_rows),
        "negative_count": len(negative_rows),
        "positive_cases": positive_rows,
        "negative_cases": negative_rows,
    }


def receipt_manifest_checks() -> dict[str, Any]:
    cases = {case.case_id: case for case in actual_projection_cases()}
    receipt_rows: dict[str, dict[str, object]] = {}
    manifest_rows: dict[str, BoundProjectionReceiptManifest] = {}
    positive_rows: list[dict[str, object]] = []

    for case in cases.values():
        if not case.expected_accepted:
            continue
        binding = bind_tight_argmax_projection(
            case.p0,
            case.p1,
            case.amount_out_total,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
        )
        if not isinstance(binding, BoundTightArgmaxProjection):
            positive_rows.append({"case_id": case.case_id, "ok": False, "reason": "accepted fixture did not bind"})
            continue
        receipt_row = build_bound_projection_receipt(
            case.case_id,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
            binding,
        ).report_row()
        manifest = build_bound_projection_receipt_manifest(
            manifest_id=f"manifest:{case.case_id}",
            case_id=case.case_id,
            raw_certificate=case.raw_certificate,
            resolver=case.resolver,
            hybrid_root_guard_raw=case.hybrid_root_guard_raw,
            hybrid_root_guard_resolver=case.hybrid_root_guard_resolver,
            receipt_row=receipt_row,
        )
        receipt_rows[case.case_id] = receipt_row
        manifest_rows[case.case_id] = manifest
        try:
            consumed = verify_bound_projection_receipt_manifest(
                manifest,
                case.p0,
                case.p1,
                case.amount_out_total,
                case.raw_certificate,
                case.resolver,
                case.hybrid_root_guard_raw,
                case.hybrid_root_guard_resolver,
                receipt_row,
            )
            positive_rows.append({
                "case_id": case.case_id,
                "ok": consumed.manifest_sha256 == manifest.manifest_sha256,
                "manifest_sha256": manifest.manifest_sha256,
                "receipt_sha256": manifest.receipt_sha256,
            })
        except ValueError as exc:
            positive_rows.append({"case_id": case.case_id, "ok": False, "reason": str(exc)})

    def expect_reject(mutation_id: str, expected_reason: str, fn: Any) -> dict[str, object]:
        try:
            fn()
        except ValueError as exc:
            reason = str(exc)
            return {
                "mutation_id": mutation_id,
                "expected_reason": expected_reason,
                "reason": reason,
                "ok": expected_reason in reason,
            }
        return {
            "mutation_id": mutation_id,
            "expected_reason": expected_reason,
            "reason": "accepted",
            "ok": False,
        }

    endpoint = cases["actual_endpoint_accept"]
    hybrid_endpoint = cases["actual_hybrid_endpoint_accept"]
    interval = cases["actual_interval_accept"]
    endpoint_manifest = manifest_rows[endpoint.case_id]
    interval_manifest = manifest_rows[interval.case_id]
    missing_ref_manifest = BoundProjectionReceiptManifest(
        schema=BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
        manifest_id="manifest:missing_interval_ref",
        case_id=interval.case_id,
        receipt_sha256=interval_manifest.receipt_sha256,
        source_refs=tuple(
            ref for ref in interval_manifest.source_refs if ref.role != SOURCE_ROLE_RESOLVER_ARTIFACT
        ),
        no_authority_boundary=NO_AUTHORITY_BOUNDARY,
    )
    extra = b"manifest extra source"
    extra_ref_manifest = BoundProjectionReceiptManifest(
        schema=BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
        manifest_id="manifest:extra_ref",
        case_id=endpoint.case_id,
        receipt_sha256=endpoint_manifest.receipt_sha256,
        source_refs=tuple(sorted(
            (*endpoint_manifest.source_refs, _manifest_source_ref(SOURCE_ROLE_RESOLVER_ARTIFACT, extra)),
            key=lambda ref: (ref.role, ref.sha256, ref.byte_len, ref.evidence_role),
        )),
        no_authority_boundary=NO_AUTHORITY_BOUNDARY,
    )

    negative_rows = [
        expect_reject(
            "missing_source_ref",
            "manifest missing source ref",
            lambda: verify_bound_projection_receipt_manifest(
                missing_ref_manifest,
                interval.p0,
                interval.p1,
                interval.amount_out_total,
                interval.raw_certificate,
                interval.resolver,
                interval.hybrid_root_guard_raw,
                interval.hybrid_root_guard_resolver,
                receipt_rows[interval.case_id],
            ),
        ),
        expect_reject(
            "undeclared_extra_source_ref",
            "manifest undeclared source ref",
            lambda: verify_bound_projection_receipt_manifest(
                extra_ref_manifest,
                endpoint.p0,
                endpoint.p1,
                endpoint.amount_out_total,
                endpoint.raw_certificate,
                endpoint.resolver,
                endpoint.hybrid_root_guard_raw,
                endpoint.hybrid_root_guard_resolver,
                receipt_rows[endpoint.case_id],
            ),
        ),
        expect_reject(
            "copied_receipt_row_from_different_case",
            "manifest receipt hash mismatch",
            lambda: verify_bound_projection_receipt_manifest(
                manifest_rows[hybrid_endpoint.case_id],
                hybrid_endpoint.p0,
                hybrid_endpoint.p1,
                hybrid_endpoint.amount_out_total,
                hybrid_endpoint.raw_certificate,
                hybrid_endpoint.resolver,
                hybrid_endpoint.hybrid_root_guard_raw,
                hybrid_endpoint.hybrid_root_guard_resolver,
                receipt_rows[endpoint.case_id],
            ),
        ),
        expect_reject(
            "theoremsearch_prior_art_as_proof",
            "TheoremSearch prior art must be retrieval-only",
            lambda: ManifestSourceRef(
                role=SOURCE_ROLE_THEOREMSEARCH_PRIOR_ART,
                sha256=_sha256_bytes(b"theoremsearch prior art"),
                byte_len=len(b"theoremsearch prior art"),
                evidence_role=PROOF_INPUT_ROLE,
            ),
        ),
        expect_reject(
            "manifest_missing_authority_boundary",
            "manifest missing no-authority boundary",
            lambda: BoundProjectionReceiptManifest(
                schema=BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
                manifest_id="manifest:missing_boundary",
                case_id=endpoint.case_id,
                receipt_sha256=endpoint_manifest.receipt_sha256,
                source_refs=endpoint_manifest.source_refs,
                no_authority_boundary="",
            ),
        ),
    ]
    return {
        "ok": all(row["ok"] for row in positive_rows) and all(row["ok"] for row in negative_rows),
        "schema": BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
        "positive_count": len(positive_rows),
        "negative_count": len(negative_rows),
        "positive_cases": positive_rows,
        "negative_cases": negative_rows,
    }


def claim_promotion_checks() -> dict[str, Any]:
    cases = {case.case_id: case for case in actual_projection_cases()}
    receipts: dict[str, dict[str, object]] = {}
    manifests: dict[str, BoundProjectionReceiptManifest] = {}
    positive_rows: list[dict[str, object]] = []

    for case in cases.values():
        if not case.expected_accepted:
            continue
        binding = bind_tight_argmax_projection(
            case.p0,
            case.p1,
            case.amount_out_total,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
        )
        if not isinstance(binding, BoundTightArgmaxProjection):
            positive_rows.append({"case_id": case.case_id, "ok": False, "reason": "accepted fixture did not bind"})
            continue
        receipt_row = build_bound_projection_receipt(
            case.case_id,
            case.raw_certificate,
            case.resolver,
            case.hybrid_root_guard_raw,
            case.hybrid_root_guard_resolver,
            binding,
        ).report_row()
        manifest = build_bound_projection_receipt_manifest(
            manifest_id=f"manifest:{case.case_id}",
            case_id=case.case_id,
            raw_certificate=case.raw_certificate,
            resolver=case.resolver,
            hybrid_root_guard_raw=case.hybrid_root_guard_raw,
            hybrid_root_guard_resolver=case.hybrid_root_guard_resolver,
            receipt_row=receipt_row,
        )
        receipts[case.case_id] = receipt_row
        manifests[case.case_id] = manifest
        for target in sorted(PROMOTION_TARGETS):
            bundle = build_claim_promotion_bundle(
                bundle_id=f"promotion:{target}:{case.case_id}",
                promotion_target=target,
                manifest=manifest,
            )
            try:
                consumed = verify_claim_promotion_bundle(
                    bundle,
                    manifest,
                    case.p0,
                    case.p1,
                    case.amount_out_total,
                    case.raw_certificate,
                    case.resolver,
                    case.hybrid_root_guard_raw,
                    case.hybrid_root_guard_resolver,
                    receipt_row,
                )
                positive_rows.append({
                    "case_id": case.case_id,
                    "promotion_target": target,
                    "ok": consumed.bundle_sha256 == bundle.bundle_sha256,
                    "bundle_sha256": bundle.bundle_sha256,
                    "manifest_sha256": bundle.manifest_sha256,
                })
            except ValueError as exc:
                positive_rows.append({
                    "case_id": case.case_id,
                    "promotion_target": target,
                    "ok": False,
                    "reason": str(exc),
                })

    def expect_reject(mutation_id: str, expected_reason: str, fn: Any) -> dict[str, object]:
        try:
            fn()
        except ValueError as exc:
            reason = str(exc)
            return {
                "mutation_id": mutation_id,
                "expected_reason": expected_reason,
                "reason": reason,
                "ok": expected_reason in reason,
            }
        return {
            "mutation_id": mutation_id,
            "expected_reason": expected_reason,
            "reason": "accepted",
            "ok": False,
        }

    endpoint = cases["actual_endpoint_accept"]
    hybrid_endpoint = cases["actual_hybrid_endpoint_accept"]
    interval = cases["actual_interval_accept"]
    endpoint_manifest = manifests[endpoint.case_id]
    endpoint_bundle = build_claim_promotion_bundle("promotion:research_kernel:endpoint", "research_kernel", endpoint_manifest)
    interval_manifest = manifests[interval.case_id]
    missing_ref_bundle = ClaimPromotionBundle(
        schema=CLAIM_PROMOTION_BUNDLE_SCHEMA,
        bundle_id="promotion:missing_ref",
        promotion_target="claims_registry",
        manifest_sha256=interval_manifest.manifest_sha256,
        replay_command=TIGHT_ARGMAX_REPLAY_COMMAND,
        source_refs=tuple(
            ref for ref in interval_manifest.source_refs if ref.role != SOURCE_ROLE_RESOLVER_ARTIFACT
        ),
        no_authority_boundary=NO_AUTHORITY_BOUNDARY,
        production_security_claim=False,
    )
    receipt_hash_bundle = ClaimPromotionBundle(
        schema=CLAIM_PROMOTION_BUNDLE_SCHEMA,
        bundle_id="promotion:receipt_hash_direct",
        promotion_target="research_kernel",
        manifest_sha256=str(receipts[endpoint.case_id]["receipt_sha256"]),
        replay_command=TIGHT_ARGMAX_REPLAY_COMMAND,
        source_refs=endpoint_manifest.source_refs,
        no_authority_boundary=NO_AUTHORITY_BOUNDARY,
        production_security_claim=False,
    )
    negative_rows = [
        expect_reject(
            "missing_manifest",
            "promotion manifest required",
            lambda: verify_claim_promotion_bundle(
                endpoint_bundle,
                None,
                endpoint.p0,
                endpoint.p1,
                endpoint.amount_out_total,
                endpoint.raw_certificate,
                endpoint.resolver,
                endpoint.hybrid_root_guard_raw,
                endpoint.hybrid_root_guard_resolver,
                receipts[endpoint.case_id],
            ),
        ),
        expect_reject(
            "receipt_hash_without_manifest",
            "promotion manifest hash mismatch",
            lambda: verify_claim_promotion_bundle(
                receipt_hash_bundle,
                endpoint_manifest,
                endpoint.p0,
                endpoint.p1,
                endpoint.amount_out_total,
                endpoint.raw_certificate,
                endpoint.resolver,
                endpoint.hybrid_root_guard_raw,
                endpoint.hybrid_root_guard_resolver,
                receipts[endpoint.case_id],
            ),
        ),
        expect_reject(
            "stale_manifest_hash",
            "promotion manifest hash mismatch",
            lambda: verify_claim_promotion_bundle(
                endpoint_bundle,
                manifests[hybrid_endpoint.case_id],
                hybrid_endpoint.p0,
                hybrid_endpoint.p1,
                hybrid_endpoint.amount_out_total,
                hybrid_endpoint.raw_certificate,
                hybrid_endpoint.resolver,
                hybrid_endpoint.hybrid_root_guard_raw,
                hybrid_endpoint.hybrid_root_guard_resolver,
                receipts[hybrid_endpoint.case_id],
            ),
        ),
        expect_reject(
            "detached_source_refs",
            "promotion source refs mismatch",
            lambda: verify_claim_promotion_bundle(
                missing_ref_bundle,
                interval_manifest,
                interval.p0,
                interval.p1,
                interval.amount_out_total,
                interval.raw_certificate,
                interval.resolver,
                interval.hybrid_root_guard_raw,
                interval.hybrid_root_guard_resolver,
                receipts[interval.case_id],
            ),
        ),
        expect_reject(
            "theoremsearch_prior_art_as_proof",
            "TheoremSearch prior art must be retrieval-only",
            lambda: ManifestSourceRef(
                role=SOURCE_ROLE_THEOREMSEARCH_PRIOR_ART,
                sha256=_sha256_bytes(b"theoremsearch prior art"),
                byte_len=len(b"theoremsearch prior art"),
                evidence_role=PROOF_INPUT_ROLE,
            ),
        ),
        expect_reject(
            "production_security_overclaim",
            "promotion bundle cannot claim production security",
            lambda: ClaimPromotionBundle(
                schema=CLAIM_PROMOTION_BUNDLE_SCHEMA,
                bundle_id="promotion:production_overclaim",
                promotion_target="claims_registry",
                manifest_sha256=endpoint_manifest.manifest_sha256,
                replay_command=TIGHT_ARGMAX_REPLAY_COMMAND,
                source_refs=endpoint_manifest.source_refs,
                no_authority_boundary=NO_AUTHORITY_BOUNDARY,
                production_security_claim=True,
            ),
        ),
        expect_reject(
            "promotion_missing_authority_boundary",
            "promotion missing no-authority boundary",
            lambda: ClaimPromotionBundle(
                schema=CLAIM_PROMOTION_BUNDLE_SCHEMA,
                bundle_id="promotion:missing_boundary",
                promotion_target="research_kernel",
                manifest_sha256=endpoint_manifest.manifest_sha256,
                replay_command=TIGHT_ARGMAX_REPLAY_COMMAND,
                source_refs=endpoint_manifest.source_refs,
                no_authority_boundary="",
                production_security_claim=False,
            ),
        ),
    ]
    return {
        "ok": all(row["ok"] for row in positive_rows) and all(row["ok"] for row in negative_rows),
        "schema": CLAIM_PROMOTION_BUNDLE_SCHEMA,
        "positive_count": len(positive_rows),
        "negative_count": len(negative_rows),
        "positive_cases": positive_rows,
        "negative_cases": negative_rows,
    }


def build_report() -> dict[str, Any]:
    mutations = mutation_checks()
    structural = _structural_checks()
    tau = _run_tau_cases()
    actual_projection = _run_actual_projection_tau_cases()
    receipt_consumer = receipt_consumer_checks()
    receipt_manifest = receipt_manifest_checks()
    claim_promotion = claim_promotion_checks()
    ok = (
        tau.get("ok") is True
        and actual_projection.get("ok") is True
        and actual_projection.get("accepted_count") == 6
        and actual_projection.get("rejected_count") == 13
        and actual_projection.get("receipt_count") == 6
        and receipt_consumer.get("ok") is True
        and receipt_manifest.get("ok") is True
        and claim_promotion.get("ok") is True
        and all(row["accepted"] is False for row in mutations)
        and all(row["ok"] is True for row in structural)
    )
    return {
        "schema": "zenodex.tight_argmax_m_source_tau_envelope_report.v1",
        "date": "2026-06-30",
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "summary": {
            "accepted_sources": ["endpoint", "interval", "stationary"],
            "optional_radius_surfaces": [
                "legacy_anchor_oracle_gross",
                "endpoint_hybrid_anchor_lipschitz",
                "nonendpoint_exact_root_guard",
            ],
            "binding_refuter_cases": [
                "m_certificate_hash_mismatch",
                "m_source_mismatch",
                "anchor_mismatch",
                "argmax_mismatch",
                "domain_mismatch",
            ],
            "typed_projection_object": "BoundTightArgmaxProjection",
            "bound_projection_receipt_schema": BOUND_PROJECTION_RECEIPT_SCHEMA,
            "bound_projection_receipt_consumer": "verify_bound_projection_receipt",
            "bound_projection_receipt_manifest_schema": BOUND_PROJECTION_RECEIPT_MANIFEST_SCHEMA,
            "bound_projection_receipt_manifest_adapter": "verify_bound_projection_receipt_manifest",
            "claim_promotion_bundle_schema": CLAIM_PROMOTION_BUNDLE_SCHEMA,
            "claim_promotion_gate": "verify_claim_promotion_bundle",
            "tau_step_complexity": "O(1) boolean host-fact combination",
            "authority_boundary": (
                "Tau admits a research certificate envelope only. It does not choose routes, "
                "parse artifacts, recompute m, authorize settlement, or affect consensus."
            ),
        },
        "tau": tau,
        "actual_certificate_projection": actual_projection,
        "receipt_consumer": receipt_consumer,
        "receipt_manifest": receipt_manifest,
        "claim_promotion": claim_promotion,
        "structural_checks": structural,
        "mutation_checks": {
            "case_count": len(mutations),
            "all_rejected": all(row["accepted"] is False for row in mutations),
            "cases": mutations,
        },
        "non_claims": [
            "The Tau envelope trusts host-projected facts after the host validates canonical bytes and referenced certificates.",
            "The host projection bridge is not an independent certificate verifier; it emits accepting Tau facts only after the existing tight-argmax verifier accepts.",
            "Hybrid radius facts are optional, but if present they must be recomputed and admitted as a complete all-or-nothing surface.",
            "Non-endpoint hybrid facts require a separate accepted exact root guard; inline non-endpoint hybrid packets remain rejected.",
            "The envelope does not prove the interval or stationary curvature theorem; it requires accepted host evidence for those sources.",
            "The receipt manifest adapter proves source binding for cited research evidence; it is not an independent mathematical verifier.",
            "The claim-promotion gate accepts research-evidence bundle citations only after receipt-manifest verification; it does not create production security evidence.",
            "The envelope is research evidence only and grants no production routing, settlement, or consensus authority.",
        ],
        "replay_command": TIGHT_ARGMAX_REPLAY_COMMAND,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path, default=REPORT_JSON)
    args = parser.parse_args(argv)

    report = build_report()
    encoded = json.dumps(report, indent=2, sort_keys=True)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
