from __future__ import annotations

import json
from dataclasses import dataclass
from math import exp, log, sqrt
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import urlparse

from ..integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    external_signal_source_registry_from_object,
)
from ..integration.autotrader_signals import (
    ExternalSignalObservation,
    SignalTrustTier,
    external_signal_observations_from_object,
)
from ..integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from ..state.canonical import canonical_json_bytes, sha256_hex
from .policy_artifacts import G2Basic, _parse_privkey_to_int, _require_bls

AUTOTRADER_KRR_BUNDLE_SCHEMA = "zenodex/autotrader-krr-bundle/v1"
KRR_SOURCE_SNAPSHOT_SCHEMA = "zenodex/krr-source-snapshot/v1"
KRR_EVIDENCE_RECORD_SCHEMA = "zenodex/krr-evidence-record/v1"
KRR_CANONICAL_CLAIM_SCHEMA = "zenodex/krr-canonical-claim/v1"
KRR_REVIEW_RECORD_SCHEMA = "zenodex/krr-review-record/v1"
KRR_SOURCE_QUALITY_SCHEMA = "zenodex/krr-source-quality/v1"
AUTOTRADER_EXTERNAL_SIGNAL_SET_SCHEMA = "zenodex/autotrader-external-signal-set/v1"

_SAFE_TOKEN_CHARS = set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.:-")
_REVIEW_DECISIONS = {"approve", "reject", "comment"}
_REVIEW_TARGET_KINDS = {"bundle", "claim", "source", "evidence"}
_SOURCE_CLASSES = {
    "official_api",
    "official_doc",
    "protocol_doc",
    "research_paper",
    "research_dataset",
    "news",
    "other",
}
_TRUST_TIERS = {tier.value for tier in SignalTrustTier}


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _require_safe_token(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if any(ch not in _SAFE_TOKEN_CHARS for ch in text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _require_optional_safe_token(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_safe_token(value, name=name)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_tier(value: object, *, name: str) -> str:
    text = _require_safe_token(value, name=name)
    if text not in _TRUST_TIERS:
        raise ValueError(f"{name} must be one of {sorted(_TRUST_TIERS)}")
    return text


def _require_isoish_timestamp(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if "T" not in text:
        raise ValueError(f"{name} must be an ISO-like timestamp")
    return text


def _require_sha256_hex(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if not text.startswith("0x") or len(text) != 66:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex string")
    try:
        bytes.fromhex(text[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    return text.lower()


def _sha256_text(value: str) -> str:
    return sha256_hex(value.encode("utf-8"))


def _canonical_json_sha256(value: Mapping[str, Any]) -> str:
    return sha256_hex(canonical_json_bytes(dict(value)))


def _uniq_preserve(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _normalize_external_signals_payload(value: object | None) -> dict[str, Any] | None:
    if value is None:
        return None
    observations = tuple(external_signal_observations_from_object(value))
    return {
        "schema": AUTOTRADER_EXTERNAL_SIGNAL_SET_SCHEMA,
        "external_signals": [row.to_dict() for row in observations],
    }


def _normalize_runtime_history(value: object | None) -> dict[str, Any] | None:
    if value is None:
        return None
    if not isinstance(value, Mapping):
        raise TypeError("runtime_history must be an object")
    return dict(value)


def _canonicalize_bundle_value(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {str(key): _canonicalize_bundle_value(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_canonicalize_bundle_value(item) for item in value]
    if isinstance(value, list):
        return [_canonicalize_bundle_value(item) for item in value]
    if isinstance(value, float):
        return format(value, ".12g")
    return value


def _normal_cdf_inv(p: float) -> float:
    if not 0.0 < p < 1.0:
        raise ValueError("p must lie in (0, 1)")
    a = [
        -3.969683028665376e01,
        2.209460984245205e02,
        -2.759285104469687e02,
        1.383577518672690e02,
        -3.066479806614716e01,
        2.506628277459239e00,
    ]
    b = [
        -5.447609879822406e01,
        1.615858368580409e02,
        -1.556989798598866e02,
        6.680131188771972e01,
        -1.328068155288572e01,
    ]
    c = [
        -7.784894002430293e-03,
        -3.223964580411365e-01,
        -2.400758277161838e00,
        -2.549732539343734e00,
        4.374664141464968e00,
        2.938163982698783e00,
    ]
    d = [
        7.784695709041462e-03,
        3.224671290700398e-01,
        2.445134137142996e00,
        3.754408661907416e00,
    ]
    plow = 0.02425
    phigh = 1.0 - plow
    if p < plow:
        q = sqrt(-2.0 * __import__("math").log(p))
        return (
            (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5])
            / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1.0)
        )
    if phigh < p:
        q = sqrt(-2.0 * __import__("math").log(1.0 - p))
        return -(
            (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5])
            / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1.0)
        )
    q = p - 0.5
    r = q * q
    return (
        (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q
        / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1.0)
    )


def beta_lower_credible_bound(alpha: float, beta: float, *, quantile: float = 0.05) -> float:
    if alpha <= 0.0 or beta <= 0.0:
        raise ValueError("alpha and beta must be positive")
    if not 0.0 < quantile < 1.0:
        raise ValueError("quantile must lie in (0, 1)")
    mean = alpha / (alpha + beta)
    var = (alpha * beta) / (((alpha + beta) ** 2) * (alpha + beta + 1.0))
    z = _normal_cdf_inv(quantile)
    return max(0.0, min(1.0, mean + (z * sqrt(max(var, 0.0)))))


def freshness_score(*, observation_age_seconds: int | None, halflife_seconds: int | None) -> float | None:
    if observation_age_seconds is None or halflife_seconds is None:
        return None
    if observation_age_seconds < 0:
        raise ValueError("observation_age_seconds must be non-negative")
    if halflife_seconds <= 0:
        raise ValueError("halflife_seconds must be positive")
    return float(exp((-observation_age_seconds * log(2.0)) / float(halflife_seconds)))


@dataclass(frozen=True)
class KRRSourceSnapshot:
    snapshot_id: str
    source_id: str
    source_class: str
    source_uri: str
    fetched_at: str
    observed_at: str
    media_type: str
    content_sha256: str
    content_bytes: int
    trust_ceiling: str
    parser_id: str
    parser_version: str
    license: str | None = None
    title: str | None = None
    transport_secure: bool = True
    http_status: int | None = None
    text_sha256: str | None = None
    notes: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "snapshot_id", _require_safe_token(self.snapshot_id, name="snapshot_id"))
        object.__setattr__(self, "source_id", _require_safe_token(self.source_id, name="source_id"))
        source_class = _require_safe_token(self.source_class, name="source_class")
        if source_class not in _SOURCE_CLASSES:
            raise ValueError(f"source_class must be one of {sorted(_SOURCE_CLASSES)}")
        object.__setattr__(self, "source_class", source_class)
        source_uri = _require_text(self.source_uri, name="source_uri")
        parsed = urlparse(source_uri)
        if parsed.scheme and parsed.scheme not in {"https", "http", "file"}:
            raise ValueError("source_uri scheme must be https, http, or file")
        object.__setattr__(self, "source_uri", source_uri)
        object.__setattr__(self, "fetched_at", _require_isoish_timestamp(self.fetched_at, name="fetched_at"))
        object.__setattr__(self, "observed_at", _require_isoish_timestamp(self.observed_at, name="observed_at"))
        object.__setattr__(self, "media_type", _require_text(self.media_type, name="media_type"))
        object.__setattr__(self, "content_sha256", _require_sha256_hex(self.content_sha256, name="content_sha256"))
        if not isinstance(self.content_bytes, int) or isinstance(self.content_bytes, bool) or self.content_bytes < 0:
            raise ValueError("content_bytes must be a non-negative int")
        object.__setattr__(self, "trust_ceiling", _require_tier(self.trust_ceiling, name="trust_ceiling"))
        object.__setattr__(self, "parser_id", _require_safe_token(self.parser_id, name="parser_id"))
        object.__setattr__(self, "parser_version", _require_safe_token(self.parser_version, name="parser_version"))
        object.__setattr__(self, "license", None if self.license is None else _require_text(self.license, name="license"))
        object.__setattr__(self, "title", None if self.title is None else _require_text(self.title, name="title"))
        if self.http_status is not None:
            if not isinstance(self.http_status, int) or isinstance(self.http_status, bool) or self.http_status <= 0:
                raise ValueError("http_status must be a positive int")
        if self.text_sha256 is not None:
            object.__setattr__(self, "text_sha256", _require_sha256_hex(self.text_sha256, name="text_sha256"))
        if not isinstance(self.transport_secure, bool):
            raise TypeError("transport_secure must be a bool")
        normalized_notes = tuple(_require_text(note, name="notes") for note in self.notes)
        object.__setattr__(self, "notes", normalized_notes)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": KRR_SOURCE_SNAPSHOT_SCHEMA,
            "snapshot_id": self.snapshot_id,
            "source_id": self.source_id,
            "source_class": self.source_class,
            "source_uri": self.source_uri,
            "fetched_at": self.fetched_at,
            "observed_at": self.observed_at,
            "media_type": self.media_type,
            "content_sha256": self.content_sha256,
            "content_bytes": self.content_bytes,
            "trust_ceiling": self.trust_ceiling,
            "parser_id": self.parser_id,
            "parser_version": self.parser_version,
            "license": self.license,
            "title": self.title,
            "transport_secure": self.transport_secure,
            "http_status": self.http_status,
            "text_sha256": self.text_sha256,
            "notes": list(self.notes),
        }


@dataclass(frozen=True)
class KRREvidenceRecord:
    evidence_id: str
    snapshot_id: str
    locator: Mapping[str, Any]
    extracted_at: str
    excerpt_sha256: str
    excerpt_text: str | None = None
    valid_from: str | None = None
    valid_until: str | None = None
    claim_family: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "evidence_id", _require_safe_token(self.evidence_id, name="evidence_id"))
        object.__setattr__(self, "snapshot_id", _require_safe_token(self.snapshot_id, name="snapshot_id"))
        locator = _require_mapping(self.locator, name="locator")
        object.__setattr__(self, "locator", dict(locator))
        object.__setattr__(self, "extracted_at", _require_isoish_timestamp(self.extracted_at, name="extracted_at"))
        object.__setattr__(self, "excerpt_sha256", _require_sha256_hex(self.excerpt_sha256, name="excerpt_sha256"))
        if self.excerpt_text is not None:
            object.__setattr__(self, "excerpt_text", _require_text(self.excerpt_text, name="excerpt_text"))
            if _sha256_text(self.excerpt_text) != self.excerpt_sha256:
                raise ValueError("excerpt_text does not match excerpt_sha256")
        object.__setattr__(self, "valid_from", None if self.valid_from is None else _require_isoish_timestamp(self.valid_from, name="valid_from"))
        object.__setattr__(self, "valid_until", None if self.valid_until is None else _require_isoish_timestamp(self.valid_until, name="valid_until"))
        object.__setattr__(self, "claim_family", _require_optional_safe_token(self.claim_family, name="claim_family"))

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": KRR_EVIDENCE_RECORD_SCHEMA,
            "evidence_id": self.evidence_id,
            "snapshot_id": self.snapshot_id,
            "locator": dict(self.locator),
            "extracted_at": self.extracted_at,
            "excerpt_sha256": self.excerpt_sha256,
            "excerpt_text": self.excerpt_text,
            "valid_from": self.valid_from,
            "valid_until": self.valid_until,
            "claim_family": self.claim_family,
        }


@dataclass(frozen=True)
class KRRCanonicalClaim:
    claim_id: str
    entity_id: str
    fact_family: str
    attribute_key: str
    value: object
    evidence_ids: tuple[str, ...]
    source_ids: tuple[str, ...]
    valid_from: str | None = None
    valid_until: str | None = None
    unit: str | None = None
    currency: str | None = None
    jurisdiction: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "claim_id", _require_safe_token(self.claim_id, name="claim_id"))
        object.__setattr__(self, "entity_id", _require_safe_token(self.entity_id, name="entity_id"))
        object.__setattr__(self, "fact_family", _require_safe_token(self.fact_family, name="fact_family"))
        object.__setattr__(self, "attribute_key", _require_safe_token(self.attribute_key, name="attribute_key"))
        evidence_ids = _uniq_preserve([_require_safe_token(raw, name="evidence_ids") for raw in self.evidence_ids])
        if not evidence_ids:
            raise ValueError("evidence_ids must be non-empty")
        object.__setattr__(self, "evidence_ids", tuple(evidence_ids))
        source_ids = _uniq_preserve([_require_safe_token(raw, name="source_ids") for raw in self.source_ids])
        if not source_ids:
            raise ValueError("source_ids must be non-empty")
        object.__setattr__(self, "source_ids", tuple(source_ids))
        object.__setattr__(self, "valid_from", None if self.valid_from is None else _require_isoish_timestamp(self.valid_from, name="valid_from"))
        object.__setattr__(self, "valid_until", None if self.valid_until is None else _require_isoish_timestamp(self.valid_until, name="valid_until"))
        object.__setattr__(self, "unit", _require_optional_safe_token(self.unit, name="unit"))
        object.__setattr__(self, "currency", _require_optional_safe_token(self.currency, name="currency"))
        object.__setattr__(self, "jurisdiction", _require_optional_safe_token(self.jurisdiction, name="jurisdiction"))

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": KRR_CANONICAL_CLAIM_SCHEMA,
            "claim_id": self.claim_id,
            "entity_id": self.entity_id,
            "fact_family": self.fact_family,
            "attribute_key": self.attribute_key,
            "value": self.value,
            "evidence_ids": list(self.evidence_ids),
            "source_ids": list(self.source_ids),
            "valid_from": self.valid_from,
            "valid_until": self.valid_until,
            "unit": self.unit,
            "currency": self.currency,
            "jurisdiction": self.jurisdiction,
        }


@dataclass(frozen=True)
class KRRReviewRecord:
    review_id: str
    target_kind: str
    target_id: str
    decision: str
    reviewer: str
    reviewed_at: str
    rationale: str
    approved_for_runtime: bool = False
    provenance_ok: bool = True

    def __post_init__(self) -> None:
        object.__setattr__(self, "review_id", _require_safe_token(self.review_id, name="review_id"))
        target_kind = _require_safe_token(self.target_kind, name="target_kind")
        if target_kind not in _REVIEW_TARGET_KINDS:
            raise ValueError(f"target_kind must be one of {sorted(_REVIEW_TARGET_KINDS)}")
        object.__setattr__(self, "target_kind", target_kind)
        object.__setattr__(self, "target_id", _require_safe_token(self.target_id, name="target_id"))
        decision = _require_safe_token(self.decision, name="decision")
        if decision not in _REVIEW_DECISIONS:
            raise ValueError(f"decision must be one of {sorted(_REVIEW_DECISIONS)}")
        object.__setattr__(self, "decision", decision)
        object.__setattr__(self, "reviewer", _require_text(self.reviewer, name="reviewer"))
        object.__setattr__(self, "reviewed_at", _require_isoish_timestamp(self.reviewed_at, name="reviewed_at"))
        object.__setattr__(self, "rationale", _require_text(self.rationale, name="rationale"))
        if not isinstance(self.approved_for_runtime, bool):
            raise TypeError("approved_for_runtime must be a bool")
        if not isinstance(self.provenance_ok, bool):
            raise TypeError("provenance_ok must be a bool")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": KRR_REVIEW_RECORD_SCHEMA,
            "review_id": self.review_id,
            "target_kind": self.target_kind,
            "target_id": self.target_id,
            "decision": self.decision,
            "reviewer": self.reviewer,
            "reviewed_at": self.reviewed_at,
            "rationale": self.rationale,
            "approved_for_runtime": self.approved_for_runtime,
            "provenance_ok": self.provenance_ok,
        }


@dataclass(frozen=True)
class KRRSourceQuality:
    source_id: str
    sample_size: int
    submit_count: int
    reject_count: int
    skip_count: int
    posterior_alpha: float
    posterior_beta: float
    posterior_mean: float
    posterior_lower_95: float

    def __post_init__(self) -> None:
        object.__setattr__(self, "source_id", _require_safe_token(self.source_id, name="source_id"))
        for field_name in ("sample_size", "submit_count", "reject_count", "skip_count"):
            value = getattr(self, field_name)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError(f"{field_name} must be a non-negative int")
        for field_name in ("posterior_alpha", "posterior_beta", "posterior_mean", "posterior_lower_95"):
            value = getattr(self, field_name)
            if not isinstance(value, (int, float)):
                raise TypeError(f"{field_name} must be numeric")
        if not 0.0 <= float(self.posterior_mean) <= 1.0:
            raise ValueError("posterior_mean must lie in [0, 1]")
        if not 0.0 <= float(self.posterior_lower_95) <= 1.0:
            raise ValueError("posterior_lower_95 must lie in [0, 1]")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": KRR_SOURCE_QUALITY_SCHEMA,
            "source_id": self.source_id,
            "sample_size": self.sample_size,
            "submit_count": self.submit_count,
            "reject_count": self.reject_count,
            "skip_count": self.skip_count,
            "posterior_alpha": round(float(self.posterior_alpha), 6),
            "posterior_beta": round(float(self.posterior_beta), 6),
            "posterior_mean": round(float(self.posterior_mean), 6),
            "posterior_lower_95": round(float(self.posterior_lower_95), 6),
        }


def derive_source_quality(
    *,
    history: Mapping[str, Any] | None,
    review_records: tuple[KRRReviewRecord, ...] = (),
) -> tuple[KRRSourceQuality, ...]:
    root = {}
    if isinstance(history, Mapping):
        candidate = history.get("history_source_stats", history)
        if isinstance(candidate, Mapping):
            root = dict(candidate)
    review_bias: dict[str, tuple[int, int]] = {}
    for review in review_records:
        if review.target_kind != "source":
            continue
        approve, reject = review_bias.get(review.target_id, (0, 0))
        if review.decision == "approve" and review.provenance_ok:
            approve += 1
        elif review.decision == "reject" or not review.provenance_ok:
            reject += 1
        review_bias[review.target_id] = (approve, reject)
    rows: list[KRRSourceQuality] = []
    for raw_source_id, raw_stats in sorted(root.items(), key=lambda item: str(item[0])):
        source_id = _require_safe_token(raw_source_id, name="source_id")
        if not isinstance(raw_stats, Mapping):
            continue
        submit = int(raw_stats.get("submit", 0) or 0)
        reject = int(raw_stats.get("reject", 0) or 0)
        skip = int(raw_stats.get("skip", 0) or 0)
        sample_size = max(0, submit) + max(0, reject)
        review_approve, review_reject = review_bias.get(source_id, (0, 0))
        alpha = 1.0 + max(0, submit) + review_approve
        beta = 1.0 + max(0, reject) + review_reject
        mean = alpha / (alpha + beta)
        lower = beta_lower_credible_bound(alpha, beta, quantile=0.05)
        rows.append(
            KRRSourceQuality(
                source_id=source_id,
                sample_size=sample_size,
                submit_count=max(0, submit),
                reject_count=max(0, reject),
                skip_count=max(0, skip),
                posterior_alpha=alpha,
                posterior_beta=beta,
                posterior_mean=mean,
                posterior_lower_95=lower,
            )
        )
    return tuple(rows)


@dataclass(frozen=True)
class AutoTraderKRRBundle:
    bundle_name: str
    built_at: str
    compiler_version: str
    policy_version: str
    runtime_krr_kb: Mapping[str, Any] | None = None
    runtime_external_signals: Mapping[str, Any] | None = None
    runtime_signal_source_registry: Mapping[str, Any] | None = None
    runtime_history: Mapping[str, Any] | None = None
    source_snapshots: tuple[KRRSourceSnapshot, ...] = ()
    evidence_records: tuple[KRREvidenceRecord, ...] = ()
    canonical_claims: tuple[KRRCanonicalClaim, ...] = ()
    review_records: tuple[KRRReviewRecord, ...] = ()
    parent_bundle_hash: str | None = None
    signature: str | None = None
    signer_pubkey: str | None = None
    derived_source_quality: tuple[KRRSourceQuality, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "bundle_name", _require_safe_token(self.bundle_name, name="bundle_name"))
        object.__setattr__(self, "built_at", _require_isoish_timestamp(self.built_at, name="built_at"))
        object.__setattr__(self, "compiler_version", _require_safe_token(self.compiler_version, name="compiler_version"))
        object.__setattr__(self, "policy_version", _require_safe_token(self.policy_version, name="policy_version"))
        if self.parent_bundle_hash is not None:
            object.__setattr__(self, "parent_bundle_hash", _require_sha256_hex(self.parent_bundle_hash, name="parent_bundle_hash"))
        if self.signature is not None:
            object.__setattr__(self, "signature", _require_text(self.signature, name="signature"))
        if self.signer_pubkey is not None:
            object.__setattr__(self, "signer_pubkey", _require_text(self.signer_pubkey, name="signer_pubkey"))

        snapshot_ids: set[str] = set()
        source_ids: set[str] = set()
        normalized_snapshots: list[KRRSourceSnapshot] = []
        for row in self.source_snapshots:
            if not isinstance(row, KRRSourceSnapshot):
                raise TypeError("source_snapshots must contain KRRSourceSnapshot rows")
            if row.snapshot_id in snapshot_ids:
                raise ValueError(f"duplicate source snapshot: {row.snapshot_id}")
            snapshot_ids.add(row.snapshot_id)
            source_ids.add(row.source_id)
            normalized_snapshots.append(row)
        object.__setattr__(self, "source_snapshots", tuple(normalized_snapshots))

        evidence_ids: set[str] = set()
        normalized_evidence: list[KRREvidenceRecord] = []
        for row in self.evidence_records:
            if not isinstance(row, KRREvidenceRecord):
                raise TypeError("evidence_records must contain KRREvidenceRecord rows")
            if row.evidence_id in evidence_ids:
                raise ValueError(f"duplicate evidence record: {row.evidence_id}")
            if row.snapshot_id not in snapshot_ids:
                raise ValueError(f"evidence record {row.evidence_id} references unknown snapshot {row.snapshot_id}")
            evidence_ids.add(row.evidence_id)
            normalized_evidence.append(row)
        object.__setattr__(self, "evidence_records", tuple(normalized_evidence))

        claim_ids: set[str] = set()
        normalized_claims: list[KRRCanonicalClaim] = []
        for row in self.canonical_claims:
            if not isinstance(row, KRRCanonicalClaim):
                raise TypeError("canonical_claims must contain KRRCanonicalClaim rows")
            if row.claim_id in claim_ids:
                raise ValueError(f"duplicate canonical claim: {row.claim_id}")
            for evidence_id in row.evidence_ids:
                if evidence_id not in evidence_ids:
                    raise ValueError(f"claim {row.claim_id} references unknown evidence {evidence_id}")
            for source_id in row.source_ids:
                if source_id not in source_ids:
                    raise ValueError(f"claim {row.claim_id} references unknown source {source_id}")
            claim_ids.add(row.claim_id)
            normalized_claims.append(row)
        object.__setattr__(self, "canonical_claims", tuple(normalized_claims))

        review_ids: set[str] = set()
        normalized_reviews: list[KRRReviewRecord] = []
        for row in self.review_records:
            if not isinstance(row, KRRReviewRecord):
                raise TypeError("review_records must contain KRRReviewRecord rows")
            if row.review_id in review_ids:
                raise ValueError(f"duplicate review record: {row.review_id}")
            if row.target_kind == "claim" and row.target_id not in claim_ids:
                raise ValueError(f"review record {row.review_id} references unknown claim {row.target_id}")
            if row.target_kind == "source" and row.target_id not in source_ids:
                raise ValueError(f"review record {row.review_id} references unknown source {row.target_id}")
            if row.target_kind == "evidence" and row.target_id not in evidence_ids:
                raise ValueError(f"review record {row.review_id} references unknown evidence {row.target_id}")
            if row.target_kind == "bundle" and row.target_id != self.bundle_name:
                raise ValueError("bundle review target_id must equal bundle_name")
            review_ids.add(row.review_id)
            normalized_reviews.append(row)
        object.__setattr__(self, "review_records", tuple(normalized_reviews))

        normalized_quality: list[KRRSourceQuality] = []
        seen_quality: set[str] = set()
        for row in self.derived_source_quality:
            if not isinstance(row, KRRSourceQuality):
                raise TypeError("derived_source_quality must contain KRRSourceQuality rows")
            if row.source_id in seen_quality:
                raise ValueError(f"duplicate source quality row: {row.source_id}")
            seen_quality.add(row.source_id)
            normalized_quality.append(row)
        object.__setattr__(self, "derived_source_quality", tuple(normalized_quality))

        if self.runtime_krr_kb is not None:
            runtime_krr_kb = _require_mapping(self.runtime_krr_kb, name="runtime_krr_kb")
            object.__setattr__(self, "runtime_krr_kb", dict(runtime_krr_kb))
        if self.runtime_external_signals is not None:
            normalized_signals = _normalize_external_signals_payload(self.runtime_external_signals)
            object.__setattr__(self, "runtime_external_signals", normalized_signals)
        if self.runtime_signal_source_registry is not None:
            runtime_signal_source_registry = _require_mapping(
                self.runtime_signal_source_registry,
                name="runtime_signal_source_registry",
            )
            object.__setattr__(self, "runtime_signal_source_registry", dict(runtime_signal_source_registry))
        if self.runtime_history is not None:
            object.__setattr__(self, "runtime_history", _normalize_runtime_history(self.runtime_history))

    def to_unsigned_dict(self) -> dict[str, Any]:
        payload = {
            "schema": AUTOTRADER_KRR_BUNDLE_SCHEMA,
            "bundle_name": self.bundle_name,
            "built_at": self.built_at,
            "compiler_version": self.compiler_version,
            "policy_version": self.policy_version,
            "runtime_krr_kb": None if self.runtime_krr_kb is None else dict(self.runtime_krr_kb),
            "runtime_external_signals": (
                None if self.runtime_external_signals is None else dict(self.runtime_external_signals)
            ),
            "runtime_signal_source_registry": (
                None
                if self.runtime_signal_source_registry is None
                else dict(self.runtime_signal_source_registry)
            ),
            "runtime_history": None if self.runtime_history is None else dict(self.runtime_history),
            "source_snapshots": [row.to_dict() for row in self.source_snapshots],
            "evidence_records": [row.to_dict() for row in self.evidence_records],
            "canonical_claims": [row.to_dict() for row in self.canonical_claims],
            "review_records": [row.to_dict() for row in self.review_records],
            "parent_bundle_hash": self.parent_bundle_hash,
            "derived_source_quality": [row.to_dict() for row in self.derived_source_quality],
        }
        normalized = _canonicalize_bundle_value(payload)
        if not isinstance(normalized, dict):
            raise TypeError("bundle payload must canonicalize to an object")
        return normalized

    def bundle_hash_hex(self) -> str:
        return _canonical_json_sha256(self.to_unsigned_dict())

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["bundle_hash"] = self.bundle_hash_hex()
        payload["signature"] = self.signature
        payload["signer_pubkey"] = self.signer_pubkey
        return payload

    def runtime_approved(self) -> bool:
        return any(
            row.target_kind == "bundle"
            and row.target_id == self.bundle_name
            and row.decision == "approve"
            and row.approved_for_runtime
            and row.provenance_ok
            for row in self.review_records
        )


def build_autotrader_krr_bundle(
    *,
    bundle_name: str,
    built_at: str,
    compiler_version: str,
    policy_version: str,
    runtime_krr_kb: Mapping[str, Any] | None = None,
    runtime_external_signals: object | None = None,
    runtime_signal_source_registry: Mapping[str, Any] | None = None,
    runtime_history: Mapping[str, Any] | None = None,
    source_snapshots: tuple[KRRSourceSnapshot, ...] = (),
    evidence_records: tuple[KRREvidenceRecord, ...] = (),
    canonical_claims: tuple[KRRCanonicalClaim, ...] = (),
    review_records: tuple[KRRReviewRecord, ...] = (),
    parent_bundle_hash: str | None = None,
) -> AutoTraderKRRBundle:
    bundle = AutoTraderKRRBundle(
        bundle_name=bundle_name,
        built_at=built_at,
        compiler_version=compiler_version,
        policy_version=policy_version,
        runtime_krr_kb=runtime_krr_kb,
        runtime_external_signals=_normalize_external_signals_payload(runtime_external_signals),
        runtime_signal_source_registry=runtime_signal_source_registry,
        runtime_history=runtime_history,
        source_snapshots=source_snapshots,
        evidence_records=evidence_records,
        canonical_claims=canonical_claims,
        review_records=review_records,
        parent_bundle_hash=parent_bundle_hash,
        derived_source_quality=derive_source_quality(
            history=runtime_history,
            review_records=review_records,
        ),
    )
    _enforce_bundle_review_gate(bundle)
    _enforce_runtime_signal_gate(bundle)
    return bundle


def sign_autotrader_krr_bundle(
    bundle: AutoTraderKRRBundle,
    *,
    privkey: str | int | bytes | bytearray,
) -> AutoTraderKRRBundle:
    if not isinstance(bundle, AutoTraderKRRBundle):
        raise TypeError("bundle must be an AutoTraderKRRBundle")
    _require_bls()
    sk = _parse_privkey_to_int(privkey)
    message = canonical_json_bytes(bundle.to_unsigned_dict())
    signature_bytes = G2Basic.Sign(sk, message)
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(sk)
    return AutoTraderKRRBundle(
        bundle_name=bundle.bundle_name,
        built_at=bundle.built_at,
        compiler_version=bundle.compiler_version,
        policy_version=bundle.policy_version,
        runtime_krr_kb=bundle.runtime_krr_kb,
        runtime_external_signals=bundle.runtime_external_signals,
        runtime_signal_source_registry=bundle.runtime_signal_source_registry,
        runtime_history=bundle.runtime_history,
        source_snapshots=bundle.source_snapshots,
        evidence_records=bundle.evidence_records,
        canonical_claims=bundle.canonical_claims,
        review_records=bundle.review_records,
        parent_bundle_hash=bundle.parent_bundle_hash,
        signature="0x" + signature_bytes.hex(),
        signer_pubkey=signer_pubkey,
        derived_source_quality=bundle.derived_source_quality,
    )


def verify_autotrader_krr_bundle_signature(bundle: AutoTraderKRRBundle) -> bool:
    if bundle.signature is None or bundle.signer_pubkey is None:
        return False
    _require_bls()
    if not bundle.signer_pubkey.startswith("0x"):
        return False
    try:
        pk = bytes.fromhex(bundle.signer_pubkey[2:])
        sig = bytes.fromhex(bundle.signature[2:] if bundle.signature.startswith("0x") else bundle.signature)
    except ValueError:
        return False
    message = canonical_json_bytes(bundle.to_unsigned_dict())
    return bool(G2Basic.Verify(pk, message, sig))


def bundle_runtime_artifacts(
    bundle: AutoTraderKRRBundle,
) -> tuple[Mapping[str, Any] | None, tuple[ExternalSignalObservation, ...], ExternalSignalSourceRegistry | None, Mapping[str, Any] | None]:
    if not isinstance(bundle, AutoTraderKRRBundle):
        raise TypeError("bundle must be an AutoTraderKRRBundle")
    external_signals = ()
    if bundle.runtime_external_signals is not None:
        external_signals = tuple(external_signal_observations_from_object(bundle.runtime_external_signals))
    signal_source_registry = None
    if bundle.runtime_signal_source_registry is not None:
        signal_source_registry = external_signal_source_registry_from_object(bundle.runtime_signal_source_registry)
    if external_signals and signal_source_registry is None:
        raise ValueError("runtime external signals require a runtime signal source registry")
    if signal_source_registry is not None:
        for signal in external_signals:
            result = signal_source_registry.validate(signal)
            if not result.ok:
                raise ValueError(f"signal source registry rejected {signal.signal_id}: {result.error}")
    return bundle.runtime_krr_kb, external_signals, signal_source_registry, bundle.runtime_history


def load_autotrader_krr_bundle_file(
    path: str | Path,
    *,
    require_signature: bool = True,
    require_review: bool = True,
) -> AutoTraderKRRBundle:
    obj = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("bundle file must be a JSON object")
    bundle = autotrader_krr_bundle_from_dict(obj)
    expected_bundle_hash = obj.get("bundle_hash")
    if expected_bundle_hash is not None:
        expected_bundle_hash = _require_sha256_hex(expected_bundle_hash, name="bundle_hash")
        if expected_bundle_hash != bundle.bundle_hash_hex():
            raise ValueError("bundle hash mismatch")
    if require_review:
        _enforce_bundle_review_gate(bundle)
    if require_signature and not verify_autotrader_krr_bundle_signature(bundle):
        raise ValueError("bundle signature verification failed")
    _enforce_runtime_signal_gate(bundle)
    return bundle


def _enforce_bundle_review_gate(bundle: AutoTraderKRRBundle) -> None:
    if not bundle.runtime_approved():
        raise ValueError("bundle is missing an approved runtime review record")
    claim_reviews = {
        row.target_id
        for row in bundle.review_records
        if row.target_kind == "claim" and row.decision == "approve" and row.provenance_ok
    }
    missing_claim_reviews = [row.claim_id for row in bundle.canonical_claims if row.claim_id not in claim_reviews]
    if missing_claim_reviews:
        raise ValueError(
            "canonical claims require approve reviews: " + ",".join(sorted(missing_claim_reviews))
        )


def _enforce_runtime_signal_gate(bundle: AutoTraderKRRBundle) -> None:
    if bundle.runtime_external_signals is None:
        return
    _, external_signals, signal_source_registry, _ = bundle_runtime_artifacts(bundle)
    source_snapshot_ids = {row.source_id for row in bundle.source_snapshots}
    if external_signals and signal_source_registry is None:
        raise ValueError("runtime external signals require a signal source registry")
    quality_by_source = {row.source_id: row for row in bundle.derived_source_quality}
    for signal in external_signals:
        if signal.source_id not in source_snapshot_ids:
            raise ValueError(f"runtime signal source {signal.source_id} is missing a source snapshot")
        quality = quality_by_source.get(signal.source_id)
        if (
            signal.trust_tier in {SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED}
            and quality is not None
            and quality.posterior_lower_95 < 0.8
        ):
            raise ValueError(
                f"runtime trusted signal source {signal.source_id} has insufficient reliability"
            )


def krr_source_snapshot_from_dict(data: Mapping[str, Any]) -> KRRSourceSnapshot:
    schema = data.get("schema")
    if schema is not None and schema != KRR_SOURCE_SNAPSHOT_SCHEMA:
        raise ValueError("unsupported source snapshot schema")
    return KRRSourceSnapshot(
        snapshot_id=data.get("snapshot_id"),
        source_id=data.get("source_id"),
        source_class=data.get("source_class"),
        source_uri=data.get("source_uri"),
        fetched_at=data.get("fetched_at"),
        observed_at=data.get("observed_at"),
        media_type=data.get("media_type"),
        content_sha256=data.get("content_sha256"),
        content_bytes=data.get("content_bytes"),
        trust_ceiling=data.get("trust_ceiling"),
        parser_id=data.get("parser_id"),
        parser_version=data.get("parser_version"),
        license=data.get("license"),
        title=data.get("title"),
        transport_secure=data.get("transport_secure", True),
        http_status=data.get("http_status"),
        text_sha256=data.get("text_sha256"),
        notes=tuple(data.get("notes", ())),
    )


def krr_evidence_record_from_dict(data: Mapping[str, Any]) -> KRREvidenceRecord:
    schema = data.get("schema")
    if schema is not None and schema != KRR_EVIDENCE_RECORD_SCHEMA:
        raise ValueError("unsupported evidence record schema")
    return KRREvidenceRecord(
        evidence_id=data.get("evidence_id"),
        snapshot_id=data.get("snapshot_id"),
        locator=_require_mapping(data.get("locator"), name="locator"),
        extracted_at=data.get("extracted_at"),
        excerpt_sha256=data.get("excerpt_sha256"),
        excerpt_text=data.get("excerpt_text"),
        valid_from=data.get("valid_from"),
        valid_until=data.get("valid_until"),
        claim_family=data.get("claim_family"),
    )


def krr_canonical_claim_from_dict(data: Mapping[str, Any]) -> KRRCanonicalClaim:
    schema = data.get("schema")
    if schema is not None and schema != KRR_CANONICAL_CLAIM_SCHEMA:
        raise ValueError("unsupported canonical claim schema")
    return KRRCanonicalClaim(
        claim_id=data.get("claim_id"),
        entity_id=data.get("entity_id"),
        fact_family=data.get("fact_family"),
        attribute_key=data.get("attribute_key"),
        value=data.get("value"),
        evidence_ids=tuple(data.get("evidence_ids", ())),
        source_ids=tuple(data.get("source_ids", ())),
        valid_from=data.get("valid_from"),
        valid_until=data.get("valid_until"),
        unit=data.get("unit"),
        currency=data.get("currency"),
        jurisdiction=data.get("jurisdiction"),
    )


def krr_review_record_from_dict(data: Mapping[str, Any]) -> KRRReviewRecord:
    schema = data.get("schema")
    if schema is not None and schema != KRR_REVIEW_RECORD_SCHEMA:
        raise ValueError("unsupported review record schema")
    return KRRReviewRecord(
        review_id=data.get("review_id"),
        target_kind=data.get("target_kind"),
        target_id=data.get("target_id"),
        decision=data.get("decision"),
        reviewer=data.get("reviewer"),
        reviewed_at=data.get("reviewed_at"),
        rationale=data.get("rationale"),
        approved_for_runtime=data.get("approved_for_runtime", False),
        provenance_ok=data.get("provenance_ok", True),
    )


def krr_source_quality_from_dict(data: Mapping[str, Any]) -> KRRSourceQuality:
    schema = data.get("schema")
    if schema is not None and schema != KRR_SOURCE_QUALITY_SCHEMA:
        raise ValueError("unsupported source quality schema")
    return KRRSourceQuality(
        source_id=data.get("source_id"),
        sample_size=int(data.get("sample_size", 0)),
        submit_count=int(data.get("submit_count", 0)),
        reject_count=int(data.get("reject_count", 0)),
        skip_count=int(data.get("skip_count", 0)),
        posterior_alpha=float(data.get("posterior_alpha", 0.0)),
        posterior_beta=float(data.get("posterior_beta", 0.0)),
        posterior_mean=float(data.get("posterior_mean", 0.0)),
        posterior_lower_95=float(data.get("posterior_lower_95", 0.0)),
    )


def autotrader_krr_bundle_from_dict(data: Mapping[str, Any]) -> AutoTraderKRRBundle:
    schema = data.get("schema")
    if schema is not None and schema != AUTOTRADER_KRR_BUNDLE_SCHEMA:
        raise ValueError("unsupported KRR bundle schema")
    runtime_external_signals = data.get("runtime_external_signals")
    if runtime_external_signals is not None:
        runtime_external_signals = _require_mapping(runtime_external_signals, name="runtime_external_signals")
    runtime_signal_source_registry = data.get("runtime_signal_source_registry")
    if runtime_signal_source_registry is not None:
        runtime_signal_source_registry = _require_mapping(
            runtime_signal_source_registry,
            name="runtime_signal_source_registry",
        )
    runtime_krr_kb = data.get("runtime_krr_kb")
    if runtime_krr_kb is not None:
        runtime_krr_kb = _require_mapping(runtime_krr_kb, name="runtime_krr_kb")
    runtime_history = data.get("runtime_history")
    if runtime_history is not None:
        runtime_history = _require_mapping(runtime_history, name="runtime_history")
    return AutoTraderKRRBundle(
        bundle_name=data.get("bundle_name"),
        built_at=data.get("built_at"),
        compiler_version=data.get("compiler_version"),
        policy_version=data.get("policy_version"),
        runtime_krr_kb=runtime_krr_kb,
        runtime_external_signals=runtime_external_signals,
        runtime_signal_source_registry=runtime_signal_source_registry,
        runtime_history=runtime_history,
        source_snapshots=tuple(
            krr_source_snapshot_from_dict(_require_mapping(row, name="source_snapshot"))
            for row in data.get("source_snapshots", ())
        ),
        evidence_records=tuple(
            krr_evidence_record_from_dict(_require_mapping(row, name="evidence_record"))
            for row in data.get("evidence_records", ())
        ),
        canonical_claims=tuple(
            krr_canonical_claim_from_dict(_require_mapping(row, name="canonical_claim"))
            for row in data.get("canonical_claims", ())
        ),
        review_records=tuple(
            krr_review_record_from_dict(_require_mapping(row, name="review_record"))
            for row in data.get("review_records", ())
        ),
        parent_bundle_hash=data.get("parent_bundle_hash"),
        signature=data.get("signature"),
        signer_pubkey=data.get("signer_pubkey"),
        derived_source_quality=tuple(
            krr_source_quality_from_dict(_require_mapping(row, name="source_quality"))
            for row in data.get("derived_source_quality", ())
        ),
    )


__all__ = [
    "AUTOTRADER_EXTERNAL_SIGNAL_SET_SCHEMA",
    "AUTOTRADER_KRR_BUNDLE_SCHEMA",
    "AutoTraderKRRBundle",
    "KRR_CANONICAL_CLAIM_SCHEMA",
    "KRR_EVIDENCE_RECORD_SCHEMA",
    "KRR_REVIEW_RECORD_SCHEMA",
    "KRR_SOURCE_QUALITY_SCHEMA",
    "KRR_SOURCE_SNAPSHOT_SCHEMA",
    "KRRCanonicalClaim",
    "KRREvidenceRecord",
    "KRRReviewRecord",
    "KRRSourceQuality",
    "KRRSourceSnapshot",
    "autotrader_krr_bundle_from_dict",
    "beta_lower_credible_bound",
    "build_autotrader_krr_bundle",
    "bundle_runtime_artifacts",
    "derive_source_quality",
    "freshness_score",
    "krr_canonical_claim_from_dict",
    "krr_evidence_record_from_dict",
    "krr_review_record_from_dict",
    "krr_source_quality_from_dict",
    "krr_source_snapshot_from_dict",
    "load_autotrader_krr_bundle_file",
    "sign_autotrader_krr_bundle",
    "verify_autotrader_krr_bundle_signature",
]
