"""Public/operator status surface for confidential features.

This module is intentionally operational rather than cryptographic.
It exposes the deploy-time feature posture so the API/UI can report whether
confidential execution is enabled, what stage it is in, and how strict the
attestation window is.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from ..core.confidential_extension_receipts import is_canonical_confidential_measurement
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


_ALLOWED_STAGES = {"disabled", "experimental", "beta", "ga"}
_MEASUREMENT_SET_HASH_DOMAIN_V1 = "zenodex.confidential_approved_measurements/v1"
_STATUS_HASH_DOMAIN_V1 = "zenodex.confidential_feature_status/v1"


def _env_bool(name: str, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None or not str(raw).strip():
        return bool(default)
    value = str(raw).strip().lower()
    if value in {"1", "true", "yes", "on"}:
        return True
    if value in {"0", "false", "no", "off"}:
        return False
    raise ValueError(
        f"{name} must be one of 1,true,yes,on,0,false,no,off; got {raw!r}"
    )


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not str(raw).strip():
        return int(default)
    try:
        value = int(str(raw).strip())
    except ValueError as exc:
        raise ValueError(
            f"{name} must be an integer in [{lo}, {hi}]; got {raw!r}"
        ) from exc
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]; got {value}")
    return int(value)


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return str(default)
    value = str(raw).strip()
    return value if value else str(default)


def _normalize_measurements(values: Iterable[str]) -> tuple[str, ...]:
    seen: set[str] = set()
    out: list[str] = []
    for raw in values:
        value = str(raw or "").strip()
        if not value or value in seen or not is_canonical_confidential_measurement(value):
            continue
        seen.add(value)
        out.append(value)
    return tuple(sorted(out))


def _measurements_from_file(path: str) -> tuple[str, ...]:
    file_path = Path(path)
    if not file_path.exists() or not file_path.is_file():
        return ()
    try:
        if file_path.stat().st_mode & 0o444 == 0:
            return ()
    except OSError:
        return ()
    try:
        text = file_path.read_text(encoding="utf-8").strip()
    except OSError:
        return ()
    if not text:
        return ()
    try:
        obj = json.loads(text)
    except Exception:
        obj = None
    if isinstance(obj, dict):
        raw = obj.get("approved_measurements")
        if isinstance(raw, list):
            return _normalize_measurements(str(x) for x in raw)
        return ()
    if isinstance(obj, list):
        return _normalize_measurements(str(x) for x in obj)
    return _normalize_measurements(part.strip() for line in text.splitlines() for part in line.split(","))


def _measurements_from_env() -> tuple[str, ...]:
    csv = _env_str("CONFIDENTIAL_APPROVED_MEASUREMENTS", "")
    items = [part.strip() for part in csv.split(",")] if csv else []
    from_file = _measurements_from_file(_env_str("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", ""))
    return _normalize_measurements([*items, *from_file])


def _providers(measurements: Iterable[str]) -> tuple[str, ...]:
    found: set[str] = set()
    for value in measurements:
        s = str(value)
        if s.startswith("nitro:"):
            found.add("nitro")
        elif s.startswith("azure-sevsnp:"):
            found.add("azure-sevsnp")
        else:
            found.add("custom")
    return tuple(sorted(found))


def _has_real_operator_contact(value: str) -> bool:
    text = str(value or "").strip()
    if not text:
        return False
    if text.endswith(".invalid"):
        return False
    return "@" in text or text.startswith("https://") or text.startswith("http://")


def _runtime_enforcement_readiness_gaps() -> tuple[str, ...]:
    return (
        "cryptographic attestation verification remains external-only",
        "confidential runtime privacy remains external to the live API path",
        "sealed-bid asset settlement remains external to the local/testnet API path",
    )


def _confidentiality_non_claims() -> tuple[str, ...]:
    return (
        "no in-repo proof of TEE hardware confidentiality",
        "no fully encrypted on-chain state",
        "no production FHE confidentiality claim",
    )


def _approved_measurements_hash(measurements: tuple[str, ...]) -> str:
    payload = {"approved_measurements": list(measurements)}
    return sha256_hex(
        domain_sep_bytes(_MEASUREMENT_SET_HASH_DOMAIN_V1) + canonical_json_bytes(payload)
    )


def _feature_status_hash(body: dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(_STATUS_HASH_DOMAIN_V1) + canonical_json_bytes(body))


@dataclass(frozen=True)
class ConfidentialFeatureStatus:
    stage: str
    tee_enabled: bool
    sealed_bid_enabled: bool
    sealed_bid_default: bool
    fhe_alpha_enabled: bool
    attestation_epoch_length_s: int
    max_attestation_age_epochs: int
    operator_contact: str
    approved_measurements: tuple[str, ...]

    def to_public_dict(self) -> dict[str, Any]:
        measurement_count = len(self.approved_measurements)
        approved_measurements_hash = _approved_measurements_hash(self.approved_measurements)
        readiness_gaps = [
            *(
                []
                if measurement_count > 0
                else ["approved measurement allowlist is empty"]
            ),
            *(
                []
                if _has_real_operator_contact(self.operator_contact)
                else ["operator contact is missing or placeholder"]
            ),
            *(
                []
                if self.tee_enabled
                else ["tee execution is disabled"]
            ),
            *(
                []
                if self.sealed_bid_enabled
                else ["sealed-bid flow is disabled"]
            ),
            *(
                []
                if self.stage in {"beta", "ga"}
                else [f"feature stage is {self.stage}, not beta/ga"]
            ),
            *(
                []
                if not self.fhe_alpha_enabled
                else ["fhe alpha must stay disabled for beta posture"]
            ),
            *_runtime_enforcement_readiness_gaps(),
        ]
        beta_ready = not readiness_gaps
        default_enabled = bool(beta_ready and self.sealed_bid_default)
        body = {
            "stage": str(self.stage),
            "tee_enabled": bool(self.tee_enabled),
            "sealed_bid_enabled": bool(self.sealed_bid_enabled),
            "sealed_bid_default": bool(self.sealed_bid_default),
            "fhe_alpha_enabled": bool(self.fhe_alpha_enabled),
            "default_enabled": bool(default_enabled),
            "beta_ready": bool(beta_ready),
            "attestation_epoch_length_s": int(self.attestation_epoch_length_s),
            "max_attestation_age_epochs": int(self.max_attestation_age_epochs),
            "approved_measurements_count": int(measurement_count),
            "approved_measurements_hash": approved_measurements_hash,
            "providers": list(_providers(self.approved_measurements)),
            "operator_contact": str(self.operator_contact),
            "user_summary": (
                "Private execution assistance for large trades and hidden-bid batch auctions, "
                "with TEE receipts and anti-griefing bond rules."
            ),
            "claim_scope": (
                "attested receipt admission, bounded runtime receipts, replay protection, "
                "response redaction, and local accounting/conservation checks"
            ),
            "non_claims": list(_confidentiality_non_claims()),
            "use_cases": [
                "large trades that would leak too much intent on the public path",
                "batch auctions or token sales where bids should stay hidden until reveal",
                "private RFQ and strategy-provider flows with auditable metering",
            ],
            "alpha_surfaces": [
                {
                    "id": "fhe_sealed_bid_alpha",
                    "enabled": bool(self.fhe_alpha_enabled),
                    "status": "alpha",
                    "max_bids": 8,
                    "max_units": 63,
                    "hcu_cap": 20_000_000,
                    "depth_hcu_cap": 5_000_000,
                    "note": "experimental FHE lane for sealed bids only; keep disabled by default",
                }
            ],
            "not_default_for": [
                "ordinary retail swaps",
                "always-on low-latency flows",
                "fully encrypted on-chain state use cases",
            ],
            "alerts": [
                "unapproved measurement seen",
                "stale attestation rate spike",
                "bond slash rate spike",
                "receipt accounting mismatch",
            ],
            "readiness_gaps": readiness_gaps,
            "docs": [
                "docs/CONFIDENTIAL_FEATURES_USE_CASES.md",
                "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
                "docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md",
                "docs/FHE_SEALED_BID_ALPHA.md",
                "docs/SEALED_BID_DISASTER_STATE_CATALOG.md",
            ],
        }
        return {**body, "status_hash": _feature_status_hash(body)}


def load_confidential_feature_status_from_env() -> ConfidentialFeatureStatus:
    stage = _env_str("CONFIDENTIAL_FEATURE_STAGE", "beta").lower()
    if stage not in _ALLOWED_STAGES:
        stage = "experimental"
    return ConfidentialFeatureStatus(
        stage=stage,
        tee_enabled=_env_bool("CONFIDENTIAL_TEE_ENABLED", True),
        sealed_bid_enabled=_env_bool("CONFIDENTIAL_SEALED_BID_ENABLED", True),
        sealed_bid_default=_env_bool("CONFIDENTIAL_SEALED_BID_DEFAULT", False),
        fhe_alpha_enabled=_env_bool("CONFIDENTIAL_FHE_ALPHA_ENABLED", False),
        attestation_epoch_length_s=_env_int("CONFIDENTIAL_ATTESTATION_EPOCH_LENGTH_S", 60, lo=1, hi=86_400),
        max_attestation_age_epochs=_env_int("CONFIDENTIAL_MAX_ATTESTATION_AGE_EPOCHS", 2, lo=0, hi=255),
        operator_contact=_env_str("CONFIDENTIAL_OPERATOR_CONTACT", "ops@example.invalid"),
        approved_measurements=_measurements_from_env(),
    )
