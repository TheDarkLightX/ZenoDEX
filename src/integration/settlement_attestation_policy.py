from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex


SETTLEMENT_ATTESTATION_POLICY_SCHEMA = "zenodex/settlement-attestation-policy/v1"


@dataclass(frozen=True)
class SettlementAttestationPolicy:
    policy_id: str
    policy_epoch: int
    chain_id: int
    registry_contract: str
    registry_root: str
    effective_from_epoch: int
    expires_at_epoch: int
    governance_approved: bool
    timelock_elapsed: bool
    multisig_approved: bool
    min_distinct_signers: int
    min_distinct_sources: int
    allowed_signers: Mapping[str, Sequence[str]]
    bundle_price_consensus_method: str = "lower_median"
    max_bundle_price_spread_bps: int = 0
    schema: str = SETTLEMENT_ATTESTATION_POLICY_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_ATTESTATION_POLICY_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.policy_id, str) or not self.policy_id.strip():
            raise ValueError("policy_id must be a non-empty string")
        object.__setattr__(self, "policy_id", self.policy_id.strip())
        object.__setattr__(
            self,
            "registry_contract",
            canonical_hex_fixed_allow_0x(self.registry_contract, nbytes=20, name="registry_contract"),
        )
        object.__setattr__(
            self,
            "registry_root",
            canonical_hex_fixed_allow_0x(self.registry_root, nbytes=32, name="registry_root"),
        )
        for name in (
            "policy_epoch",
            "chain_id",
            "effective_from_epoch",
            "expires_at_epoch",
            "min_distinct_signers",
            "min_distinct_sources",
            "max_bundle_price_spread_bps",
        ):
            value = getattr(self, name)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError(f"{name} must be a non-negative int")
        if self.expires_at_epoch < self.effective_from_epoch:
            raise ValueError("expires_at_epoch must be >= effective_from_epoch")
        if self.min_distinct_signers < 1:
            raise ValueError("min_distinct_signers must be >= 1")
        if self.min_distinct_sources < 1:
            raise ValueError("min_distinct_sources must be >= 1")
        for name in ("governance_approved", "timelock_elapsed", "multisig_approved"):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")
        if self.bundle_price_consensus_method != "lower_median":
            raise ValueError("bundle_price_consensus_method must be 'lower_median'")
        normalized_allowlist = canonical_attestation_policy_allowlist(self.allowed_signers)
        if not normalized_allowlist:
            raise ValueError("allowed_signers must be non-empty")
        object.__setattr__(self, "allowed_signers", normalized_allowlist)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "policy_id": self.policy_id,
            "policy_epoch": int(self.policy_epoch),
            "chain_id": int(self.chain_id),
            "registry_contract": self.registry_contract,
            "registry_root": self.registry_root,
            "effective_from_epoch": int(self.effective_from_epoch),
            "expires_at_epoch": int(self.expires_at_epoch),
            "governance_approved": bool(self.governance_approved),
            "timelock_elapsed": bool(self.timelock_elapsed),
            "multisig_approved": bool(self.multisig_approved),
            "min_distinct_signers": int(self.min_distinct_signers),
            "min_distinct_sources": int(self.min_distinct_sources),
            "allowed_signers": {pubkey: list(source_ids) for pubkey, source_ids in self.allowed_signers.items()},
            "bundle_price_consensus_method": self.bundle_price_consensus_method,
            "max_bundle_price_spread_bps": int(self.max_bundle_price_spread_bps),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementAttestationPolicy":
        if not isinstance(payload, Mapping):
            raise ValueError("attestation_policy must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            policy_id=str(payload.get("policy_id", "")),
            policy_epoch=int(payload.get("policy_epoch", -1)),
            chain_id=int(payload.get("chain_id", -1)),
            registry_contract=str(payload.get("registry_contract", "")),
            registry_root=str(payload.get("registry_root", "")),
            effective_from_epoch=int(payload.get("effective_from_epoch", -1)),
            expires_at_epoch=int(payload.get("expires_at_epoch", -1)),
            governance_approved=_coerce_policy_bool_field(payload, "governance_approved"),
            timelock_elapsed=_coerce_policy_bool_field(payload, "timelock_elapsed"),
            multisig_approved=_coerce_policy_bool_field(payload, "multisig_approved"),
            min_distinct_signers=int(payload.get("min_distinct_signers", 0)),
            min_distinct_sources=int(payload.get("min_distinct_sources", 0)),
            allowed_signers=payload.get("allowed_signers", {}),
            bundle_price_consensus_method=str(payload.get("bundle_price_consensus_method", "lower_median")),
            max_bundle_price_spread_bps=int(payload.get("max_bundle_price_spread_bps", 0)),
        )

    def policy_hash_hex(self) -> str:
        return sha256_hex(
            domain_sep_bytes("settlement_attestation_policy", version=1) + canonical_json_bytes(self.to_dict())
        )


@dataclass(frozen=True)
class SettlementAttestationPolicyCheckResult:
    ok: bool
    policy_present: bool
    governance_approved: bool
    timelock_elapsed: bool
    multisig_approved: bool
    epoch_active: bool
    epoch_unexpired: bool
    allowlist_nonempty: bool
    signer_allowlisted: bool
    source_policy_ok: bool
    distinct_signers_ok: bool
    distinct_sources_ok: bool
    error: str | None = None
    error_code: str | None = None
    details: Mapping[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "ok": bool(self.ok),
            "policy_present": bool(self.policy_present),
            "governance_approved": bool(self.governance_approved),
            "timelock_elapsed": bool(self.timelock_elapsed),
            "multisig_approved": bool(self.multisig_approved),
            "epoch_active": bool(self.epoch_active),
            "epoch_unexpired": bool(self.epoch_unexpired),
            "allowlist_nonempty": bool(self.allowlist_nonempty),
            "signer_allowlisted": bool(self.signer_allowlisted),
            "source_policy_ok": bool(self.source_policy_ok),
            "distinct_signers_ok": bool(self.distinct_signers_ok),
            "distinct_sources_ok": bool(self.distinct_sources_ok),
            "error": self.error,
            "error_code": self.error_code,
            "details": None if self.details is None else dict(self.details),
        }

    def telemetry_payload(self) -> dict[str, Any]:
        return self.to_dict()


def canonical_attestation_policy_allowlist(
    allowed_signers: Mapping[str, Sequence[str]],
) -> dict[str, tuple[str, ...]]:
    if not isinstance(allowed_signers, Mapping):
        raise TypeError("allowed_signers must be a mapping")
    normalized: dict[str, tuple[str, ...]] = {}
    for raw_pubkey, raw_sources in allowed_signers.items():
        pubkey = canonical_hex_fixed_allow_0x(str(raw_pubkey), nbytes=48, name="allowed_signer_pubkey")
        if not isinstance(raw_sources, Sequence) or isinstance(raw_sources, (str, bytes, bytearray)):
            raise TypeError("allowed_signer source ids must be a sequence of strings")
        source_ids: list[str] = []
        for raw_source in raw_sources:
            if not isinstance(raw_source, str):
                raise TypeError("allowed_signer source ids must be strings")
            source_id = raw_source.strip()
            if not source_id:
                raise ValueError("allowed_signer source ids must be non-empty")
            source_ids.append(source_id)
        normalized[pubkey] = tuple(sorted(set(source_ids)))
    return dict(sorted(normalized.items()))


def check_settlement_attestation_policy(
    *,
    policy: SettlementAttestationPolicy | None,
    consumer_now_epoch: int,
    signer_pubkeys: Sequence[str],
    packet_source_ids: Sequence[str],
) -> SettlementAttestationPolicyCheckResult:
    if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
        raise ValueError("consumer_now_epoch must be a non-negative int")

    policy_present = policy is not None
    canonical_signers = tuple(
        canonical_hex_fixed_allow_0x(str(pubkey), nbytes=48, name="signer_pubkey") for pubkey in signer_pubkeys
    )
    canonical_sources: tuple[str, ...] = tuple(_canonical_source_id(source_id) for source_id in packet_source_ids)

    if not policy_present:
        error_code = "attestation_policy_missing"
        details = {
            "consumer_now_epoch": int(consumer_now_epoch),
            "observed_signer_pubkeys": canonical_signers,
            "observed_source_ids": canonical_sources,
            "observed_distinct_signers": len(set(canonical_signers)),
            "observed_distinct_sources": len(set(canonical_sources)),
        }
        return SettlementAttestationPolicyCheckResult(
            ok=False,
            policy_present=False,
            governance_approved=False,
            timelock_elapsed=False,
            multisig_approved=False,
            epoch_active=False,
            epoch_unexpired=False,
            allowlist_nonempty=False,
            signer_allowlisted=False,
            source_policy_ok=False,
            distinct_signers_ok=False,
            distinct_sources_ok=False,
            error=_format_policy_error(
                "settlement spot price attestation requires attestation_policy",
                details=details,
            ),
            error_code=error_code,
            details=details,
        )

    governance_approved = bool(policy.governance_approved)
    timelock_elapsed = bool(policy.timelock_elapsed)
    multisig_approved = bool(policy.multisig_approved)
    epoch_active = int(policy.effective_from_epoch) <= int(consumer_now_epoch)
    epoch_unexpired = int(consumer_now_epoch) <= int(policy.expires_at_epoch)
    allowlist_nonempty = bool(policy.allowed_signers)
    distinct_signers_ok = len(set(canonical_signers)) >= int(policy.min_distinct_signers)
    distinct_sources_ok = len(set(canonical_sources)) >= int(policy.min_distinct_sources)
    signer_allowlisted = bool(canonical_signers) and all(pubkey in policy.allowed_signers for pubkey in canonical_signers)

    source_policy_ok = signer_allowlisted
    violating_source: str | None = None
    allowlisted_sources_for_observed_signers: dict[str, tuple[str, ...]] = {}
    if signer_allowlisted:
        for pubkey in canonical_signers:
            allowlisted_sources_for_observed_signers[pubkey] = tuple(policy.allowed_signers[pubkey])
            allowed_sources = set(policy.allowed_signers[pubkey])
            for source_id in canonical_sources:
                if source_id not in allowed_sources:
                    source_policy_ok = False
                    violating_source = source_id
                    break
            if not source_policy_ok:
                break

    ok = (
        governance_approved
        and timelock_elapsed
        and multisig_approved
        and epoch_active
        and epoch_unexpired
        and allowlist_nonempty
        and distinct_signers_ok
        and distinct_sources_ok
        and signer_allowlisted
        and source_policy_ok
    )
    details = {
        "policy_id": policy.policy_id,
        "policy_epoch": int(policy.policy_epoch),
        "chain_id": int(policy.chain_id),
        "registry_contract": policy.registry_contract,
        "registry_root": policy.registry_root,
        "policy_hash": policy.policy_hash_hex(),
        "consumer_now_epoch": int(consumer_now_epoch),
        "effective_from_epoch": int(policy.effective_from_epoch),
        "expires_at_epoch": int(policy.expires_at_epoch),
        "observed_signer_pubkeys": canonical_signers,
        "observed_source_ids": canonical_sources,
        "observed_distinct_signers": len(set(canonical_signers)),
        "observed_distinct_sources": len(set(canonical_sources)),
        "required_distinct_signers": int(policy.min_distinct_signers),
        "required_distinct_sources": int(policy.min_distinct_sources),
        "bundle_price_consensus_method": policy.bundle_price_consensus_method,
        "max_bundle_price_spread_bps": int(policy.max_bundle_price_spread_bps),
        "allowlisted_sources_for_observed_signers": allowlisted_sources_for_observed_signers,
    }
    error_code, error = _resolve_policy_failure(
        governance_approved=governance_approved,
        timelock_elapsed=timelock_elapsed,
        multisig_approved=multisig_approved,
        epoch_active=epoch_active,
        epoch_unexpired=epoch_unexpired,
        allowlist_nonempty=allowlist_nonempty,
        distinct_signers_ok=distinct_signers_ok,
        distinct_sources_ok=distinct_sources_ok,
        signer_allowlisted=signer_allowlisted,
        source_policy_ok=source_policy_ok,
        violating_source=violating_source,
        details=details,
    )
    return SettlementAttestationPolicyCheckResult(
        ok=ok,
        policy_present=policy_present,
        governance_approved=governance_approved,
        timelock_elapsed=timelock_elapsed,
        multisig_approved=multisig_approved,
        epoch_active=epoch_active,
        epoch_unexpired=epoch_unexpired,
        allowlist_nonempty=allowlist_nonempty,
        signer_allowlisted=signer_allowlisted,
        source_policy_ok=source_policy_ok,
        distinct_signers_ok=distinct_signers_ok,
        distinct_sources_ok=distinct_sources_ok,
        error=error,
        error_code=error_code,
        details=details,
    )


def coerce_settlement_attestation_policy(
    policy: SettlementAttestationPolicy | Mapping[str, Any] | None,
) -> SettlementAttestationPolicy | None:
    if policy is None:
        return None
    if isinstance(policy, SettlementAttestationPolicy):
        return policy
    if isinstance(policy, Mapping):
        return SettlementAttestationPolicy.from_dict(policy)
    raise TypeError("attestation_policy must be a SettlementAttestationPolicy or object mapping")


def _coerce_policy_bool_field(payload: Mapping[str, Any], field_name: str) -> bool:
    value = payload.get(field_name, False)
    if not isinstance(value, bool):
        raise TypeError(f"{field_name} must be a bool")
    return value


def _canonical_source_id(source_id: object) -> str:
    if not isinstance(source_id, str):
        raise TypeError("packet source ids must be strings")
    out = source_id.strip()
    if not out:
        raise ValueError("packet source ids must be non-empty")
    return out


def _resolve_policy_failure(
    *,
    governance_approved: bool,
    timelock_elapsed: bool,
    multisig_approved: bool,
    epoch_active: bool,
    epoch_unexpired: bool,
    allowlist_nonempty: bool,
    distinct_signers_ok: bool,
    distinct_sources_ok: bool,
    signer_allowlisted: bool,
    source_policy_ok: bool,
    violating_source: str | None,
    details: Mapping[str, Any],
) -> tuple[str | None, str | None]:
    if not governance_approved:
        return (
            "attestation_policy_governance_missing",
            _format_policy_error("attestation policy governance approval missing", details=details),
        )
    if not timelock_elapsed:
        return (
            "attestation_policy_timelock_not_elapsed",
            _format_policy_error("attestation policy timelock not elapsed", details=details),
        )
    if not multisig_approved:
        return (
            "attestation_policy_multisig_missing",
            _format_policy_error("attestation policy multisig approval missing", details=details),
        )
    if not epoch_active:
        return (
            "attestation_policy_not_active",
            _format_policy_error("attestation policy is not active yet", details=details),
        )
    if not epoch_unexpired:
        return (
            "attestation_policy_expired",
            _format_policy_error("attestation policy expired", details=details),
        )
    if not allowlist_nonempty:
        return (
            "attestation_policy_allowlist_empty",
            _format_policy_error("attestation policy requires non-empty allowed_signers", details=details),
        )
    if not distinct_signers_ok:
        return (
            "attestation_policy_signer_quorum_not_met",
            _format_policy_error("attestation policy signer quorum not met", details=details),
        )
    if not distinct_sources_ok:
        return (
            "attestation_policy_source_quorum_not_met",
            _format_policy_error("attestation policy source quorum not met", details=details),
        )
    if not signer_allowlisted:
        return (
            "attestation_policy_signer_not_allowlisted",
            _format_policy_error("signer_pubkey not allowlisted by attestation policy", details=details),
        )
    if not source_policy_ok:
        if violating_source is None:
            return (
                "attestation_policy_sources_not_allowlisted",
                _format_policy_error("packet source ids not allowlisted by attestation policy", details=details),
            )
        detail_map = dict(details)
        detail_map["violating_source"] = violating_source
        return (
            "attestation_policy_source_not_allowlisted",
            _format_policy_error(
                f"source_id not allowlisted by attestation policy: {violating_source}",
                details=detail_map,
            ),
        )
    return None, None


def _format_policy_error(base_error: str, *, details: Mapping[str, Any]) -> str:
    rendered = ", ".join(
        f"{key}={_format_detail_value(value)}" for key, value in sorted(details.items()) if value is not None
    )
    if not rendered:
        return base_error
    return f"{base_error} [{rendered}]"


def _format_detail_value(value: Any) -> str:
    if isinstance(value, Mapping):
        return "{" + ", ".join(
            f"{_format_detail_value(k)}:{_format_detail_value(v)}" for k, v in sorted(value.items(), key=lambda item: str(item[0]))
        ) + "}"
    if isinstance(value, tuple):
        return "(" + ", ".join(_format_detail_value(item) for item in value) + ")"
    if isinstance(value, list):
        return "[" + ", ".join(_format_detail_value(item) for item in value) + "]"
    return str(value)


__all__ = [
    "SETTLEMENT_ATTESTATION_POLICY_SCHEMA",
    "SettlementAttestationPolicy",
    "SettlementAttestationPolicyCheckResult",
    "canonical_attestation_policy_allowlist",
    "check_settlement_attestation_policy",
    "coerce_settlement_attestation_policy",
]
