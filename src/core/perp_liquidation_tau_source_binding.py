"""Source-bound facts for the Tau perps liquidation oracle-sanity guard."""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

from src.core.perp_v2.math import (
    is_liquidatable,
    is_oracle_fresh,
    oracle_move_violated,
)
from src.state.canonical import canonical_json_bytes
from src.state.jmt import (
    decode_jmt_membership_proof,
    verify_jmt_membership,
)

try:
    from py_ecc.bls import G2Basic as _PyEccG2Basic
except ImportError:  # pragma: no cover - exercised in no-BLS environments
    _PyEccG2Basic = None

G2Basic: Any | None = _PyEccG2Basic

PARTIAL_LIQUIDATE_ACTION = "partial_liquidate"
JMT_SOURCE_STATE_ROOT_KIND = "typed_app_root_jmt_v1"
SOURCE_ROOT_AUTHORITY_SCHEMA = "zenodex.perp_liquidation_tau_source_root_authority.v1"
SOURCE_ROOT_AUTHORITY_BINDING_SCHEMA = "zenodex.perp_liquidation_tau_source_root_authority_binding.v1"
SOURCE_ADMISSION_ENVELOPE_SCHEMA = "zenodex.perp_liquidation_tau_source_admission_envelope.v1"

FLAG_NAMES = (
    "liquidation_requested",
    "account_under_maint",
    "oracle_seen",
    "oracle_fresh_ok",
    "mark_oracle_gap_ok",
    "breaker_inactive",
    "proof_ok",
    "binding_ok",
)

INPUT_BY_FLAG = {
    "liquidation_requested": "i1",
    "account_under_maint": "i2",
    "oracle_seen": "i3",
    "oracle_fresh_ok": "i4",
    "mark_oracle_gap_ok": "i5",
    "breaker_inactive": "i6",
    "proof_ok": "i7",
    "binding_ok": "i8",
}


def _require_bls() -> Any:
    if G2Basic is None:
        raise RuntimeError("py_ecc.bls is required for perp liquidation Tau source signatures")
    return G2Basic


@dataclass(frozen=True)
class PerpLiquidationTauSourceFacts:
    request_id: str
    market_id: str
    account_id: str
    action: str
    fraction_bps: int
    now_epoch: int
    position_base: int
    collateral_quote: int
    index_price_e8: int
    maintenance_margin_bps: int
    depeg_buffer_bps: int
    oracle_seen: bool
    oracle_last_update_epoch: int
    max_oracle_staleness_epochs: int
    clearing_price_e8: int
    max_oracle_move_bps: int
    breaker_active: bool
    proof_result_ok: bool
    proof_receipt_hash: str

    def __post_init__(self) -> None:
        _require_non_empty_str(self.request_id, name="request_id")
        _require_non_empty_str(self.market_id, name="market_id")
        _require_non_empty_str(self.account_id, name="account_id")
        _require_non_empty_str(self.action, name="action")
        _require_int(self.fraction_bps, name="fraction_bps")
        _require_int(self.now_epoch, name="now_epoch")
        _require_int(self.position_base, name="position_base")
        _require_int(self.collateral_quote, name="collateral_quote")
        _require_int(self.index_price_e8, name="index_price_e8")
        _require_int(self.maintenance_margin_bps, name="maintenance_margin_bps")
        _require_int(self.depeg_buffer_bps, name="depeg_buffer_bps")
        _require_bool(self.oracle_seen, name="oracle_seen")
        _require_int(self.oracle_last_update_epoch, name="oracle_last_update_epoch")
        _require_int(
            self.max_oracle_staleness_epochs,
            name="max_oracle_staleness_epochs",
        )
        _require_int(self.clearing_price_e8, name="clearing_price_e8")
        _require_int(self.max_oracle_move_bps, name="max_oracle_move_bps")
        _require_bool(self.breaker_active, name="breaker_active")
        _require_bool(self.proof_result_ok, name="proof_result_ok")
        _require_sha256_ref(self.proof_receipt_hash, name="proof_receipt_hash")


@dataclass(frozen=True)
class PerpLiquidationTauSourceMembershipProof:
    source_facts_hash: str
    source_membership_key_hash: str
    source_membership_value_hash: str
    jmt_membership_proof_payload_hex: str

    def __post_init__(self) -> None:
        _require_sha256_ref(self.source_facts_hash, name="source_facts_hash")
        _require_sha256_ref(
            self.source_membership_key_hash,
            name="source_membership_key_hash",
        )
        _require_sha256_ref(
            self.source_membership_value_hash,
            name="source_membership_value_hash",
        )
        _require_hex_bytes(
            self.jmt_membership_proof_payload_hex,
            name="jmt_membership_proof_payload_hex",
        )


@dataclass(frozen=True)
class PerpLiquidationTauSourceStateRootBinding:
    source_facts_hash: str
    source_state_root_hash: str
    state_root_kind: str
    request_id: str
    market_id: str
    account_id: str
    action: str
    fraction_bps: int
    source_membership_proof: PerpLiquidationTauSourceMembershipProof | None = None
    source_root_authority: "PerpLiquidationTauSourceRootAuthority | None" = None
    source_root_authority_binding: "PerpLiquidationTauSourceRootAuthorityBinding | None" = None

    def __post_init__(self) -> None:
        _require_sha256_ref(self.source_facts_hash, name="source_facts_hash")
        _require_sha256_ref(
            self.source_state_root_hash,
            name="source_state_root_hash",
        )
        _require_non_empty_str(self.state_root_kind, name="state_root_kind")
        _require_non_empty_str(self.request_id, name="request_id")
        _require_non_empty_str(self.market_id, name="market_id")
        _require_non_empty_str(self.account_id, name="account_id")
        _require_non_empty_str(self.action, name="action")
        _require_int(self.fraction_bps, name="fraction_bps")
        if (
            self.source_membership_proof is not None
            and not isinstance(
                self.source_membership_proof,
                PerpLiquidationTauSourceMembershipProof,
            )
        ):
            raise TypeError(
                "source_membership_proof must be PerpLiquidationTauSourceMembershipProof"
            )
        if (
            self.source_root_authority is not None
            and not isinstance(
                self.source_root_authority,
                PerpLiquidationTauSourceRootAuthority,
            )
        ):
            raise TypeError(
                "source_root_authority must be PerpLiquidationTauSourceRootAuthority"
            )
        if (
            self.source_root_authority_binding is not None
            and not isinstance(
                self.source_root_authority_binding,
                PerpLiquidationTauSourceRootAuthorityBinding,
            )
        ):
            raise TypeError(
                "source_root_authority_binding must be PerpLiquidationTauSourceRootAuthorityBinding"
            )


@dataclass(frozen=True)
class PerpLiquidationTauSourceRootAuthority:
    schema: str
    market_id: str
    action: str
    source_state_root_hash: str
    state_root_kind: str
    valid_from_epoch: int
    valid_until_epoch: int
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != SOURCE_ROOT_AUTHORITY_SCHEMA:
            raise ValueError("invalid source root authority schema")
        _require_non_empty_str(self.market_id, name="market_id")
        _require_non_empty_str(self.action, name="action")
        _require_sha256_ref(
            self.source_state_root_hash,
            name="source_state_root_hash",
        )
        _require_non_empty_str(self.state_root_kind, name="state_root_kind")
        _require_non_negative_int(self.valid_from_epoch, name="valid_from_epoch")
        _require_non_negative_int(self.valid_until_epoch, name="valid_until_epoch")
        if self.valid_from_epoch > self.valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_sha256_ref(self.canonical_sha256, name="canonical_sha256")
        if self.canonical_sha256 != perp_liquidation_tau_source_root_authority_hash(
            self
        ):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> Mapping[str, object]:
        return {
            "action": self.action,
            "market_id": self.market_id,
            "schema": self.schema,
            "source_state_root_hash": self.source_state_root_hash,
            "state_root_kind": self.state_root_kind,
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }


@dataclass(frozen=True)
class PerpLiquidationTauSourceRootAuthorityBinding:
    schema: str
    market_id: str
    action: str
    valid_from_epoch: int
    valid_until_epoch: int
    authority_hash: str
    authority_state_root_hash: str
    policy_hash: str
    signer_pubkey: str
    signature: str
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != SOURCE_ROOT_AUTHORITY_BINDING_SCHEMA:
            raise ValueError("invalid source root authority binding schema")
        _require_non_empty_str(self.market_id, name="market_id")
        _require_non_empty_str(self.action, name="action")
        _require_non_negative_int(self.valid_from_epoch, name="valid_from_epoch")
        _require_non_negative_int(self.valid_until_epoch, name="valid_until_epoch")
        if self.valid_from_epoch > self.valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_sha256_ref(self.authority_hash, name="authority_hash")
        _require_sha256_ref(
            self.authority_state_root_hash,
            name="authority_state_root_hash",
        )
        _require_sha256_ref(self.policy_hash, name="policy_hash")
        _require_prefixed_hex(self.signer_pubkey, name="signer_pubkey", nbytes=48)
        _require_prefixed_hex(self.signature, name="signature", nbytes=96)
        _require_sha256_ref(self.canonical_sha256, name="canonical_sha256")
        if (
            self.canonical_sha256
            != perp_liquidation_tau_source_root_authority_binding_hash(self)
        ):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> Mapping[str, object]:
        return {
            "action": self.action,
            "authority_hash": self.authority_hash,
            "authority_state_root_hash": self.authority_state_root_hash,
            "market_id": self.market_id,
            "policy_hash": self.policy_hash,
            "schema": self.schema,
            "signer_pubkey": self.signer_pubkey,
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }


@dataclass(frozen=True)
class PerpLiquidationTauSourceBinding:
    facts: PerpLiquidationTauSourceFacts
    expected_source_facts_hash: str
    proof_source_facts_hash: str
    source_state_root_binding: PerpLiquidationTauSourceStateRootBinding | None = None
    source_admission_envelope: "PerpLiquidationTauSourceAdmissionEnvelope | None" = None

    def __post_init__(self) -> None:
        if not isinstance(self.facts, PerpLiquidationTauSourceFacts):
            raise TypeError("facts must be PerpLiquidationTauSourceFacts")
        _require_sha256_ref(
            self.expected_source_facts_hash,
            name="expected_source_facts_hash",
        )
        _require_sha256_ref(
            self.proof_source_facts_hash,
            name="proof_source_facts_hash",
        )
        if (
            self.source_state_root_binding is not None
            and not isinstance(
                self.source_state_root_binding,
                PerpLiquidationTauSourceStateRootBinding,
            )
        ):
            raise TypeError(
                "source_state_root_binding must be PerpLiquidationTauSourceStateRootBinding"
            )
        if (
            self.source_admission_envelope is not None
            and not isinstance(
                self.source_admission_envelope,
                PerpLiquidationTauSourceAdmissionEnvelope,
            )
        ):
            raise TypeError(
                "source_admission_envelope must be PerpLiquidationTauSourceAdmissionEnvelope"
            )


@dataclass(frozen=True)
class PerpLiquidationTauSourceAdmissionEnvelope:
    schema: str
    request_id: str
    market_id: str
    account_id: str
    action: str
    fraction_bps: int
    source_facts_hash: str
    proof_receipt_hash: str
    source_state_root_hash: str
    state_root_kind: str
    source_state_root_binding_hash: str
    source_membership_proof_hash: str
    source_root_authority_hash: str
    source_root_authority_binding_hash: str
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != SOURCE_ADMISSION_ENVELOPE_SCHEMA:
            raise ValueError("invalid source admission envelope schema")
        _require_non_empty_str(self.request_id, name="request_id")
        _require_non_empty_str(self.market_id, name="market_id")
        _require_non_empty_str(self.account_id, name="account_id")
        _require_non_empty_str(self.action, name="action")
        _require_int(self.fraction_bps, name="fraction_bps")
        _require_sha256_ref(self.source_facts_hash, name="source_facts_hash")
        _require_sha256_ref(self.proof_receipt_hash, name="proof_receipt_hash")
        _require_sha256_ref(
            self.source_state_root_hash,
            name="source_state_root_hash",
        )
        _require_non_empty_str(self.state_root_kind, name="state_root_kind")
        _require_sha256_ref(
            self.source_state_root_binding_hash,
            name="source_state_root_binding_hash",
        )
        _require_sha256_ref(
            self.source_membership_proof_hash,
            name="source_membership_proof_hash",
        )
        _require_sha256_ref(
            self.source_root_authority_hash,
            name="source_root_authority_hash",
        )
        _require_sha256_ref(
            self.source_root_authority_binding_hash,
            name="source_root_authority_binding_hash",
        )
        _require_sha256_ref(self.canonical_sha256, name="canonical_sha256")
        if self.canonical_sha256 != perp_liquidation_tau_source_admission_envelope_hash(
            self
        ):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> Mapping[str, object]:
        return {
            "account_id": self.account_id,
            "action": self.action,
            "fraction_bps": int(self.fraction_bps),
            "market_id": self.market_id,
            "proof_receipt_hash": self.proof_receipt_hash,
            "request_id": self.request_id,
            "schema": self.schema,
            "source_facts_hash": self.source_facts_hash,
            "source_membership_proof_hash": self.source_membership_proof_hash,
            "source_root_authority_binding_hash": (
                self.source_root_authority_binding_hash
            ),
            "source_root_authority_hash": self.source_root_authority_hash,
            "source_state_root_binding_hash": self.source_state_root_binding_hash,
            "source_state_root_hash": self.source_state_root_hash,
            "state_root_kind": self.state_root_kind,
        }


def flags_to_tau_step(flags: Mapping[str, int]) -> Mapping[str, int]:
    normalized = normalize_perp_liquidation_tau_flags(flags)
    return {
        input_name: normalized[flag_name]
        for flag_name, input_name in sorted(
            INPUT_BY_FLAG.items(),
            key=lambda item: int(item[1][1:]),
        )
    }


def expected_perp_liquidation_o4(flags: Mapping[str, int]) -> int:
    normalized = normalize_perp_liquidation_tau_flags(flags)
    oracle_ready = (
        normalized["oracle_seen"] == 1
        and normalized["oracle_fresh_ok"] == 1
        and normalized["mark_oracle_gap_ok"] == 1
        and normalized["breaker_inactive"] == 1
    )
    liquidation_preconditions_ok = normalized["liquidation_requested"] == 0 or (
        normalized["account_under_maint"] == 1 and oracle_ready
    )
    return int(
        liquidation_preconditions_ok
        and normalized["proof_ok"] == 1
        and normalized["binding_ok"] == 1
    )


def source_binding_to_tau_step(
    binding: PerpLiquidationTauSourceBinding,
) -> Mapping[str, int]:
    return flags_to_tau_step(derive_perp_liquidation_flags_from_source_binding(binding))


def source_binding_tau_o4(binding: PerpLiquidationTauSourceBinding) -> int:
    return expected_perp_liquidation_o4(
        derive_perp_liquidation_flags_from_source_binding(binding)
    )


def derive_perp_liquidation_flags_from_source_binding(
    binding: PerpLiquidationTauSourceBinding,
) -> Mapping[str, int]:
    if not isinstance(binding, PerpLiquidationTauSourceBinding):
        raise TypeError("binding must be PerpLiquidationTauSourceBinding")
    facts = binding.facts
    source_facts_hash = perp_liquidation_tau_source_facts_hash(facts)
    binding_ok = (
        binding.expected_source_facts_hash == source_facts_hash
        and binding.proof_source_facts_hash == source_facts_hash
    )
    mark_oracle_gap_ok = not oracle_move_violated(
        facts.clearing_price_e8,
        facts.index_price_e8,
        facts.max_oracle_move_bps,
        facts.oracle_seen,
    )
    return {
        "liquidation_requested": int(facts.action == PARTIAL_LIQUIDATE_ACTION),
        "account_under_maint": int(
            is_liquidatable(
                facts.position_base,
                facts.collateral_quote,
                facts.index_price_e8,
                facts.maintenance_margin_bps,
                facts.depeg_buffer_bps,
            )
        ),
        "oracle_seen": int(facts.oracle_seen),
        "oracle_fresh_ok": int(
            is_oracle_fresh(
                facts.now_epoch,
                facts.oracle_last_update_epoch,
                facts.max_oracle_staleness_epochs,
                facts.oracle_seen,
            )
        ),
        "mark_oracle_gap_ok": int(mark_oracle_gap_ok),
        "breaker_inactive": int(not facts.breaker_active),
        "proof_ok": int(facts.proof_result_ok),
        "binding_ok": int(binding_ok),
    }


def source_binding_reject_reasons(
    binding: PerpLiquidationTauSourceBinding,
) -> tuple[str, ...]:
    flags = derive_perp_liquidation_flags_from_source_binding(binding)
    reasons: list[str] = []
    if flags["liquidation_requested"] != 1:
        reasons.append("not_liquidation_request")
    if flags["account_under_maint"] != 1:
        reasons.append("account_not_under_maintenance")
    if flags["oracle_seen"] != 1:
        reasons.append("oracle_not_seen")
    if flags["oracle_fresh_ok"] != 1:
        reasons.append("oracle_stale")
    if flags["mark_oracle_gap_ok"] != 1:
        reasons.append("mark_oracle_gap_exceeded")
    if flags["breaker_inactive"] != 1:
        reasons.append("breaker_active")
    if flags["proof_ok"] != 1:
        reasons.append("proof_not_ok")
    if flags["binding_ok"] != 1:
        reasons.append("source_binding_mismatch")
    return tuple(reasons)


def host_flags_match_source_binding(
    flags: Mapping[str, int],
    binding: PerpLiquidationTauSourceBinding,
) -> bool:
    return normalize_perp_liquidation_tau_flags(flags) == derive_perp_liquidation_flags_from_source_binding(binding)


def mismatched_host_flags(
    flags: Mapping[str, int],
    binding: PerpLiquidationTauSourceBinding,
) -> Mapping[str, tuple[int, int]]:
    normalized = normalize_perp_liquidation_tau_flags(flags)
    derived = derive_perp_liquidation_flags_from_source_binding(binding)
    return {
        name: (normalized[name], derived[name])
        for name in FLAG_NAMES
        if normalized[name] != derived[name]
    }


def source_state_root_binding_reject_reason(
    binding: PerpLiquidationTauSourceBinding,
    *,
    expected_source_state_root_hash: str | None = None,
    expected_state_root_kind: str | None = None,
) -> str | None:
    root_binding = binding.source_state_root_binding
    if root_binding is None:
        return "missing_source_state_root_binding"
    facts = binding.facts
    facts_hash = perp_liquidation_tau_source_facts_hash(facts)
    if root_binding.source_facts_hash != facts_hash:
        return "source_state_root_binding_facts_hash_mismatch"
    if root_binding.request_id != facts.request_id:
        return "source_state_root_binding_source_mismatch"
    if root_binding.market_id != facts.market_id:
        return "source_state_root_binding_source_mismatch"
    if root_binding.account_id != facts.account_id:
        return "source_state_root_binding_source_mismatch"
    if root_binding.action != facts.action:
        return "source_state_root_binding_source_mismatch"
    if root_binding.fraction_bps != facts.fraction_bps:
        return "source_state_root_binding_source_mismatch"
    if expected_source_state_root_hash is not None:
        expected_root = _require_sha256_ref(
            expected_source_state_root_hash,
            name="expected_source_state_root_hash",
        )
        if root_binding.source_state_root_hash != expected_root:
            return "source_state_root_binding_root_mismatch"
    if expected_state_root_kind is not None:
        expected_kind = _require_non_empty_str(
            expected_state_root_kind,
            name="expected_state_root_kind",
        )
        if root_binding.state_root_kind != expected_kind:
            return "source_state_root_binding_kind_mismatch"
    return None


def source_membership_proof_reject_reason(
    binding: PerpLiquidationTauSourceBinding,
) -> str | None:
    root_binding = binding.source_state_root_binding
    if root_binding is None:
        return "missing_source_state_root_binding"
    proof_binding = root_binding.source_membership_proof
    if proof_binding is None:
        return "missing_source_membership_proof"
    if root_binding.state_root_kind != JMT_SOURCE_STATE_ROOT_KIND:
        return "source_membership_proof_kind_mismatch"

    facts = binding.facts
    facts_hash = perp_liquidation_tau_source_facts_hash(facts)
    if proof_binding.source_facts_hash != facts_hash:
        return "source_membership_proof_facts_hash_mismatch"
    expected_key = perp_liquidation_tau_source_membership_key(facts)
    expected_value = perp_liquidation_tau_source_membership_value(facts)
    if proof_binding.source_membership_key_hash != _sha256_ref(expected_key):
        return "source_membership_proof_key_mismatch"
    if proof_binding.source_membership_value_hash != _sha256_ref(expected_value):
        return "source_membership_proof_value_hash_mismatch"

    try:
        proof_payload = _hex_to_bytes(
            proof_binding.jmt_membership_proof_payload_hex,
            name="jmt_membership_proof_payload_hex",
        )
        proof = decode_jmt_membership_proof(proof_payload)
        source_root = _sha256_ref_to_jmt_root(root_binding.source_state_root_hash)
    except (TypeError, ValueError):
        return "source_membership_proof_invalid"
    if not verify_jmt_membership(source_root, expected_key, expected_value, proof):
        return "source_membership_proof_root_mismatch"
    return None


def source_root_authority_reject_reason(
    binding: PerpLiquidationTauSourceBinding,
    *,
    now_epoch: int,
    expected_authority_state_root_hash: str,
    expected_policy_hash: str,
    allowed_signer_pubkeys: tuple[str, ...],
) -> str | None:
    root_binding = binding.source_state_root_binding
    if root_binding is None:
        return "missing_source_state_root_binding"
    authority = root_binding.source_root_authority
    if authority is None:
        return "missing_source_root_authority"
    authority_binding = root_binding.source_root_authority_binding
    if authority_binding is None:
        return "missing_source_root_authority_binding"

    facts = binding.facts
    epoch = _require_non_negative_int(now_epoch, name="now_epoch")
    expected_authority_root = _require_sha256_ref(
        expected_authority_state_root_hash,
        name="expected_authority_state_root_hash",
    )
    expected_policy = _require_sha256_ref(
        expected_policy_hash,
        name="expected_policy_hash",
    )
    allowed_signers = _require_signer_pubkeys(
        allowed_signer_pubkeys,
        name="allowed_signer_pubkeys",
    )

    if authority.market_id != facts.market_id or authority.action != facts.action:
        return "source_root_authority_source_mismatch"
    if authority.source_state_root_hash != root_binding.source_state_root_hash:
        return "source_root_authority_root_mismatch"
    if authority.state_root_kind != root_binding.state_root_kind:
        return "source_root_authority_kind_mismatch"
    if epoch < authority.valid_from_epoch or epoch > authority.valid_until_epoch:
        return "source_root_authority_epoch_out_of_range"

    if (
        authority_binding.market_id != facts.market_id
        or authority_binding.action != facts.action
    ):
        return "source_root_authority_binding_source_mismatch"
    if (
        epoch < authority_binding.valid_from_epoch
        or epoch > authority_binding.valid_until_epoch
    ):
        return "source_root_authority_binding_epoch_out_of_range"
    if authority_binding.authority_hash != perp_liquidation_tau_source_root_authority_hash(
        authority
    ):
        return "source_root_authority_binding_authority_hash_mismatch"
    if authority_binding.authority_state_root_hash != expected_authority_root:
        return "source_root_authority_binding_state_root_hash_mismatch"
    if authority_binding.policy_hash != expected_policy:
        return "source_root_authority_binding_policy_hash_mismatch"
    if authority_binding.signer_pubkey not in allowed_signers:
        return "source_root_authority_binding_signer_not_allowed"

    if G2Basic is None:
        return "source_root_authority_binding_bls_unavailable"
    try:
        signature_ok = G2Basic.Verify(
            bytes.fromhex(authority_binding.signer_pubkey.removeprefix("0x")),
            _signature_message(authority_binding.unsigned_payload()),
            bytes.fromhex(authority_binding.signature.removeprefix("0x")),
        )
    except AssertionError:
        signature_ok = False
    if not signature_ok:
        return "source_root_authority_binding_signature_invalid"
    return None


def source_admission_envelope_reject_reason(
    binding: PerpLiquidationTauSourceBinding,
    *,
    oracle_adapter_proof_receipt_hash: str | None,
) -> str | None:
    envelope = binding.source_admission_envelope
    if envelope is None:
        return "missing_source_admission_envelope"
    root_binding = binding.source_state_root_binding
    if root_binding is None:
        return "source_admission_envelope_missing_source_state_root_binding"
    membership = root_binding.source_membership_proof
    if membership is None:
        return "source_admission_envelope_missing_membership_proof"
    authority = root_binding.source_root_authority
    if authority is None:
        return "source_admission_envelope_missing_source_root_authority"
    authority_binding = root_binding.source_root_authority_binding
    if authority_binding is None:
        return "source_admission_envelope_missing_source_root_authority_binding"
    if oracle_adapter_proof_receipt_hash is None:
        return "source_admission_envelope_missing_oracle_adapter_receipt"

    facts = binding.facts
    facts_hash = perp_liquidation_tau_source_facts_hash(facts)
    oracle_receipt_hash = _require_sha256_ref(
        oracle_adapter_proof_receipt_hash,
        name="oracle_adapter_proof_receipt_hash",
    )
    if envelope.request_id != facts.request_id:
        return "source_admission_envelope_source_mismatch"
    if envelope.market_id != facts.market_id:
        return "source_admission_envelope_source_mismatch"
    if envelope.account_id != facts.account_id:
        return "source_admission_envelope_source_mismatch"
    if envelope.action != facts.action:
        return "source_admission_envelope_source_mismatch"
    if envelope.fraction_bps != facts.fraction_bps:
        return "source_admission_envelope_source_mismatch"
    if envelope.source_facts_hash != facts_hash:
        return "source_admission_envelope_facts_hash_mismatch"
    if envelope.proof_receipt_hash != facts.proof_receipt_hash:
        return "source_admission_envelope_proof_receipt_mismatch"
    if oracle_receipt_hash != facts.proof_receipt_hash:
        return "source_admission_envelope_oracle_receipt_mismatch"
    if envelope.source_state_root_hash != root_binding.source_state_root_hash:
        return "source_admission_envelope_root_mismatch"
    if envelope.state_root_kind != root_binding.state_root_kind:
        return "source_admission_envelope_kind_mismatch"
    if (
        envelope.source_state_root_binding_hash
        != perp_liquidation_tau_source_state_root_binding_hash(root_binding)
    ):
        return "source_admission_envelope_root_binding_hash_mismatch"
    if (
        envelope.source_membership_proof_hash
        != perp_liquidation_tau_source_membership_proof_hash(membership)
    ):
        return "source_admission_envelope_membership_hash_mismatch"
    if (
        envelope.source_root_authority_hash
        != perp_liquidation_tau_source_root_authority_hash(authority)
    ):
        return "source_admission_envelope_authority_hash_mismatch"
    if (
        envelope.source_root_authority_binding_hash
        != perp_liquidation_tau_source_root_authority_binding_payload_hash(
            authority_binding
        )
    ):
        return "source_admission_envelope_authority_binding_hash_mismatch"
    return None


def perp_liquidation_tau_source_facts_payload(
    facts: PerpLiquidationTauSourceFacts,
) -> Mapping[str, object]:
    return {
        "schema": "zenodex.perp_liquidation_tau_source_facts.v1",
        "request_id": facts.request_id,
        "market_id": facts.market_id,
        "account_id": facts.account_id,
        "action": facts.action,
        "fraction_bps": facts.fraction_bps,
        "now_epoch": facts.now_epoch,
        "position_base": facts.position_base,
        "collateral_quote": facts.collateral_quote,
        "index_price_e8": facts.index_price_e8,
        "maintenance_margin_bps": facts.maintenance_margin_bps,
        "depeg_buffer_bps": facts.depeg_buffer_bps,
        "oracle_seen": facts.oracle_seen,
        "oracle_last_update_epoch": facts.oracle_last_update_epoch,
        "max_oracle_staleness_epochs": facts.max_oracle_staleness_epochs,
        "clearing_price_e8": facts.clearing_price_e8,
        "max_oracle_move_bps": facts.max_oracle_move_bps,
        "breaker_active": facts.breaker_active,
        "proof_result_ok": facts.proof_result_ok,
        "proof_receipt_hash": facts.proof_receipt_hash,
    }


def perp_liquidation_tau_source_facts_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceFacts:
    if not isinstance(payload, Mapping):
        raise TypeError("source_facts must be an object")
    if payload.get("schema") != "zenodex.perp_liquidation_tau_source_facts.v1":
        raise ValueError("bad source_facts schema")
    return PerpLiquidationTauSourceFacts(
        request_id=_require_non_empty_str(payload.get("request_id"), name="request_id"),
        market_id=_require_non_empty_str(payload.get("market_id"), name="market_id"),
        account_id=_require_non_empty_str(payload.get("account_id"), name="account_id"),
        action=_require_non_empty_str(payload.get("action"), name="action"),
        fraction_bps=_require_int(payload.get("fraction_bps"), name="fraction_bps"),
        now_epoch=_require_int(payload.get("now_epoch"), name="now_epoch"),
        position_base=_require_int(payload.get("position_base"), name="position_base"),
        collateral_quote=_require_int(payload.get("collateral_quote"), name="collateral_quote"),
        index_price_e8=_require_int(payload.get("index_price_e8"), name="index_price_e8"),
        maintenance_margin_bps=_require_int(
            payload.get("maintenance_margin_bps"),
            name="maintenance_margin_bps",
        ),
        depeg_buffer_bps=_require_int(payload.get("depeg_buffer_bps"), name="depeg_buffer_bps"),
        oracle_seen=_require_bool(payload.get("oracle_seen"), name="oracle_seen"),
        oracle_last_update_epoch=_require_int(
            payload.get("oracle_last_update_epoch"),
            name="oracle_last_update_epoch",
        ),
        max_oracle_staleness_epochs=_require_int(
            payload.get("max_oracle_staleness_epochs"),
            name="max_oracle_staleness_epochs",
        ),
        clearing_price_e8=_require_int(payload.get("clearing_price_e8"), name="clearing_price_e8"),
        max_oracle_move_bps=_require_int(payload.get("max_oracle_move_bps"), name="max_oracle_move_bps"),
        breaker_active=_require_bool(payload.get("breaker_active"), name="breaker_active"),
        proof_result_ok=_require_bool(payload.get("proof_result_ok"), name="proof_result_ok"),
        proof_receipt_hash=_require_sha256_ref(
            payload.get("proof_receipt_hash"),
            name="proof_receipt_hash",
        ),
    )


def perp_liquidation_tau_source_facts_hash(
    facts: PerpLiquidationTauSourceFacts,
) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(perp_liquidation_tau_source_facts_payload(facts))
    ).hexdigest()


def perp_liquidation_tau_source_membership_key_payload(
    facts: PerpLiquidationTauSourceFacts,
) -> Mapping[str, object]:
    return {
        "schema": "zenodex.perp_liquidation_tau_source_membership_key.v1",
        "request_id": facts.request_id,
        "market_id": facts.market_id,
        "account_id": facts.account_id,
        "action": facts.action,
        "fraction_bps": facts.fraction_bps,
    }


def perp_liquidation_tau_source_membership_key(
    facts: PerpLiquidationTauSourceFacts,
) -> bytes:
    return hashlib.sha256(
        canonical_json_bytes(perp_liquidation_tau_source_membership_key_payload(facts))
    ).digest()


def perp_liquidation_tau_source_membership_value(
    facts: PerpLiquidationTauSourceFacts,
) -> bytes:
    return canonical_json_bytes(
        {
            "schema": "zenodex.perp_liquidation_tau_source_membership_value.v1",
            "source_facts_hash": perp_liquidation_tau_source_facts_hash(facts),
        }
    )


def build_perp_liquidation_tau_source_membership_proof(
    facts: PerpLiquidationTauSourceFacts,
    *,
    jmt_membership_proof_payload: bytes,
) -> PerpLiquidationTauSourceMembershipProof:
    proof_payload = _require_bytes(
        jmt_membership_proof_payload,
        name="jmt_membership_proof_payload",
    )
    key = perp_liquidation_tau_source_membership_key(facts)
    value = perp_liquidation_tau_source_membership_value(facts)
    return PerpLiquidationTauSourceMembershipProof(
        source_facts_hash=perp_liquidation_tau_source_facts_hash(facts),
        source_membership_key_hash=_sha256_ref(key),
        source_membership_value_hash=_sha256_ref(value),
        jmt_membership_proof_payload_hex=_bytes_to_hex(proof_payload),
    )


def build_perp_liquidation_tau_source_state_root_binding(
    facts: PerpLiquidationTauSourceFacts,
    *,
    source_state_root_hash: str,
    state_root_kind: str,
    source_membership_proof: PerpLiquidationTauSourceMembershipProof | None = None,
    source_root_authority: PerpLiquidationTauSourceRootAuthority | None = None,
    source_root_authority_binding: PerpLiquidationTauSourceRootAuthorityBinding | None = None,
) -> PerpLiquidationTauSourceStateRootBinding:
    return PerpLiquidationTauSourceStateRootBinding(
        source_facts_hash=perp_liquidation_tau_source_facts_hash(facts),
        source_state_root_hash=source_state_root_hash,
        state_root_kind=state_root_kind,
        request_id=facts.request_id,
        market_id=facts.market_id,
        account_id=facts.account_id,
        action=facts.action,
        fraction_bps=facts.fraction_bps,
        source_membership_proof=source_membership_proof,
        source_root_authority=source_root_authority,
        source_root_authority_binding=source_root_authority_binding,
    )


def perp_liquidation_tau_source_root_authority_hash(
    authority: PerpLiquidationTauSourceRootAuthority,
) -> str:
    if not isinstance(authority, PerpLiquidationTauSourceRootAuthority):
        raise TypeError("authority must be PerpLiquidationTauSourceRootAuthority")
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(authority.unsigned_payload())
    ).hexdigest()


def perp_liquidation_tau_source_root_authority_binding_hash(
    binding: PerpLiquidationTauSourceRootAuthorityBinding,
) -> str:
    if not isinstance(binding, PerpLiquidationTauSourceRootAuthorityBinding):
        raise TypeError(
            "binding must be PerpLiquidationTauSourceRootAuthorityBinding"
        )
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(binding.unsigned_payload())
    ).hexdigest()


def perp_liquidation_tau_source_membership_proof_hash(
    proof: PerpLiquidationTauSourceMembershipProof,
) -> str:
    if not isinstance(proof, PerpLiquidationTauSourceMembershipProof):
        raise TypeError("proof must be PerpLiquidationTauSourceMembershipProof")
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(perp_liquidation_tau_source_membership_proof_payload(proof))
    ).hexdigest()


def perp_liquidation_tau_source_state_root_binding_hash(
    binding: PerpLiquidationTauSourceStateRootBinding,
) -> str:
    if not isinstance(binding, PerpLiquidationTauSourceStateRootBinding):
        raise TypeError("binding must be PerpLiquidationTauSourceStateRootBinding")
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(perp_liquidation_tau_source_state_root_binding_payload(binding))
    ).hexdigest()


def perp_liquidation_tau_source_root_authority_binding_payload_hash(
    binding: PerpLiquidationTauSourceRootAuthorityBinding,
) -> str:
    if not isinstance(binding, PerpLiquidationTauSourceRootAuthorityBinding):
        raise TypeError(
            "binding must be PerpLiquidationTauSourceRootAuthorityBinding"
        )
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(perp_liquidation_tau_source_root_authority_binding_payload(binding))
    ).hexdigest()


def perp_liquidation_tau_source_admission_envelope_hash(
    envelope: PerpLiquidationTauSourceAdmissionEnvelope,
) -> str:
    if not isinstance(envelope, PerpLiquidationTauSourceAdmissionEnvelope):
        raise TypeError("envelope must be PerpLiquidationTauSourceAdmissionEnvelope")
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(envelope.unsigned_payload())
    ).hexdigest()


def build_perp_liquidation_tau_source_admission_envelope(
    binding: PerpLiquidationTauSourceBinding,
) -> PerpLiquidationTauSourceAdmissionEnvelope:
    if not isinstance(binding, PerpLiquidationTauSourceBinding):
        raise TypeError("binding must be PerpLiquidationTauSourceBinding")
    root_binding = binding.source_state_root_binding
    if root_binding is None:
        raise ValueError("source_state_root_binding required")
    membership = root_binding.source_membership_proof
    if membership is None:
        raise ValueError("source_membership_proof required")
    authority = root_binding.source_root_authority
    if authority is None:
        raise ValueError("source_root_authority required")
    authority_binding = root_binding.source_root_authority_binding
    if authority_binding is None:
        raise ValueError("source_root_authority_binding required")
    facts = binding.facts
    unsigned = {
        "account_id": facts.account_id,
        "action": facts.action,
        "fraction_bps": int(facts.fraction_bps),
        "market_id": facts.market_id,
        "proof_receipt_hash": facts.proof_receipt_hash,
        "request_id": facts.request_id,
        "schema": SOURCE_ADMISSION_ENVELOPE_SCHEMA,
        "source_facts_hash": perp_liquidation_tau_source_facts_hash(facts),
        "source_membership_proof_hash": (
            perp_liquidation_tau_source_membership_proof_hash(membership)
        ),
        "source_root_authority_binding_hash": (
            perp_liquidation_tau_source_root_authority_binding_payload_hash(
                authority_binding
            )
        ),
        "source_root_authority_hash": (
            perp_liquidation_tau_source_root_authority_hash(authority)
        ),
        "source_state_root_binding_hash": (
            perp_liquidation_tau_source_state_root_binding_hash(root_binding)
        ),
        "source_state_root_hash": root_binding.source_state_root_hash,
        "state_root_kind": root_binding.state_root_kind,
    }
    return PerpLiquidationTauSourceAdmissionEnvelope(
        schema=SOURCE_ADMISSION_ENVELOPE_SCHEMA,
        request_id=str(unsigned["request_id"]),
        market_id=str(unsigned["market_id"]),
        account_id=str(unsigned["account_id"]),
        action=str(unsigned["action"]),
        fraction_bps=int(unsigned["fraction_bps"]),
        source_facts_hash=str(unsigned["source_facts_hash"]),
        proof_receipt_hash=str(unsigned["proof_receipt_hash"]),
        source_state_root_hash=str(unsigned["source_state_root_hash"]),
        state_root_kind=str(unsigned["state_root_kind"]),
        source_state_root_binding_hash=str(
            unsigned["source_state_root_binding_hash"]
        ),
        source_membership_proof_hash=str(unsigned["source_membership_proof_hash"]),
        source_root_authority_hash=str(unsigned["source_root_authority_hash"]),
        source_root_authority_binding_hash=str(
            unsigned["source_root_authority_binding_hash"]
        ),
        canonical_sha256="sha256:"
        + hashlib.sha256(canonical_json_bytes(unsigned)).hexdigest(),
    )


def build_perp_liquidation_tau_source_root_authority(
    *,
    market_id: str,
    action: str,
    source_state_root_hash: str,
    state_root_kind: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
) -> PerpLiquidationTauSourceRootAuthority:
    unsigned = {
        "action": _require_non_empty_str(action, name="action"),
        "market_id": _require_non_empty_str(market_id, name="market_id"),
        "schema": SOURCE_ROOT_AUTHORITY_SCHEMA,
        "source_state_root_hash": _require_sha256_ref(
            source_state_root_hash,
            name="source_state_root_hash",
        ),
        "state_root_kind": _require_non_empty_str(
            state_root_kind,
            name="state_root_kind",
        ),
        "valid_from_epoch": _require_non_negative_int(
            valid_from_epoch,
            name="valid_from_epoch",
        ),
        "valid_until_epoch": _require_non_negative_int(
            valid_until_epoch,
            name="valid_until_epoch",
        ),
    }
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    return PerpLiquidationTauSourceRootAuthority(
        schema=SOURCE_ROOT_AUTHORITY_SCHEMA,
        market_id=str(unsigned["market_id"]),
        action=str(unsigned["action"]),
        source_state_root_hash=str(unsigned["source_state_root_hash"]),
        state_root_kind=str(unsigned["state_root_kind"]),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        canonical_sha256="sha256:"
        + hashlib.sha256(canonical_json_bytes(unsigned)).hexdigest(),
    )


def build_perp_liquidation_tau_source_root_authority_binding(
    *,
    market_id: str,
    action: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authority_hash: str,
    authority_state_root_hash: str,
    policy_hash: str,
    signer_privkey: int,
) -> PerpLiquidationTauSourceRootAuthorityBinding:
    if (
        not isinstance(signer_privkey, int)
        or isinstance(signer_privkey, bool)
        or signer_privkey <= 0
    ):
        raise ValueError("signer_privkey must be a positive int")
    bls = _require_bls()
    signer_pubkey = "0x" + bls.SkToPk(signer_privkey).hex()
    unsigned = {
        "action": _require_non_empty_str(action, name="action"),
        "authority_hash": _require_sha256_ref(
            authority_hash,
            name="authority_hash",
        ),
        "authority_state_root_hash": _require_sha256_ref(
            authority_state_root_hash,
            name="authority_state_root_hash",
        ),
        "market_id": _require_non_empty_str(market_id, name="market_id"),
        "policy_hash": _require_sha256_ref(policy_hash, name="policy_hash"),
        "schema": SOURCE_ROOT_AUTHORITY_BINDING_SCHEMA,
        "signer_pubkey": signer_pubkey,
        "valid_from_epoch": _require_non_negative_int(
            valid_from_epoch,
            name="valid_from_epoch",
        ),
        "valid_until_epoch": _require_non_negative_int(
            valid_until_epoch,
            name="valid_until_epoch",
        ),
    }
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    signature = "0x" + bls.Sign(
        signer_privkey,
        _signature_message(unsigned),
    ).hex()
    return PerpLiquidationTauSourceRootAuthorityBinding(
        schema=SOURCE_ROOT_AUTHORITY_BINDING_SCHEMA,
        market_id=str(unsigned["market_id"]),
        action=str(unsigned["action"]),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        authority_hash=str(unsigned["authority_hash"]),
        authority_state_root_hash=str(unsigned["authority_state_root_hash"]),
        policy_hash=str(unsigned["policy_hash"]),
        signer_pubkey=signer_pubkey,
        signature=signature,
        canonical_sha256="sha256:"
        + hashlib.sha256(canonical_json_bytes(unsigned)).hexdigest(),
    )


def perp_liquidation_tau_source_state_root_binding_payload(
    binding: PerpLiquidationTauSourceStateRootBinding,
) -> Mapping[str, object]:
    payload: dict[str, object] = {
        "schema": "zenodex.perp_liquidation_tau_source_state_root_binding.v1",
        "source_facts_hash": binding.source_facts_hash,
        "source_state_root_hash": binding.source_state_root_hash,
        "state_root_kind": binding.state_root_kind,
        "request_id": binding.request_id,
        "market_id": binding.market_id,
        "account_id": binding.account_id,
        "action": binding.action,
        "fraction_bps": binding.fraction_bps,
    }
    if binding.source_membership_proof is not None:
        payload["source_membership_proof"] = (
            perp_liquidation_tau_source_membership_proof_payload(
                binding.source_membership_proof
            )
        )
    if binding.source_root_authority is not None:
        payload["source_root_authority"] = (
            perp_liquidation_tau_source_root_authority_payload(
                binding.source_root_authority
            )
        )
    if binding.source_root_authority_binding is not None:
        payload["source_root_authority_binding"] = (
            perp_liquidation_tau_source_root_authority_binding_payload(
                binding.source_root_authority_binding
            )
        )
    return payload


def perp_liquidation_tau_source_membership_proof_payload(
    proof: PerpLiquidationTauSourceMembershipProof,
) -> Mapping[str, object]:
    return {
        "schema": "zenodex.perp_liquidation_tau_source_membership_proof.v1",
        "source_facts_hash": proof.source_facts_hash,
        "source_membership_key_hash": proof.source_membership_key_hash,
        "source_membership_value_hash": proof.source_membership_value_hash,
        "jmt_membership_proof_payload_hex": proof.jmt_membership_proof_payload_hex,
    }


def perp_liquidation_tau_source_membership_proof_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceMembershipProof:
    if not isinstance(payload, Mapping):
        raise TypeError("source_membership_proof must be an object")
    if payload.get("schema") != "zenodex.perp_liquidation_tau_source_membership_proof.v1":
        raise ValueError("bad source_membership_proof schema")
    return PerpLiquidationTauSourceMembershipProof(
        source_facts_hash=_require_sha256_ref(
            payload.get("source_facts_hash"),
            name="source_facts_hash",
        ),
        source_membership_key_hash=_require_sha256_ref(
            payload.get("source_membership_key_hash"),
            name="source_membership_key_hash",
        ),
        source_membership_value_hash=_require_sha256_ref(
            payload.get("source_membership_value_hash"),
            name="source_membership_value_hash",
        ),
        jmt_membership_proof_payload_hex=_require_hex_bytes(
            payload.get("jmt_membership_proof_payload_hex"),
            name="jmt_membership_proof_payload_hex",
        ),
    )


def perp_liquidation_tau_source_root_authority_payload(
    authority: PerpLiquidationTauSourceRootAuthority,
) -> Mapping[str, object]:
    if not isinstance(authority, PerpLiquidationTauSourceRootAuthority):
        raise TypeError("authority must be PerpLiquidationTauSourceRootAuthority")
    payload = dict(authority.unsigned_payload())
    payload["canonical_sha256"] = authority.canonical_sha256
    return payload


def perp_liquidation_tau_source_root_authority_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceRootAuthority:
    if not isinstance(payload, Mapping):
        raise TypeError("source_root_authority must be an object")
    if payload.get("schema") != SOURCE_ROOT_AUTHORITY_SCHEMA:
        raise ValueError("bad source_root_authority schema")
    return PerpLiquidationTauSourceRootAuthority(
        schema=_require_non_empty_str(payload.get("schema"), name="schema"),
        market_id=_require_non_empty_str(payload.get("market_id"), name="market_id"),
        action=_require_non_empty_str(payload.get("action"), name="action"),
        source_state_root_hash=_require_sha256_ref(
            payload.get("source_state_root_hash"),
            name="source_state_root_hash",
        ),
        state_root_kind=_require_non_empty_str(
            payload.get("state_root_kind"),
            name="state_root_kind",
        ),
        valid_from_epoch=_require_non_negative_int(
            payload.get("valid_from_epoch"),
            name="valid_from_epoch",
        ),
        valid_until_epoch=_require_non_negative_int(
            payload.get("valid_until_epoch"),
            name="valid_until_epoch",
        ),
        canonical_sha256=_require_sha256_ref(
            payload.get("canonical_sha256"),
            name="canonical_sha256",
        ),
    )


def perp_liquidation_tau_source_root_authority_binding_payload(
    binding: PerpLiquidationTauSourceRootAuthorityBinding,
) -> Mapping[str, object]:
    if not isinstance(binding, PerpLiquidationTauSourceRootAuthorityBinding):
        raise TypeError(
            "binding must be PerpLiquidationTauSourceRootAuthorityBinding"
        )
    payload = dict(binding.unsigned_payload())
    payload["canonical_sha256"] = binding.canonical_sha256
    payload["signature"] = binding.signature
    return payload


def perp_liquidation_tau_source_admission_envelope_payload(
    envelope: PerpLiquidationTauSourceAdmissionEnvelope,
) -> Mapping[str, object]:
    if not isinstance(envelope, PerpLiquidationTauSourceAdmissionEnvelope):
        raise TypeError("envelope must be PerpLiquidationTauSourceAdmissionEnvelope")
    payload = dict(envelope.unsigned_payload())
    payload["canonical_sha256"] = envelope.canonical_sha256
    return payload


def perp_liquidation_tau_source_admission_envelope_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceAdmissionEnvelope:
    if not isinstance(payload, Mapping):
        raise TypeError("source_admission_envelope must be an object")
    if payload.get("schema") != SOURCE_ADMISSION_ENVELOPE_SCHEMA:
        raise ValueError("bad source_admission_envelope schema")
    return PerpLiquidationTauSourceAdmissionEnvelope(
        schema=_require_non_empty_str(payload.get("schema"), name="schema"),
        request_id=_require_non_empty_str(
            payload.get("request_id"),
            name="request_id",
        ),
        market_id=_require_non_empty_str(payload.get("market_id"), name="market_id"),
        account_id=_require_non_empty_str(
            payload.get("account_id"),
            name="account_id",
        ),
        action=_require_non_empty_str(payload.get("action"), name="action"),
        fraction_bps=_require_int(payload.get("fraction_bps"), name="fraction_bps"),
        source_facts_hash=_require_sha256_ref(
            payload.get("source_facts_hash"),
            name="source_facts_hash",
        ),
        proof_receipt_hash=_require_sha256_ref(
            payload.get("proof_receipt_hash"),
            name="proof_receipt_hash",
        ),
        source_state_root_hash=_require_sha256_ref(
            payload.get("source_state_root_hash"),
            name="source_state_root_hash",
        ),
        state_root_kind=_require_non_empty_str(
            payload.get("state_root_kind"),
            name="state_root_kind",
        ),
        source_state_root_binding_hash=_require_sha256_ref(
            payload.get("source_state_root_binding_hash"),
            name="source_state_root_binding_hash",
        ),
        source_membership_proof_hash=_require_sha256_ref(
            payload.get("source_membership_proof_hash"),
            name="source_membership_proof_hash",
        ),
        source_root_authority_hash=_require_sha256_ref(
            payload.get("source_root_authority_hash"),
            name="source_root_authority_hash",
        ),
        source_root_authority_binding_hash=_require_sha256_ref(
            payload.get("source_root_authority_binding_hash"),
            name="source_root_authority_binding_hash",
        ),
        canonical_sha256=_require_sha256_ref(
            payload.get("canonical_sha256"),
            name="canonical_sha256",
        ),
    )


def perp_liquidation_tau_source_root_authority_binding_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceRootAuthorityBinding:
    if not isinstance(payload, Mapping):
        raise TypeError("source_root_authority_binding must be an object")
    if payload.get("schema") != SOURCE_ROOT_AUTHORITY_BINDING_SCHEMA:
        raise ValueError("bad source_root_authority_binding schema")
    return PerpLiquidationTauSourceRootAuthorityBinding(
        schema=_require_non_empty_str(payload.get("schema"), name="schema"),
        market_id=_require_non_empty_str(payload.get("market_id"), name="market_id"),
        action=_require_non_empty_str(payload.get("action"), name="action"),
        valid_from_epoch=_require_non_negative_int(
            payload.get("valid_from_epoch"),
            name="valid_from_epoch",
        ),
        valid_until_epoch=_require_non_negative_int(
            payload.get("valid_until_epoch"),
            name="valid_until_epoch",
        ),
        authority_hash=_require_sha256_ref(
            payload.get("authority_hash"),
            name="authority_hash",
        ),
        authority_state_root_hash=_require_sha256_ref(
            payload.get("authority_state_root_hash"),
            name="authority_state_root_hash",
        ),
        policy_hash=_require_sha256_ref(payload.get("policy_hash"), name="policy_hash"),
        signer_pubkey=_require_prefixed_hex(
            payload.get("signer_pubkey"),
            name="signer_pubkey",
            nbytes=48,
        ),
        signature=_require_prefixed_hex(
            payload.get("signature"),
            name="signature",
            nbytes=96,
        ),
        canonical_sha256=_require_sha256_ref(
            payload.get("canonical_sha256"),
            name="canonical_sha256",
        ),
    )


def perp_liquidation_tau_source_state_root_binding_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceStateRootBinding:
    if not isinstance(payload, Mapping):
        raise TypeError("source_state_root_binding must be an object")
    if (
        payload.get("schema")
        != "zenodex.perp_liquidation_tau_source_state_root_binding.v1"
    ):
        raise ValueError("bad source_state_root_binding schema")
    membership_payload = payload.get("source_membership_proof")
    authority_payload = payload.get("source_root_authority")
    authority_binding_payload = payload.get("source_root_authority_binding")
    return PerpLiquidationTauSourceStateRootBinding(
        source_facts_hash=_require_sha256_ref(
            payload.get("source_facts_hash"),
            name="source_facts_hash",
        ),
        source_state_root_hash=_require_sha256_ref(
            payload.get("source_state_root_hash"),
            name="source_state_root_hash",
        ),
        state_root_kind=_require_non_empty_str(
            payload.get("state_root_kind"),
            name="state_root_kind",
        ),
        request_id=_require_non_empty_str(payload.get("request_id"), name="request_id"),
        market_id=_require_non_empty_str(payload.get("market_id"), name="market_id"),
        account_id=_require_non_empty_str(payload.get("account_id"), name="account_id"),
        action=_require_non_empty_str(payload.get("action"), name="action"),
        fraction_bps=_require_int(payload.get("fraction_bps"), name="fraction_bps"),
        source_membership_proof=(
            None
            if membership_payload is None
            else perp_liquidation_tau_source_membership_proof_from_payload(
                _require_mapping(membership_payload, name="source_membership_proof")
            )
        ),
        source_root_authority=(
            None
            if authority_payload is None
            else perp_liquidation_tau_source_root_authority_from_payload(
                _require_mapping(authority_payload, name="source_root_authority")
            )
        ),
        source_root_authority_binding=(
            None
            if authority_binding_payload is None
            else perp_liquidation_tau_source_root_authority_binding_from_payload(
                _require_mapping(
                    authority_binding_payload,
                    name="source_root_authority_binding",
                )
            )
        ),
    )


def perp_liquidation_tau_source_binding_payload(
    binding: PerpLiquidationTauSourceBinding,
) -> Mapping[str, object]:
    facts_hash = perp_liquidation_tau_source_facts_hash(binding.facts)
    payload = {
        "schema": "zenodex.perp_liquidation_tau_source_binding.v1",
        "source_facts": perp_liquidation_tau_source_facts_payload(binding.facts),
        "source_facts_hash": facts_hash,
        "expected_source_facts_hash": binding.expected_source_facts_hash,
        "proof_source_facts_hash": binding.proof_source_facts_hash,
        "derived_flags": dict(
            derive_perp_liquidation_flags_from_source_binding(binding)
        ),
        "reject_reasons": list(source_binding_reject_reasons(binding)),
    }
    if binding.source_state_root_binding is not None:
        payload["source_state_root_binding"] = (
            perp_liquidation_tau_source_state_root_binding_payload(
                binding.source_state_root_binding
            )
        )
    if binding.source_admission_envelope is not None:
        payload["source_admission_envelope"] = (
            perp_liquidation_tau_source_admission_envelope_payload(
                binding.source_admission_envelope
            )
        )
    return payload


def perp_liquidation_tau_source_binding_from_payload(
    payload: Mapping[str, Any],
) -> PerpLiquidationTauSourceBinding:
    if not isinstance(payload, Mapping):
        raise TypeError("tau_source_binding must be an object")
    if payload.get("schema") != "zenodex.perp_liquidation_tau_source_binding.v1":
        raise ValueError("bad tau_source_binding schema")
    root_binding_payload = payload.get("source_state_root_binding")
    envelope_payload = payload.get("source_admission_envelope")
    return PerpLiquidationTauSourceBinding(
        facts=perp_liquidation_tau_source_facts_from_payload(
            _require_mapping(payload.get("source_facts"), name="source_facts")
        ),
        expected_source_facts_hash=_require_sha256_ref(
            payload.get("expected_source_facts_hash"),
            name="expected_source_facts_hash",
        ),
        proof_source_facts_hash=_require_sha256_ref(
            payload.get("proof_source_facts_hash"),
            name="proof_source_facts_hash",
        ),
        source_state_root_binding=(
            None
            if root_binding_payload is None
            else perp_liquidation_tau_source_state_root_binding_from_payload(
                _require_mapping(
                    root_binding_payload,
                    name="source_state_root_binding",
                )
            )
        ),
        source_admission_envelope=(
            None
            if envelope_payload is None
            else perp_liquidation_tau_source_admission_envelope_from_payload(
                _require_mapping(
                    envelope_payload,
                    name="source_admission_envelope",
                )
            )
        ),
    )


def normalize_perp_liquidation_tau_flags(flags: Mapping[str, int]) -> Mapping[str, int]:
    if set(flags.keys()) != set(FLAG_NAMES):
        missing = sorted(set(FLAG_NAMES) - set(flags.keys()))
        extra = sorted(set(flags.keys()) - set(FLAG_NAMES))
        raise ValueError(f"flags must contain exactly FLAG_NAMES; missing={missing} extra={extra}")
    return {name: _require_bit(flags[name], name=name) for name in FLAG_NAMES}


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_bit(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int bit")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return int(value)


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_non_empty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_sha256_ref(value: object, *, name: str) -> str:
    text = _require_non_empty_str(value, name=name)
    if not text.startswith("sha256:"):
        raise ValueError(f"{name} must start with sha256:")
    digest = text.removeprefix("sha256:")
    if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
        raise ValueError(f"{name} must be a lowercase sha256 ref")
    return text


def _sha256_ref(value: bytes) -> str:
    return "sha256:" + hashlib.sha256(_require_bytes(value, name="hash input")).hexdigest()


def _signature_message(payload: object) -> bytes:
    return hashlib.sha256(canonical_json_bytes(payload)).digest()


def _sha256_ref_to_jmt_root(value: object) -> str:
    return "0x" + _require_sha256_ref(value, name="source_state_root_hash").removeprefix("sha256:")


def _require_bytes(value: object, *, name: str) -> bytes:
    if not isinstance(value, bytes):
        raise TypeError(f"{name} must be bytes")
    return bytes(value)


def _bytes_to_hex(value: bytes) -> str:
    return "0x" + _require_bytes(value, name="hex input").hex()


def _require_hex_bytes(value: object, *, name: str) -> str:
    text = _require_non_empty_str(value, name=name)
    _hex_to_bytes(text, name=name)
    return text


def _hex_to_bytes(value: object, *, name: str) -> bytes:
    text = _require_non_empty_str(value, name=name)
    if not text.startswith("0x"):
        raise ValueError(f"{name} must start with 0x")
    digest = text.removeprefix("0x")
    if len(digest) % 2 != 0:
        raise ValueError(f"{name} must have an even number of hex digits")
    if any(ch not in "0123456789abcdef" for ch in digest):
        raise ValueError(f"{name} must be lowercase hex")
    return bytes.fromhex(digest)


def _require_prefixed_hex(value: object, *, name: str, nbytes: int) -> str:
    text = _require_non_empty_str(value, name=name)
    expected_len = 2 + 2 * nbytes
    if not text.startswith("0x") or len(text) != expected_len:
        raise ValueError(f"{name} must be 0x-prefixed {nbytes}-byte hex")
    digest = text.removeprefix("0x")
    if digest != digest.lower() or any(ch not in "0123456789abcdef" for ch in digest):
        raise ValueError(f"{name} must be 0x-prefixed lowercase hex")
    return text


def _require_signer_pubkeys(value: object, *, name: str) -> tuple[str, ...]:
    if not isinstance(value, tuple):
        raise TypeError(f"{name} must be a tuple")
    out = tuple(
        _require_prefixed_hex(signer, name="signer_pubkey", nbytes=48)
        for signer in value
    )
    if not out:
        raise ValueError(f"{name} must be non-empty")
    if list(out) != sorted(out):
        raise ValueError(f"{name} must be sorted")
    if len(out) != len(set(out)):
        raise ValueError(f"{name} must be unique")
    return out
