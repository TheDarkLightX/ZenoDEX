from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence

from src.core.settlement import Settlement
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.lp import LPTable
from src.state.pools import PoolState

from .decision_witness import (
    DecisionWitness,
    build_decision_witness_from_settlement_end_to_end_certificate_packet,
    verify_decision_witness_against_settlement_end_to_end_certificate_packet,
)
from .settlement_end_to_end_certificate_packet import (
    SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA,
    SettlementEndToEndCertificateInputs,
    SettlementEndToEndCertificatePacket,
    _end_to_end_packet_rejection_reason,
    build_settlement_end_to_end_certificate_packet_from_price_attestation,
    build_settlement_end_to_end_certificate_packet_from_price_packet,
)

SETTLEMENT_WITNESS_LIFECYCLE_PACKET_SCHEMA = "zenodex/settlement-witness-lifecycle-packet/v1"
_LIFECYCLE_DOMAIN_ERRORS = (TypeError, ValueError, ArithmeticError)


@dataclass(frozen=True)
class SettlementWitnessLifecyclePacket:
    decision_witness: DecisionWitness | None
    end_to_end_packet: SettlementEndToEndCertificatePacket | None
    packet_built: bool
    end_to_end_packet_ok: bool
    witness_present: bool
    witness_valid: bool
    before_expiry: bool
    settled: bool
    rejected_with_reason: bool
    rejection_reason_present: bool
    rejection_reason: str | None
    lifecycle_ok: bool
    schema: str = SETTLEMENT_WITNESS_LIFECYCLE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_WITNESS_LIFECYCLE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.end_to_end_packet is not None and self.end_to_end_packet.schema != SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA:
            raise ValueError("unexpected end_to_end_packet schema")
        for name in (
            "packet_built",
            "end_to_end_packet_ok",
            "witness_present",
            "witness_valid",
            "before_expiry",
            "settled",
            "rejected_with_reason",
            "rejection_reason_present",
            "lifecycle_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")
        if self.packet_built != (self.end_to_end_packet is not None):
            raise ValueError("packet_built mismatch")
        if self.end_to_end_packet_ok != (
            self.end_to_end_packet is not None and bool(self.end_to_end_packet.packet_ok)
        ):
            raise ValueError("end_to_end_packet_ok mismatch")
        if self.witness_present != (self.decision_witness is not None):
            raise ValueError("witness_present mismatch")
        if self.witness_valid and not self.witness_present:
            raise ValueError("witness_valid requires witness_present")
        if self.settled and not self.witness_valid:
            raise ValueError("settled requires witness_valid")
        if self.settled and not self.end_to_end_packet_ok:
            raise ValueError("settled requires end_to_end_packet_ok")
        if self.rejected_with_reason != (not self.settled):
            raise ValueError("rejected_with_reason mismatch")
        if self.rejection_reason is not None and (
            not isinstance(self.rejection_reason, str) or not self.rejection_reason.strip()
        ):
            raise ValueError("rejection_reason must be a non-empty string when present")
        if self.rejection_reason_present != bool(
            isinstance(self.rejection_reason, str) and self.rejection_reason.strip()
        ):
            raise ValueError("rejection_reason_present mismatch")
        if self.rejected_with_reason and not self.rejection_reason_present:
            raise ValueError("rejected_with_reason requires rejection_reason_present")
        lifecycle_formula = bool(
            ((not self.witness_valid) or (not self.before_expiry) or self.settled or self.rejected_with_reason)
            and ((not self.rejected_with_reason) or self.rejection_reason_present)
            and ((not self.witness_valid) or self.witness_present)
            and ((not self.settled) or self.witness_valid)
            and ((not self.settled) or self.end_to_end_packet_ok)
            and (self.settled != self.rejected_with_reason)
        )
        if self.lifecycle_ok != lifecycle_formula:
            raise ValueError("lifecycle_ok formula mismatch")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "decision_witness": None if self.decision_witness is None else self.decision_witness.to_dict(),
            "end_to_end_packet": None if self.end_to_end_packet is None else self.end_to_end_packet.to_dict(),
            "packet_built": bool(self.packet_built),
            "end_to_end_packet_ok": bool(self.end_to_end_packet_ok),
            "witness_present": bool(self.witness_present),
            "witness_valid": bool(self.witness_valid),
            "before_expiry": bool(self.before_expiry),
            "settled": bool(self.settled),
            "rejected_with_reason": bool(self.rejected_with_reason),
            "rejection_reason_present": bool(self.rejection_reason_present),
            "rejection_reason": self.rejection_reason,
            "lifecycle_ok": bool(self.lifecycle_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementWitnessLifecyclePacket":
        from .decision_witness import DecisionWitness

        if not isinstance(payload, Mapping):
            raise ValueError("settlement witness lifecycle packet must be an object")
        witness_payload = payload.get("decision_witness")
        end_to_end_packet_payload = payload.get("end_to_end_packet")
        return cls(
            schema=str(payload.get("schema", "")),
            decision_witness=(
                None if witness_payload is None else DecisionWitness.from_dict(witness_payload)
            ),
            end_to_end_packet=(
                None
                if end_to_end_packet_payload is None
                else SettlementEndToEndCertificatePacket.from_dict(end_to_end_packet_payload)
            ),
            packet_built=_require_bool(payload.get("packet_built", False), name="packet_built"),
            end_to_end_packet_ok=_require_bool(
                payload.get("end_to_end_packet_ok", False),
                name="end_to_end_packet_ok",
            ),
            witness_present=_require_bool(payload.get("witness_present", False), name="witness_present"),
            witness_valid=_require_bool(payload.get("witness_valid", False), name="witness_valid"),
            before_expiry=_require_bool(payload.get("before_expiry", False), name="before_expiry"),
            settled=_require_bool(payload.get("settled", False), name="settled"),
            rejected_with_reason=_require_bool(
                payload.get("rejected_with_reason", False),
                name="rejected_with_reason",
            ),
            rejection_reason_present=_require_bool(
                payload.get("rejection_reason_present", False),
                name="rejection_reason_present",
            ),
            rejection_reason=payload.get("rejection_reason"),
            lifecycle_ok=_require_bool(payload.get("lifecycle_ok", False), name="lifecycle_ok"),
        )


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def build_settlement_witness_lifecycle_packet(
    *,
    intents: Sequence[Intent],
    settlement: Settlement,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable | None,
    block_timestamp: int,
    settlement_end_to_end_certificate_inputs: SettlementEndToEndCertificateInputs,
    settlement_validation: str = "strong_replay",
    swap_ordering: str = "greedy_ab_refined",
    quote_bindings_validated: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[str] = None,
) -> SettlementWitnessLifecyclePacket:
    if not intents:
        raise ValueError("intents must be non-empty")
    if not isinstance(block_timestamp, int) or isinstance(block_timestamp, bool):
        raise TypeError("block_timestamp must be an int")

    min_deadline = min(int(intent.deadline) for intent in intents)
    before_expiry = bool(int(block_timestamp) <= int(min_deadline))
    allow_cow_netting = str(swap_ordering) == "cow_pair_netting_v1"

    ok, error = validate_settlement_strong(
        settlement=settlement,
        intents=list(intents),
        pre_balances=balances,
        pre_pools=dict(pools),
        pre_lp_balances=lp_balances,
        mode=str(settlement_validation),
        allow_cow_netting=bool(allow_cow_netting),
        allow_snapshot_bound_quote_bindings=bool(quote_bindings_validated),
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    if not ok:
        return SettlementWitnessLifecyclePacket(
            decision_witness=None,
            end_to_end_packet=None,
            packet_built=False,
            end_to_end_packet_ok=False,
            witness_present=False,
            witness_valid=False,
            before_expiry=before_expiry,
            settled=False,
            rejected_with_reason=True,
            rejection_reason_present=True,
            rejection_reason=str(error),
            lifecycle_ok=True,
        )

    packet: SettlementEndToEndCertificatePacket | None = None
    rejection_reason: str | None = None
    try:
        if settlement_end_to_end_certificate_inputs.price_packet is not None:
            packet = build_settlement_end_to_end_certificate_packet_from_price_packet(
                settlement=settlement,
                proof_flags=settlement_end_to_end_certificate_inputs.proof_flags,
                price_history=settlement_end_to_end_certificate_inputs.price_history,
                feature_extension_inputs=settlement_end_to_end_certificate_inputs.feature_extension_inputs,
                price_packet=settlement_end_to_end_certificate_inputs.price_packet,
                lp_unit_values=settlement_end_to_end_certificate_inputs.lp_unit_values,
                pool_snapshots=settlement_end_to_end_certificate_inputs.pool_snapshots,
            )
        else:
            packet = build_settlement_end_to_end_certificate_packet_from_price_attestation(
                settlement=settlement,
                proof_flags=settlement_end_to_end_certificate_inputs.proof_flags,
                price_history=settlement_end_to_end_certificate_inputs.price_history,
                feature_extension_inputs=settlement_end_to_end_certificate_inputs.feature_extension_inputs,
                price_attestation=settlement_end_to_end_certificate_inputs.price_attestation,
                consumer_now_epoch=int(settlement_end_to_end_certificate_inputs.consumer_now_epoch),
                max_attestation_age_epochs=int(settlement_end_to_end_certificate_inputs.max_attestation_age_epochs),
                lp_unit_values=settlement_end_to_end_certificate_inputs.lp_unit_values,
                pool_snapshots=settlement_end_to_end_certificate_inputs.pool_snapshots,
                allowed_signers=settlement_end_to_end_certificate_inputs.allowed_signers,
            )
    except _LIFECYCLE_DOMAIN_ERRORS as exc:
        rejection_reason = str(exc)

    if packet is not None and not packet.packet_ok:
        rejection_reason = _end_to_end_packet_rejection_reason(packet)

    expired_reason = _expired_intent_reason(intents=intents, block_timestamp=int(block_timestamp))
    if expired_reason is not None:
        rejection_reason = expired_reason

    witness: DecisionWitness | None = None
    witness_valid = False
    if packet is not None and packet.packet_ok:
        try:
            witness = build_decision_witness_from_settlement_end_to_end_certificate_packet(
                settlement=settlement,
                packet=packet,
                expires_at=int(min_deadline),
            )
            witness_valid, witness_err = verify_decision_witness_against_settlement_end_to_end_certificate_packet(
                settlement=settlement,
                packet=packet,
                expires_at=int(min_deadline),
                witness_payload=witness.to_dict(),
            )
            if not witness_valid:
                rejection_reason = str(witness_err or "settlement decision witness invalid")
                witness = None
        except _LIFECYCLE_DOMAIN_ERRORS as exc:
            rejection_reason = str(exc)
            witness = None
            witness_valid = False

    settled = bool(witness_valid and packet is not None and packet.packet_ok and expired_reason is None)
    rejected_with_reason = not settled
    rejection_reason_present = bool(isinstance(rejection_reason, str) and rejection_reason.strip())
    if rejected_with_reason and not rejection_reason_present:
        rejection_reason = "settlement witness lifecycle missing rejection reason"
        rejection_reason_present = True

    return SettlementWitnessLifecyclePacket(
        decision_witness=witness,
        end_to_end_packet=packet,
        packet_built=bool(packet is not None),
        end_to_end_packet_ok=bool(packet is not None and packet.packet_ok),
        witness_present=bool(witness is not None),
        witness_valid=bool(witness_valid),
        before_expiry=before_expiry,
        settled=settled,
        rejected_with_reason=rejected_with_reason,
        rejection_reason_present=rejection_reason_present,
        rejection_reason=rejection_reason,
        lifecycle_ok=True,
    )


def verify_settlement_witness_lifecycle_packet_payload(
    *,
    intents: Sequence[Intent],
    settlement: Settlement,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable | None,
    block_timestamp: int,
    settlement_end_to_end_certificate_inputs: SettlementEndToEndCertificateInputs,
    packet_payload: object,
    settlement_validation: str = "strong_replay",
    swap_ordering: str = "greedy_ab_refined",
    quote_bindings_validated: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[str] = None,
) -> tuple[bool, str | None]:
    if not isinstance(packet_payload, Mapping):
        return False, "settlement witness lifecycle packet payload must be a dict"
    if str(packet_payload.get("schema", "")) != SETTLEMENT_WITNESS_LIFECYCLE_PACKET_SCHEMA:
        return False, "unsupported settlement witness lifecycle packet schema"
    try:
        expected = build_settlement_witness_lifecycle_packet(
            intents=intents,
            settlement=settlement,
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            block_timestamp=block_timestamp,
            settlement_end_to_end_certificate_inputs=settlement_end_to_end_certificate_inputs,
            settlement_validation=settlement_validation,
            swap_ordering=swap_ordering,
            quote_bindings_validated=quote_bindings_validated,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
    except _LIFECYCLE_DOMAIN_ERRORS as exc:
        return False, str(exc)
    if dict(packet_payload) != expected.to_dict():
        return False, "settlement witness lifecycle packet payload mismatch"
    return True, None


def _expired_intent_reason(*, intents: Sequence[Intent], block_timestamp: int) -> str | None:
    for intent in intents:
        if int(intent.deadline) < int(block_timestamp):
            return f"Intent expired: {intent.intent_id}"
    return None
