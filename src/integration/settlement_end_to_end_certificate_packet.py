from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Mapping, Sequence

from src.core.settlement import Settlement
from src.core.settlement_strong_validator import validate_settlement_strong

from .settlement_endogenous_lp_value_packet import (
    SettlementEndogenousLPValuePacket,
    _pool_from_dict,
    build_settlement_endogenous_lp_value_packet_from_price_attestation,
    build_settlement_endogenous_lp_value_packet_from_price_packet,
)
from .settlement_feature_extension_packet import (
    SettlementFeatureExtensionInputs,
    SettlementFeatureExtensionPacket,
    build_settlement_feature_extension_packet,
)
from .settlement_price_provenance import SettlementSpotPricePacket
from .settlement_strong_certificate import (
    SettlementProofFlags,
    SettlementStrongCertificate,
    build_replay_bound_settlement_strong_certificate,
    derive_replay_bound_certificate_flags,
    verify_settlement_strong_certificate,
)
from .settlement_value_packet import (
    SettlementValuePacket,
    build_settlement_value_packet_from_price_attestation,
    build_settlement_value_packet_from_price_packet,
)

if TYPE_CHECKING:
    from src.state.pools import PoolState

    from .settlement_price_attestation import SettlementSpotPriceAttestation


SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA = "zenodex/settlement-end-to-end-certificate-packet/v1"


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class SettlementEndToEndCertificateInputs:
    proof_flags: SettlementProofFlags
    price_history: tuple[int, int, int]
    feature_extension_inputs: SettlementFeatureExtensionInputs
    price_packet: SettlementSpotPricePacket | None = None
    price_attestation: SettlementSpotPriceAttestation | None = None
    consumer_now_epoch: int | None = None
    max_attestation_age_epochs: int | None = None
    lp_unit_values: Mapping[str, int] | None = None
    pool_snapshots: Sequence[PoolState] | None = None
    allowed_signers: Mapping[str, Sequence[str]] | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.proof_flags, SettlementProofFlags):
            raise TypeError("proof_flags must be a SettlementProofFlags")
        if not isinstance(self.feature_extension_inputs, SettlementFeatureExtensionInputs):
            raise TypeError("feature_extension_inputs must be a SettlementFeatureExtensionInputs")
        if (
            not isinstance(self.price_history, tuple)
            or len(self.price_history) != 3
            or any(not isinstance(v, int) or isinstance(v, bool) for v in self.price_history)
        ):
            raise ValueError("price_history must be a 3-tuple of ints")
        if (self.price_packet is None) == (self.price_attestation is None):
            raise ValueError("exactly one of price_packet or price_attestation must be provided")
        if self.price_packet is not None and not isinstance(self.price_packet, SettlementSpotPricePacket):
            raise TypeError("price_packet must be a SettlementSpotPricePacket")
        if self.price_attestation is not None:
            from .settlement_price_attestation import (
                SettlementSpotPriceAttestation as RuntimeSettlementSpotPriceAttestation,
            )

            if not isinstance(self.price_attestation, RuntimeSettlementSpotPriceAttestation):
                raise TypeError("price_attestation must be a SettlementSpotPriceAttestation")
            if self.consumer_now_epoch is None or self.max_attestation_age_epochs is None:
                raise ValueError(
                    "attestation mode requires consumer_now_epoch and max_attestation_age_epochs"
                )
            if not isinstance(self.consumer_now_epoch, int) or isinstance(self.consumer_now_epoch, bool):
                raise TypeError("consumer_now_epoch must be an int")
            if not isinstance(self.max_attestation_age_epochs, int) or isinstance(
                self.max_attestation_age_epochs, bool
            ):
                raise TypeError("max_attestation_age_epochs must be an int")
        _validate_value_mode_inputs(
            lp_unit_values=self.lp_unit_values,
            pool_snapshots=self.pool_snapshots,
        )


@dataclass(frozen=True)
class SettlementEndToEndCertificatePacket:
    price_input_kind: str
    value_packet_kind: str
    strong_certificate: SettlementStrongCertificate
    feature_extension_packet: SettlementFeatureExtensionPacket
    value_packet: SettlementValuePacket | None
    endogenous_lp_value_packet: SettlementEndogenousLPValuePacket | None
    strong_certificate_ok: bool
    feature_extension_packet_ok: bool
    module_bundle_ok: bool
    full_price_rails_ok: bool
    price_provenance_ok: bool
    attestation_ok: bool
    asset_conservation_ok: bool
    lp_liability_balanced_ok: bool
    value_conservation_ok: bool
    packet_ok: bool
    schema: str = SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.price_input_kind not in {"packet", "attestation"}:
            raise ValueError("price_input_kind must be 'packet' or 'attestation'")
        if self.value_packet_kind not in {"declared_value", "endogenous_lp_value"}:
            raise ValueError("value_packet_kind must be 'declared_value' or 'endogenous_lp_value'")
        if not isinstance(self.strong_certificate, SettlementStrongCertificate):
            raise TypeError("strong_certificate must be a SettlementStrongCertificate")
        if not isinstance(self.feature_extension_packet, SettlementFeatureExtensionPacket):
            raise TypeError("feature_extension_packet must be a SettlementFeatureExtensionPacket")
        if self.value_packet_kind == "declared_value":
            if not isinstance(self.value_packet, SettlementValuePacket) or self.endogenous_lp_value_packet is not None:
                raise ValueError("declared_value mode requires only value_packet")
            if self.price_input_kind != self.value_packet.price_input_kind:
                raise ValueError("price_input_kind must match nested value_packet")
        else:
            if (
                not isinstance(self.endogenous_lp_value_packet, SettlementEndogenousLPValuePacket)
                or self.value_packet is not None
            ):
                raise ValueError("endogenous_lp_value mode requires only endogenous_lp_value_packet")
            if self.price_input_kind != self.endogenous_lp_value_packet.price_input_kind:
                raise ValueError("price_input_kind must match nested endogenous_lp_value_packet")
        for name in (
            "strong_certificate_ok",
            "feature_extension_packet_ok",
            "module_bundle_ok",
            "full_price_rails_ok",
            "price_provenance_ok",
            "attestation_ok",
            "asset_conservation_ok",
            "lp_liability_balanced_ok",
            "value_conservation_ok",
            "packet_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "price_input_kind": self.price_input_kind,
            "value_packet_kind": self.value_packet_kind,
            "strong_certificate": self.strong_certificate.to_dict(),
            "feature_extension_packet": self.feature_extension_packet.to_dict(),
            "value_packet": None if self.value_packet is None else self.value_packet.to_dict(),
            "endogenous_lp_value_packet": (
                None if self.endogenous_lp_value_packet is None else self.endogenous_lp_value_packet.to_dict()
            ),
            "strong_certificate_ok": bool(self.strong_certificate_ok),
            "feature_extension_packet_ok": bool(self.feature_extension_packet_ok),
            "module_bundle_ok": bool(self.module_bundle_ok),
            "full_price_rails_ok": bool(self.full_price_rails_ok),
            "price_provenance_ok": bool(self.price_provenance_ok),
            "attestation_ok": bool(self.attestation_ok),
            "asset_conservation_ok": bool(self.asset_conservation_ok),
            "lp_liability_balanced_ok": bool(self.lp_liability_balanced_ok),
            "value_conservation_ok": bool(self.value_conservation_ok),
            "packet_ok": bool(self.packet_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementEndToEndCertificatePacket":
        if not isinstance(payload, Mapping):
            raise ValueError("packet must be an object")
        value_packet_payload = payload.get("value_packet")
        endogenous_lp_value_packet_payload = payload.get("endogenous_lp_value_packet")
        return cls(
            schema=str(payload.get("schema", "")),
            price_input_kind=str(payload.get("price_input_kind", "")),
            value_packet_kind=str(payload.get("value_packet_kind", "")),
            strong_certificate=SettlementStrongCertificate.from_dict(payload.get("strong_certificate", {})),
            feature_extension_packet=SettlementFeatureExtensionPacket.from_dict(
                payload.get("feature_extension_packet", {})
            ),
            value_packet=(
                None if value_packet_payload is None else SettlementValuePacket.from_dict(value_packet_payload)
            ),
            endogenous_lp_value_packet=(
                None
                if endogenous_lp_value_packet_payload is None
                else SettlementEndogenousLPValuePacket.from_dict(endogenous_lp_value_packet_payload)
            ),
            strong_certificate_ok=_require_bool(payload["strong_certificate_ok"], name="strong_certificate_ok"),
            feature_extension_packet_ok=_require_bool(
                payload["feature_extension_packet_ok"],
                name="feature_extension_packet_ok",
            ),
            module_bundle_ok=_require_bool(payload["module_bundle_ok"], name="module_bundle_ok"),
            full_price_rails_ok=_require_bool(payload["full_price_rails_ok"], name="full_price_rails_ok"),
            price_provenance_ok=_require_bool(payload["price_provenance_ok"], name="price_provenance_ok"),
            attestation_ok=_require_bool(payload["attestation_ok"], name="attestation_ok"),
            asset_conservation_ok=_require_bool(payload["asset_conservation_ok"], name="asset_conservation_ok"),
            lp_liability_balanced_ok=_require_bool(
                payload["lp_liability_balanced_ok"],
                name="lp_liability_balanced_ok",
            ),
            value_conservation_ok=_require_bool(payload["value_conservation_ok"], name="value_conservation_ok"),
            packet_ok=_require_bool(payload["packet_ok"], name="packet_ok"),
        )


def build_settlement_end_to_end_certificate_packet_from_price_packet(
    *,
    settlement: Settlement,
    proof_flags: SettlementProofFlags,
    price_history: tuple[int, int, int],
    feature_extension_inputs: SettlementFeatureExtensionInputs,
    price_packet: SettlementSpotPricePacket,
    lp_unit_values: Mapping[str, int] | None = None,
    pool_snapshots: Sequence[PoolState] | None = None,
) -> SettlementEndToEndCertificatePacket:
    _validate_value_mode_inputs(lp_unit_values=lp_unit_values, pool_snapshots=pool_snapshots)
    feature_extension_packet = build_settlement_feature_extension_packet(feature_extension_inputs)
    effective_flags = _internalize_feature_extension_flags(
        proof_flags=proof_flags,
        feature_extension_packet=feature_extension_packet,
    )
    strong_certificate = build_replay_bound_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=effective_flags,
        price_history=price_history,
    )
    strong_certificate_ok, err = verify_settlement_strong_certificate(
        settlement=settlement,
        certificate=strong_certificate,
    )
    if not strong_certificate_ok:
        raise ValueError(f"invalid settlement strong certificate: {err}")
    if pool_snapshots is None:
        nested = build_settlement_value_packet_from_price_packet(
            settlement=settlement,
            price_packet=price_packet,
            lp_unit_values=lp_unit_values,
        )
        return _assemble_packet(
            price_input_kind="packet",
            value_packet_kind="declared_value",
            strong_certificate=strong_certificate,
            strong_certificate_ok=strong_certificate_ok,
            feature_extension_packet=feature_extension_packet,
            value_packet=nested,
            endogenous_lp_value_packet=None,
        )
    nested_endogenous = build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        pool_snapshots=pool_snapshots,
    )
    return _assemble_packet(
        price_input_kind="packet",
        value_packet_kind="endogenous_lp_value",
        strong_certificate=strong_certificate,
        strong_certificate_ok=strong_certificate_ok,
        feature_extension_packet=feature_extension_packet,
        value_packet=None,
        endogenous_lp_value_packet=nested_endogenous,
    )


def build_settlement_end_to_end_certificate_packet_from_price_attestation(
    *,
    settlement: Settlement,
    proof_flags: SettlementProofFlags,
    price_history: tuple[int, int, int],
    feature_extension_inputs: SettlementFeatureExtensionInputs,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    lp_unit_values: Mapping[str, int] | None = None,
    pool_snapshots: Sequence[PoolState] | None = None,
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
) -> SettlementEndToEndCertificatePacket:
    _validate_value_mode_inputs(lp_unit_values=lp_unit_values, pool_snapshots=pool_snapshots)
    feature_extension_packet = build_settlement_feature_extension_packet(feature_extension_inputs)
    effective_flags = _internalize_feature_extension_flags(
        proof_flags=proof_flags,
        feature_extension_packet=feature_extension_packet,
    )
    strong_certificate = build_replay_bound_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=effective_flags,
        price_history=price_history,
    )
    strong_certificate_ok, err = verify_settlement_strong_certificate(
        settlement=settlement,
        certificate=strong_certificate,
    )
    if not strong_certificate_ok:
        raise ValueError(f"invalid settlement strong certificate: {err}")
    if pool_snapshots is None:
        nested = build_settlement_value_packet_from_price_attestation(
            settlement=settlement,
            price_attestation=price_attestation,
            consumer_now_epoch=consumer_now_epoch,
            max_attestation_age_epochs=max_attestation_age_epochs,
            lp_unit_values=lp_unit_values,
            allowed_signers=allowed_signers,
        )
        return _assemble_packet(
            price_input_kind="attestation",
            value_packet_kind="declared_value",
            strong_certificate=strong_certificate,
            strong_certificate_ok=strong_certificate_ok,
            feature_extension_packet=feature_extension_packet,
            value_packet=nested,
            endogenous_lp_value_packet=None,
        )
    nested_endogenous = build_settlement_end_to_end_endogenous_from_attestation(
        settlement=settlement,
        price_attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        pool_snapshots=pool_snapshots,
        allowed_signers=allowed_signers,
    )
    return _assemble_packet(
        price_input_kind="attestation",
        value_packet_kind="endogenous_lp_value",
        strong_certificate=strong_certificate,
        strong_certificate_ok=strong_certificate_ok,
        feature_extension_packet=feature_extension_packet,
        value_packet=None,
        endogenous_lp_value_packet=nested_endogenous,
    )


def verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
    *,
    settlement: Settlement,
    proof_flags: SettlementProofFlags,
    price_history: tuple[int, int, int],
    feature_extension_inputs_payload: Mapping[str, Any],
    price_packet_payload: Mapping[str, Any],
    packet_payload: Mapping[str, Any],
    lp_unit_values: Mapping[str, int] | None = None,
    pool_snapshots_payload: Sequence[Mapping[str, Any]] | None = None,
) -> tuple[bool, str | None]:
    try:
        price_packet = SettlementSpotPricePacket.from_dict(price_packet_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, str(exc)
    try:
        pool_snapshots = None
        if pool_snapshots_payload is not None:
            pool_snapshots = tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_payload)
        expected = build_settlement_end_to_end_certificate_packet_from_price_packet(
            settlement=settlement,
            proof_flags=proof_flags,
            price_history=price_history,
            feature_extension_inputs=SettlementFeatureExtensionInputs.from_dict(feature_extension_inputs_payload),
            price_packet=price_packet,
            lp_unit_values=lp_unit_values,
            pool_snapshots=pool_snapshots,
        )
    except (TypeError, ValueError, KeyError) as exc:
        return False, str(exc)
    if not isinstance(packet_payload, Mapping):
        return False, "packet must be an object"
    if str(packet_payload.get("schema", "")) != expected.schema:
        return False, "schema mismatch"
    if dict(packet_payload) != expected.to_dict():
        return False, "settlement end-to-end certificate packet mismatch"
    return True, None


def enforce_settlement_end_to_end_certificate(
    *,
    settlement: Settlement,
    certificate_inputs: SettlementEndToEndCertificateInputs,
    intents: list[Any],
    pre_balances: Any,
    pre_pools: Mapping[str, Any],
    pre_lp_balances: Any | None = None,
    mode: str = "strong_replay",
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[str] = None,
) -> tuple[bool, str | None, SettlementEndToEndCertificatePacket | None]:
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=intents,
        pre_balances=pre_balances,
        pre_pools=dict(pre_pools),
        pre_lp_balances=pre_lp_balances,
        mode=mode,
        allow_cow_netting=allow_cow_netting,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    if not ok:
        return False, err, None

    effective_flags = derive_replay_bound_certificate_flags(certificate_inputs.proof_flags)
    try:
        if certificate_inputs.price_packet is not None:
            packet = build_settlement_end_to_end_certificate_packet_from_price_packet(
                settlement=settlement,
                proof_flags=effective_flags,
                price_history=certificate_inputs.price_history,
                feature_extension_inputs=certificate_inputs.feature_extension_inputs,
                price_packet=certificate_inputs.price_packet,
                lp_unit_values=certificate_inputs.lp_unit_values,
                pool_snapshots=certificate_inputs.pool_snapshots,
            )
        else:
            packet = build_settlement_end_to_end_certificate_packet_from_price_attestation(
                settlement=settlement,
                proof_flags=effective_flags,
                price_history=certificate_inputs.price_history,
                feature_extension_inputs=certificate_inputs.feature_extension_inputs,
                price_attestation=certificate_inputs.price_attestation,
                consumer_now_epoch=int(certificate_inputs.consumer_now_epoch),
                max_attestation_age_epochs=int(certificate_inputs.max_attestation_age_epochs),
                lp_unit_values=certificate_inputs.lp_unit_values,
                pool_snapshots=certificate_inputs.pool_snapshots,
                allowed_signers=certificate_inputs.allowed_signers,
            )
    except (TypeError, ValueError, KeyError) as exc:
        return False, str(exc), None

    if not packet.packet_ok:
        return False, _end_to_end_packet_rejection_reason(packet), None
    return True, None, packet


def verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation(
    *,
    settlement: Settlement,
    proof_flags: SettlementProofFlags,
    price_history: tuple[int, int, int],
    feature_extension_inputs_payload: Mapping[str, Any],
    price_attestation_payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    packet_payload: Mapping[str, Any],
    lp_unit_values: Mapping[str, int] | None = None,
    pool_snapshots_payload: Sequence[Mapping[str, Any]] | None = None,
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
) -> tuple[bool, str | None]:
    from .settlement_price_attestation import SettlementSpotPriceAttestation

    try:
        price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, str(exc)
    try:
        pool_snapshots = None
        if pool_snapshots_payload is not None:
            pool_snapshots = tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_payload)
        expected = build_settlement_end_to_end_certificate_packet_from_price_attestation(
            settlement=settlement,
            proof_flags=proof_flags,
            price_history=price_history,
            feature_extension_inputs=SettlementFeatureExtensionInputs.from_dict(feature_extension_inputs_payload),
            price_attestation=price_attestation,
            consumer_now_epoch=consumer_now_epoch,
            max_attestation_age_epochs=max_attestation_age_epochs,
            lp_unit_values=lp_unit_values,
            pool_snapshots=pool_snapshots,
            allowed_signers=allowed_signers,
        )
    except (TypeError, ValueError, KeyError) as exc:
        return False, str(exc)
    if not isinstance(packet_payload, Mapping):
        return False, "packet must be an object"
    if str(packet_payload.get("schema", "")) != expected.schema:
        return False, "schema mismatch"
    if dict(packet_payload) != expected.to_dict():
        return False, "settlement end-to-end certificate packet mismatch"
    return True, None


def _assemble_packet(
    *,
    price_input_kind: str,
    value_packet_kind: str,
    strong_certificate: SettlementStrongCertificate,
    strong_certificate_ok: bool,
    feature_extension_packet: SettlementFeatureExtensionPacket,
    value_packet: SettlementValuePacket | None,
    endogenous_lp_value_packet: SettlementEndogenousLPValuePacket | None,
) -> SettlementEndToEndCertificatePacket:
    if value_packet is not None:
        price_provenance_ok = bool(value_packet.price_provenance_ok)
        attestation_ok = bool(value_packet.attestation_ok)
        asset_conservation_ok = bool(value_packet.asset_conservation_ok)
        lp_liability_balanced_ok = bool(value_packet.lp_liability_balanced_ok)
        value_conservation_ok = bool(value_packet.value_conservation_ok)
        value_packet_ok = bool(value_packet.packet_ok)
    else:
        if endogenous_lp_value_packet is None:
            raise ValueError("endogenous_lp_value_packet required when value_packet is absent")
        price_provenance_ok = bool(endogenous_lp_value_packet.price_provenance_ok)
        attestation_ok = bool(endogenous_lp_value_packet.attestation_ok)
        asset_conservation_ok = bool(endogenous_lp_value_packet.asset_conservation_ok)
        lp_liability_balanced_ok = bool(endogenous_lp_value_packet.lp_liability_balanced_ok)
        value_conservation_ok = bool(endogenous_lp_value_packet.value_conservation_ok)
        value_packet_ok = bool(endogenous_lp_value_packet.packet_ok)
    feature_extension_packet_ok = bool(feature_extension_packet.packet_ok)
    module_bundle_ok = bool(strong_certificate.module_bundle_ok == 1)
    full_price_rails_ok = bool(strong_certificate.full_price_rails_ok == 1)
    return SettlementEndToEndCertificatePacket(
        price_input_kind=price_input_kind,
        value_packet_kind=value_packet_kind,
        strong_certificate=strong_certificate,
        feature_extension_packet=feature_extension_packet,
        value_packet=value_packet,
        endogenous_lp_value_packet=endogenous_lp_value_packet,
        strong_certificate_ok=bool(strong_certificate_ok),
        feature_extension_packet_ok=feature_extension_packet_ok,
        module_bundle_ok=module_bundle_ok,
        full_price_rails_ok=full_price_rails_ok,
        price_provenance_ok=price_provenance_ok,
        attestation_ok=attestation_ok,
        asset_conservation_ok=asset_conservation_ok,
        lp_liability_balanced_ok=lp_liability_balanced_ok,
        value_conservation_ok=value_conservation_ok,
        packet_ok=bool(
            strong_certificate_ok
            and feature_extension_packet_ok
            and module_bundle_ok
            and full_price_rails_ok
            and value_packet_ok
        ),
    )


def _end_to_end_packet_rejection_reason(packet: SettlementEndToEndCertificatePacket) -> str:
    if not packet.strong_certificate_ok:
        return "settlement end-to-end certificate strong certificate rejected"
    if not packet.feature_extension_packet_ok:
        return "settlement end-to-end certificate feature extension rejected"
    if not packet.module_bundle_ok:
        return "settlement end-to-end certificate module bundle rejected"
    if not packet.full_price_rails_ok:
        return "settlement end-to-end certificate full price rails rejected"
    if not packet.price_provenance_ok:
        return "settlement end-to-end certificate price provenance rejected"
    if packet.price_input_kind == "attestation" and not packet.attestation_ok:
        return "settlement end-to-end certificate attestation rejected"
    if not packet.asset_conservation_ok:
        return "settlement end-to-end certificate asset conservation rejected"
    if packet.value_packet_kind == "endogenous_lp_value" and not packet.lp_liability_balanced_ok:
        return "settlement end-to-end certificate LP liability rejected"
    if not packet.value_conservation_ok:
        return "settlement end-to-end certificate value conservation rejected"
    return "settlement end-to-end certificate packet rejected"


def _validate_value_mode_inputs(
    *,
    lp_unit_values: Mapping[str, int] | None,
    pool_snapshots: Sequence[PoolState] | None,
) -> None:
    if lp_unit_values is not None and pool_snapshots is not None:
        raise ValueError("lp_unit_values and pool_snapshots are mutually exclusive")


def build_settlement_end_to_end_endogenous_from_attestation(
    *,
    settlement: Settlement,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    pool_snapshots: Sequence[PoolState],
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
) -> SettlementEndogenousLPValuePacket:
    return build_settlement_endogenous_lp_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        pool_snapshots=pool_snapshots,
        allowed_signers=allowed_signers,
    )


def _internalize_feature_extension_flags(
    *,
    proof_flags: SettlementProofFlags,
    feature_extension_packet: SettlementFeatureExtensionPacket,
) -> SettlementProofFlags:
    return SettlementProofFlags(
        cpmm_ok=int(proof_flags.cpmm_ok),
        balance_ok=int(proof_flags.balance_ok),
        token_ok=int(proof_flags.token_ok),
        buyback_floor_ok=int(feature_extension_packet.buyback_floor_ok),
        buyback_floor_fixedpoint_ok=int(feature_extension_packet.buyback_floor_fixedpoint_ok),
        rebate_ok=int(feature_extension_packet.rebate_ok),
        lock_weight_ok=int(feature_extension_packet.lock_weight_ok),
        proof_ok=int(proof_flags.proof_ok),
        binding_ok=int(proof_flags.binding_ok),
    )
