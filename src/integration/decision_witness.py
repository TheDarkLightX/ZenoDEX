from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


DECISION_WITNESS_SCHEMA = "zenodex/decision-witness/v1"
ALLOWED_DECISION_WITNESS_KINDS = {
    "exact_in_route",
    "exact_out_route",
    "batch_winner",
    "settlement_step",
    "autotrader_binary_decision",
    "autotrader_multiaction_decision",
}


def _is_nonempty_string(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _require_nonempty_string(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _as_plain_dict(value: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if value is None:
        return None
    return dict(value)


def _payload_digest_hex(label: str, payload: Mapping[str, Any]) -> str:
    return sha256_hex(
        domain_sep_bytes(f"decision_witness::{label}", version=1) + canonical_json_bytes(dict(payload))
    )


def _build_binding(
    *,
    binding_kind: str,
    binding_id: str,
    payload: Mapping[str, Any],
) -> "DecisionWitnessBinding":
    return DecisionWitnessBinding(
        binding_kind=binding_kind,
        binding_id=binding_id,
        binding_digest=_payload_digest_hex(f"binding::{binding_kind}", payload),
        payload=dict(payload),
    )


def _canonical_key_from_payload(value: object) -> tuple[int | str | bool, ...]:
    if not isinstance(value, list):
        raise ValueError("canonical_key must be a list")
    out: list[int | str | bool] = []
    for item in value:
        if isinstance(item, bool):
            out.append(item)
        elif isinstance(item, int):
            out.append(item)
        elif isinstance(item, str):
            out.append(item)
        else:
            raise ValueError("canonical_key items must be int, str, or bool")
    return tuple(out)


@dataclass(frozen=True)
class DecisionWitnessBinding:
    binding_kind: str
    binding_id: str
    binding_digest: str
    payload: Mapping[str, Any] | None = None

    def __post_init__(self) -> None:
        if not _is_nonempty_string(self.binding_kind):
            raise ValueError("binding_kind must be a non-empty string")
        if not _is_nonempty_string(self.binding_id):
            raise ValueError("binding_id must be a non-empty string")
        if not _is_nonempty_string(self.binding_digest):
            raise ValueError("binding_digest must be a non-empty string")
        if self.payload is not None and not isinstance(self.payload, Mapping):
            raise TypeError("payload must be a mapping")

    def to_dict(self) -> dict[str, Any]:
        return {
            "binding_kind": self.binding_kind,
            "binding_id": self.binding_id,
            "binding_digest": self.binding_digest,
            "payload": _as_plain_dict(self.payload),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "DecisionWitnessBinding":
        if not isinstance(payload, Mapping):
            raise ValueError("binding must be an object")
        nested_payload = payload.get("payload")
        if nested_payload is not None and not isinstance(nested_payload, Mapping):
            raise ValueError("binding.payload must be an object when present")
        return cls(
            binding_kind=_require_nonempty_string(payload.get("binding_kind"), name="binding_kind"),
            binding_id=_require_nonempty_string(payload.get("binding_id"), name="binding_id"),
            binding_digest=_require_nonempty_string(payload.get("binding_digest"), name="binding_digest"),
            payload=None if nested_payload is None else dict(nested_payload),
        )


@dataclass(frozen=True)
class DecisionWitness:
    witness_kind: str
    state_binding: DecisionWitnessBinding
    request_binding: DecisionWitnessBinding
    quote_binding: DecisionWitnessBinding | None
    epoch_binding: DecisionWitnessBinding | None
    expires_at: int | None
    feasibility_payload: Mapping[str, Any]
    canonical_key: tuple[int | str | bool, ...]
    accounting_receipt: Mapping[str, Any] | None
    proof_payload: Mapping[str, Any] | None
    metadata: Mapping[str, Any] | None = None
    schema: str = DECISION_WITNESS_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != DECISION_WITNESS_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.witness_kind not in ALLOWED_DECISION_WITNESS_KINDS:
            raise ValueError(
                "witness_kind must be one of "
                + ", ".join(sorted(ALLOWED_DECISION_WITNESS_KINDS))
            )
        if not isinstance(self.state_binding, DecisionWitnessBinding):
            raise TypeError("state_binding must be a DecisionWitnessBinding")
        if not isinstance(self.request_binding, DecisionWitnessBinding):
            raise TypeError("request_binding must be a DecisionWitnessBinding")
        if self.quote_binding is not None and not isinstance(self.quote_binding, DecisionWitnessBinding):
            raise TypeError("quote_binding must be a DecisionWitnessBinding when present")
        if self.epoch_binding is not None and not isinstance(self.epoch_binding, DecisionWitnessBinding):
            raise TypeError("epoch_binding must be a DecisionWitnessBinding when present")
        if self.expires_at is not None and (not isinstance(self.expires_at, int) or isinstance(self.expires_at, bool)):
            raise TypeError("expires_at must be an int when present")
        if not isinstance(self.feasibility_payload, Mapping):
            raise TypeError("feasibility_payload must be a mapping")
        if not isinstance(self.canonical_key, tuple):
            raise TypeError("canonical_key must be a tuple")
        for item in self.canonical_key:
            if not isinstance(item, (int, str, bool)):
                raise TypeError("canonical_key items must be int, str, or bool")
        if self.accounting_receipt is not None and not isinstance(self.accounting_receipt, Mapping):
            raise TypeError("accounting_receipt must be a mapping when present")
        if self.proof_payload is not None and not isinstance(self.proof_payload, Mapping):
            raise TypeError("proof_payload must be a mapping when present")
        if self.metadata is not None and not isinstance(self.metadata, Mapping):
            raise TypeError("metadata must be a mapping when present")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "witness_kind": self.witness_kind,
            "state_binding": self.state_binding.to_dict(),
            "request_binding": self.request_binding.to_dict(),
            "quote_binding": None if self.quote_binding is None else self.quote_binding.to_dict(),
            "epoch_binding": None if self.epoch_binding is None else self.epoch_binding.to_dict(),
            "expires_at": self.expires_at,
            "feasibility_payload": dict(self.feasibility_payload),
            "canonical_key": list(self.canonical_key),
            "accounting_receipt": _as_plain_dict(self.accounting_receipt),
            "proof_payload": _as_plain_dict(self.proof_payload),
            "metadata": _as_plain_dict(self.metadata),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "DecisionWitness":
        if not isinstance(payload, Mapping):
            raise ValueError("witness must be an object")
        state_binding_payload = payload.get("state_binding")
        request_binding_payload = payload.get("request_binding")
        if not isinstance(state_binding_payload, Mapping):
            raise ValueError("state_binding must be an object")
        if not isinstance(request_binding_payload, Mapping):
            raise ValueError("request_binding must be an object")
        quote_binding_payload = payload.get("quote_binding")
        epoch_binding_payload = payload.get("epoch_binding")
        feasibility_payload = payload.get("feasibility_payload")
        if not isinstance(feasibility_payload, Mapping):
            raise ValueError("feasibility_payload must be an object")
        accounting_receipt = payload.get("accounting_receipt")
        proof_payload = payload.get("proof_payload")
        metadata = payload.get("metadata")
        for name, value in (
            ("accounting_receipt", accounting_receipt),
            ("proof_payload", proof_payload),
            ("metadata", metadata),
        ):
            if value is not None and not isinstance(value, Mapping):
                raise ValueError(f"{name} must be an object when present")
        expires_at = payload.get("expires_at")
        if expires_at is not None and (not isinstance(expires_at, int) or isinstance(expires_at, bool)):
            raise ValueError("expires_at must be an int when present")
        return cls(
            schema=str(payload.get("schema", "")),
            witness_kind=str(payload.get("witness_kind", "")),
            state_binding=DecisionWitnessBinding.from_dict(state_binding_payload),
            request_binding=DecisionWitnessBinding.from_dict(request_binding_payload),
            quote_binding=(
                None
                if quote_binding_payload is None
                else DecisionWitnessBinding.from_dict(quote_binding_payload)
            ),
            epoch_binding=(
                None
                if epoch_binding_payload is None
                else DecisionWitnessBinding.from_dict(epoch_binding_payload)
            ),
            expires_at=expires_at,
            feasibility_payload=dict(feasibility_payload),
            canonical_key=_canonical_key_from_payload(payload.get("canonical_key")),
            accounting_receipt=None if accounting_receipt is None else dict(accounting_receipt),
            proof_payload=None if proof_payload is None else dict(proof_payload),
            metadata=None if metadata is None else dict(metadata),
        )


def verify_decision_witness_payload(
    payload: object,
    *,
    expected_witness_kind: str | None = None,
) -> tuple[bool, str | None]:
    try:
        witness = DecisionWitness.from_dict(payload)  # type: ignore[arg-type]
    except Exception as exc:
        return False, str(exc)
    if expected_witness_kind is not None and witness.witness_kind != expected_witness_kind:
        return False, "decision witness kind mismatch"
    return True, None


def _quote_receipt_from_exact_in_payload(winner_quote_payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "amount_in": int(winner_quote_payload["amount_in"]),
        "amount_out": int(winner_quote_payload["amount_out"]),
        "leg_count": len(list(winner_quote_payload.get("legs", ()))),
        "winner_quote": dict(winner_quote_payload),
    }


def _quote_receipt_from_exact_out_payload(winner_quote_payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "amount_out_total": int(winner_quote_payload["amount_out_total"]),
        "amount_in_total": int(winner_quote_payload["amount_in_total"]),
        "leg_count": len(list(winner_quote_payload.get("legs", ()))),
        "winner_quote": dict(winner_quote_payload),
    }


def _settlement_normalized_payload(settlement: object) -> dict[str, Any]:
    from src.core.settlement import Settlement
    from src.core.settlement_normal_form import normalize_settlement_op_for_commitment
    from src.integration.operations import create_settlement_operation

    if not isinstance(settlement, Settlement):
        raise TypeError("settlement must be a Settlement")
    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, Mapping):
        raise TypeError("internal error: settlement operation must be a dict")
    return normalize_settlement_op_for_commitment(op)


def _settlement_value_lane_payload(packet_payload: Mapping[str, Any]) -> dict[str, Any]:
    if packet_payload.get("value_packet") is not None:
        return dict(packet_payload["value_packet"])
    return dict(packet_payload["endogenous_lp_value_packet"])


def _settlement_epoch_binding_from_packet_payload(
    packet_payload: Mapping[str, Any],
) -> DecisionWitnessBinding:
    value_lane_payload = _settlement_value_lane_payload(packet_payload)
    price_packet_payload = dict(value_lane_payload["price_packet"])
    if value_lane_payload.get("price_attestation") is not None:
        attestation_payload = dict(value_lane_payload["price_attestation"])
        signed_at_epoch = int(attestation_payload["signed_at_epoch"])
        return _build_binding(
            binding_kind="settlement_attestation_epoch",
            binding_id=str(signed_at_epoch),
            payload={
                "signed_at_epoch": signed_at_epoch,
                "packet_now_epoch": int(price_packet_payload["now_epoch"]),
                "max_staleness_epochs": int(price_packet_payload["max_staleness_epochs"]),
            },
        )
    now_epoch = int(price_packet_payload["now_epoch"])
    return _build_binding(
        binding_kind="settlement_price_epoch",
        binding_id=str(now_epoch),
        payload={
            "now_epoch": now_epoch,
            "max_staleness_epochs": int(price_packet_payload["max_staleness_epochs"]),
        },
    )


def _flatten_settlement_canonical_key(
    *,
    settlement_commitment_sha256: str,
    delta_commitment_sha256: str,
    price_input_kind: str,
    value_packet_kind: str,
) -> tuple[int | str | bool, ...]:
    return (
        settlement_commitment_sha256,
        delta_commitment_sha256,
        price_input_kind,
        value_packet_kind,
    )


def _flatten_exact_out_canonical_key(route_key: object) -> tuple[int | str | bool, ...]:
    amount_in_total = int(getattr(route_key, "amount_in_total"))
    leg_count = int(getattr(route_key, "leg_count"))
    legs_lex = tuple(getattr(route_key, "legs_lex"))
    return (
        amount_in_total,
        leg_count,
        *[f"{str(pool_id)}:{int(amount_out)}" for pool_id, amount_out in legs_lex],
    )


def _autotrader_accounting_receipt_from_observation_payload(
    observation_payload: Mapping[str, Any],
) -> dict[str, Any]:
    primary_signal = observation_payload["primary_signal"]
    return {
        "current_epoch": int(observation_payload["current_epoch"]),
        "asset_in": str(primary_signal["asset_in"]),
        "asset_out": str(primary_signal["asset_out"]),
        "amount_in": int(primary_signal["amount_in"]),
        "amount_out": int(primary_signal["amount_out"]),
        "primary_signal": dict(primary_signal),
    }


def build_decision_witness_from_exact_in_true_key_interpretation_packet(
    packet: object,
    *,
    epoch_binding: DecisionWitnessBinding | None = None,
    expires_at: int | None = None,
    metadata: Mapping[str, Any] | None = None,
) -> DecisionWitness:
    from src.integration.exact_in_route_certificate import (
        ExactInRouteTrueKeyInterpretationPacket,
        exact_in_route_canonical_key,
    )

    if not isinstance(packet, ExactInRouteTrueKeyInterpretationPacket):
        raise TypeError("packet must be an ExactInRouteTrueKeyInterpretationPacket")
    if not packet.packet_ok:
        raise ValueError("exact-in true-key interpretation packet must be packet_ok")

    payload = packet.to_dict()
    certificate_payload = payload["certificate"]
    winner_quote_payload = certificate_payload["winner_quote"]
    candidate_count = len(certificate_payload["candidates"])
    winner_key = exact_in_route_canonical_key(packet.certificate.winner_quote)
    source_packet_digest = _payload_digest_hex("exact_in_true_key_interpretation_packet", payload)

    state_payload = {
        "asset_in": packet.asset_in,
        "asset_out": packet.asset_out,
        "amount_in": int(packet.amount_in),
        "candidate_set_hash": packet.candidate_set_hash,
        "candidate_count": int(candidate_count),
    }
    request_payload = {
        "asset_in": packet.asset_in,
        "asset_out": packet.asset_out,
        "amount_in": int(packet.amount_in),
    }
    quote_payload = dict(winner_quote_payload)
    proof_payload = {
        "source_packet_schema": str(packet.schema),
        "source_packet_digest": source_packet_digest,
        "certificate_schema": str(packet.certificate.schema),
        "certificate_hash": str(packet.certificate.certificate_hash_hex()),
        "rank_projection_packet_ok": bool(packet.rank_projection_packet.packet_ok),
        "winner_index": int(packet.certificate.winner_index),
        "winner_route_key_rank_u64": int(packet.certificate.winner_route_key_rank_u64),
        "candidate_set_hash": str(packet.candidate_set_hash),
        "packet_ok": bool(packet.packet_ok),
    }
    feasibility_payload = {
        "packet_ok": bool(packet.packet_ok),
        "rank_projection_packet_ok": bool(packet.rank_projection_packet.packet_ok),
        "winner_index_in_range": bool(packet.winner_index_in_range),
        "candidate_indices_match_stream": bool(packet.candidate_indices_match_stream),
        "candidate_route_keys_match_quotes": bool(packet.candidate_route_keys_match_quotes),
        "winner_matches_certificate_candidate": bool(packet.winner_matches_certificate_candidate),
        "winner_true_key_minimal": bool(packet.winner_true_key_minimal),
    }

    return DecisionWitness(
        witness_kind="exact_in_route",
        state_binding=_build_binding(
            binding_kind="exact_in_candidate_set",
            binding_id=str(packet.candidate_set_hash),
            payload=state_payload,
        ),
        request_binding=_build_binding(
            binding_kind="exact_in_request",
            binding_id=f"{packet.asset_in}->{packet.asset_out}:{int(packet.amount_in)}",
            payload=request_payload,
        ),
        quote_binding=_build_binding(
            binding_kind="exact_in_winner_quote",
            binding_id=source_packet_digest,
            payload=quote_payload,
        ),
        epoch_binding=epoch_binding,
        expires_at=expires_at,
        feasibility_payload=feasibility_payload,
        canonical_key=tuple(winner_key),
        accounting_receipt=_quote_receipt_from_exact_in_payload(winner_quote_payload),
        proof_payload=proof_payload,
        metadata={
            "source_adapter": "exact_in_true_key_interpretation_packet",
            "source_schema": str(packet.schema),
            **({} if metadata is None else dict(metadata)),
        },
    )


def verify_decision_witness_against_exact_in_true_key_interpretation_packet(
    packet: object,
    witness_payload: object,
) -> tuple[bool, str | None]:
    try:
        expected = build_decision_witness_from_exact_in_true_key_interpretation_packet(packet)
    except Exception as exc:
        return False, str(exc)
    ok, err = verify_decision_witness_payload(witness_payload, expected_witness_kind="exact_in_route")
    if not ok:
        return ok, err
    try:
        witness = DecisionWitness.from_dict(witness_payload)  # type: ignore[arg-type]
    except Exception as exc:
        return False, str(exc)
    if witness.to_dict() != expected.to_dict():
        return False, "decision witness payload mismatch for exact-in packet"
    return True, None


def build_decision_witness_from_exact_out_repaired_key_cover_interpretation_packet(
    packet: object,
    *,
    epoch_binding: DecisionWitnessBinding | None = None,
    expires_at: int | None = None,
    metadata: Mapping[str, Any] | None = None,
) -> DecisionWitness:
    from src.core.split_routing_dispatch import exact_out_route_canonical_key
    from src.integration.exact_out_route_certificate import (
        ExactOutManyPoolRepairedKeyCoverInterpretationPacket,
    )

    if not isinstance(packet, ExactOutManyPoolRepairedKeyCoverInterpretationPacket):
        raise TypeError("packet must be an ExactOutManyPoolRepairedKeyCoverInterpretationPacket")
    if not packet.packet_ok:
        raise ValueError("repaired exact-out key-cover interpretation packet must be packet_ok")

    payload = packet.to_dict()
    key_cover_payload = payload["key_cover_packet"]
    selected_domain_payload = key_cover_payload["selected_domain_contract"]
    repaired_full_domain_payload = key_cover_payload["repaired_full_domain_packet"]
    repaired_contract_payload = selected_domain_payload["repaired_contract"]
    runtime_quote_payload = selected_domain_payload["repaired_selected_domain_runtime_quote"]
    full_domain_quote_payload = repaired_full_domain_payload["full_domain_canonical_quote"]
    selected_domain_contract = packet.key_cover_packet.selected_domain_contract
    runtime_quote = selected_domain_contract.audit.runtime_quote
    winner_key = exact_out_route_canonical_key(runtime_quote)
    source_packet_digest = _payload_digest_hex("exact_out_repaired_key_cover_interpretation_packet", payload)

    state_payload = {
        "pool_snapshots": [dict(snapshot) for snapshot in selected_domain_contract.pool_snapshots],
        "feasible_pool_ids": list(repaired_contract_payload["feasible_pool_ids"]),
        "repaired_selected_pool_ids": list(repaired_contract_payload["repaired_selected_pool_ids"]),
        "full_domain_feasible_pool_ids": list(repaired_full_domain_payload["full_domain_feasible_pool_ids"]),
    }
    request_payload = {
        "asset_in": str(selected_domain_contract.asset_in),
        "asset_out": str(selected_domain_contract.asset_out),
        "amount_out_total": int(selected_domain_contract.amount_out_total),
        "max_legs": int(selected_domain_contract.max_legs),
        "max_candidate_pools": int(selected_domain_contract.max_candidate_pools),
        "max_candidates": int(selected_domain_contract.max_candidates),
        "max_iters": int(selected_domain_contract.max_iters),
        "window": int(selected_domain_contract.window),
        "brute_force_max": int(selected_domain_contract.brute_force_max),
        "max_full_domain_pools": int(selected_domain_contract.max_full_domain_pools),
        "max_enumerated_candidates": int(selected_domain_contract.max_enumerated_candidates),
    }
    proof_payload = {
        "source_packet_schema": str(packet.schema),
        "source_packet_digest": source_packet_digest,
        "key_cover_packet_schema": str(packet.key_cover_packet.schema),
        "selected_domain_contract_schema": str(packet.key_cover_packet.selected_domain_contract.schema),
        "repaired_full_domain_packet_schema": str(packet.key_cover_packet.repaired_full_domain_packet.schema),
        "selected_domain_contract_ok": bool(packet.key_cover_packet.selected_domain_contract.contract_ok),
        "repaired_full_domain_packet_ok": bool(packet.key_cover_packet.repaired_full_domain_packet.packet_ok),
        "key_cover_packet_ok": bool(packet.key_cover_packet.packet_ok),
        "packet_ok": bool(packet.packet_ok),
        "selected_candidate_count": int(packet.key_cover_packet.selected_candidate_count),
        "full_candidate_count": int(packet.key_cover_packet.full_candidate_count),
        "selected_domain_canonical_matches_full_domain_canonical": bool(
            packet.key_cover_packet.selected_domain_canonical_matches_full_domain_canonical
        ),
    }
    feasibility_payload = {
        "packet_ok": bool(packet.packet_ok),
        "key_cover_packet_ok": bool(packet.key_cover_packet.packet_ok),
        "selected_domain_contract_ok": bool(packet.key_cover_packet.selected_domain_contract.contract_ok),
        "repaired_full_domain_packet_ok": bool(packet.key_cover_packet.repaired_full_domain_packet.packet_ok),
        "selected_winner_index_in_range": bool(packet.selected_winner_index_in_range),
        "selected_winner_matches_certificate": bool(packet.selected_winner_matches_certificate),
        "selected_winner_key_minimal": bool(packet.selected_winner_key_minimal),
        "domination_witness_indices_in_range": bool(packet.domination_witness_indices_in_range),
        "domination_witnesses_cover_full_candidates": bool(packet.domination_witnesses_cover_full_candidates),
        "domination_witness_keys_match_candidates": bool(packet.domination_witness_keys_match_candidates),
        "domination_witnesses_dominate": bool(packet.domination_witnesses_dominate),
        "selected_domain_canonical_matches_full_domain_canonical": bool(
            packet.key_cover_packet.selected_domain_canonical_matches_full_domain_canonical
        ),
        "repaired_selected_domain_matches_full_canonical": bool(
            packet.key_cover_packet.selected_domain_contract.repaired_contract.repaired_selected_domain_matches_full_canonical
        ),
    }
    accounting_receipt = _quote_receipt_from_exact_out_payload(runtime_quote_payload)
    accounting_receipt["full_domain_canonical_quote"] = dict(full_domain_quote_payload)
    accounting_receipt["selected_domain_runtime_matches_full_domain_canonical"] = bool(
        runtime_quote_payload == full_domain_quote_payload
    )

    return DecisionWitness(
        witness_kind="exact_out_route",
        state_binding=_build_binding(
            binding_kind="exact_out_repaired_audit_domain",
            binding_id=source_packet_digest,
            payload=state_payload,
        ),
        request_binding=_build_binding(
            binding_kind="exact_out_request",
            binding_id=(
                f"{selected_domain_contract.asset_in}->{selected_domain_contract.asset_out}:"
                f"{int(selected_domain_contract.amount_out_total)}"
            ),
            payload=request_payload,
        ),
        quote_binding=_build_binding(
            binding_kind="exact_out_repaired_runtime_quote",
            binding_id=source_packet_digest,
            payload=dict(runtime_quote_payload),
        ),
        epoch_binding=epoch_binding,
        expires_at=expires_at,
        feasibility_payload=feasibility_payload,
        canonical_key=_flatten_exact_out_canonical_key(winner_key),
        accounting_receipt=accounting_receipt,
        proof_payload=proof_payload,
        metadata={
            "source_adapter": "exact_out_repaired_key_cover_interpretation_packet",
            "source_schema": str(packet.schema),
            **({} if metadata is None else dict(metadata)),
        },
    )


def verify_decision_witness_against_exact_out_repaired_key_cover_interpretation_packet(
    packet: object,
    witness_payload: object,
) -> tuple[bool, str | None]:
    try:
        expected = build_decision_witness_from_exact_out_repaired_key_cover_interpretation_packet(packet)
    except Exception as exc:
        return False, str(exc)
    ok, err = verify_decision_witness_payload(witness_payload, expected_witness_kind="exact_out_route")
    if not ok:
        return ok, err
    try:
        witness = DecisionWitness.from_dict(witness_payload)  # type: ignore[arg-type]
    except Exception as exc:
        return False, str(exc)
    if witness.to_dict() != expected.to_dict():
        return False, "decision witness payload mismatch for exact-out packet"
    return True, None


def build_decision_witness_from_settlement_end_to_end_certificate_packet(
    *,
    settlement: object,
    packet: object,
    expires_at: int | None = None,
    metadata: Mapping[str, Any] | None = None,
) -> DecisionWitness:
    from src.integration.settlement_end_to_end_certificate_packet import SettlementEndToEndCertificatePacket
    from src.integration.settlement_strong_certificate import _sha256_json

    if not isinstance(packet, SettlementEndToEndCertificatePacket):
        raise TypeError("packet must be a SettlementEndToEndCertificatePacket")
    if not packet.packet_ok:
        raise ValueError("settlement end-to-end certificate packet must be packet_ok")

    normalized_settlement = _settlement_normalized_payload(settlement)
    packet_payload = packet.to_dict()
    strong_certificate_payload = dict(packet_payload["strong_certificate"])
    feature_extension_packet_payload = dict(packet_payload["feature_extension_packet"])
    value_lane_payload = _settlement_value_lane_payload(packet_payload)
    price_packet_payload = dict(value_lane_payload["price_packet"])
    attestation_payload = value_lane_payload.get("price_attestation")
    packet_digest = _payload_digest_hex("settlement_end_to_end_certificate_packet", packet_payload)

    expected_settlement_commitment = _sha256_json(normalized_settlement)
    expected_delta_commitment = _sha256_json(
        {
            "balance_deltas": normalized_settlement.get("balance_deltas", []),
            "reserve_deltas": normalized_settlement.get("reserve_deltas", []),
            "lp_deltas": normalized_settlement.get("lp_deltas", []),
        }
    )

    feasibility_payload = {
        "packet_ok": bool(packet.packet_ok),
        "strong_certificate_ok": bool(packet.strong_certificate_ok),
        "feature_extension_packet_ok": bool(packet.feature_extension_packet_ok),
        "module_bundle_ok": bool(packet.module_bundle_ok),
        "full_price_rails_ok": bool(packet.full_price_rails_ok),
        "price_provenance_ok": bool(packet.price_provenance_ok),
        "attestation_ok": bool(packet.attestation_ok),
        "asset_conservation_ok": bool(packet.asset_conservation_ok),
        "lp_liability_balanced_ok": bool(packet.lp_liability_balanced_ok),
        "value_conservation_ok": bool(packet.value_conservation_ok),
        "settlement_commitment_matches": (
            str(packet.strong_certificate.settlement_commitment_sha256) == expected_settlement_commitment
        ),
        "delta_commitment_matches": (
            str(packet.strong_certificate.delta_commitment_sha256) == expected_delta_commitment
        ),
    }

    accounting_receipt = {
        "settlement_commitment_sha256": str(packet.strong_certificate.settlement_commitment_sha256),
        "delta_commitment_sha256": str(packet.strong_certificate.delta_commitment_sha256),
        "balance_deltas": list(normalized_settlement.get("balance_deltas", [])),
        "reserve_deltas": list(normalized_settlement.get("reserve_deltas", [])),
        "lp_deltas": list(normalized_settlement.get("lp_deltas", [])),
        "full_price_rails_ok": bool(packet.full_price_rails_ok),
        "price_input_kind": str(packet.price_input_kind),
        "value_packet_kind": str(packet.value_packet_kind),
        "value_lane_result": dict(value_lane_payload),
    }

    if strong_certificate_payload.get("price_history_certificate") is not None:
        accounting_receipt["price_history_certificate"] = dict(
            strong_certificate_payload["price_history_certificate"]
        )

    quote_binding_payload: Mapping[str, Any]
    if attestation_payload is not None:
        quote_binding_kind = "settlement_price_attestation"
        quote_binding_id = str(attestation_payload["packet_hash"])
        quote_binding_payload = dict(attestation_payload)
    else:
        quote_binding_kind = "settlement_price_packet"
        quote_binding_id = str(price_packet_payload["provenance_vector_sha256"])
        quote_binding_payload = price_packet_payload

    proof_payload = {
        "source_adapter": "settlement_end_to_end_certificate_packet",
        "source_packet_schema": str(packet.schema),
        "source_packet_digest": packet_digest,
        "strong_certificate_schema": str(packet.strong_certificate.schema),
        "feature_extension_packet_schema": str(packet.feature_extension_packet.schema),
        "value_lane_schema": str(value_lane_payload["schema"]),
        "settlement_commitment_sha256": str(packet.strong_certificate.settlement_commitment_sha256),
        "delta_commitment_sha256": str(packet.strong_certificate.delta_commitment_sha256),
        "full_price_rails_ok": bool(packet.full_price_rails_ok),
        "packet_ok": bool(packet.packet_ok),
    }

    return DecisionWitness(
        witness_kind="settlement_step",
        state_binding=_build_binding(
            binding_kind="settlement_certificate_boundary",
            binding_id=packet_digest,
            payload={
                "price_input_kind": str(packet.price_input_kind),
                "value_packet_kind": str(packet.value_packet_kind),
                "price_vector_sha256": str(price_packet_payload["price_vector_sha256"]),
                "provenance_vector_sha256": str(price_packet_payload["provenance_vector_sha256"]),
                "settlement_commitment_sha256": str(packet.strong_certificate.settlement_commitment_sha256),
                "delta_commitment_sha256": str(packet.strong_certificate.delta_commitment_sha256),
                "packet_ok": bool(packet.packet_ok),
            },
        ),
        request_binding=_build_binding(
            binding_kind="settlement_request",
            binding_id=str(packet.strong_certificate.settlement_commitment_sha256),
            payload=normalized_settlement,
        ),
        quote_binding=_build_binding(
            binding_kind=quote_binding_kind,
            binding_id=quote_binding_id,
            payload=quote_binding_payload,
        ),
        epoch_binding=_settlement_epoch_binding_from_packet_payload(packet_payload),
        expires_at=expires_at,
        feasibility_payload=feasibility_payload,
        canonical_key=_flatten_settlement_canonical_key(
            settlement_commitment_sha256=str(packet.strong_certificate.settlement_commitment_sha256),
            delta_commitment_sha256=str(packet.strong_certificate.delta_commitment_sha256),
            price_input_kind=str(packet.price_input_kind),
            value_packet_kind=str(packet.value_packet_kind),
        ),
        accounting_receipt=accounting_receipt,
        proof_payload=proof_payload,
        metadata={
            "source_schema": str(packet.schema),
            "price_input_kind": str(packet.price_input_kind),
            "value_packet_kind": str(packet.value_packet_kind),
            **({} if metadata is None else dict(metadata)),
        },
    )


def verify_decision_witness_against_settlement_end_to_end_certificate_packet(
    *,
    settlement: object,
    packet: object,
    expires_at: int | None = None,
    witness_payload: object,
) -> tuple[bool, str | None]:
    try:
        expected = build_decision_witness_from_settlement_end_to_end_certificate_packet(
            settlement=settlement,
            packet=packet,
            expires_at=expires_at,
        )
    except Exception as exc:
        return False, str(exc)
    ok, err = verify_decision_witness_payload(witness_payload, expected_witness_kind="settlement_step")
    if not ok:
        return ok, err
    try:
        witness = DecisionWitness.from_dict(witness_payload)  # type: ignore[arg-type]
    except Exception as exc:
        return False, str(exc)
    if witness.to_dict() != expected.to_dict():
        return False, "decision witness payload mismatch for settlement packet"
    return True, None


def build_decision_witness_from_autotrader_binary_decision(
    *,
    strategy: object,
    observation_packet: object,
    candidate_set: object,
    certificate: object,
    metadata: Mapping[str, Any] | None = None,
) -> DecisionWitness:
    from src.agents.strategy_ir import StrategyIR
    from src.integration.autotrader_decision import (
        StrategyCandidateSet,
        StrategyDecisionCertificate,
        derive_strategy_decision_binding_ok,
        verify_strategy_decision_certificate,
    )
    from src.integration.autotrader_signals import AutoTraderObservationPacket

    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(observation_packet, AutoTraderObservationPacket):
        raise TypeError("observation_packet must be an AutoTraderObservationPacket")
    if not isinstance(candidate_set, StrategyCandidateSet):
        raise TypeError("candidate_set must be a StrategyCandidateSet")
    if not isinstance(certificate, StrategyDecisionCertificate):
        raise TypeError("certificate must be a StrategyDecisionCertificate")

    ok, error = verify_strategy_decision_certificate(
        candidate_set=candidate_set,
        certificate=certificate,
        expected_kill_switch_active=certificate.kill_switch_active,
    )
    if not ok:
        raise ValueError(f"autotrader binary decision certificate must verify: {error}")

    observation_payload = observation_packet.to_dict()
    strategy_payload = strategy.to_dict()
    candidate_set_payload = candidate_set.to_dict()
    certificate_payload = certificate.to_dict()
    observation_digest = _payload_digest_hex("autotrader_observation_packet", observation_payload)
    certificate_digest = _payload_digest_hex("autotrader_binary_decision_certificate", certificate_payload)
    binding_ok = derive_strategy_decision_binding_ok(
        candidate_set=candidate_set,
        winner_index=certificate.winner_index,
        winner_key=certificate.winner_key,
        kill_switch_active=certificate.kill_switch_active,
    )

    return DecisionWitness(
        witness_kind="autotrader_binary_decision",
        state_binding=_build_binding(
            binding_kind="autotrader_binary_candidate_set",
            binding_id=str(candidate_set.candidate_set_hash_hex()),
            payload=candidate_set_payload,
        ),
        request_binding=_build_binding(
            binding_kind="autotrader_strategy",
            binding_id=str(strategy.strategy_hash_hex()),
            payload=strategy_payload,
        ),
        quote_binding=_build_binding(
            binding_kind="autotrader_observation_packet",
            binding_id=observation_digest,
            payload=observation_payload,
        ),
        epoch_binding=_build_binding(
            binding_kind="autotrader_epoch",
            binding_id=str(observation_packet.current_epoch),
            payload={"current_epoch": int(observation_packet.current_epoch)},
        ),
        expires_at=int(strategy.strategy_window.valid_until_epoch),
        feasibility_payload={
            "decision_verified": True,
            "binding_ok": bool(binding_ok),
            "candidate_count": len(candidate_set.candidates),
            "winner_index": int(certificate.winner_index),
            "winner_kind": certificate.winner_kind.value,
            "kill_switch_active": bool(certificate.kill_switch_active),
        },
        canonical_key=(-int(certificate.winner_key), int(certificate.winner_index)),
        accounting_receipt=_autotrader_accounting_receipt_from_observation_payload(observation_payload),
        proof_payload={
            "source_adapter": "autotrader_binary_decision",
            "candidate_set_hash": str(candidate_set.candidate_set_hash_hex()),
            "decision_hash": str(certificate.decision_hash_hex()),
            "certificate_digest": certificate_digest,
            "binding_ok": bool(binding_ok),
        },
        metadata={
            "strategy_template": strategy.template.value,
            "allowed_actions": [action.value for action in strategy.allowed_actions],
            **({} if metadata is None else dict(metadata)),
        },
    )


def verify_decision_witness_against_autotrader_binary_decision(
    *,
    strategy: object,
    observation_packet: object,
    candidate_set: object,
    certificate: object,
    witness_payload: object,
) -> tuple[bool, str | None]:
    try:
        expected = build_decision_witness_from_autotrader_binary_decision(
            strategy=strategy,
            observation_packet=observation_packet,
            candidate_set=candidate_set,
            certificate=certificate,
        )
    except Exception as exc:
        return False, str(exc)
    ok, err = verify_decision_witness_payload(
        witness_payload, expected_witness_kind="autotrader_binary_decision"
    )
    if not ok:
        return ok, err
    try:
        witness = DecisionWitness.from_dict(witness_payload)  # type: ignore[arg-type]
    except Exception as exc:
        return False, str(exc)
    if witness.to_dict() != expected.to_dict():
        return False, "decision witness payload mismatch for autotrader binary decision"
    return True, None


def build_decision_witness_from_autotrader_multiaction_decision(
    *,
    strategy: object,
    observation_packet: object,
    candidate_set: object,
    certificate: object,
    metadata: Mapping[str, Any] | None = None,
) -> DecisionWitness:
    from src.agents.strategy_ir import StrategyIR
    from src.integration.autotrader_multiaction_decision import (
        BoundedMultiActionCandidateSet,
        BoundedMultiActionDecisionCertificate,
        derive_bounded_multi_action_decision_binding_ok,
        verify_bounded_multi_action_decision_certificate,
    )
    from src.integration.autotrader_signals import AutoTraderObservationPacket

    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(observation_packet, AutoTraderObservationPacket):
        raise TypeError("observation_packet must be an AutoTraderObservationPacket")
    if not isinstance(candidate_set, BoundedMultiActionCandidateSet):
        raise TypeError("candidate_set must be a BoundedMultiActionCandidateSet")
    if not isinstance(certificate, BoundedMultiActionDecisionCertificate):
        raise TypeError("certificate must be a BoundedMultiActionDecisionCertificate")

    ok, error = verify_bounded_multi_action_decision_certificate(
        candidate_set=candidate_set,
        certificate=certificate,
    )
    if not ok:
        raise ValueError(f"autotrader multi-action decision certificate must verify: {error}")

    observation_payload = observation_packet.to_dict()
    strategy_payload = strategy.to_dict()
    candidate_set_payload = candidate_set.to_dict()
    certificate_payload = certificate.to_dict()
    observation_digest = _payload_digest_hex("autotrader_observation_packet", observation_payload)
    certificate_digest = _payload_digest_hex("autotrader_multiaction_decision_certificate", certificate_payload)
    binding_ok = derive_bounded_multi_action_decision_binding_ok(
        candidate_set=candidate_set,
        winner_index=certificate.winner_index,
        winner_key=certificate.winner_key,
    )

    return DecisionWitness(
        witness_kind="autotrader_multiaction_decision",
        state_binding=_build_binding(
            binding_kind="autotrader_multiaction_candidate_set",
            binding_id=str(candidate_set.candidate_set_hash_hex()),
            payload=candidate_set_payload,
        ),
        request_binding=_build_binding(
            binding_kind="autotrader_strategy",
            binding_id=str(strategy.strategy_hash_hex()),
            payload=strategy_payload,
        ),
        quote_binding=_build_binding(
            binding_kind="autotrader_observation_packet",
            binding_id=observation_digest,
            payload=observation_payload,
        ),
        epoch_binding=_build_binding(
            binding_kind="autotrader_epoch",
            binding_id=str(observation_packet.current_epoch),
            payload={"current_epoch": int(observation_packet.current_epoch)},
        ),
        expires_at=int(strategy.strategy_window.valid_until_epoch),
        feasibility_payload={
            "decision_verified": True,
            "binding_ok": bool(binding_ok),
            "candidate_count": len(candidate_set.candidates),
            "winner_index": int(certificate.winner_index),
            "winner_kind": certificate.winner_kind.value,
            "frontier_width": int(certificate.frontier_width),
        },
        canonical_key=(-int(certificate.winner_key), int(certificate.winner_index)),
        accounting_receipt=_autotrader_accounting_receipt_from_observation_payload(observation_payload),
        proof_payload={
            "source_adapter": "autotrader_multiaction_decision",
            "candidate_set_hash": str(candidate_set.candidate_set_hash_hex()),
            "decision_hash": str(certificate.decision_hash_hex()),
            "certificate_digest": certificate_digest,
            "binding_ok": bool(binding_ok),
            "frontier_width": int(certificate.frontier_width),
        },
        metadata={
            "strategy_template": strategy.template.value,
            "allowed_actions": [action.value for action in strategy.allowed_actions],
            **({} if metadata is None else dict(metadata)),
        },
    )


def verify_decision_witness_against_autotrader_multiaction_decision(
    *,
    strategy: object,
    observation_packet: object,
    candidate_set: object,
    certificate: object,
    witness_payload: object,
) -> tuple[bool, str | None]:
    try:
        expected = build_decision_witness_from_autotrader_multiaction_decision(
            strategy=strategy,
            observation_packet=observation_packet,
            candidate_set=candidate_set,
            certificate=certificate,
        )
    except Exception as exc:
        return False, str(exc)
    ok, err = verify_decision_witness_payload(
        witness_payload, expected_witness_kind="autotrader_multiaction_decision"
    )
    if not ok:
        return ok, err
    try:
        witness = DecisionWitness.from_dict(witness_payload)  # type: ignore[arg-type]
    except Exception as exc:
        return False, str(exc)
    if witness.to_dict() != expected.to_dict():
        return False, "decision witness payload mismatch for autotrader multi-action decision"
    return True, None
