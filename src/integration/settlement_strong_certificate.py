from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping, Optional

from src.core.settlement import Settlement
from src.core.settlement_normal_form import normalize_settlement_op_for_commitment

from ..core.settlement_strong_validator import validate_settlement_strong
from .operations import create_settlement_operation
from .tau_witness import (
    SETTLEMENT_MODULE_FLAG_BUNDLE_V1,
    SETTLEMENT_PRICE_RAILS_ALIGNED_V1,
    SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE,
    build_settlement_core_module_bundle_v1_step,
    build_settlement_feature_extension_bundle_v1_step,
    build_settlement_module_flag_bundle_v1_step,
    build_settlement_price_rails_aligned_v1_step,
    build_settlement_proof_binding_bundle_v1_step,
    build_settlement_v5_aligned_compact_bundle_step,
)

SETTLEMENT_STRONG_CERTIFICATE_SCHEMA = "zenodex/settlement-strong-certificate/v1"
SETTLEMENT_PRICE_HISTORY_CERTIFICATE_SCHEMA = "zenodex/settlement-price-history-certificate/v1"


def _require_int_field(payload: Mapping[str, Any], field: str, *, default: int = -1) -> int:
    value = payload.get(field, default)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{field} must be an int")
    return int(value)


def _require_optional_int_field(payload: Mapping[str, Any], field: str) -> int | None:
    if payload.get(field) is None:
        return None
    return _require_int_field(payload, field)


def _require_binary_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be a 0/1 int, got {value!r}")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1, got {value!r}")
    return int(value)


@dataclass(frozen=True)
class SettlementProofFlags:
    cpmm_ok: int
    balance_ok: int
    token_ok: int
    buyback_floor_ok: int
    buyback_floor_fixedpoint_ok: int
    rebate_ok: int
    lock_weight_ok: int
    proof_ok: int
    binding_ok: int

    def __post_init__(self) -> None:
        for name in (
            "cpmm_ok",
            "balance_ok",
            "token_ok",
            "buyback_floor_ok",
            "buyback_floor_fixedpoint_ok",
            "rebate_ok",
            "lock_weight_ok",
            "proof_ok",
            "binding_ok",
        ):
            _require_binary_int(getattr(self, name), name=name)

    def to_dict(self) -> dict[str, int]:
        return {
            "cpmm_ok": int(self.cpmm_ok),
            "balance_ok": int(self.balance_ok),
            "token_ok": int(self.token_ok),
            "buyback_floor_ok": int(self.buyback_floor_ok),
            "buyback_floor_fixedpoint_ok": int(self.buyback_floor_fixedpoint_ok),
            "rebate_ok": int(self.rebate_ok),
            "lock_weight_ok": int(self.lock_weight_ok),
            "proof_ok": int(self.proof_ok),
            "binding_ok": int(self.binding_ok),
        }

    @classmethod
    def all_true(cls) -> "SettlementProofFlags":
        return cls(
            cpmm_ok=1,
            balance_ok=1,
            token_ok=1,
            buyback_floor_ok=1,
            buyback_floor_fixedpoint_ok=1,
            rebate_ok=1,
            lock_weight_ok=1,
            proof_ok=1,
            binding_ok=1,
        )

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementProofFlags":
        if not isinstance(payload, Mapping):
            raise ValueError("proof_flags must be an object")
        return cls(
            cpmm_ok=_require_int_field(payload, "cpmm_ok"),
            balance_ok=_require_int_field(payload, "balance_ok"),
            token_ok=_require_int_field(payload, "token_ok"),
            buyback_floor_ok=_require_int_field(payload, "buyback_floor_ok"),
            buyback_floor_fixedpoint_ok=_require_int_field(payload, "buyback_floor_fixedpoint_ok"),
            rebate_ok=_require_int_field(payload, "rebate_ok"),
            lock_weight_ok=_require_int_field(payload, "lock_weight_ok"),
            proof_ok=_require_int_field(payload, "proof_ok"),
            binding_ok=_require_int_field(payload, "binding_ok"),
        )


@dataclass(frozen=True)
class SettlementSemanticSummary:
    a: int
    b: int
    c: int
    d: int
    price_pp: int
    price_prev: int
    price_curr: int

    def __post_init__(self) -> None:
        for name in ("a", "b", "c", "d"):
            _require_u16(getattr(self, name), name=name)
        for name in ("price_pp", "price_prev", "price_curr"):
            _require_u16(getattr(self, name), name=name)

    def to_dict(self) -> dict[str, int]:
        return {
            "a": int(self.a),
            "b": int(self.b),
            "c": int(self.c),
            "d": int(self.d),
            "price_pp": int(self.price_pp),
            "price_prev": int(self.price_prev),
            "price_curr": int(self.price_curr),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSemanticSummary":
        if not isinstance(payload, Mapping):
            raise ValueError("semantic_summary must be an object")
        return cls(
            a=_require_int_field(payload, "a"),
            b=_require_int_field(payload, "b"),
            c=_require_int_field(payload, "c"),
            d=_require_int_field(payload, "d"),
            price_pp=_require_int_field(payload, "price_pp"),
            price_prev=_require_int_field(payload, "price_prev"),
            price_curr=_require_int_field(payload, "price_curr"),
        )


@dataclass(frozen=True)
class SettlementPriceHistoryCertificate:
    price_pp: int
    price_prev: int
    price_curr: int
    price_trace_sha256: str
    schema: str = SETTLEMENT_PRICE_HISTORY_CERTIFICATE_SCHEMA

    def __post_init__(self) -> None:
        for name in ("price_pp", "price_prev", "price_curr"):
            _require_u16(getattr(self, name), name=name)
        _require_hex_digest(self.price_trace_sha256, name="price_trace_sha256")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "price_pp": int(self.price_pp),
            "price_prev": int(self.price_prev),
            "price_curr": int(self.price_curr),
            "price_trace_sha256": self.price_trace_sha256,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementPriceHistoryCertificate":
        if not isinstance(payload, Mapping):
            raise ValueError("price_history_certificate must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            price_pp=_require_int_field(payload, "price_pp"),
            price_prev=_require_int_field(payload, "price_prev"),
            price_curr=_require_int_field(payload, "price_curr"),
            price_trace_sha256=str(payload.get("price_trace_sha256", "")),
        )


@dataclass(frozen=True)
class SettlementStrongCertificate:
    settlement_commitment_sha256: str
    delta_commitment_sha256: str
    proof_flags: SettlementProofFlags
    core_module_ok: int
    feature_extension_ok: int
    proof_binding_ok: int
    module_bundle_ok: int
    core_module_step: dict[str, int]
    feature_extension_step: dict[str, int]
    proof_binding_step: dict[str, int]
    module_bundle_step: dict[str, int]
    semantic_summary: Optional[SettlementSemanticSummary] = None
    price_history_certificate: Optional[SettlementPriceHistoryCertificate] = None
    compact_bundle_step: Optional[dict[str, int]] = None
    compact_bundle_ok: Optional[int] = None
    full_price_rails_step: Optional[dict[str, int]] = None
    full_price_rails_ok: Optional[int] = None
    schema: str = SETTLEMENT_STRONG_CERTIFICATE_SCHEMA
    module_bundle_spec_id: str = SETTLEMENT_MODULE_FLAG_BUNDLE_V1.spec_id
    proof_binding_spec_id: str = "settlement_proof_binding_bundle_v1"
    compact_bundle_spec_id: str = SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE.spec_id
    full_price_rails_spec_id: str = SETTLEMENT_PRICE_RAILS_ALIGNED_V1.spec_id

    def __post_init__(self) -> None:
        _require_hex_digest(self.settlement_commitment_sha256, name="settlement_commitment_sha256")
        _require_hex_digest(self.delta_commitment_sha256, name="delta_commitment_sha256")
        for name in ("core_module_ok", "feature_extension_ok", "proof_binding_ok", "module_bundle_ok"):
            _require_binary_int(getattr(self, name), name=name)
        if self.compact_bundle_ok is not None:
            _require_binary_int(self.compact_bundle_ok, name="compact_bundle_ok")
        if self.full_price_rails_ok is not None:
            _require_binary_int(self.full_price_rails_ok, name="full_price_rails_ok")
        if (self.semantic_summary is None) != (self.compact_bundle_step is None):
            raise ValueError("semantic_summary and compact_bundle_step must either both be present or both be absent")
        if (self.semantic_summary is None) != (self.compact_bundle_ok is None):
            raise ValueError("semantic_summary and compact_bundle_ok must either both be present or both be absent")
        if (self.semantic_summary is None) != (self.full_price_rails_step is None):
            raise ValueError("semantic_summary and full_price_rails_step must either both be present or both be absent")
        if (self.semantic_summary is None) != (self.full_price_rails_ok is None):
            raise ValueError("semantic_summary and full_price_rails_ok must either both be present or both be absent")
        if (self.semantic_summary is None) != (self.price_history_certificate is None):
            raise ValueError(
                "semantic_summary and price_history_certificate must either both be present or both be absent"
            )
        if self.semantic_summary is not None and self.price_history_certificate is not None:
            if self.price_history_certificate.schema != SETTLEMENT_PRICE_HISTORY_CERTIFICATE_SCHEMA:
                raise ValueError("price history certificate schema mismatch")
            if self.price_history_certificate.price_pp != self.semantic_summary.price_pp:
                raise ValueError("price history certificate price_pp mismatch")
            if self.price_history_certificate.price_prev != self.semantic_summary.price_prev:
                raise ValueError("price history certificate price_prev mismatch")
            if self.price_history_certificate.price_curr != self.semantic_summary.price_curr:
                raise ValueError("price history certificate price_curr mismatch")

    def to_dict(self) -> dict[str, Any]:
        out = {
            "schema": self.schema,
            "settlement_commitment_sha256": self.settlement_commitment_sha256,
            "delta_commitment_sha256": self.delta_commitment_sha256,
            "proof_flags": self.proof_flags.to_dict(),
            "core_module_ok": int(self.core_module_ok),
            "feature_extension_ok": int(self.feature_extension_ok),
            "proof_binding_ok": int(self.proof_binding_ok),
            "module_bundle_ok": int(self.module_bundle_ok),
            "module_bundle_spec_id": self.module_bundle_spec_id,
            "proof_binding_spec_id": self.proof_binding_spec_id,
            "compact_bundle_spec_id": self.compact_bundle_spec_id,
            "full_price_rails_spec_id": self.full_price_rails_spec_id,
            "core_module_step": dict(self.core_module_step),
            "feature_extension_step": dict(self.feature_extension_step),
            "proof_binding_step": dict(self.proof_binding_step),
            "module_bundle_step": dict(self.module_bundle_step),
        }
        if self.semantic_summary is not None:
            price_history_certificate = self.price_history_certificate
            compact_bundle_step = self.compact_bundle_step
            compact_bundle_ok = self.compact_bundle_ok
            full_price_rails_step = self.full_price_rails_step
            full_price_rails_ok = self.full_price_rails_ok
            if (
                price_history_certificate is None
                or compact_bundle_step is None
                or compact_bundle_ok is None
                or full_price_rails_step is None
                or full_price_rails_ok is None
            ):
                raise ValueError("semantic settlement certificate fields are incomplete")
            out["semantic_summary"] = self.semantic_summary.to_dict()
            out["price_history_certificate"] = price_history_certificate.to_dict()
            out["compact_bundle_step"] = dict(compact_bundle_step)
            out["compact_bundle_ok"] = int(compact_bundle_ok)
            out["full_price_rails_step"] = dict(full_price_rails_step)
            out["full_price_rails_ok"] = int(full_price_rails_ok)
        return out

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementStrongCertificate":
        if not isinstance(payload, Mapping):
            raise ValueError("settlement strong certificate must be an object")
        semantic_summary_payload = payload.get("semantic_summary")
        price_history_certificate_payload = payload.get("price_history_certificate")
        return cls(
            schema=str(payload.get("schema", "")),
            settlement_commitment_sha256=str(payload.get("settlement_commitment_sha256", "")),
            delta_commitment_sha256=str(payload.get("delta_commitment_sha256", "")),
            proof_flags=SettlementProofFlags.from_dict(payload.get("proof_flags", {})),
            core_module_ok=_require_int_field(payload, "core_module_ok"),
            feature_extension_ok=_require_int_field(payload, "feature_extension_ok"),
            proof_binding_ok=_require_int_field(payload, "proof_binding_ok"),
            module_bundle_ok=_require_int_field(payload, "module_bundle_ok"),
            core_module_step=dict(payload.get("core_module_step", {})),
            feature_extension_step=dict(payload.get("feature_extension_step", {})),
            proof_binding_step=dict(payload.get("proof_binding_step", {})),
            module_bundle_step=dict(payload.get("module_bundle_step", {})),
            semantic_summary=(
                None
                if semantic_summary_payload is None
                else SettlementSemanticSummary.from_dict(semantic_summary_payload)
            ),
            price_history_certificate=(
                None
                if price_history_certificate_payload is None
                else SettlementPriceHistoryCertificate.from_dict(price_history_certificate_payload)
            ),
            compact_bundle_step=(
                None if payload.get("compact_bundle_step") is None else dict(payload.get("compact_bundle_step", {}))
            ),
            compact_bundle_ok=_require_optional_int_field(payload, "compact_bundle_ok"),
            full_price_rails_step=(
                None
                if payload.get("full_price_rails_step") is None
                else dict(payload.get("full_price_rails_step", {}))
            ),
            full_price_rails_ok=_require_optional_int_field(payload, "full_price_rails_ok"),
            module_bundle_spec_id=str(payload.get("module_bundle_spec_id", SETTLEMENT_MODULE_FLAG_BUNDLE_V1.spec_id)),
            proof_binding_spec_id=str(payload.get("proof_binding_spec_id", "settlement_proof_binding_bundle_v1")),
            compact_bundle_spec_id=str(payload.get("compact_bundle_spec_id", SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE.spec_id)),
            full_price_rails_spec_id=str(payload.get("full_price_rails_spec_id", SETTLEMENT_PRICE_RAILS_ALIGNED_V1.spec_id)),
        )


def build_settlement_price_history_certificate(
    *,
    price_pp: int,
    price_prev: int,
    price_curr: int,
) -> SettlementPriceHistoryCertificate:
    return SettlementPriceHistoryCertificate(
        price_pp=int(price_pp),
        price_prev=int(price_prev),
        price_curr=int(price_curr),
        price_trace_sha256=_sha256_json(
            {
                "price_pp": int(price_pp),
                "price_prev": int(price_prev),
                "price_curr": int(price_curr),
            }
        ),
    )


def build_settlement_strong_certificate(
    *,
    settlement: Settlement,
    proof_flags: SettlementProofFlags,
    semantic_summary: Optional[SettlementSemanticSummary] = None,
) -> SettlementStrongCertificate:
    normalized = _normalized_settlement_dict(settlement)
    settlement_digest = _sha256_json(normalized)
    delta_digest = _sha256_json(
        {
            "balance_deltas": normalized.get("balance_deltas", []),
            "reserve_deltas": normalized.get("reserve_deltas", []),
            "lp_deltas": normalized.get("lp_deltas", []),
        }
    )

    core_module_ok = int(proof_flags.cpmm_ok and proof_flags.balance_ok and proof_flags.token_ok)
    feature_extension_ok = int(
        proof_flags.buyback_floor_ok
        and proof_flags.buyback_floor_fixedpoint_ok
        and proof_flags.rebate_ok
        and proof_flags.lock_weight_ok
    )
    proof_binding_ok = int(proof_flags.proof_ok and proof_flags.binding_ok)
    module_bundle_ok = int(core_module_ok and feature_extension_ok and proof_binding_ok)

    core_module_step = build_settlement_core_module_bundle_v1_step(
        cpmm_ok=proof_flags.cpmm_ok,
        balance_ok=proof_flags.balance_ok,
        token_ok=proof_flags.token_ok,
    )
    feature_extension_step = build_settlement_feature_extension_bundle_v1_step(
        buyback_floor_ok=proof_flags.buyback_floor_ok,
        buyback_floor_fixedpoint_ok=proof_flags.buyback_floor_fixedpoint_ok,
        rebate_ok=proof_flags.rebate_ok,
        lock_weight_ok=proof_flags.lock_weight_ok,
    )
    proof_binding_step = build_settlement_proof_binding_bundle_v1_step(
        proof_ok=proof_flags.proof_ok,
        binding_ok=proof_flags.binding_ok,
    )
    module_bundle_step = build_settlement_module_flag_bundle_v1_step(
        cpmm_ok=proof_flags.cpmm_ok,
        balance_ok=proof_flags.balance_ok,
        token_ok=proof_flags.token_ok,
        buyback_floor_ok=proof_flags.buyback_floor_ok,
        buyback_floor_fixedpoint_ok=proof_flags.buyback_floor_fixedpoint_ok,
        rebate_ok=proof_flags.rebate_ok,
        lock_weight_ok=proof_flags.lock_weight_ok,
        proof_ok=proof_flags.proof_ok,
        binding_ok=proof_flags.binding_ok,
    )

    compact_bundle_step: Optional[dict[str, int]] = None
    compact_bundle_ok: Optional[int] = None
    full_price_rails_step: Optional[dict[str, int]] = None
    full_price_rails_ok: Optional[int] = None
    price_history_certificate: Optional[SettlementPriceHistoryCertificate] = None
    if semantic_summary is not None:
        price_history_certificate = build_settlement_price_history_certificate(
            price_pp=semantic_summary.price_pp,
            price_prev=semantic_summary.price_prev,
            price_curr=semantic_summary.price_curr,
        )
        compact_bundle_step = build_settlement_v5_aligned_compact_bundle_step(
            a=semantic_summary.a,
            b=semantic_summary.b,
            c=semantic_summary.c,
            d=semantic_summary.d,
            price_pp=semantic_summary.price_pp,
            price_prev=semantic_summary.price_prev,
            price_curr=semantic_summary.price_curr,
            cpmm_ok=proof_flags.cpmm_ok,
            balance_ok=proof_flags.balance_ok,
            token_ok=proof_flags.token_ok,
            buyback_floor_ok=proof_flags.buyback_floor_ok,
            buyback_floor_fixedpoint_ok=proof_flags.buyback_floor_fixedpoint_ok,
            rebate_ok=proof_flags.rebate_ok,
            lock_weight_ok=proof_flags.lock_weight_ok,
            proof_ok=proof_flags.proof_ok,
            binding_ok=proof_flags.binding_ok,
        )
        compact_bundle_ok = int(
            settlement_compact_price_gate_ok(
                a=semantic_summary.a,
                b=semantic_summary.b,
                c=semantic_summary.c,
                d=semantic_summary.d,
                price_pp=semantic_summary.price_pp,
                price_prev=semantic_summary.price_prev,
                price_curr=semantic_summary.price_curr,
            )
            and module_bundle_ok == 1
        )
        full_price_rails_step = build_settlement_price_rails_aligned_v1_step(
            a=semantic_summary.a,
            b=semantic_summary.b,
            c=semantic_summary.c,
            d=semantic_summary.d,
            price_pp=semantic_summary.price_pp,
            price_prev=semantic_summary.price_prev,
            price_curr=semantic_summary.price_curr,
        )
        full_price_rails_ok = int(
            settlement_full_price_rails_ok(
                a=semantic_summary.a,
                b=semantic_summary.b,
                c=semantic_summary.c,
                d=semantic_summary.d,
                price_pp=semantic_summary.price_pp,
                price_prev=semantic_summary.price_prev,
                price_curr=semantic_summary.price_curr,
            )
            and module_bundle_ok == 1
        )

    return SettlementStrongCertificate(
        settlement_commitment_sha256=settlement_digest,
        delta_commitment_sha256=delta_digest,
        proof_flags=proof_flags,
        core_module_ok=core_module_ok,
        feature_extension_ok=feature_extension_ok,
        proof_binding_ok=proof_binding_ok,
        module_bundle_ok=module_bundle_ok,
        core_module_step=core_module_step,
        feature_extension_step=feature_extension_step,
        proof_binding_step=proof_binding_step,
        module_bundle_step=module_bundle_step,
        semantic_summary=semantic_summary,
        price_history_certificate=price_history_certificate,
        compact_bundle_step=compact_bundle_step,
        compact_bundle_ok=compact_bundle_ok,
        full_price_rails_step=full_price_rails_step,
        full_price_rails_ok=full_price_rails_ok,
    )


def derive_replay_settlement_semantic_summary(
    *,
    settlement: Settlement,
    price_history: tuple[int, int, int],
) -> SettlementSemanticSummary:
    if not isinstance(price_history, tuple) or len(price_history) != 3:
        raise ValueError("price_history must be a 3-tuple: (price_pp, price_prev, price_curr)")
    price_pp, price_prev, price_curr = price_history
    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if len(included_ids) != 4:
        raise ValueError(f"replay-bound compact summary requires exactly 4 included intents, got {len(included_ids)}")
    # The compact settlement Tau lane currently consumes 16-bit order ids.
    # Bind to the low 16 bits explicitly rather than relying on implicit truncation.
    ids16 = tuple(_intent_id_to_u16(intent_id) for intent_id in included_ids)
    return SettlementSemanticSummary(
        a=ids16[0],
        b=ids16[1],
        c=ids16[2],
        d=ids16[3],
        price_pp=int(price_pp),
        price_prev=int(price_prev),
        price_curr=int(price_curr),
    )


def build_replay_bound_settlement_strong_certificate(
    *,
    settlement: Settlement,
    proof_flags: SettlementProofFlags,
    price_history: tuple[int, int, int],
) -> SettlementStrongCertificate:
    return build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=proof_flags,
        semantic_summary=derive_replay_settlement_semantic_summary(
            settlement=settlement,
            price_history=price_history,
        ),
    )


def derive_replay_bound_certificate_flags(external_proof_flags: SettlementProofFlags) -> SettlementProofFlags:
    # A successful strong validator run already discharges the core settlement
    # lanes, so the replay-bound certificate does not need to trust these three
    # bits from the caller.
    return SettlementProofFlags(
        cpmm_ok=1,
        balance_ok=1,
        token_ok=1,
        buyback_floor_ok=external_proof_flags.buyback_floor_ok,
        buyback_floor_fixedpoint_ok=external_proof_flags.buyback_floor_fixedpoint_ok,
        rebate_ok=external_proof_flags.rebate_ok,
        lock_weight_ok=external_proof_flags.lock_weight_ok,
        proof_ok=external_proof_flags.proof_ok,
        binding_ok=external_proof_flags.binding_ok,
    )


def derive_verified_replay_bound_certificate_flags(
    external_proof_flags: SettlementProofFlags,
    *,
    proof_ok: bool,
    binding_ok: bool,
) -> SettlementProofFlags:
    if not isinstance(proof_ok, bool):
        raise TypeError("proof_ok must be a bool")
    if not isinstance(binding_ok, bool):
        raise TypeError("binding_ok must be a bool")
    base = derive_replay_bound_certificate_flags(external_proof_flags)
    return SettlementProofFlags(
        cpmm_ok=base.cpmm_ok,
        balance_ok=base.balance_ok,
        token_ok=base.token_ok,
        buyback_floor_ok=base.buyback_floor_ok,
        buyback_floor_fixedpoint_ok=base.buyback_floor_fixedpoint_ok,
        rebate_ok=base.rebate_ok,
        lock_weight_ok=base.lock_weight_ok,
        proof_ok=int(proof_ok),
        binding_ok=int(binding_ok),
    )


def verify_settlement_strong_certificate(
    *,
    settlement: Settlement,
    certificate: SettlementStrongCertificate,
) -> tuple[bool, Optional[str]]:
    if certificate.schema != SETTLEMENT_STRONG_CERTIFICATE_SCHEMA:
        return False, f"unsupported certificate schema: {certificate.schema!r}"
    if certificate.module_bundle_spec_id != SETTLEMENT_MODULE_FLAG_BUNDLE_V1.spec_id:
        return False, "module bundle spec id mismatch"
    if certificate.proof_binding_spec_id != "settlement_proof_binding_bundle_v1":
        return False, "proof binding spec id mismatch"
    if certificate.compact_bundle_spec_id != SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE.spec_id:
        return False, "compact bundle spec id mismatch"
    if certificate.full_price_rails_spec_id != SETTLEMENT_PRICE_RAILS_ALIGNED_V1.spec_id:
        return False, "full price rails spec id mismatch"
    if certificate.price_history_certificate is not None:
        if certificate.price_history_certificate.schema != SETTLEMENT_PRICE_HISTORY_CERTIFICATE_SCHEMA:
            return False, "price history certificate schema mismatch"
    expected = build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=certificate.proof_flags,
        semantic_summary=certificate.semantic_summary,
    )
    if certificate.settlement_commitment_sha256 != expected.settlement_commitment_sha256:
        return False, "settlement commitment mismatch"
    if certificate.delta_commitment_sha256 != expected.delta_commitment_sha256:
        return False, "delta commitment mismatch"
    if certificate.core_module_step != expected.core_module_step:
        return False, "core module bundle step mismatch"
    if certificate.feature_extension_step != expected.feature_extension_step:
        return False, "feature extension bundle step mismatch"
    if certificate.proof_binding_step != expected.proof_binding_step:
        return False, "proof binding bundle step mismatch"
    if certificate.module_bundle_step != expected.module_bundle_step:
        return False, "module bundle step mismatch"
    if certificate.core_module_ok != expected.core_module_ok:
        return False, "core_module_ok mismatch"
    if certificate.feature_extension_ok != expected.feature_extension_ok:
        return False, "feature_extension_ok mismatch"
    if certificate.proof_binding_ok != expected.proof_binding_ok:
        return False, "proof_binding_ok mismatch"
    if certificate.module_bundle_ok != expected.module_bundle_ok:
        return False, "module_bundle_ok mismatch"
    if certificate.price_history_certificate != expected.price_history_certificate:
        return False, "price history certificate mismatch"
    if certificate.compact_bundle_step != expected.compact_bundle_step:
        return False, "compact bundle step mismatch"
    if certificate.compact_bundle_ok != expected.compact_bundle_ok:
        return False, "compact_bundle_ok mismatch"
    if certificate.full_price_rails_step != expected.full_price_rails_step:
        return False, "full price rails step mismatch"
    if certificate.full_price_rails_ok != expected.full_price_rails_ok:
        return False, "full_price_rails_ok mismatch"
    return True, None


def validate_settlement_strong_with_certificate(
    *,
    settlement: Settlement,
    certificate: SettlementStrongCertificate,
    intents: list[Any],
    pre_balances: Any,
    pre_pools: Mapping[str, Any],
    pre_lp_balances: Optional[Any] = None,
    mode: str = "strong_replay",
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[str] = None,
) -> tuple[bool, Optional[str]]:
    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=certificate)
    if not ok:
        return False, err
    if certificate.module_bundle_ok != 1:
        return False, "settlement certificate module bundle rejected"
    if certificate.semantic_summary is not None and certificate.full_price_rails_ok != 1:
        return False, "settlement certificate full price rails rejected"
    return validate_settlement_strong(
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


def enforce_replay_bound_settlement_certificate(
    *,
    settlement: Settlement,
    external_proof_flags: SettlementProofFlags,
    price_history: tuple[int, int, int],
    intents: list[Any],
    pre_balances: Any,
    pre_pools: Mapping[str, Any],
    pre_lp_balances: Optional[Any] = None,
    mode: str = "strong_replay",
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[str] = None,
) -> tuple[bool, Optional[str], Optional[SettlementStrongCertificate]]:
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
    effective_flags = derive_replay_bound_certificate_flags(external_proof_flags)

    certificate = build_replay_bound_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=effective_flags,
        price_history=price_history,
    )
    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=certificate)
    if not ok:
        return False, err, None
    if certificate.module_bundle_ok != 1:
        return False, "settlement certificate module bundle rejected", None
    if certificate.full_price_rails_ok != 1:
        return False, "settlement certificate full price rails rejected", None
    return True, None, certificate


def _normalized_settlement_dict(settlement: Settlement) -> dict[str, Any]:
    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, dict):
        raise TypeError("internal error: settlement operation must be a dict")
    return normalize_settlement_op_for_commitment(op)


def _sha256_json(value: Mapping[str, Any]) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def _require_u16(value: int, *, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > 0xFFFF:
        raise ValueError(f"{name} out of u16 range: {value!r}")


def _require_hex_digest(value: str, *, name: str) -> None:
    if not isinstance(value, str) or len(value) != 64:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest")
    try:
        int(value, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest") from exc


def _intent_id_to_u16(intent_id: str) -> int:
    if not isinstance(intent_id, str) or not intent_id.startswith("0x") or len(intent_id) <= 2:
        raise ValueError(f"invalid intent_id for settlement certificate: {intent_id!r}")
    return int(intent_id, 16) & 0xFFFF


def settlement_ids_are_strictly_ordered(*, a: int, b: int, c: int, d: int) -> bool:
    return a < b < c < d


def settlement_price_trace_is_monotone(*, price_pp: int, price_prev: int, price_curr: int) -> bool:
    return (price_pp <= price_prev <= price_curr) or (price_pp >= price_prev >= price_curr)


def settlement_compact_price_gate_ok(
    *,
    a: int,
    b: int,
    c: int,
    d: int,
    price_pp: int,
    price_prev: int,
    price_curr: int,
) -> bool:
    return (
        settlement_ids_are_strictly_ordered(a=a, b=b, c=c, d=d)
        and settlement_price_trace_is_monotone(
            price_pp=price_pp,
            price_prev=price_prev,
            price_curr=price_curr,
        )
        and abs(price_curr - price_prev) < 50
    )


def settlement_full_price_rails_ok(
    *,
    a: int,
    b: int,
    c: int,
    d: int,
    price_pp: int,
    price_prev: int,
    price_curr: int,
) -> bool:
    return (
        settlement_compact_price_gate_ok(
            a=a,
            b=b,
            c=c,
            d=d,
            price_pp=price_pp,
            price_prev=price_prev,
            price_curr=price_curr,
        )
        and abs(price_prev - price_pp) < 50
    )
