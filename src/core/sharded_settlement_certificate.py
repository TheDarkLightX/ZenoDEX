from __future__ import annotations

from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

SHARDED_SETTLEMENT_CERTIFICATE_SCHEMA = "zenodex/sharded_settlement_certificate/v1"
SHARDED_SETTLEMENT_SHARD_IDS_SCHEMA = "zenodex/sharded_settlement_shard_ids/v1"
MAX_SETTLEMENT_DELTA_ABS = (1 << 127) - 1

_CERTIFICATE_KEYS = frozenset(
    {
        "schema",
        "batch_id",
        "shard_ids_hash",
        "shards",
        "cross_shard_legs",
    }
)
_SHARD_KEYS = frozenset(
    {
        "shard_id",
        "settlement_root_hash",
        "dx_atoms",
        "dy_atoms",
    }
)
_CROSS_SHARD_LEG_KEYS = frozenset(
    {
        "transfer_id",
        "side",
        "shard_id",
        "counterparty_shard_id",
        "asset_id",
        "amount_atoms",
    }
)


@dataclass(frozen=True)
class ShardedSettlementShardV1:
    shard_id: str
    settlement_root_hash: str
    dx_atoms: int
    dy_atoms: int

    def __post_init__(self) -> None:
        _require_id(self.shard_id, name="shard.shard_id")
        _require_hash(self.settlement_root_hash, name="shard.settlement_root_hash")
        _require_bounded_int(self.dx_atoms, name="shard.dx_atoms")
        _require_bounded_int(self.dy_atoms, name="shard.dy_atoms")

    def to_payload(self) -> dict[str, Any]:
        return {
            "shard_id": self.shard_id,
            "settlement_root_hash": self.settlement_root_hash,
            "dx_atoms": int(self.dx_atoms),
            "dy_atoms": int(self.dy_atoms),
        }

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "ShardedSettlementShardV1":
        _reject_unknown_keys(payload, allowed=_SHARD_KEYS, name="shard")
        return cls(
            shard_id=_require_id(payload.get("shard_id"), name="shard.shard_id"),
            settlement_root_hash=_require_hash(
                payload.get("settlement_root_hash"),
                name="shard.settlement_root_hash",
            ),
            dx_atoms=_require_bounded_int(payload.get("dx_atoms"), name="shard.dx_atoms"),
            dy_atoms=_require_bounded_int(payload.get("dy_atoms"), name="shard.dy_atoms"),
        )


@dataclass(frozen=True)
class CrossShardLegV1:
    transfer_id: str
    side: str
    shard_id: str
    counterparty_shard_id: str
    asset_id: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_id(self.transfer_id, name="leg.transfer_id")
        _require_side(self.side, name="leg.side")
        _require_id(self.shard_id, name="leg.shard_id")
        _require_id(self.counterparty_shard_id, name="leg.counterparty_shard_id")
        _require_id(self.asset_id, name="leg.asset_id")
        _require_positive_int(self.amount_atoms, name="leg.amount_atoms")
        if self.shard_id == self.counterparty_shard_id:
            raise ValueError("cross-shard leg cannot target the same shard")

    def to_payload(self) -> dict[str, Any]:
        return {
            "transfer_id": self.transfer_id,
            "side": self.side,
            "shard_id": self.shard_id,
            "counterparty_shard_id": self.counterparty_shard_id,
            "asset_id": self.asset_id,
            "amount_atoms": int(self.amount_atoms),
        }

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "CrossShardLegV1":
        _reject_unknown_keys(payload, allowed=_CROSS_SHARD_LEG_KEYS, name="cross_shard_leg")
        return cls(
            transfer_id=_require_id(payload.get("transfer_id"), name="leg.transfer_id"),
            side=_require_side(payload.get("side"), name="leg.side"),
            shard_id=_require_id(payload.get("shard_id"), name="leg.shard_id"),
            counterparty_shard_id=_require_id(
                payload.get("counterparty_shard_id"),
                name="leg.counterparty_shard_id",
            ),
            asset_id=_require_id(payload.get("asset_id"), name="leg.asset_id"),
            amount_atoms=_require_positive_int(payload.get("amount_atoms"), name="leg.amount_atoms"),
        )


@dataclass(frozen=True)
class ShardedSettlementCertificateV1:
    batch_id: str
    shard_ids_hash: str
    shards: tuple[ShardedSettlementShardV1, ...]
    cross_shard_legs: tuple[CrossShardLegV1, ...] = ()
    schema: str = SHARDED_SETTLEMENT_CERTIFICATE_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SHARDED_SETTLEMENT_CERTIFICATE_SCHEMA:
            raise ValueError("unsupported sharded settlement certificate schema")
        _require_id(self.batch_id, name="certificate.batch_id")
        _require_hash(self.shard_ids_hash, name="certificate.shard_ids_hash")
        if not isinstance(self.shards, tuple):
            raise TypeError("certificate.shards must be a tuple")
        if not self.shards:
            raise ValueError("certificate.shards must be non-empty")
        for shard in self.shards:
            if not isinstance(shard, ShardedSettlementShardV1):
                raise TypeError("certificate.shards must contain shard records")
        if not isinstance(self.cross_shard_legs, tuple):
            raise TypeError("certificate.cross_shard_legs must be a tuple")
        for leg in self.cross_shard_legs:
            if not isinstance(leg, CrossShardLegV1):
                raise TypeError("certificate.cross_shard_legs must contain leg records")

    def to_payload(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "batch_id": self.batch_id,
            "shard_ids_hash": self.shard_ids_hash,
            "shards": [shard.to_payload() for shard in self.shards],
            "cross_shard_legs": [leg.to_payload() for leg in self.cross_shard_legs],
        }

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "ShardedSettlementCertificateV1":
        _reject_unknown_keys(payload, allowed=_CERTIFICATE_KEYS, name="certificate")
        schema = _require_id(payload.get("schema"), name="certificate.schema")
        if schema != SHARDED_SETTLEMENT_CERTIFICATE_SCHEMA:
            raise ValueError("unsupported sharded settlement certificate schema")
        return cls(
            schema=schema,
            batch_id=_require_id(payload.get("batch_id"), name="certificate.batch_id"),
            shard_ids_hash=_require_hash(
                payload.get("shard_ids_hash"),
                name="certificate.shard_ids_hash",
            ),
            shards=_parse_shards(payload.get("shards")),
            cross_shard_legs=_parse_cross_shard_legs(payload.get("cross_shard_legs")),
        )

    def hash(self) -> str:
        return sharded_settlement_certificate_hash(self)


@dataclass(frozen=True)
class ShardedSettlementVerificationResult:
    ok: bool
    error: str | None
    certificate_hash: str | None = None
    shard_ids_hash: str | None = None
    shard_count: int | None = None
    cross_shard_transfer_count: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted sharded settlement result cannot include error")
            _require_hash(self.certificate_hash, name="result.certificate_hash")
            _require_hash(self.shard_ids_hash, name="result.shard_ids_hash")
            _require_positive_int(self.shard_count, name="result.shard_count")
            _require_non_negative_int(
                self.cross_shard_transfer_count,
                name="result.cross_shard_transfer_count",
            )
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected sharded settlement result must include error")
        if (
            self.certificate_hash is not None
            or self.shard_ids_hash is not None
            or self.shard_count is not None
            or self.cross_shard_transfer_count is not None
        ):
            raise ValueError("rejected sharded settlement result cannot include accepted artifacts")


def shard_ids_hash(shard_ids: Sequence[str]) -> str:
    ids = _parse_expected_shard_ids(shard_ids)
    if tuple(sorted(ids)) != ids:
        raise ValueError("expected shard ids must be sorted")
    body = {
        "schema": SHARDED_SETTLEMENT_SHARD_IDS_SCHEMA,
        "shard_ids": list(ids),
    }
    return sha256_hex(
        domain_sep_bytes("sharded_settlement_shard_ids", version=1)
        + canonical_json_bytes(body)
    )


def sharded_settlement_certificate_hash(
    certificate: ShardedSettlementCertificateV1 | Mapping[str, Any],
) -> str:
    payload = (
        certificate.to_payload()
        if isinstance(certificate, ShardedSettlementCertificateV1)
        else ShardedSettlementCertificateV1.from_payload(certificate).to_payload()
    )
    return sha256_hex(
        domain_sep_bytes("sharded_settlement_certificate", version=1)
        + canonical_json_bytes(payload)
    )


def verify_sharded_settlement_certificate_payload(
    payload: Mapping[str, Any],
    *,
    expected_shard_ids: Sequence[str] | None = None,
    expected_shard_ids_hash: str | None = None,
) -> ShardedSettlementVerificationResult:
    try:
        certificate = ShardedSettlementCertificateV1.from_payload(payload)
        _validate_shards(
            certificate,
            expected_shard_ids=expected_shard_ids,
            expected_shard_ids_hash=expected_shard_ids_hash,
        )
        transfer_count = _validate_cross_shard_legs(certificate)
    except (TypeError, ValueError) as exc:
        return ShardedSettlementVerificationResult(ok=False, error=str(exc))
    return ShardedSettlementVerificationResult(
        ok=True,
        error=None,
        certificate_hash=certificate.hash(),
        shard_ids_hash=certificate.shard_ids_hash,
        shard_count=len(certificate.shards),
        cross_shard_transfer_count=transfer_count,
    )


def build_sharded_settlement_certificate(
    *,
    batch_id: str,
    shards: Sequence[ShardedSettlementShardV1],
    cross_shard_legs: Sequence[CrossShardLegV1] = (),
) -> ShardedSettlementCertificateV1:
    parsed_shards = tuple(shards)
    parsed_legs = tuple(cross_shard_legs)
    ids = tuple(shard.shard_id for shard in parsed_shards)
    return ShardedSettlementCertificateV1(
        batch_id=batch_id,
        shard_ids_hash=shard_ids_hash(ids),
        shards=parsed_shards,
        cross_shard_legs=parsed_legs,
    )


def _validate_shards(
    certificate: ShardedSettlementCertificateV1,
    *,
    expected_shard_ids: Sequence[str] | None,
    expected_shard_ids_hash: str | None,
) -> None:
    shard_ids = tuple(shard.shard_id for shard in certificate.shards)
    if tuple(sorted(shard_ids)) != shard_ids:
        raise ValueError("certificate.shards must be sorted by shard_id")
    if len(set(shard_ids)) != len(shard_ids):
        raise ValueError("duplicate shard_id in certificate.shards")
    computed_hash = shard_ids_hash(shard_ids)
    if computed_hash != certificate.shard_ids_hash:
        raise ValueError("certificate.shard_ids_hash mismatch")
    if expected_shard_ids is not None and tuple(_parse_expected_shard_ids(expected_shard_ids)) != shard_ids:
        raise ValueError("certificate shard ids do not match expected shard ids")
    if expected_shard_ids_hash is not None:
        expected_hash = _require_hash(expected_shard_ids_hash, name="expected_shard_ids_hash")
        if expected_hash != certificate.shard_ids_hash:
            raise ValueError("certificate shard_ids_hash does not match expected shard ids hash")
    total_delta = 0
    for shard in certificate.shards:
        local_delta = shard.dx_atoms + shard.dy_atoms
        if local_delta != 0:
            raise ValueError(f"shard {shard.shard_id} is not balanced")
        total_delta += local_delta
    if total_delta != 0:
        raise ValueError("aggregate shard delta is not balanced")


def _validate_cross_shard_legs(certificate: ShardedSettlementCertificateV1) -> int:
    known_shards = {shard.shard_id for shard in certificate.shards}
    previous_key: tuple[str, str, str, str, str] | None = None
    grouped: dict[str, list[CrossShardLegV1]] = defaultdict(list)
    for leg in certificate.cross_shard_legs:
        key = (
            leg.transfer_id,
            leg.side,
            leg.shard_id,
            leg.counterparty_shard_id,
            leg.asset_id,
        )
        if previous_key is not None and key <= previous_key:
            raise ValueError("certificate.cross_shard_legs must be strictly sorted")
        previous_key = key
        if leg.shard_id not in known_shards:
            raise ValueError("cross-shard leg references unknown shard_id")
        if leg.counterparty_shard_id not in known_shards:
            raise ValueError("cross-shard leg references unknown counterparty_shard_id")
        grouped[leg.transfer_id].append(leg)

    for transfer_id, legs in grouped.items():
        if len(legs) != 2:
            raise ValueError(f"cross-shard transfer {transfer_id} must have exactly two legs")
        debit = next((leg for leg in legs if leg.side == "debit"), None)
        credit = next((leg for leg in legs if leg.side == "credit"), None)
        if debit is None or credit is None:
            raise ValueError(f"cross-shard transfer {transfer_id} must have one debit and one credit")
        if debit.shard_id != credit.counterparty_shard_id:
            raise ValueError(f"cross-shard transfer {transfer_id} shard endpoints mismatch")
        if debit.counterparty_shard_id != credit.shard_id:
            raise ValueError(f"cross-shard transfer {transfer_id} counterparty endpoints mismatch")
        if debit.asset_id != credit.asset_id:
            raise ValueError(f"cross-shard transfer {transfer_id} asset mismatch")
        if debit.amount_atoms != credit.amount_atoms:
            raise ValueError(f"cross-shard transfer {transfer_id} amount mismatch")
    return len(grouped)


def _parse_shards(value: object) -> tuple[ShardedSettlementShardV1, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("certificate.shards must be a sequence")
    return tuple(
        ShardedSettlementShardV1.from_payload(_require_mapping(row, name="certificate.shard"))
        for row in value
    )


def _parse_cross_shard_legs(value: object) -> tuple[CrossShardLegV1, ...]:
    if value is None:
        return ()
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("certificate.cross_shard_legs must be a sequence")
    return tuple(
        CrossShardLegV1.from_payload(_require_mapping(row, name="certificate.cross_shard_leg"))
        for row in value
    )


def _parse_expected_shard_ids(value: Sequence[str]) -> tuple[str, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("expected shard ids must be a sequence")
    return tuple(_require_id(item, name="expected_shard_id") for item in value)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    text = _require_id(value, name=name)
    if not text.startswith("0x") or len(text) != 66:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex digest")
    try:
        int(text[2:], 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex digest") from exc
    if text[2:].lower() != text[2:]:
        raise ValueError(f"{name} must use lowercase hex")
    return text


def _require_side(value: object, *, name: str) -> str:
    side = _require_id(value, name=name)
    if side not in {"credit", "debit"}:
        raise ValueError(f"{name} must be credit or debit")
    return side


def _require_bounded_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if abs(out) > MAX_SETTLEMENT_DELTA_ABS:
        raise ValueError(f"{name} exceeds sharded settlement delta bound")
    return out


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _reject_unknown_keys(
    payload: Mapping[str, Any],
    *,
    allowed: frozenset[str],
    name: str,
) -> None:
    unknown = sorted(set(payload) - set(allowed))
    if unknown:
        raise ValueError(f"{name} has unsupported fields: {', '.join(unknown)}")
