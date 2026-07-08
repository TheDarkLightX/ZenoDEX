from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass

from py_ecc.bls import G2Basic

from ..state.canonical import canonical_json_bytes

OI_DEPTH_CERTIFICATE_SCHEMA = "zenodex.perp.oi_depth_certificate.v1"
OI_DEPTH_SOURCE_AUTHORITY_BINDING_SCHEMA = "zenodex.perp.oi_depth_source_authority_binding.v1"
OI_DEPTH_SOURCE_AUTHORITY_SCHEMA = "zenodex.perp.oi_depth_source_authority.v1"
OI_DEPTH_SOURCE_SET_SCHEMA = "zenodex.perp.oi_depth_source_set.v1"

_CERT_KEYS = frozenset(
    {
        "arbitrage_absorb_bps",
        "canonical_sha256",
        "market_id",
        "schema",
        "source_ids",
        "source_set_hash",
        "spot_depth_quote",
        "valid_from_epoch",
        "valid_until_epoch",
    }
)
_SOURCE_AUTHORITY_KEYS = frozenset(
    {
        "authorized_source_ids",
        "canonical_sha256",
        "market_id",
        "schema",
        "valid_from_epoch",
        "valid_until_epoch",
    }
)
_SOURCE_AUTHORITY_BINDING_KEYS = frozenset(
    {
        "authority_hash",
        "authority_state_root_hash",
        "canonical_sha256",
        "market_id",
        "policy_hash",
        "schema",
        "signature",
        "signer_pubkey",
        "valid_from_epoch",
        "valid_until_epoch",
    }
)
_BPS_SCALE = 10_000


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_market_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_schema(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value.startswith("sha256:") or len(value) != len("sha256:") + 64:
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    suffix = value[len("sha256:") :]
    if suffix.lower() != suffix or any(ch not in "0123456789abcdef" for ch in suffix):
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    return value


def _require_prefixed_hex(value: object, *, name: str, nbytes: int) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    expected_len = len("0x") + 2 * nbytes
    if not value.startswith("0x") or len(value) != expected_len:
        raise ValueError(f"{name} must be 0x-prefixed {nbytes}-byte hex")
    suffix = value[2:]
    if suffix.lower() != suffix or any(ch not in "0123456789abcdef" for ch in suffix):
        raise ValueError(f"{name} must be 0x-prefixed lowercase hex")
    return value


def _require_source_ids(value: object) -> tuple[str, ...]:
    if not isinstance(value, tuple):
        raise TypeError("source_ids must be a tuple")
    out = tuple(_require_market_id(source_id, name="source_id") for source_id in value)
    if not out:
        raise ValueError("source_ids must be non-empty")
    if list(out) != sorted(out):
        raise ValueError("source_ids must be sorted")
    if len(out) != len(set(out)):
        raise ValueError("source_ids must be unique")
    return out


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


def _sha256_payload(payload: object) -> str:
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _signature_message(payload: object) -> bytes:
    return hashlib.sha256(canonical_json_bytes(payload)).digest()


def source_set_hash(source_ids: tuple[str, ...]) -> str:
    checked = _require_source_ids(source_ids)
    return _sha256_payload(
        {
            "schema": OI_DEPTH_SOURCE_SET_SCHEMA,
            "source_ids": list(checked),
        }
    )


@dataclass(frozen=True)
class OIDepthSourceAuthorityBinding:
    schema: str
    market_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    authority_hash: str
    authority_state_root_hash: str
    policy_hash: str
    signer_pubkey: str
    signature: str
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != OI_DEPTH_SOURCE_AUTHORITY_BINDING_SCHEMA:
            raise ValueError("invalid OI depth source authority binding schema")
        _require_market_id(self.market_id, name="market_id")
        _require_non_negative_int(self.valid_from_epoch, name="valid_from_epoch")
        _require_non_negative_int(self.valid_until_epoch, name="valid_until_epoch")
        if self.valid_from_epoch > self.valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_hash(self.authority_hash, name="authority_hash")
        _require_hash(self.authority_state_root_hash, name="authority_state_root_hash")
        _require_hash(self.policy_hash, name="policy_hash")
        _require_prefixed_hex(self.signer_pubkey, name="signer_pubkey", nbytes=48)
        _require_prefixed_hex(self.signature, name="signature", nbytes=96)
        _require_hash(self.canonical_sha256, name="canonical_sha256")
        if self.canonical_sha256 != oi_depth_source_authority_binding_hash(self):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> dict[str, object]:
        return {
            "authority_hash": self.authority_hash,
            "authority_state_root_hash": self.authority_state_root_hash,
            "market_id": self.market_id,
            "policy_hash": self.policy_hash,
            "schema": self.schema,
            "signer_pubkey": self.signer_pubkey,
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }

    def to_payload(self) -> dict[str, object]:
        payload = self.unsigned_payload()
        payload["canonical_sha256"] = self.canonical_sha256
        payload["signature"] = self.signature
        return payload


@dataclass(frozen=True)
class OIDepthSourceAuthority:
    schema: str
    market_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    authorized_source_ids: tuple[str, ...]
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != OI_DEPTH_SOURCE_AUTHORITY_SCHEMA:
            raise ValueError("invalid OI depth source authority schema")
        _require_market_id(self.market_id, name="market_id")
        _require_non_negative_int(self.valid_from_epoch, name="valid_from_epoch")
        _require_non_negative_int(self.valid_until_epoch, name="valid_until_epoch")
        if self.valid_from_epoch > self.valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_source_ids(self.authorized_source_ids)
        _require_hash(self.canonical_sha256, name="canonical_sha256")
        if self.canonical_sha256 != oi_depth_source_authority_hash(self):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> dict[str, object]:
        return {
            "authorized_source_ids": list(self.authorized_source_ids),
            "market_id": self.market_id,
            "schema": self.schema,
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }

    def to_payload(self) -> dict[str, object]:
        payload = self.unsigned_payload()
        payload["canonical_sha256"] = self.canonical_sha256
        return payload


@dataclass(frozen=True)
class OIDepthCertificate:
    schema: str
    market_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    spot_depth_quote: int
    arbitrage_absorb_bps: int
    source_ids: tuple[str, ...]
    source_set_hash: str
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != OI_DEPTH_CERTIFICATE_SCHEMA:
            raise ValueError("invalid OI depth certificate schema")
        _require_market_id(self.market_id, name="market_id")
        _require_non_negative_int(self.valid_from_epoch, name="valid_from_epoch")
        _require_non_negative_int(self.valid_until_epoch, name="valid_until_epoch")
        if self.valid_from_epoch > self.valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_non_negative_int(self.spot_depth_quote, name="spot_depth_quote")
        absorb = _require_non_negative_int(self.arbitrage_absorb_bps, name="arbitrage_absorb_bps")
        if absorb > _BPS_SCALE:
            raise ValueError("arbitrage_absorb_bps must be <= 10000")
        _require_source_ids(self.source_ids)
        _require_hash(self.source_set_hash, name="source_set_hash")
        _require_hash(self.canonical_sha256, name="canonical_sha256")
        if self.source_set_hash != source_set_hash(self.source_ids):
            raise ValueError("source_set_hash mismatch")
        if self.canonical_sha256 != oi_depth_certificate_hash(self):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> dict[str, object]:
        return {
            "arbitrage_absorb_bps": int(self.arbitrage_absorb_bps),
            "market_id": self.market_id,
            "schema": self.schema,
            "source_ids": list(self.source_ids),
            "source_set_hash": self.source_set_hash,
            "spot_depth_quote": int(self.spot_depth_quote),
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }

    def to_payload(self) -> dict[str, object]:
        payload = self.unsigned_payload()
        payload["canonical_sha256"] = self.canonical_sha256
        return payload


@dataclass(frozen=True)
class CertificateVerdict:
    ok: bool
    error: str | None = None
    certificate: OIDepthCertificate | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")
        if self.certificate is not None and not isinstance(self.certificate, OIDepthCertificate):
            raise TypeError("certificate must be an OIDepthCertificate or None")


@dataclass(frozen=True)
class SourceAuthorityVerdict:
    ok: bool
    error: str | None = None
    authority: OIDepthSourceAuthority | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")
        if self.authority is not None and not isinstance(self.authority, OIDepthSourceAuthority):
            raise TypeError("authority must be an OIDepthSourceAuthority or None")


@dataclass(frozen=True)
class SourceAuthorityBindingVerdict:
    ok: bool
    error: str | None = None
    binding: OIDepthSourceAuthorityBinding | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")
        if self.binding is not None and not isinstance(self.binding, OIDepthSourceAuthorityBinding):
            raise TypeError("binding must be an OIDepthSourceAuthorityBinding or None")


def oi_depth_source_authority_binding_hash(binding: OIDepthSourceAuthorityBinding) -> str:
    return _sha256_payload(binding.unsigned_payload())


def oi_depth_source_authority_hash(authority: OIDepthSourceAuthority) -> str:
    return _sha256_payload(authority.unsigned_payload())


def oi_depth_certificate_hash(certificate: OIDepthCertificate) -> str:
    return _sha256_payload(certificate.unsigned_payload())


def build_oi_depth_source_authority(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authorized_source_ids: tuple[str, ...],
) -> OIDepthSourceAuthority:
    unsigned = {
        "authorized_source_ids": list(_require_source_ids(authorized_source_ids)),
        "market_id": _require_market_id(market_id, name="market_id"),
        "schema": OI_DEPTH_SOURCE_AUTHORITY_SCHEMA,
        "valid_from_epoch": _require_non_negative_int(valid_from_epoch, name="valid_from_epoch"),
        "valid_until_epoch": _require_non_negative_int(valid_until_epoch, name="valid_until_epoch"),
    }
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    return OIDepthSourceAuthority(
        schema=OI_DEPTH_SOURCE_AUTHORITY_SCHEMA,
        market_id=_require_market_id(unsigned["market_id"], name="market_id"),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        authorized_source_ids=authorized_source_ids,
        canonical_sha256=_sha256_payload(unsigned),
    )


def build_oi_depth_source_authority_binding(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authority_hash: str,
    authority_state_root_hash: str,
    policy_hash: str,
    signer_privkey: int,
) -> OIDepthSourceAuthorityBinding:
    if not isinstance(signer_privkey, int) or isinstance(signer_privkey, bool) or signer_privkey <= 0:
        raise ValueError("signer_privkey must be a positive int")
    signer_pubkey = "0x" + G2Basic.SkToPk(signer_privkey).hex()
    unsigned = {
        "authority_hash": _require_hash(authority_hash, name="authority_hash"),
        "authority_state_root_hash": _require_hash(
            authority_state_root_hash,
            name="authority_state_root_hash",
        ),
        "market_id": _require_market_id(market_id, name="market_id"),
        "policy_hash": _require_hash(policy_hash, name="policy_hash"),
        "schema": OI_DEPTH_SOURCE_AUTHORITY_BINDING_SCHEMA,
        "signer_pubkey": signer_pubkey,
        "valid_from_epoch": _require_non_negative_int(valid_from_epoch, name="valid_from_epoch"),
        "valid_until_epoch": _require_non_negative_int(valid_until_epoch, name="valid_until_epoch"),
    }
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    signature = "0x" + G2Basic.Sign(signer_privkey, _signature_message(unsigned)).hex()
    return OIDepthSourceAuthorityBinding(
        schema=OI_DEPTH_SOURCE_AUTHORITY_BINDING_SCHEMA,
        market_id=_require_market_id(unsigned["market_id"], name="market_id"),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        authority_hash=_require_hash(unsigned["authority_hash"], name="authority_hash"),
        authority_state_root_hash=_require_hash(
            unsigned["authority_state_root_hash"],
            name="authority_state_root_hash",
        ),
        policy_hash=_require_hash(unsigned["policy_hash"], name="policy_hash"),
        signer_pubkey=signer_pubkey,
        signature=signature,
        canonical_sha256=_sha256_payload(unsigned),
    )


def build_oi_depth_certificate(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    spot_depth_quote: int,
    arbitrage_absorb_bps: int,
    source_ids: tuple[str, ...],
) -> OIDepthCertificate:
    source_hash = source_set_hash(source_ids)
    unsigned = {
        "arbitrage_absorb_bps": _require_non_negative_int(arbitrage_absorb_bps, name="arbitrage_absorb_bps"),
        "market_id": _require_market_id(market_id, name="market_id"),
        "schema": OI_DEPTH_CERTIFICATE_SCHEMA,
        "source_ids": list(_require_source_ids(source_ids)),
        "source_set_hash": source_hash,
        "spot_depth_quote": _require_non_negative_int(spot_depth_quote, name="spot_depth_quote"),
        "valid_from_epoch": _require_non_negative_int(valid_from_epoch, name="valid_from_epoch"),
        "valid_until_epoch": _require_non_negative_int(valid_until_epoch, name="valid_until_epoch"),
    }
    if int(unsigned["arbitrage_absorb_bps"]) > _BPS_SCALE:
        raise ValueError("arbitrage_absorb_bps must be <= 10000")
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    return OIDepthCertificate(
        schema=OI_DEPTH_CERTIFICATE_SCHEMA,
        market_id=str(unsigned["market_id"]),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        spot_depth_quote=int(unsigned["spot_depth_quote"]),
        arbitrage_absorb_bps=int(unsigned["arbitrage_absorb_bps"]),
        source_ids=tuple(source_ids),
        source_set_hash=source_hash,
        canonical_sha256=_sha256_payload(unsigned),
    )


def _payload_to_source_authority_binding(payload: Mapping[str, object]) -> OIDepthSourceAuthorityBinding:
    if set(payload.keys()) != _SOURCE_AUTHORITY_BINDING_KEYS:
        missing = sorted(_SOURCE_AUTHORITY_BINDING_KEYS - set(payload.keys()))
        extra = sorted(set(payload.keys()) - _SOURCE_AUTHORITY_BINDING_KEYS)
        if missing:
            raise ValueError(f"missing OI depth source authority binding field: {missing[0]}")
        raise ValueError(f"unknown OI depth source authority binding field: {extra[0]}")
    return OIDepthSourceAuthorityBinding(
        schema=_require_schema(payload["schema"], name="schema"),
        market_id=_require_market_id(payload["market_id"], name="market_id"),
        valid_from_epoch=_require_non_negative_int(payload["valid_from_epoch"], name="valid_from_epoch"),
        valid_until_epoch=_require_non_negative_int(payload["valid_until_epoch"], name="valid_until_epoch"),
        authority_hash=_require_hash(payload["authority_hash"], name="authority_hash"),
        authority_state_root_hash=_require_hash(
            payload["authority_state_root_hash"],
            name="authority_state_root_hash",
        ),
        policy_hash=_require_hash(payload["policy_hash"], name="policy_hash"),
        signer_pubkey=_require_prefixed_hex(payload["signer_pubkey"], name="signer_pubkey", nbytes=48),
        signature=_require_prefixed_hex(payload["signature"], name="signature", nbytes=96),
        canonical_sha256=_require_hash(payload["canonical_sha256"], name="canonical_sha256"),
    )


def _payload_to_source_authority(payload: Mapping[str, object]) -> OIDepthSourceAuthority:
    if set(payload.keys()) != _SOURCE_AUTHORITY_KEYS:
        missing = sorted(_SOURCE_AUTHORITY_KEYS - set(payload.keys()))
        extra = sorted(set(payload.keys()) - _SOURCE_AUTHORITY_KEYS)
        if missing:
            raise ValueError(f"missing OI depth source authority field: {missing[0]}")
        raise ValueError(f"unknown OI depth source authority field: {extra[0]}")
    authorized_source_ids_raw = payload["authorized_source_ids"]
    if not isinstance(authorized_source_ids_raw, list):
        raise TypeError("authorized_source_ids must be a list")
    return OIDepthSourceAuthority(
        schema=_require_schema(payload["schema"], name="schema"),
        market_id=_require_market_id(payload["market_id"], name="market_id"),
        valid_from_epoch=_require_non_negative_int(payload["valid_from_epoch"], name="valid_from_epoch"),
        valid_until_epoch=_require_non_negative_int(payload["valid_until_epoch"], name="valid_until_epoch"),
        authorized_source_ids=tuple(authorized_source_ids_raw),
        canonical_sha256=_require_hash(payload["canonical_sha256"], name="canonical_sha256"),
    )


def _payload_to_certificate(payload: Mapping[str, object]) -> OIDepthCertificate:
    if set(payload.keys()) != _CERT_KEYS:
        missing = sorted(_CERT_KEYS - set(payload.keys()))
        extra = sorted(set(payload.keys()) - _CERT_KEYS)
        if missing:
            raise ValueError(f"missing OI depth certificate field: {missing[0]}")
        raise ValueError(f"unknown OI depth certificate field: {extra[0]}")
    source_ids_raw = payload["source_ids"]
    if not isinstance(source_ids_raw, list):
        raise TypeError("source_ids must be a list")
    return OIDepthCertificate(
        schema=_require_schema(payload["schema"], name="schema"),
        market_id=_require_market_id(payload["market_id"], name="market_id"),
        valid_from_epoch=_require_non_negative_int(payload["valid_from_epoch"], name="valid_from_epoch"),
        valid_until_epoch=_require_non_negative_int(payload["valid_until_epoch"], name="valid_until_epoch"),
        spot_depth_quote=_require_non_negative_int(payload["spot_depth_quote"], name="spot_depth_quote"),
        arbitrage_absorb_bps=_require_non_negative_int(payload["arbitrage_absorb_bps"], name="arbitrage_absorb_bps"),
        source_ids=tuple(source_ids_raw),
        source_set_hash=_require_hash(payload["source_set_hash"], name="source_set_hash"),
        canonical_sha256=_require_hash(payload["canonical_sha256"], name="canonical_sha256"),
    )


def verify_oi_depth_source_authority_binding_payload(
    payload: object,
    *,
    authority: OIDepthSourceAuthority,
    expected_market_id: str,
    now_epoch: int,
    expected_authority_state_root_hash: str,
    expected_policy_hash: str,
    allowed_signer_pubkeys: tuple[str, ...],
) -> SourceAuthorityBindingVerdict:
    if not isinstance(payload, Mapping):
        return SourceAuthorityBindingVerdict(False, "OI depth source authority binding must be an object")
    try:
        if not isinstance(authority, OIDepthSourceAuthority):
            raise TypeError("authority must be an OIDepthSourceAuthority")
        binding = _payload_to_source_authority_binding(payload)
        market_id = _require_market_id(expected_market_id, name="expected_market_id")
        epoch = _require_non_negative_int(now_epoch, name="now_epoch")
        expected_root = _require_hash(
            expected_authority_state_root_hash,
            name="expected_authority_state_root_hash",
        )
        expected_policy = _require_hash(expected_policy_hash, name="expected_policy_hash")
        allowed_signers = _require_signer_pubkeys(allowed_signer_pubkeys, name="allowed_signer_pubkeys")
        if binding.market_id != market_id:
            return SourceAuthorityBindingVerdict(False, "source authority binding market_id mismatch")
        if epoch < binding.valid_from_epoch or epoch > binding.valid_until_epoch:
            return SourceAuthorityBindingVerdict(False, "source authority binding epoch out of range")
        if binding.authority_hash != oi_depth_source_authority_hash(authority):
            return SourceAuthorityBindingVerdict(False, "source authority binding authority_hash mismatch")
        if binding.authority_state_root_hash != expected_root:
            return SourceAuthorityBindingVerdict(False, "source authority binding state_root_hash mismatch")
        if binding.policy_hash != expected_policy:
            return SourceAuthorityBindingVerdict(False, "source authority binding policy_hash mismatch")
        if binding.signer_pubkey not in allowed_signers:
            return SourceAuthorityBindingVerdict(False, "source authority binding signer not allowed")
        try:
            signature_ok = G2Basic.Verify(
                bytes.fromhex(binding.signer_pubkey.removeprefix("0x")),
                _signature_message(binding.unsigned_payload()),
                bytes.fromhex(binding.signature.removeprefix("0x")),
            )
        except AssertionError:
            signature_ok = False
        if not signature_ok:
            return SourceAuthorityBindingVerdict(False, "source authority binding signature invalid")
    except (TypeError, ValueError) as exc:
        return SourceAuthorityBindingVerdict(False, str(exc))
    return SourceAuthorityBindingVerdict(True, None, binding)


def verify_oi_depth_source_authority_payload(
    payload: object,
    *,
    expected_market_id: str,
    now_epoch: int,
    required_source_ids: tuple[str, ...],
) -> SourceAuthorityVerdict:
    if not isinstance(payload, Mapping):
        return SourceAuthorityVerdict(False, "OI depth source authority must be an object")
    try:
        authority = _payload_to_source_authority(payload)
        market_id = _require_market_id(expected_market_id, name="expected_market_id")
        epoch = _require_non_negative_int(now_epoch, name="now_epoch")
        required_sources = _require_source_ids(required_source_ids)
        if authority.market_id != market_id:
            return SourceAuthorityVerdict(False, "source authority market_id mismatch")
        if epoch < authority.valid_from_epoch or epoch > authority.valid_until_epoch:
            return SourceAuthorityVerdict(False, "source authority epoch out of range")
        authorized = set(authority.authorized_source_ids)
        for source_id in required_sources:
            if source_id not in authorized:
                return SourceAuthorityVerdict(False, f"source_id not authorized: {source_id}")
    except (TypeError, ValueError) as exc:
        return SourceAuthorityVerdict(False, str(exc))
    return SourceAuthorityVerdict(True, None, authority)


def verify_oi_depth_certificate_payload(
    payload: object,
    *,
    expected_market_id: str,
    now_epoch: int,
    expected_spot_depth_quote: int | None = None,
    expected_arbitrage_absorb_bps: int | None = None,
) -> CertificateVerdict:
    if not isinstance(payload, Mapping):
        return CertificateVerdict(False, "OI depth certificate must be an object")
    try:
        certificate = _payload_to_certificate(payload)
        market_id = _require_market_id(expected_market_id, name="expected_market_id")
        epoch = _require_non_negative_int(now_epoch, name="now_epoch")
        if certificate.market_id != market_id:
            return CertificateVerdict(False, "market_id mismatch")
        if epoch < certificate.valid_from_epoch or epoch > certificate.valid_until_epoch:
            return CertificateVerdict(False, "certificate epoch out of range")
        if expected_spot_depth_quote is not None:
            expected_depth = _require_non_negative_int(
                expected_spot_depth_quote,
                name="expected_spot_depth_quote",
            )
            if certificate.spot_depth_quote != expected_depth:
                return CertificateVerdict(False, "spot_depth_quote mismatch")
        if expected_arbitrage_absorb_bps is not None:
            expected_absorb = _require_non_negative_int(
                expected_arbitrage_absorb_bps,
                name="expected_arbitrage_absorb_bps",
            )
            if certificate.arbitrage_absorb_bps != expected_absorb:
                return CertificateVerdict(False, "arbitrage_absorb_bps mismatch")
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))
    return CertificateVerdict(True, None, certificate)


def certificate_payload(certificate: OIDepthCertificate) -> dict[str, object]:
    if not isinstance(certificate, OIDepthCertificate):
        raise TypeError("certificate must be an OIDepthCertificate")
    return certificate.to_payload()


def source_authority_payload(authority: OIDepthSourceAuthority) -> dict[str, object]:
    if not isinstance(authority, OIDepthSourceAuthority):
        raise TypeError("authority must be an OIDepthSourceAuthority")
    return authority.to_payload()


def source_authority_binding_payload(binding: OIDepthSourceAuthorityBinding) -> dict[str, object]:
    if not isinstance(binding, OIDepthSourceAuthorityBinding):
        raise TypeError("binding must be an OIDepthSourceAuthorityBinding")
    return binding.to_payload()


def source_authority_binding_payload_from_fields(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authority_hash: str,
    authority_state_root_hash: str,
    policy_hash: str,
    signer_privkey: int,
) -> dict[str, object]:
    return source_authority_binding_payload(
        build_oi_depth_source_authority_binding(
            market_id=market_id,
            valid_from_epoch=valid_from_epoch,
            valid_until_epoch=valid_until_epoch,
            authority_hash=authority_hash,
            authority_state_root_hash=authority_state_root_hash,
            policy_hash=policy_hash,
            signer_privkey=signer_privkey,
        )
    )


def source_authority_payload_from_fields(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authorized_source_ids: tuple[str, ...],
) -> dict[str, object]:
    return source_authority_payload(
        build_oi_depth_source_authority(
            market_id=market_id,
            valid_from_epoch=valid_from_epoch,
            valid_until_epoch=valid_until_epoch,
            authorized_source_ids=authorized_source_ids,
        )
    )


def certificate_payload_from_fields(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    spot_depth_quote: int,
    arbitrage_absorb_bps: int,
    source_ids: tuple[str, ...],
) -> dict[str, object]:
    return certificate_payload(
        build_oi_depth_certificate(
            market_id=market_id,
            valid_from_epoch=valid_from_epoch,
            valid_until_epoch=valid_until_epoch,
            spot_depth_quote=spot_depth_quote,
            arbitrage_absorb_bps=arbitrage_absorb_bps,
            source_ids=source_ids,
        )
    )
