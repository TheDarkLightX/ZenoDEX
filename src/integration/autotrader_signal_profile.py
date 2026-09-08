"""Canonical finite metadata codec for external AutoTrader signal profiles.

The codec carries provenance metadata only.  It does not authorize a signal or
replace the existing ``ExternalSignalObservation`` acceptance guard.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..kernels.python.external_signal_profile_decode_v2 import transform as _decode_transform
from ..kernels.python.external_signal_profile_encode_v2 import transform as _encode_transform

PROFILE_TYPE = "profile_type"
SOURCE_INDEX_TYPE = "source_index_type"
SOURCE_INDEX_RANGE = "source_index_range"
TRUST_INDEX_TYPE = "trust_index_type"
TRUST_INDEX_RANGE = "trust_index_range"
FRESHNESS_TYPE = "freshness_ok_type"
AUTH_TYPE = "auth_ok_type"
ADVISORY_ONLY_TYPE = "advisory_only_type"
CODE_TYPE = "code_type"
CODE_RANGE = "code_range"
CODE_RESERVED = "code_reserved"
ENCODED_CODE_RESERVED = "encoded_code_reserved"

MAX_PROFILE_INDEX = 3
MAX_U8 = 0xFF
RESERVED_BIT = 0x80
RESERVED_SENTINEL = 0xFF


def _validate_index(value: object, *, type_code: str, range_code: str) -> int:
    if type(value) is not int:
        raise TypeError(type_code)
    if value < 0 or value > MAX_PROFILE_INDEX:
        raise ValueError(range_code)
    return value


def _validate_bool(value: object, *, type_code: str) -> bool:
    if type(value) is not bool:
        raise TypeError(type_code)
    return value


@dataclass(frozen=True, slots=True)
class SignalProfile:
    """The five exact metadata fields carried by one external signal."""

    source_index: int
    trust_index: int
    freshness_ok: bool
    auth_ok: bool
    advisory_only: bool

    def __post_init__(self) -> None:
        _validate_profile_fields(self)


def _validate_profile_fields(profile: SignalProfile) -> None:
    _validate_index(
        profile.source_index,
        type_code=SOURCE_INDEX_TYPE,
        range_code=SOURCE_INDEX_RANGE,
    )
    _validate_index(
        profile.trust_index,
        type_code=TRUST_INDEX_TYPE,
        range_code=TRUST_INDEX_RANGE,
    )
    _validate_bool(profile.freshness_ok, type_code=FRESHNESS_TYPE)
    _validate_bool(profile.auth_ok, type_code=AUTH_TYPE)
    _validate_bool(profile.advisory_only, type_code=ADVISORY_ONLY_TYPE)


def _validate_profile(profile: object) -> SignalProfile:
    if type(profile) is not SignalProfile:
        raise TypeError(PROFILE_TYPE)
    _validate_profile_fields(profile)
    return profile


def _validate_code(code: object) -> int:
    if type(code) is not int:
        raise TypeError(CODE_TYPE)
    if code < 0 or code > MAX_U8:
        raise ValueError(CODE_RANGE)
    return code


def encode_profile(profile: SignalProfile) -> int:
    """Pack one validated profile into its canonical seven-bit byte value."""

    profile = _validate_profile(profile)
    packed = (profile.source_index << 5) | (profile.trust_index << 3)
    if profile.freshness_ok:
        packed |= 1 << 2
    if profile.auth_ok:
        packed |= 1 << 1
    if profile.advisory_only:
        packed |= 1
    encoded = _encode_transform(packed)
    if encoded == RESERVED_SENTINEL:
        raise ValueError(ENCODED_CODE_RESERVED)
    return encoded


def decode_profile(code: object) -> SignalProfile:
    """Unpack a canonical byte into metadata, rejecting the reserved-bit lane."""

    code = _validate_code(code)
    decoded = _decode_transform(code)
    if decoded == RESERVED_SENTINEL:
        raise ValueError(CODE_RESERVED)
    return SignalProfile(
        source_index=(decoded >> 5) & 0b11,
        trust_index=(decoded >> 3) & 0b11,
        freshness_ok=bool(decoded & (1 << 2)),
        auth_ok=bool(decoded & (1 << 1)),
        advisory_only=bool(decoded & 1),
    )


__all__ = [
    "ADVISORY_ONLY_TYPE",
    "AUTH_TYPE",
    "CODE_RANGE",
    "CODE_RESERVED",
    "CODE_TYPE",
    "ENCODED_CODE_RESERVED",
    "FRESHNESS_TYPE",
    "MAX_PROFILE_INDEX",
    "MAX_U8",
    "PROFILE_TYPE",
    "RESERVED_BIT",
    "RESERVED_SENTINEL",
    "SOURCE_INDEX_RANGE",
    "SOURCE_INDEX_TYPE",
    "SignalProfile",
    "TRUST_INDEX_RANGE",
    "TRUST_INDEX_TYPE",
    "decode_profile",
    "encode_profile",
]
