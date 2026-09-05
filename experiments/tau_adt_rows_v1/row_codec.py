"""Bounded, research-only codec for Tau ADT settlement rows.

The codec is a pure adapter around the exact ``EconomicAmountV2`` value.  It
does not run Tau, read files, or grant any settlement authority.  Identity
strings use their complete fixed-width ASCII payload, so a caller can compare
decoded rows with its expected snapshot without losing identity information.
"""

from __future__ import annotations

import re
from typing import Final, cast

from src.core.global_settlement_primitives_v2 import (
    MAX_ATOMS_V2,
    MAX_TOKEN_BYTES_V2,
    EconomicAmountV2,
)

MAX_ROWS_V1: Final = 8
MAX_IDENTITY_BYTES_V1: Final = MAX_TOKEN_BYTES_V2
MAX_BV1280_BITS_V1: Final = 1280
MAX_BV128_BITS_V1: Final = 128
MAX_BV1280_VALUE_V1: Final = (1 << MAX_BV1280_BITS_V1) - 1
MAX_BV128_VALUE_V1: Final = (1 << MAX_BV128_BITS_V1) - 1
MAX_BV1280_DECIMAL_DIGITS_V1: Final = len(str(MAX_BV1280_VALUE_V1))
MAX_BV128_DECIMAL_DIGITS_V1: Final = len(str(MAX_BV128_VALUE_V1))

# These limits are deliberately small compared with the engine's general
# output limits.  A valid eight-row transcript is below 16 KiB; every bound is
# checked before parsing an untrusted line or converting a decimal integer.
MAX_ROW_LINE_BYTES_V1: Final = 2_048
MAX_STDOUT_BYTES_V1: Final = 64 * 1_024
MAX_STDERR_BYTES_V1: Final = 4 * 1_024
MAX_INPUT_BYTES_V1: Final = MAX_STDOUT_BYTES_V1

TYPE_BANNER_V1: Final = (
    "[1] type Row = {owner:bv[1280], asset:bv[1280], "
    "custody_domain:bv[1280], amount_atoms:bv[128]}"
)
INPUT_BANNER_V1: Final = "[1] i:Row := in /dev/stdin."
OUTPUT_BANNER_V1: Final = "[2] o:Row := out console."

_DECIMAL_RE = re.compile(r"[0-9]+")
_ROW_RE = re.compile(
    r'^o\[([0-9]+)\] := \{ owner: "([0-9]+)", asset: "([0-9]+)", '
    r'custody_domain: "([0-9]+)", amount_atoms: "([0-9]+)" \}$'
)
_TIMING_RE = re.compile(r"\tstep: [0-9]{1,12}(?:\.[0-9]{1,12})? ms")
_MISSING = object()
_RowFieldsV1 = tuple[str, str, str, int]


def _require_identity(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must not be empty")
    if len(value) > MAX_IDENTITY_BYTES_V1:
        raise ValueError(f"{name} exceeds {MAX_IDENTITY_BYTES_V1} ASCII bytes")
    if any(ord(char) < 0x21 or ord(char) > 0x7E for char in value):
        raise ValueError(f"{name} must use printable ASCII")
    return value


def _require_amount(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if value > MAX_ATOMS_V2:
        raise ValueError(f"{name} must fit an unsigned 128-bit integer")
    return value


def _pack_identity(value: object, *, name: str) -> str:
    identity = _require_identity(value, name=name)
    packed = identity.encode("ascii").ljust(MAX_IDENTITY_BYTES_V1, b"\x00")
    return str(int.from_bytes(packed, "big"))


def _require_rows(rows: object) -> tuple[EconomicAmountV2, ...]:
    if type(rows) is not tuple:
        raise TypeError("rows must be an exact tuple")
    if len(rows) > MAX_ROWS_V1:
        raise ValueError(f"rows exceeds the {MAX_ROWS_V1}-row ceiling")
    for index, row in enumerate(rows):
        if type(row) is not EconomicAmountV2:
            raise TypeError(f"rows[{index}] must be an exact EconomicAmountV2")
    return cast(tuple[EconomicAmountV2, ...], rows)


def _snapshot_row(row: EconomicAmountV2, *, index: int) -> _RowFieldsV1:
    owner = getattr(row, "owner", _MISSING)
    asset = getattr(row, "asset", _MISSING)
    custody_domain = getattr(row, "custody_domain", _MISSING)
    amount_atoms = getattr(row, "amount_atoms", _MISSING)
    if any(
        value is _MISSING
        for value in (owner, asset, custody_domain, amount_atoms)
    ):
        raise TypeError(f"rows[{index}] is a malformed EconomicAmountV2")
    return (
        _require_identity(owner, name=f"rows[{index}].owner"),
        _require_identity(asset, name=f"rows[{index}].asset"),
        _require_identity(custody_domain, name=f"rows[{index}].custody_domain"),
        _require_amount(amount_atoms, name=f"rows[{index}].amount_atoms"),
    )


def _require_canonical_keys(rows: tuple[_RowFieldsV1, ...]) -> None:
    keys = tuple((fields[1], fields[0], fields[2]) for fields in rows)
    if keys != tuple(sorted(set(keys))):
        raise ValueError("rows must be canonically ordered and unique by row.key")


def _encode_row(fields: _RowFieldsV1) -> str:
    owner_text, asset_text, custody_domain_text, amount_atoms = fields
    owner = _pack_identity(owner_text, name="row owner")
    asset = _pack_identity(asset_text, name="row asset")
    custody_domain = _pack_identity(custody_domain_text, name="row custody domain")
    amount_atoms = _require_amount(amount_atoms, name="row amount_atoms")
    return (
        '{ owner: "'
        + owner
        + '", asset: "'
        + asset
        + '", custody_domain: "'
        + custody_domain
        + '", amount_atoms: "'
        + str(amount_atoms)
        + '" }'
    )


def encode_rows_v1(rows: object) -> str:
    """Encode canonical rows as newline-delimited Tau ADT records.

    ``rows`` must be an exact tuple containing at most eight exact
    ``EconomicAmountV2`` values.  The tuple is ordered by each row's
    ``(asset, owner, custody_domain)`` key.  Identity fields retain all ASCII
    bytes in a 160-byte big-endian ``bv[1280]`` payload; amounts are unsigned
    128-bit decimal strings.  The result is deterministic and has no I/O.
    """

    validated = _require_rows(rows)
    snapshots = tuple(
        _snapshot_row(row, index=index) for index, row in enumerate(validated)
    )
    _require_canonical_keys(snapshots)
    lines = tuple(_encode_row(fields) for fields in snapshots)
    encoded = "\n".join(lines) + ("\n" if lines else "")
    if len(encoded) > MAX_INPUT_BYTES_V1:
        raise ValueError(f"encoded rows exceed the {MAX_INPUT_BYTES_V1}-byte ceiling")
    return encoded


def _require_text(value: object, *, name: str, max_bytes: int) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if len(value) > max_bytes:
        raise ValueError(f"{name} exceeds the {max_bytes}-byte ceiling")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must use ASCII") from exc
    if len(encoded) > max_bytes:
        raise ValueError(f"{name} exceeds the {max_bytes}-byte ceiling")
    return value


def _parse_decimal(value: str, *, name: str, maximum: int, max_digits: int) -> int:
    # Bound the decimal text before the regex and before Python's arbitrary
    # precision conversion.  Canonical decimal has no leading zero padding.
    if not 1 <= len(value) <= max_digits:
        raise ValueError(f"{name} has an out-of-bounds decimal width")
    if value[0] == "0" and value != "0":
        raise ValueError(f"{name} is not canonical decimal")
    if _DECIMAL_RE.fullmatch(value) is None:
        raise ValueError(f"{name} is not decimal")
    parsed = int(value)
    if parsed > maximum:
        raise ValueError(f"{name} overflows its unsigned width")
    return parsed


def _unpack_identity(value: str, *, name: str) -> str:
    packed_value = _parse_decimal(
        value,
        name=name,
        maximum=MAX_BV1280_VALUE_V1,
        max_digits=MAX_BV1280_DECIMAL_DIGITS_V1,
    )
    if packed_value == 0:
        raise ValueError(f"{name} cannot encode an empty identity")
    packed = packed_value.to_bytes(MAX_IDENTITY_BYTES_V1, "big")
    payload = packed.rstrip(b"\x00")
    if not payload or b"\x00" in payload:
        raise ValueError(f"{name} contains a non-trailing NUL or has invalid width")
    try:
        identity = payload.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{name} is not ASCII") from exc
    return _require_identity(identity, name=name)


def _decode_row(fields: tuple[str, str, str, str]) -> EconomicAmountV2:
    owner_decimal, asset_decimal, custody_decimal, amount_decimal = fields
    owner = _unpack_identity(owner_decimal, name="row owner")
    asset = _unpack_identity(asset_decimal, name="row asset")
    custody_domain = _unpack_identity(custody_decimal, name="row custody domain")
    amount_atoms = _parse_decimal(
        amount_decimal,
        name="row amount_atoms",
        maximum=MAX_BV128_VALUE_V1,
        max_digits=MAX_BV128_DECIMAL_DIGITS_V1,
    )
    return EconomicAmountV2(owner, asset, custody_domain, amount_atoms)


def decode_output_v1(
    stdout: object,
    stderr: object,
    *,
    expected_count: object,
) -> tuple[EconomicAmountV2, ...]:
    """Decode one exact Tau ADT transcript into owned economic rows.

    The decoder accepts only the three observed banners, blank lines, exact
    row assignments, and a bounded ``step`` timing line after a row.  It
    requires row indices ``0..expected_count-1`` in order, empty stderr, and
    canonical unique row keys.  It never invokes Tau or performs I/O.
    """

    if type(expected_count) is not int:
        raise TypeError("expected_count must be an integer")
    if not 0 <= expected_count <= MAX_ROWS_V1:
        raise ValueError(f"expected_count must be between zero and {MAX_ROWS_V1}")
    output = _require_text(stdout, name="stdout", max_bytes=MAX_STDOUT_BYTES_V1)
    errors = _require_text(stderr, name="stderr", max_bytes=MAX_STDERR_BYTES_V1)
    if errors:
        raise ValueError("stderr must be empty")

    stage = 0
    rows: list[EconomicAmountV2] = []
    last_event = "banner"
    for line in output.split("\n"):
        if not line:
            continue
        if line == TYPE_BANNER_V1:
            if stage != 0:
                raise ValueError("unexpected or duplicate Tau type banner")
            stage = 1
            continue
        if line == INPUT_BANNER_V1:
            if stage != 1:
                raise ValueError("unexpected or duplicate Tau input banner")
            stage = 2
            continue
        if line == OUTPUT_BANNER_V1:
            if stage != 2:
                raise ValueError("unexpected or duplicate Tau output banner")
            stage = 3
            last_event = "banner"
            continue
        if len(line) > MAX_ROW_LINE_BYTES_V1:
            raise ValueError(f"Tau output line exceeds the {MAX_ROW_LINE_BYTES_V1}-byte ceiling")
        if stage != 3:
            raise ValueError("unexpected Tau output before exact banners")
        if _TIMING_RE.fullmatch(line) is not None:
            if not rows or last_event != "row":
                raise ValueError("Tau timing must follow a row")
            last_event = "timing"
            continue
        match = _ROW_RE.fullmatch(line)
        if match is None:
            raise ValueError("unrecognized Tau output or diagnostic")
        index_text, owner, asset, custody_domain, amount_atoms = match.groups()
        if len(index_text) > 2:
            raise ValueError("Tau output index exceeds its resource bound")
        index = int(index_text)
        if str(index) != index_text:
            raise ValueError("Tau output indices must use canonical decimal")
        if len(rows) >= expected_count:
            raise ValueError("Tau emitted more rows than expected")
        if index != len(rows):
            raise ValueError("Tau output indices must be exact and ordered")
        rows.append(_decode_row((owner, asset, custody_domain, amount_atoms)))
        last_event = "row"

    if stage != 3:
        raise ValueError("Tau output is missing an exact banner")
    if len(rows) != expected_count:
        raise ValueError("Tau output row count does not match expected_count")
    decoded = tuple(rows)
    snapshots = tuple(
        _snapshot_row(row, index=index) for index, row in enumerate(decoded)
    )
    _require_canonical_keys(snapshots)
    return decoded


__all__ = [
    "MAX_ROWS_V1",
    "MAX_IDENTITY_BYTES_V1",
    "MAX_BV1280_BITS_V1",
    "MAX_BV128_BITS_V1",
    "MAX_BV1280_VALUE_V1",
    "MAX_BV128_VALUE_V1",
    "MAX_BV1280_DECIMAL_DIGITS_V1",
    "MAX_BV128_DECIMAL_DIGITS_V1",
    "MAX_ROW_LINE_BYTES_V1",
    "MAX_STDOUT_BYTES_V1",
    "MAX_STDERR_BYTES_V1",
    "MAX_INPUT_BYTES_V1",
    "TYPE_BANNER_V1",
    "INPUT_BANNER_V1",
    "OUTPUT_BANNER_V1",
    "encode_rows_v1",
    "decode_output_v1",
]
