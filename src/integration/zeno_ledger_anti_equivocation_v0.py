"""Anti-equivocation checks for ZenoLedger v0 evidence sets."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_v0 import validate_checkpoint_v0
from src.integration.zeno_ledger_watcher import WATCHER_ATTESTATION_SCHEMA_V0, WATCHER_ATTESTATION_STATUS_V0
from src.state.canonical import canonical_hex_fixed_allow_0x


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_sequence(value: object, *, name: str) -> Sequence[object]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (value == "" and not allow_empty):
        requirement = "a str" if allow_empty else "a non-empty str"
        raise ValueError(f"{name} must be {requirement}")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def validate_checkpoint_non_equivocation_v0(checkpoints: Sequence[Mapping[str, Any]]) -> None:
    """Reject conflicting checkpoints for the same `(chain_id, height)`."""

    items = _require_sequence(checkpoints, name="checkpoints")
    if not items:
        raise ValueError("checkpoints must be non-empty")
    by_height: dict[tuple[str, int], str] = {}
    for index, raw_checkpoint in enumerate(items):
        checkpoint = dict(_require_mapping(raw_checkpoint, name=f"checkpoints[{index}]"))
        validate_checkpoint_v0(checkpoint)
        key = (str(checkpoint["chain_id"]), int(checkpoint["height"]))
        header_hash = str(checkpoint["header_hash"])
        previous = by_height.get(key)
        if previous is not None and previous != header_hash:
            raise ValueError(f"checkpoint equivocation detected for chain_id={key[0]!r}, height={key[1]}")
        by_height[key] = header_hash


def _validate_watcher_attestation_shape(
    attestation: Mapping[str, Any],
    *,
    index: int,
) -> tuple[str, str, int, int, str]:
    obj = _require_mapping(attestation, name=f"watcher_attestations[{index}]")
    if obj.get("schema") != WATCHER_ATTESTATION_SCHEMA_V0:
        raise ValueError(f"watcher_attestations[{index}] schema mismatch")
    if obj.get("status") != WATCHER_ATTESTATION_STATUS_V0:
        raise ValueError(f"watcher_attestations[{index}] status mismatch")
    profile_id = _require_root(
        obj.get("profile_id"),
        name=f"watcher_attestations[{index}].profile_id",
    )
    chain_id = _require_str(
        obj.get("chain_id"),
        name=f"watcher_attestations[{index}].chain_id",
        allow_empty=True,
    )
    from_height = _require_nonnegative_int(
        obj.get("from_height"),
        name=f"watcher_attestations[{index}].from_height",
    )
    to_height = _require_nonnegative_int(
        obj.get("to_height"),
        name=f"watcher_attestations[{index}].to_height",
    )
    if to_height < from_height:
        raise ValueError(f"watcher_attestations[{index}] to_height precedes from_height")
    header_hash = _require_root(
        obj.get("last_header_hash"),
        name=f"watcher_attestations[{index}].last_header_hash",
    )
    return profile_id, chain_id, from_height, to_height, header_hash


def validate_watcher_attestation_non_equivocation_v0(
    watcher_attestations: Sequence[Mapping[str, Any]],
) -> None:
    """Reject conflicting watcher range evidence for the same `(chain_id, range)`."""

    items = _require_sequence(watcher_attestations, name="watcher_attestations")
    if not items:
        raise ValueError("watcher_attestations must be non-empty")
    by_range: dict[tuple[str, str, int, int], str] = {}
    by_tip: dict[tuple[str, str, int], str] = {}
    for index, raw_attestation in enumerate(items):
        profile_id, chain_id, from_height, to_height, header_hash = _validate_watcher_attestation_shape(
            raw_attestation,
            index=index,
        )
        range_key = (profile_id, chain_id, from_height, to_height)
        previous_range = by_range.get(range_key)
        if previous_range is not None and previous_range != header_hash:
            raise ValueError(
                f"watcher attestation equivocation detected for profile_id={profile_id!r}, "
                f"chain_id={chain_id!r}, range={from_height}..{to_height}"
            )
        by_range[range_key] = header_hash

        tip_key = (profile_id, chain_id, to_height)
        previous_tip = by_tip.get(tip_key)
        if previous_tip is not None and previous_tip != header_hash:
            raise ValueError(
                f"watcher attestation tip equivocation detected for profile_id={profile_id!r}, "
                f"chain_id={chain_id!r}, height={to_height}"
            )
        by_tip[tip_key] = header_hash
