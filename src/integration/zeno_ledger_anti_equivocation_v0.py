"""Anti-equivocation checks for ZenoLedger v0 evidence sets."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_v0 import hash_v0, validate_checkpoint_v0
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


SLASHING_EVIDENCE_SCHEMA_V0 = "zenodex/zeno_ledger/slashing_evidence/v0"


def _hash_object(domain: str, value: Mapping[str, Any]) -> str:
    return hash_v0(domain, dict(value))


def _watcher_attestation_artifact_hash_v0(attestation: Mapping[str, Any]) -> str:
    body = {key: value for key, value in attestation.items() if key != "attestation_hash"}
    expected_hash = hash_v0("watcher_attestation_v0", body)
    provided_hash = attestation.get("attestation_hash")
    if provided_hash is not None and provided_hash != expected_hash:
        raise ValueError("watcher equivocation evidence attestation_hash mismatch")
    return expected_hash


def _slashing_evidence_v0(body: Mapping[str, Any]) -> dict[str, Any]:
    obj = dict(body)
    if obj.get("schema") != SLASHING_EVIDENCE_SCHEMA_V0:
        raise ValueError("slashing evidence schema mismatch")
    if obj.get("status") != "slashable":
        raise ValueError("slashing evidence status mismatch")
    evidence_hash = hash_v0("zeno_ledger_slashing_evidence_v0", obj)
    return {**obj, "evidence_hash": evidence_hash}


def validate_slashing_evidence_v0(evidence: Mapping[str, Any]) -> None:
    """Validate the shape and hash binding of a slashing evidence packet."""

    obj = dict(_require_mapping(evidence, name="slashing_evidence"))
    if obj.get("schema") != SLASHING_EVIDENCE_SCHEMA_V0:
        raise ValueError("slashing evidence schema mismatch")
    if obj.get("status") != "slashable":
        raise ValueError("slashing evidence status mismatch")
    _require_str(obj.get("evidence_kind"), name="slashing_evidence.evidence_kind")
    _require_str(obj.get("chain_id"), name="slashing_evidence.chain_id", allow_empty=True)
    _require_nonnegative_int(obj.get("height"), name="slashing_evidence.height")
    _require_str(obj.get("subject_id"), name="slashing_evidence.subject_id")
    _require_mapping(obj.get("conflict_key"), name="slashing_evidence.conflict_key")
    header_hashes = _require_sequence(
        obj.get("conflicting_header_hashes"),
        name="slashing_evidence.conflicting_header_hashes",
    )
    if len(header_hashes) != 2:
        raise ValueError("slashing evidence requires two conflicting header hashes")
    header_a = _require_root(header_hashes[0], name="slashing_evidence.conflicting_header_hashes[0]")
    header_b = _require_root(header_hashes[1], name="slashing_evidence.conflicting_header_hashes[1]")
    if header_a == header_b:
        raise ValueError("slashing evidence header hashes must conflict")
    if list(header_hashes) != sorted([header_a, header_b]):
        raise ValueError("slashing evidence header hashes must be sorted")
    artifact_hashes = _require_sequence(obj.get("artifact_hashes"), name="slashing_evidence.artifact_hashes")
    if len(artifact_hashes) != 2:
        raise ValueError("slashing evidence requires two artifact hashes")
    artifact_a = _require_root(artifact_hashes[0], name="slashing_evidence.artifact_hashes[0]")
    artifact_b = _require_root(artifact_hashes[1], name="slashing_evidence.artifact_hashes[1]")
    if artifact_a == artifact_b:
        raise ValueError("slashing evidence artifact hashes must be distinct")
    if list(artifact_hashes) != sorted([artifact_a, artifact_b]):
        raise ValueError("slashing evidence artifact hashes must be sorted")
    _require_str(obj.get("recommended_action"), name="slashing_evidence.recommended_action")
    expected_hash = hash_v0(
        "zeno_ledger_slashing_evidence_v0",
        {key: value for key, value in obj.items() if key != "evidence_hash"},
    )
    if obj.get("evidence_hash") != expected_hash:
        raise ValueError("slashing evidence hash mismatch")


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


def build_checkpoint_equivocation_slashing_evidence_v0(
    checkpoint_a: Mapping[str, Any],
    checkpoint_b: Mapping[str, Any],
) -> dict[str, Any]:
    """Build a deterministic evidence packet for conflicting checkpoints."""

    a = dict(_require_mapping(checkpoint_a, name="checkpoint_a"))
    b = dict(_require_mapping(checkpoint_b, name="checkpoint_b"))
    validate_checkpoint_v0(a)
    validate_checkpoint_v0(b)
    if a["chain_id"] != b["chain_id"]:
        raise ValueError("checkpoint equivocation evidence requires matching chain_id")
    if int(a["height"]) != int(b["height"]):
        raise ValueError("checkpoint equivocation evidence requires matching height")
    if a["sequencer_set_hash"] != b["sequencer_set_hash"]:
        raise ValueError("checkpoint equivocation evidence requires matching sequencer_set_hash")
    if a["header_hash"] == b["header_hash"]:
        raise ValueError("checkpoint equivocation evidence requires conflicting header hashes")
    header_hashes = sorted([str(a["header_hash"]), str(b["header_hash"])])
    checkpoint_hashes = sorted(
        [
            _hash_object("checkpoint_equivocation_artifact_v0", a),
            _hash_object("checkpoint_equivocation_artifact_v0", b),
        ]
    )
    return _slashing_evidence_v0(
        {
            "schema": SLASHING_EVIDENCE_SCHEMA_V0,
            "status": "slashable",
            "evidence_kind": "checkpoint_equivocation",
            "chain_id": str(a["chain_id"]),
            "height": int(a["height"]),
            "subject_id": str(a["sequencer_set_hash"]),
            "conflict_key": {
                "chain_id": str(a["chain_id"]),
                "height": int(a["height"]),
            },
            "conflicting_header_hashes": header_hashes,
            "artifact_hashes": checkpoint_hashes,
            "artifacts": [a, b],
            "recommended_action": "operator_review_then_slash_if_policy_allows",
        }
    )


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


def build_watcher_attestation_equivocation_slashing_evidence_v0(
    attestation_a: Mapping[str, Any],
    attestation_b: Mapping[str, Any],
) -> dict[str, Any]:
    """Build a deterministic evidence packet for conflicting watcher attestations."""

    a = dict(_require_mapping(attestation_a, name="attestation_a"))
    b = dict(_require_mapping(attestation_b, name="attestation_b"))
    profile_a, chain_a, from_a, to_a, header_a = _validate_watcher_attestation_shape(a, index=0)
    profile_b, chain_b, from_b, to_b, header_b = _validate_watcher_attestation_shape(b, index=1)
    if profile_a != profile_b:
        raise ValueError("watcher equivocation evidence requires matching profile_id")
    if chain_a != chain_b:
        raise ValueError("watcher equivocation evidence requires matching chain_id")
    same_range = from_a == from_b and to_a == to_b
    same_tip = to_a == to_b
    if not (same_range or same_tip):
        raise ValueError("watcher equivocation evidence requires matching range or tip height")
    if header_a == header_b:
        raise ValueError("watcher equivocation evidence requires conflicting header hashes")
    attestation_hashes = sorted(
        [
            _watcher_attestation_artifact_hash_v0(a),
            _watcher_attestation_artifact_hash_v0(b),
        ]
    )
    header_hashes = sorted([header_a, header_b])
    return _slashing_evidence_v0(
        {
            "schema": SLASHING_EVIDENCE_SCHEMA_V0,
            "status": "slashable",
            "evidence_kind": "watcher_attestation_equivocation",
            "chain_id": chain_a,
            "height": to_a,
            "subject_id": profile_a,
            "conflict_key": {
                "profile_id": profile_a,
                "chain_id": chain_a,
                "from_height": from_a if same_range else None,
                "to_height": to_a,
                "conflict_scope": "range" if same_range else "tip",
            },
            "conflicting_header_hashes": header_hashes,
            "artifact_hashes": attestation_hashes,
            "artifacts": [a, b],
            "recommended_action": "operator_review_then_slash_if_policy_allows",
        }
    )
