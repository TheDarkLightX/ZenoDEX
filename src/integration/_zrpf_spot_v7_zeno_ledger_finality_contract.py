"""Bounded plain-data contract for the Spot V7 ZenoLedger finality adapter.

This module owns deterministic input snapshotting and policy identity
derivation.  It does not authenticate signatures or mint authority-bearing
capabilities.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Final

from src.integration.zeno_ledger_live_quorum_v0 import (
    LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0,
)
from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
)
from src.integration.zeno_ledger_signer_registry import SIGNER_REGISTRY_SCHEMA_V0
from src.integration.zeno_ledger_v0 import (
    CHECKPOINT_SCHEMA_V0,
    HEADER_SCHEMA_V0,
    canonical_json_bytes_v0,
    hash_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    _hash_bytes,
    _require_uint,
)

SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V1: Final = (
    "zenodex/zrpf/spot_v7/zeno_ledger_checkpoint_finality_evidence/v1"
)

_FINALITY_NETWORK_DOMAIN_V1: Final = "zrpf_spot_v7_zeno_ledger_finality_network_v1"
_FINALITY_PROTOCOL_DOMAIN_V1: Final = "zrpf_spot_v7_zeno_ledger_finality_protocol_v1"
_EXTERNAL_FINALITY_POLICY_DOMAIN_V1: Final = "zrpf_spot_v7_zeno_ledger_external_finality_policy_v1"
_MAX_FINALITY_INPUT_BYTES_V1: Final = 1 * 1_024 * 1_024
_MAX_FINALITY_VALIDATORS_V1: Final = 256
_ZERO_ROOT: Final = "0x" + "00" * 32


class SpotV7ZenoLedgerFinalityBindingErrorV1(ValueError):
    """Stable fail-closed binding error before private capability minting."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_ZENO_LEDGER_FINALITY_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class ZenoLedgerCheckpointFinalityCursorV1:
    """Proposed prior application checkpoint; durable store CAS remains final."""

    sequence: int
    checkpoint_hash: str

    def __post_init__(self) -> None:
        _require_uint(self.sequence, name="checkpoint cursor sequence", maximum=MAX_U64)
        _hash_bytes(self.checkpoint_hash, name="checkpoint cursor hash")


@dataclass(frozen=True, slots=True)
class _FinalityInputSnapshotV1:
    header: dict[str, Any]
    checkpoint: dict[str, Any]
    registry: dict[str, Any]
    envelopes: tuple[dict[str, Any], ...]


def derive_zeno_ledger_finality_network_id_v1(chain_id: str) -> str:
    """Derive the policy identity for one exact ZenoLedger chain."""

    return hash_v0(
        _FINALITY_NETWORK_DOMAIN_V1,
        {"chain_id": _require_nonempty_string(chain_id, name="chain_id")},
    )


def derive_zeno_ledger_finality_protocol_id_v1() -> str:
    """Derive the fixed protocol identity for this adapter version."""

    return hash_v0(
        _FINALITY_PROTOCOL_DOMAIN_V1,
        {
            "checkpoint_schema": CHECKPOINT_SCHEMA_V0,
            "header_schema": HEADER_SCHEMA_V0,
            "live_quorum_schema": LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0,
            "signature_algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
            "signer_registry_schema": SIGNER_REGISTRY_SCHEMA_V0,
        },
    )


def derive_zeno_ledger_external_finality_policy_hash_v1(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
) -> str:
    """Bind chain config and the strict quorum-intersection policy."""

    return hash_v0(
        _EXTERNAL_FINALITY_POLICY_DOMAIN_V1,
        {
            "chain_id": _require_nonempty_string(chain_id, name="chain_id"),
            "config_digest": _require_hash(config_digest, name="config_digest"),
            "sequencer_set_hash": _require_hash(
                sequencer_set_hash,
                name="sequencer_set_hash",
            ),
            "checkpoint_signatures_are_external": True,
            "embedded_signature_set_required_empty": True,
            "quorum_rule": "strictly_more_than_two_thirds_active_weight",
            "signature_algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        },
    )


def _snapshot_inputs(
    *,
    header: object,
    checkpoint: object,
    registry: object,
    envelopes: object,
) -> _FinalityInputSnapshotV1:
    header_value = _snapshot_plain_dict(header, name="header")
    checkpoint_value = _snapshot_plain_dict(checkpoint, name="checkpoint")
    registry_value = _snapshot_plain_dict(registry, name="registry")
    if type(envelopes) is not tuple:
        raise TypeError("envelopes must be an exact tuple")
    if not envelopes or len(envelopes) > _MAX_FINALITY_VALIDATORS_V1:
        raise ValueError("envelopes count is outside the governed bound")
    envelope_values = tuple(
        _snapshot_plain_dict(value, name=f"envelopes[{index}]")
        for index, value in enumerate(envelopes)
    )
    envelope_values = tuple(sorted(envelope_values, key=_envelope_order_key))
    _require_bounded_canonical_json(
        {
            "header": header_value,
            "checkpoint": checkpoint_value,
            "registry": registry_value,
            "envelopes": envelope_values,
        },
        name="checkpoint finality input",
    )
    return _FinalityInputSnapshotV1(
        header=header_value,
        checkpoint=checkpoint_value,
        registry=registry_value,
        envelopes=envelope_values,
    )


def _snapshot_plain_dict(value: object, *, name: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise TypeError(f"{name} must be an exact dict")
    encoded = _require_bounded_canonical_json(value, name=name)
    decoded = json.loads(encoded)
    if type(decoded) is not dict:
        raise TypeError(f"{name} did not decode to an exact dict")
    return decoded


def _require_bounded_canonical_json(value: object, *, name: str) -> bytes:
    encoded = canonical_json_bytes_v0(value)
    if not encoded or len(encoded) > _MAX_FINALITY_INPUT_BYTES_V1:
        raise ValueError(f"{name} exceeds the governed canonical byte bound")
    return encoded


def _envelope_order_key(envelope: dict[str, Any]) -> tuple[str, str]:
    return (
        _require_nonempty_string(envelope.get("signer_id"), name="envelope.signer_id"),
        _require_nonempty_string(envelope.get("key_id"), name="envelope.key_id"),
    )


def _require_nonempty_string(value: object, *, name: str) -> str:
    if type(value) is not str or not value:
        raise ValueError(f"{name} must be an exact nonempty string")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")
    _hash_bytes(value, name=name)
    return value


def _require_positive_u64(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    _require_uint(value, name=name, minimum=1, maximum=MAX_U64)
    return value
