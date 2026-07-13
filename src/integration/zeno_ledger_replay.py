"""Replay-bound ZenoLedger state-transition validation."""

from __future__ import annotations

import math
from dataclasses import asdict
from typing import Any, Mapping

from src.core.dex import DexConfig, DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.zeno_ledger_v0 import (
    apply_body_transactions_v0,
    dex_state_root_v0,
    hash_v0,
    validate_block_state_transition_v0,
    validate_header_chain_state_continuity_v0,
)

REPLAY_ENGINE_CONFIG_SCHEMA = "zenodex/zeno_ledger/replay_engine_config/v0"
REPLAY_ENGINE_CONFIG_PROFILE = "bounded_dex_engine_v0"


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty str")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_optional_str(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be null or a non-empty str")
    return value


def _canonical_config_projection(value: object) -> object:
    if value is None or isinstance(value, (bool, int, str)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("engine config contains a non-finite float")
        return {"float64_hex": value.hex()}
    if isinstance(value, Mapping):
        if not all(isinstance(key, str) for key in value):
            raise TypeError("engine config mapping keys must be strings")
        return {key: _canonical_config_projection(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_canonical_config_projection(item) for item in value]
    raise TypeError(f"engine config contains unsupported value type: {type(value).__name__}")


def replay_engine_config_document_v0(config: DexEngineConfig) -> dict[str, Any]:
    """Return the complete config commitment for the bounded replay profile."""

    if not isinstance(config, DexEngineConfig):
        raise TypeError("config must be a DexEngineConfig")
    replay_config = DexEngineConfig(
        allow_missing_settlement=config.allow_missing_settlement,
        require_intent_signatures=config.require_intent_signatures,
        allow_unsigned_intents_if_tx_sender_matches=config.allow_unsigned_intents_if_tx_sender_matches,
        chain_id=config.chain_id,
        dex_config=DexConfig(
            protocol_fee_share_bps=config.dex_config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=config.dex_config.protocol_fee_recipient_pubkey,
        ),
        min_lp_position_age_seconds=config.min_lp_position_age_seconds,
    )
    if config != replay_config:
        raise ValueError("engine config is outside bounded_dex_engine_v0")
    return {
        "schema": REPLAY_ENGINE_CONFIG_SCHEMA,
        "profile": REPLAY_ENGINE_CONFIG_PROFILE,
        "config": _canonical_config_projection(asdict(config)),
    }


def parse_replay_engine_config_v0(
    document: Mapping[str, Any],
) -> tuple[DexEngineConfig, dict[str, Any]]:
    """Parse an exact canonical config commitment for deterministic replay."""

    obj = dict(document)
    if set(obj) != {"schema", "profile", "config"}:
        raise ValueError("replay engine config keys mismatch")
    if obj.get("schema") != REPLAY_ENGINE_CONFIG_SCHEMA:
        raise ValueError("replay engine config schema mismatch")
    if obj.get("profile") != REPLAY_ENGINE_CONFIG_PROFILE:
        raise ValueError("replay engine config profile mismatch")
    config_obj = obj.get("config")
    if not isinstance(config_obj, Mapping):
        raise TypeError("engine_config.config must be a JSON object")
    dex_config_obj = config_obj.get("dex_config")
    if not isinstance(dex_config_obj, Mapping):
        raise TypeError("engine_config.config.dex_config must be a JSON object")
    protocol_fee_share_bps = _require_nonnegative_int(
        dex_config_obj.get("protocol_fee_share_bps"),
        name="engine_config.config.dex_config.protocol_fee_share_bps",
    )
    if protocol_fee_share_bps > 10_000:
        raise ValueError("engine_config.config.dex_config.protocol_fee_share_bps must be at most 10000")
    config = DexEngineConfig(
        allow_missing_settlement=_require_bool(
            config_obj.get("allow_missing_settlement"),
            name="engine_config.config.allow_missing_settlement",
        ),
        require_intent_signatures=_require_bool(
            config_obj.get("require_intent_signatures"),
            name="engine_config.config.require_intent_signatures",
        ),
        allow_unsigned_intents_if_tx_sender_matches=_require_bool(
            config_obj.get("allow_unsigned_intents_if_tx_sender_matches"),
            name="engine_config.config.allow_unsigned_intents_if_tx_sender_matches",
        ),
        chain_id=_require_str(
            config_obj.get("chain_id"),
            name="engine_config.config.chain_id",
        ),
        dex_config=DexConfig(
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=_require_optional_str(
                dex_config_obj.get("protocol_fee_recipient_pubkey"),
                name="engine_config.config.dex_config.protocol_fee_recipient_pubkey",
            ),
        ),
        min_lp_position_age_seconds=_require_nonnegative_int(
            config_obj.get("min_lp_position_age_seconds"),
            name="engine_config.config.min_lp_position_age_seconds",
        ),
    )
    canonical_document = replay_engine_config_document_v0(config)
    if obj != canonical_document:
        raise ValueError("replay engine config is not canonical")
    return config, canonical_document


def replay_engine_config_digest_v0(document: Mapping[str, Any]) -> str:
    """Hash a validated canonical config commitment."""

    _config, canonical_document = parse_replay_engine_config_v0(document)
    return hash_v0("zeno_ledger_replay_engine_config_v0", canonical_document)


def load_replay_snapshot_v0(snapshot: Mapping[str, Any]) -> tuple[DexState, dict[str, Any]]:
    """Load a snapshot only when its decoded state has the same canonical form."""

    snapshot_obj = dict(snapshot)
    state = state_from_snapshot(snapshot_obj)
    version = snapshot_obj.get("version")
    if not isinstance(version, int) or isinstance(version, bool):
        raise ValueError("snapshot.version must be an int")
    canonical_snapshot = snapshot_from_state(state, version=version).data
    if snapshot_obj != canonical_snapshot:
        raise ValueError("pre-state snapshot is not canonical")
    return state, canonical_snapshot


def validate_replay_bound_block_v0(
    *,
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    pre_snapshot: Mapping[str, Any],
    config: DexEngineConfig,
    config_digest: str,
    parent_header: Mapping[str, Any] | None,
    carried_state: DexState | None,
) -> DexState:
    """Validate and replay one block, returning the only admissible next state."""

    if header.get("config_digest") != config_digest:
        raise ValueError("header config_digest does not match governed engine config")
    if header.get("chain_id") != config.chain_id:
        raise ValueError("header chain_id does not match governed engine config")
    if parent_header is not None:
        validate_header_chain_state_continuity_v0([parent_header, header])

    snapshot_state, canonical_snapshot = load_replay_snapshot_v0(pre_snapshot)
    replay_state = snapshot_state if carried_state is None else carried_state
    if carried_state is not None:
        carried_root = dex_state_root_v0(carried_state)
        if dex_state_root_v0(snapshot_state) != carried_root:
            raise ValueError("pre-state snapshot root does not match carried replay state")
        carried_snapshot = snapshot_from_state(
            carried_state,
            version=int(canonical_snapshot["version"]),
        ).data
        if canonical_snapshot != carried_snapshot:
            raise ValueError("pre-state snapshot bytes do not match carried replay state")

    validate_block_state_transition_v0(
        pre_state=replay_state,
        header=header,
        body=body,
        config=config,
    )
    next_state, replayed_body, _receipts = apply_body_transactions_v0(
        state=replay_state,
        body=body,
        config=config,
    )
    if body["evidence"]["rejection_receipts"] != replayed_body["evidence"]["rejection_receipts"]:
        raise ValueError("committed rejection receipts do not match deterministic replay")
    if dex_state_root_v0(next_state) != header["post_state_root"]:
        raise ValueError("carried replay state does not match header post_state_root")
    return next_state
