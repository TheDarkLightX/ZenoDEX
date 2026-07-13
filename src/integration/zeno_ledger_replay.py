"""Replay-bound ZenoLedger state-transition validation."""

from __future__ import annotations

from dataclasses import asdict
from typing import Any, Mapping

from src.core.dex import DexConfig, DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.zeno_ledger_proof_authority_consumer_v1 import (
    GovernedProofAuthorityBindingV1,
    governed_proof_authority_binding_document_v1,
    parse_governed_proof_authority_binding_v1,
)
from src.integration.zeno_ledger_v0 import (
    dex_state_root_v0,
    hash_v0,
    replay_block_state_transition_v0,
    validate_header_chain_state_continuity_v0,
)

REPLAY_ENGINE_CONFIG_SCHEMA = "zenodex/zeno_ledger/replay_engine_config/v0"
REPLAY_ENGINE_CONFIG_PROFILE = "bounded_dex_engine_v0"
REPLAY_ENGINE_CONFIG_SCHEMA_V1 = "zenodex/zeno_ledger/replay_engine_config/v1"
REPLAY_ENGINE_CONFIG_PROFILE_V1 = "bounded_dex_engine_proof_authority_v1"
_MAX_U64 = (1 << 64) - 1


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


def _require_u64(value: object, *, name: str) -> int:
    parsed = _require_nonnegative_int(value, name=name)
    if parsed > _MAX_U64:
        raise ValueError(f"{name} must fit in a u64")
    return parsed


def _require_optional_str(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be null or a non-empty str")
    return value


def _require_optional_ascii_str(value: object, *, name: str) -> str | None:
    parsed = _require_optional_str(value, name=name)
    if parsed is not None and not parsed.isascii():
        raise ValueError(f"{name} must contain only ASCII characters")
    return parsed


def _canonical_config_projection(value: object) -> object:
    if value is None or isinstance(value, (bool, int, str)):
        return value
    if isinstance(value, float):
        raise TypeError("engine config floats are not allowed")
    if isinstance(value, Mapping):
        if not all(isinstance(key, str) for key in value):
            raise TypeError("engine config mapping keys must be strings")
        return {key: _canonical_config_projection(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_canonical_config_projection(item) for item in value]
    raise TypeError(f"engine config contains unsupported value type: {type(value).__name__}")


def _governed_config_projection(config: DexEngineConfig) -> object:
    projection = asdict(config)
    proof_config = projection.get("proof_config")
    if not isinstance(proof_config, dict) or "timeout_s" not in proof_config:
        raise ValueError("engine proof config projection is malformed")
    # External tools are disabled by the bounded profile. Their wall-clock timeout
    # is outside deterministic execution and therefore outside the governed digest.
    del proof_config["timeout_s"]
    return _canonical_config_projection(projection)


def replay_engine_config_document_v0(config: DexEngineConfig) -> dict[str, Any]:
    """Return the deterministic config commitment for the bounded replay profile."""

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
    _require_u64(
        config.min_lp_position_age_seconds,
        name="engine_config.config.min_lp_position_age_seconds",
    )
    _require_optional_ascii_str(
        config.dex_config.protocol_fee_recipient_pubkey,
        name="engine_config.config.dex_config.protocol_fee_recipient_pubkey",
    )
    return {
        "schema": REPLAY_ENGINE_CONFIG_SCHEMA,
        "profile": REPLAY_ENGINE_CONFIG_PROFILE,
        "config": _governed_config_projection(config),
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
    _canonical_config_projection(config_obj)
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
            protocol_fee_recipient_pubkey=_require_optional_ascii_str(
                dex_config_obj.get("protocol_fee_recipient_pubkey"),
                name="engine_config.config.dex_config.protocol_fee_recipient_pubkey",
            ),
        ),
        min_lp_position_age_seconds=_require_u64(
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


def replay_engine_config_document_v1(
    config: DexEngineConfig,
    *,
    proof_authority_policy: GovernedProofAuthorityBindingV1,
) -> dict[str, Any]:
    """Return the cycle-free config V1 that commits proof-authority policy."""

    if type(proof_authority_policy) is not GovernedProofAuthorityBindingV1:
        raise TypeError(
            "proof_authority_policy must be exactly GovernedProofAuthorityBindingV1"
        )
    v0_document = replay_engine_config_document_v0(config)
    if proof_authority_policy.chain_id != config.chain_id:
        raise ValueError("proof-authority policy chain_id does not match engine config")
    return {
        "schema": REPLAY_ENGINE_CONFIG_SCHEMA_V1,
        "profile": REPLAY_ENGINE_CONFIG_PROFILE_V1,
        "config": v0_document["config"],
        "proof_authority_policy": governed_proof_authority_binding_document_v1(
            proof_authority_policy
        ),
    }


def parse_replay_engine_config_v1(
    document: Mapping[str, Any],
) -> tuple[DexEngineConfig, GovernedProofAuthorityBindingV1, dict[str, Any]]:
    """Parse exact config V1 without accepting a V0 policy projection."""

    obj = dict(document)
    if set(obj) != {"schema", "profile", "config", "proof_authority_policy"}:
        raise ValueError("replay engine config V1 keys mismatch")
    if obj.get("schema") != REPLAY_ENGINE_CONFIG_SCHEMA_V1:
        raise ValueError("replay engine config V1 schema mismatch")
    if obj.get("profile") != REPLAY_ENGINE_CONFIG_PROFILE_V1:
        raise ValueError("replay engine config V1 profile mismatch")
    config_obj = obj.get("config")
    if not isinstance(config_obj, Mapping):
        raise TypeError("engine_config.config must be a JSON object")
    policy_obj = obj.get("proof_authority_policy")
    if not isinstance(policy_obj, Mapping):
        raise TypeError("engine_config.proof_authority_policy must be a JSON object")
    config, _v0_canonical = parse_replay_engine_config_v0(
        {
            "schema": REPLAY_ENGINE_CONFIG_SCHEMA,
            "profile": REPLAY_ENGINE_CONFIG_PROFILE,
            "config": dict(config_obj),
        }
    )
    policy = parse_governed_proof_authority_binding_v1(policy_obj)
    canonical_document = replay_engine_config_document_v1(
        config,
        proof_authority_policy=policy,
    )
    if obj != canonical_document:
        raise ValueError("replay engine config V1 is not canonical")
    return config, policy, canonical_document


def replay_engine_config_digest_v1(document: Mapping[str, Any]) -> str:
    """Hash a validated config V1 including the complete governed policy."""

    _config, _policy, canonical_document = parse_replay_engine_config_v1(document)
    return hash_v0("zeno_ledger_replay_engine_config_v1", canonical_document)


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
    pre_snapshot: Mapping[str, Any] | None,
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

    if carried_state is None:
        if pre_snapshot is None:
            raise ValueError("anchor pre-state snapshot is required")
        replay_state, _canonical_snapshot = load_replay_snapshot_v0(pre_snapshot)
    else:
        replay_state = carried_state
    if carried_state is not None and pre_snapshot is not None:
        snapshot_state, canonical_snapshot = load_replay_snapshot_v0(pre_snapshot)
        carried_root = dex_state_root_v0(carried_state)
        if dex_state_root_v0(snapshot_state) != carried_root:
            raise ValueError("pre-state snapshot root does not match carried replay state")
        carried_snapshot = snapshot_from_state(
            carried_state,
            version=int(canonical_snapshot["version"]),
        ).data
        if canonical_snapshot != carried_snapshot:
            raise ValueError("pre-state snapshot bytes do not match carried replay state")

    next_state, replayed_body, _receipts = replay_block_state_transition_v0(
        pre_state=replay_state,
        header=dict(header),
        body=dict(body),
        config=config,
    )
    if body["evidence"]["rejection_receipts"] != replayed_body["evidence"]["rejection_receipts"]:
        raise ValueError("committed rejection receipts do not match deterministic replay")
    return next_state
