from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping

from src.fire.registry.instance_v1 import FireObjectInstanceManifest
from src.fire.registry.object_manifest_v1 import FireObjectManifest
from src.fire.verifier.cert_v1 import _require_sha256_prefixed


FIRE_REPLAY_INPUT_SCHEMA = "zenodex/fire-replay-input/v1"

_DEFAULT_REPLAY_PROFILES: dict[tuple[str, str, str], dict[str, object]] = {
    ("BurnBoostCall", "v1", "capped_index_call"): {
        "default_balances": {"holder": 100, "writer": 250},
        "witness_map": {"witness_final": "BurnCertificate[TDEX]"},
    },
    ("FeeNote", "v1", "capped_index_note"): {
        "default_balances": {"holder": 40, "writer": 90},
        "witness_map": {"witness_final": "FeeIndexPacket"},
    },
    ("LPLossCover", "v1", "capped_lp_loss_cover"): {
        "default_balances": {"holder": 80, "writer": 200},
        "witness_map": {
            "witness_hodl_final": "HODLValuePacket",
            "witness_lpv_final": "LPValuePacket",
        },
    },
}


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_nonnegative_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(dict(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


@dataclass(frozen=True)
class FireReplayInput:
    object_name: str
    object_version: str
    object_family: str
    object_hash: str
    instance_hash: str
    holder_posted: int
    writer_posted: int
    holder_balance: int
    writer_balance: int
    witness_inputs: Mapping[str, int]
    schema: str = FIRE_REPLAY_INPUT_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "object_family", _require_nonempty_str("object_family", self.object_family))
        object.__setattr__(self, "object_hash", _require_sha256_prefixed("object_hash", self.object_hash))
        object.__setattr__(self, "instance_hash", _require_sha256_prefixed("instance_hash", self.instance_hash))
        object.__setattr__(self, "holder_posted", _require_nonnegative_int("holder_posted", self.holder_posted))
        object.__setattr__(self, "writer_posted", _require_nonnegative_int("writer_posted", self.writer_posted))
        object.__setattr__(self, "holder_balance", _require_nonnegative_int("holder_balance", self.holder_balance))
        object.__setattr__(self, "writer_balance", _require_nonnegative_int("writer_balance", self.writer_balance))
        if self.schema != FIRE_REPLAY_INPUT_SCHEMA:
            raise ValueError(f"unsupported replay input schema: {self.schema}")
        normalized: dict[str, int] = {}
        if not isinstance(self.witness_inputs, Mapping):
            raise TypeError("witness_inputs must be a mapping")
        for key, value in self.witness_inputs.items():
            normalized[_require_nonempty_str("witness_input_name", key)] = _require_nonnegative_int(
                f"witness_inputs[{key}]",
                value,
            )
        object.__setattr__(self, "witness_inputs", dict(sorted(normalized.items())))

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "holder_posted": self.holder_posted,
            "writer_posted": self.writer_posted,
            "holder_balance": self.holder_balance,
            "writer_balance": self.writer_balance,
            "witness_inputs": dict(self.witness_inputs),
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireReplayInput":
        if not isinstance(payload, dict):
            raise TypeError("replay input payload must be an object")
        witness_inputs = payload.get("witness_inputs")
        if not isinstance(witness_inputs, dict):
            raise TypeError("witness_inputs must be an object")
        return cls(
            schema=payload.get("schema", FIRE_REPLAY_INPUT_SCHEMA),
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            object_family=payload.get("object_family"),
            object_hash=payload.get("object_hash"),
            instance_hash=payload.get("instance_hash"),
            holder_posted=payload.get("holder_posted"),
            writer_posted=payload.get("writer_posted"),
            holder_balance=payload.get("holder_balance"),
            writer_balance=payload.get("writer_balance"),
            witness_inputs={str(key): value for key, value in witness_inputs.items()},
        )


def build_default_fire_replay_input(
    *,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> FireReplayInput:
    key = (object_manifest.object_name, object_manifest.object_version, object_manifest.object_family)
    profile = _DEFAULT_REPLAY_PROFILES.get(key)
    if profile is None:
        raise KeyError(
            f"no replay profile for {object_manifest.object_name}:{object_manifest.object_version}:{object_manifest.object_family}"
        )
    witness_bounds = {item.name: item.lower for item in object_manifest.witnesses}
    witness_inputs = {
        runtime_name: int(witness_bounds[witness_name])
        for runtime_name, witness_name in dict(profile["witness_map"]).items()
    }
    default_balances = dict(profile["default_balances"])
    return FireReplayInput(
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        object_family=object_manifest.object_family,
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        holder_posted=object_manifest.holder_collateral_required,
        writer_posted=object_manifest.writer_collateral_required,
        holder_balance=int(default_balances["holder"]),
        writer_balance=int(default_balances["writer"]),
        witness_inputs=witness_inputs,
    )


def verify_fire_replay_input(
    replay_input: FireReplayInput,
    *,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> tuple[bool, str | None]:
    if replay_input.object_name != object_manifest.object_name:
        return False, "replay_input_object_name_mismatch"
    if replay_input.object_version != object_manifest.object_version:
        return False, "replay_input_object_version_mismatch"
    if replay_input.object_family != object_manifest.object_family:
        return False, "replay_input_object_family_mismatch"
    if replay_input.object_hash != object_manifest.manifest_hash:
        return False, "replay_input_object_hash_mismatch"
    if replay_input.instance_hash != object_instance.instance_hash:
        return False, "replay_input_instance_hash_mismatch"
    if replay_input.holder_posted < object_manifest.holder_collateral_required:
        return False, "replay_input_holder_collateral_insufficient"
    if replay_input.writer_posted < object_manifest.writer_collateral_required:
        return False, "replay_input_writer_collateral_insufficient"
    witness_bounds = {item.name: (item.lower, item.upper) for item in object_manifest.witnesses}
    profile = _DEFAULT_REPLAY_PROFILES.get(
        (object_manifest.object_name, object_manifest.object_version, object_manifest.object_family)
    )
    if profile is None:
        return False, "replay_input_profile_missing"
    expected_runtime_names = set(dict(profile["witness_map"]).keys())
    if set(replay_input.witness_inputs) != expected_runtime_names:
        return False, "replay_input_witness_keys_mismatch"
    for runtime_name, witness_name in dict(profile["witness_map"]).items():
        lower, upper = witness_bounds[witness_name]
        value = replay_input.witness_inputs[runtime_name]
        if value < lower or value > upper:
            return False, f"replay_input_witness_out_of_range:{runtime_name}"
    return True, None


def write_fire_replay_input(path: str | Path, replay_input: FireReplayInput) -> str:
    file_path = Path(path)
    payload = _canonical_json_bytes(replay_input.to_dict())
    file_path.write_bytes(payload)
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def load_fire_replay_input(path: str | Path) -> tuple[FireReplayInput, str]:
    file_path = Path(path)
    payload_bytes = file_path.read_bytes()
    payload = json.loads(payload_bytes.decode("utf-8"))
    replay_input = FireReplayInput.from_dict(payload)
    return replay_input, "sha256:" + hashlib.sha256(payload_bytes).hexdigest()


__all__ = [
    "FIRE_REPLAY_INPUT_SCHEMA",
    "FireReplayInput",
    "build_default_fire_replay_input",
    "load_fire_replay_input",
    "verify_fire_replay_input",
    "write_fire_replay_input",
]
