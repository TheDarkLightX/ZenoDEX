#!/usr/bin/env python3
"""Build or apply a bounded proof-mining-manager packet from a solver claim."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Mapping

_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.proof_mining_manager import (  # noqa: E402
    ProofMiningManagerSnapshot,
    apply_submit_proof_packet,
    build_submit_proof_packet,
)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _plain_jsonish(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {str(key): _plain_jsonish(inner) for key, inner in value.items()}
    if isinstance(value, tuple):
        return [_plain_jsonish(inner) for inner in value]
    return value


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    return _require_mapping(obj, name=str(path))


def _snapshot_from_obj(obj: Mapping[str, Any]) -> ProofMiningManagerSnapshot:
    claimed_raw = _require_mapping(obj.get("claimed_slots", {}), name="snapshot.claimed_slots")
    claimed_slots: dict[int, str] = {}
    raw_keys_by_slot: dict[int, str] = {}
    for raw_slot, proposal in claimed_raw.items():
        slot_text = str(raw_slot)
        slot = _require_int(int(slot_text), name="snapshot.claimed_slots key")
        if slot in claimed_slots and raw_keys_by_slot[slot] != slot_text:
            raise ValueError("duplicate claimed_slots key after normalization")
        raw_keys_by_slot[slot] = slot_text
        claimed_slots[slot] = _require_str(proposal, name=f"snapshot.claimed_slots[{slot_text}]")
    return ProofMiningManagerSnapshot(
        epoch=_require_int(obj.get("epoch"), name="snapshot.epoch"),
        base_reward=_require_int(obj.get("base_reward"), name="snapshot.base_reward"),
        initial_pool=_require_int(obj.get("initial_pool"), name="snapshot.initial_pool"),
        reward_pool_balance=_require_int(obj.get("reward_pool_balance"), name="snapshot.reward_pool_balance"),
        total_paid=_require_int(obj.get("total_paid"), name="snapshot.total_paid"),
        claimed_slots=claimed_slots,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build or apply a bounded proof-mining-manager packet")
    parser.add_argument("--claim", required=True, help="Proof-mining claim JSON path")
    parser.add_argument("--snapshot", required=True, help="Manager snapshot JSON path")
    parser.add_argument("--output", required=True, help="Output JSON path")
    parser.add_argument("--apply", action="store_true", help="Execute the kernel step and emit the apply result")
    parser.add_argument("--proof-ok", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--binding-ok", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--policy-ok", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--nonce-ok", action=argparse.BooleanOptionalAction, default=False)
    args = parser.parse_args(argv)

    claim = _load_json(Path(args.claim))
    snapshot_obj = _load_json(Path(args.snapshot))
    snapshot = _snapshot_from_obj(snapshot_obj)
    verification_flags = {
        "proof_ok": bool(args.proof_ok),
        "binding_ok": bool(args.binding_ok),
        "policy_ok": bool(args.policy_ok),
        "nonce_ok": bool(args.nonce_ok),
    }
    packet = build_submit_proof_packet(claim_artifact=claim, snapshot=snapshot, verification_flags=verification_flags)

    if not bool(args.apply):
        out = {
            "schema": "zenodex/proof_mining_manager_packet/v1",
            "packet": {
                "claim": _plain_jsonish(packet.claim),
                "state_before": _plain_jsonish(packet.state_before),
                "command_tag": str(packet.command_tag),
                "command_args": _plain_jsonish(packet.command_args),
                "assigned_slot": int(packet.assigned_slot),
                "proposal_hash": str(packet.proposal_hash),
            },
        }
    else:
        res = apply_submit_proof_packet(packet=packet, snapshot=snapshot, verification_flags=verification_flags)
        out = {
            "schema": "zenodex/proof_mining_manager_apply_result/v1",
            "ok": bool(res.ok),
            "packet": {
                "assigned_slot": int(packet.assigned_slot),
                "proposal_hash": str(packet.proposal_hash),
                "command_tag": str(packet.command_tag),
                "command_args": _plain_jsonish(packet.command_args),
            },
            "state_after": None if res.state_after is None else dict(res.state_after),
            "effects": None if res.effects is None else dict(res.effects),
            "claimed_slots_after": {str(k): v for k, v in sorted(dict(res.claimed_slots_after).items())},
            "error_code": res.error_code,
            "error_message": res.error_message,
        }

    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
