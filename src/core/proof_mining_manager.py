from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Mapping

import yaml

from .proof_mining_claim_gate import (
    PROOF_MINING_BASE_REWARD_MAX,
    PROOF_MINING_EPOCH_MAX,
    PROOF_MINING_POOL_BALANCE_MAX,
)
from .proof_mining_claims import validate_proof_mining_claim_artifact
from .proof_mining_claim_identity_gate import (
    preferred_proposal_slot,
    resolve_proof_mining_claim_identity,
    validate_proof_mining_claimed_slots_registry,
)
from .proof_mining_slot_assignment_gate import (
    PROOF_MINING_SLOT_MAX,
)
from .proof_mining_manager_packet_envelope_gate import (
    build_proof_mining_manager_packet_envelope,
)
from .proof_mining_manager_verification_flags_gate import (
    PROOF_MINING_MANAGER_VERIFICATION_FLAG_NAMES as _PROOF_MINING_MANAGER_VERIFICATION_FLAG_NAMES,
    submit_proof_verification_flags_all_true as _submit_proof_verification_flags_all_true,
)


_PROOF_MINING_MANAGER_MODEL = Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "proof_mining_manager_v1.yaml")
_MAX_SLOT = PROOF_MINING_SLOT_MAX
PROOF_MINING_MANAGER_VERIFICATION_FLAG_NAMES = _PROOF_MINING_MANAGER_VERIFICATION_FLAG_NAMES


@dataclass(frozen=True)
class ProofMiningManagerSnapshot:
    epoch: int
    base_reward: int
    initial_pool: int
    reward_pool_balance: int
    total_paid: int
    claimed_slots: Mapping[int, str]


@dataclass(frozen=True)
class ProofMiningManagerPacket:
    claim: Mapping[str, Any]
    state_before: Mapping[str, Any]
    command_tag: str
    command_args: Mapping[str, Any]
    assigned_slot: int
    proposal_hash: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "claim", _deep_freeze_jsonish(self.claim))
        object.__setattr__(self, "state_before", _deep_freeze_jsonish(self.state_before))
        object.__setattr__(self, "command_args", _deep_freeze_jsonish(self.command_args))


@dataclass(frozen=True)
class ProofMiningManagerApplyResult:
    ok: bool
    packet: ProofMiningManagerPacket
    state_after: Mapping[str, Any] | None
    effects: Mapping[str, Any] | None
    claimed_slots_after: Mapping[int, str]
    error_code: str | None = None
    error_message: str | None = None


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _deep_freeze_jsonish(value: Any) -> Any:
    if isinstance(value, Mapping):
        frozen = {str(key): _deep_freeze_jsonish(inner) for key, inner in value.items()}
        return MappingProxyType(frozen)
    if isinstance(value, list) or isinstance(value, tuple):
        return tuple(_deep_freeze_jsonish(inner) for inner in value)
    return value


def _deep_thaw_jsonish(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {str(key): _deep_thaw_jsonish(inner) for key, inner in value.items()}
    if isinstance(value, tuple):
        return [_deep_thaw_jsonish(inner) for inner in value]
    return value


def submit_proof_verification_flags_all_true() -> dict[str, bool]:
    return _submit_proof_verification_flags_all_true()


def assign_proposal_slot(*, proposal_hash: str, claimed_slots: Mapping[int, str]) -> tuple[int, bool]:
    resolution = resolve_proof_mining_claim_identity(
        proposal_hash=_require_str(proposal_hash, name="proposal_hash"),
        claimed_slots=claimed_slots,
    )
    if resolution.already_claimed:
        return int(resolution.assigned_slot), True
    if resolution.free_found:
        return int(resolution.assigned_slot), False
    raise ValueError("no free proposal slots")


def snapshot_to_kernel_state(snapshot: ProofMiningManagerSnapshot) -> dict[str, Any]:
    registry = validate_proof_mining_claimed_slots_registry(snapshot.claimed_slots)
    epoch = _require_int(snapshot.epoch, name="snapshot.epoch")
    base_reward = _require_int(snapshot.base_reward, name="snapshot.base_reward")
    initial_pool = _require_int(snapshot.initial_pool, name="snapshot.initial_pool")
    reward_pool_balance = _require_int(snapshot.reward_pool_balance, name="snapshot.reward_pool_balance")
    total_paid = _require_int(snapshot.total_paid, name="snapshot.total_paid")
    if epoch < 0 or epoch > _MAX_SLOT:
        raise ValueError("snapshot.epoch out of range")
    if base_reward < 1 or base_reward > PROOF_MINING_BASE_REWARD_MAX:
        raise ValueError("snapshot.base_reward out of range")
    if initial_pool < 0 or reward_pool_balance < 0 or total_paid < 0:
        raise ValueError("snapshot balances must be non-negative")
    if initial_pool > PROOF_MINING_POOL_BALANCE_MAX:
        raise ValueError("snapshot.initial_pool out of range")
    if reward_pool_balance > PROOF_MINING_POOL_BALANCE_MAX:
        raise ValueError("snapshot.reward_pool_balance out of range")
    if total_paid > PROOF_MINING_POOL_BALANCE_MAX:
        raise ValueError("snapshot.total_paid out of range")
    if total_paid + reward_pool_balance != initial_pool:
        raise ValueError("snapshot pool conservation mismatch")
    out = {
        "epoch": epoch,
        "base_reward": base_reward,
        "initial_pool": initial_pool,
        "reward_pool_balance": reward_pool_balance,
        "total_paid": total_paid,
    }
    for slot in range(_MAX_SLOT + 1):
        out[f"claimed_{slot}"] = bool(slot in registry)
    return out


def load_proof_mining_manager_ir() -> Any:
    from ESSO.ir.schema import CandidateIR  # type: ignore

    obj = yaml.safe_load(_PROOF_MINING_MANAGER_MODEL.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise TypeError("proof_mining_manager_v1.yaml must decode to a mapping")
    return CandidateIR.from_json_dict(obj, path=str(_PROOF_MINING_MANAGER_MODEL)).canonicalized()


def _epoch_reward(*, epoch: int, base_reward: int) -> int:
    divisor = 1 << min(max(int(epoch), 0), _MAX_SLOT)
    scheduled = int(base_reward) // divisor
    return scheduled if scheduled > 0 else 1


def _apply_submit_proof_native(packet: ProofMiningManagerPacket) -> tuple[dict[str, Any], dict[str, Any]]:
    state_before = _deep_thaw_jsonish(packet.state_before)
    command_args = _deep_thaw_jsonish(packet.command_args)
    slot = _require_int(command_args.get("proposal_slot"), name="command_args.proposal_slot")
    prover_id = _require_int(command_args.get("prover_id"), name="command_args.prover_id")
    if slot < 0 or slot > _MAX_SLOT:
        raise ValueError("proposal_slot out of range")
    if any(bool(command_args.get(flag)) is not True for flag in PROOF_MINING_MANAGER_VERIFICATION_FLAG_NAMES):
        raise ValueError("verification flag rejected")
    if bool(state_before.get(f"claimed_{slot}")):
        raise ValueError("proposal slot already claimed")

    reward_amount = _epoch_reward(
        epoch=_require_int(state_before.get("epoch"), name="state_before.epoch"),
        base_reward=_require_int(state_before.get("base_reward"), name="state_before.base_reward"),
    )
    reward_pool_balance = _require_int(
        state_before.get("reward_pool_balance"),
        name="state_before.reward_pool_balance",
    )
    if reward_pool_balance < reward_amount:
        raise ValueError("insufficient reward pool balance")

    state_after = dict(state_before)
    state_after["reward_pool_balance"] = reward_pool_balance - reward_amount
    state_after["total_paid"] = _require_int(state_before.get("total_paid"), name="state_before.total_paid") + reward_amount
    state_after[f"claimed_{slot}"] = True
    effects = {
        "proposal_slot": slot,
        "prover_id": prover_id,
        "reward_amount": reward_amount,
        "reward_kind": "TreasuryTransfer",
        "paid": True,
    }
    return state_after, effects


def build_submit_proof_packet(
    *,
    claim_artifact: Mapping[str, Any],
    snapshot: ProofMiningManagerSnapshot,
    verification_flags: Mapping[str, Any],
) -> ProofMiningManagerPacket:
    claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=True)
    state_before = snapshot_to_kernel_state(snapshot)
    if _require_int(claim.get("epoch"), name="claim.epoch") != _require_int(snapshot.epoch, name="snapshot.epoch"):
        raise ValueError("claim epoch does not match snapshot")
    if _require_int(claim.get("base_reward"), name="claim.base_reward") != _require_int(snapshot.base_reward, name="snapshot.base_reward"):
        raise ValueError("claim base_reward does not match snapshot")
    if _require_int(claim.get("reward_pool_before"), name="claim.reward_pool_before") != _require_int(snapshot.reward_pool_balance, name="snapshot.reward_pool_balance"):
        raise ValueError("claim reward_pool_before does not match snapshot")
    assigned_slot, already_claimed = assign_proposal_slot(
        proposal_hash=_require_str(claim.get("proposal_hash"), name="claim.proposal_hash"),
        claimed_slots=snapshot.claimed_slots,
    )
    if already_claimed:
        raise ValueError("proposal_hash already claimed")
    envelope = build_proof_mining_manager_packet_envelope(
        state_before=state_before,
        assigned_slot=int(assigned_slot),
        prover_id=_require_int(claim.get("prover_id"), name="claim.prover_id"),
        verification_flags=verification_flags,
        verification_flags_name="verification_flags",
        proposal_hash=_require_str(claim.get("proposal_hash"), name="claim.proposal_hash"),
    )
    return ProofMiningManagerPacket(
        claim=_deep_thaw_jsonish(claim_artifact),
        state_before=envelope.state_before,
        command_tag=envelope.command_tag,
        command_args=envelope.command_args,
        assigned_slot=int(envelope.assigned_slot),
        proposal_hash=str(envelope.proposal_hash),
    )


def apply_submit_proof_packet(
    *,
    packet: ProofMiningManagerPacket,
    snapshot: ProofMiningManagerSnapshot,
    verification_flags: Mapping[str, Any],
    ir: Any | None = None,
) -> ProofMiningManagerApplyResult:
    try:
        trusted_packet = build_submit_proof_packet(
            claim_artifact=_deep_thaw_jsonish(packet.claim),
            snapshot=snapshot,
            verification_flags=verification_flags,
        )
    except (TypeError, ValueError) as exc:
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code="InvalidPacket",
            error_message=str(exc),
        )
    if (
        packet.command_tag != trusted_packet.command_tag
        or int(packet.assigned_slot) != int(trusted_packet.assigned_slot)
        or str(packet.proposal_hash) != str(trusted_packet.proposal_hash)
        or _deep_thaw_jsonish(packet.state_before) != _deep_thaw_jsonish(trusted_packet.state_before)
        or _deep_thaw_jsonish(packet.command_args) != _deep_thaw_jsonish(trusted_packet.command_args)
    ):
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code="InvalidPacket",
            error_message="packet fields do not match claim and snapshot",
        )
    if ir is None:
        try:
            state_after, effects = _apply_submit_proof_native(trusted_packet)
        except (TypeError, ValueError) as exc:
            return ProofMiningManagerApplyResult(
                ok=False,
                packet=trusted_packet,
                state_after=None,
                effects=None,
                claimed_slots_after=dict(snapshot.claimed_slots),
                error_code="GuardRejected",
                error_message=str(exc),
            )
        claimed_after = dict(validate_proof_mining_claimed_slots_registry(snapshot.claimed_slots))
        claimed_after[int(trusted_packet.assigned_slot)] = str(trusted_packet.proposal_hash)
        return ProofMiningManagerApplyResult(
            ok=True,
            packet=trusted_packet,
            state_after=state_after,
            effects=effects,
            claimed_slots_after=claimed_after,
        )

    from ESSO.kernel.runner import Command, prepare_step_context, step_ctx  # type: ignore

    ctx = prepare_step_context(load_proof_mining_manager_ir() if ir is None else ir)
    if getattr(ctx, "code", None) is not None and getattr(ctx, "message", None) is not None:
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=trusted_packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code=str(getattr(ctx, "code", "InvalidIR")),
            error_message=str(getattr(ctx, "message", "invalid context")),
        )
    res = step_ctx(
        _deep_thaw_jsonish(trusted_packet.state_before),
        Command(tag=trusted_packet.command_tag, args=_deep_thaw_jsonish(trusted_packet.command_args)),
        ctx,
    )
    if getattr(res, "code", None) is not None and getattr(res, "message", None) is not None:
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=trusted_packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code=str(getattr(res, "code", "StepError")),
            error_message=str(getattr(res, "message", "step failed")),
        )
    claimed_after = dict(validate_proof_mining_claimed_slots_registry(snapshot.claimed_slots))
    claimed_after[int(trusted_packet.assigned_slot)] = str(trusted_packet.proposal_hash)
    return ProofMiningManagerApplyResult(
        ok=True,
        packet=trusted_packet,
        state_after=dict(res.state),
        effects=dict(res.effects),
        claimed_slots_after=claimed_after,
    )
