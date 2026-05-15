from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Mapping

try:
    import yaml
    from ESSO.ir.schema import CandidateIR
    from ESSO.kernel.runner import Command, prepare_step_context, step_ctx
except ModuleNotFoundError:  # pragma: no cover - exercised through public node smoke on minimal installs
    yaml = None  # type: ignore[assignment]
    CandidateIR = Any  # type: ignore[misc, assignment]
    Command = None  # type: ignore[assignment]
    prepare_step_context = None  # type: ignore[assignment]
    step_ctx = None  # type: ignore[assignment]

from .proof_mining_claims import schedule_reward_amount, validate_proof_mining_claim_artifact


_PROOF_MINING_MANAGER_MODEL = Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "proof_mining_manager_v1.yaml")
_MAX_SLOT = 7


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


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


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


def _validate_slot_registry(claimed_slots: Mapping[int, str]) -> dict[int, str]:
    out: dict[int, str] = {}
    seen_hashes: set[str] = set()
    for raw_slot, raw_hash in dict(claimed_slots).items():
        slot = _require_int(raw_slot, name="claimed_slots key")
        if slot < 0 or slot > _MAX_SLOT:
            raise ValueError("claimed slot out of range")
        proposal_hash = _require_str(raw_hash, name=f"claimed_slots[{slot}]")
        if proposal_hash in seen_hashes:
            raise ValueError("duplicate proposal_hash in claimed_slots")
        seen_hashes.add(proposal_hash)
        out[slot] = proposal_hash
    return out


def preferred_proposal_slot(proposal_hash: str) -> int:
    digest = hashlib.sha256(_require_str(proposal_hash, name="proposal_hash").encode("utf-8")).digest()
    return int(digest[0] & 0x07)


def assign_proposal_slot(*, proposal_hash: str, claimed_slots: Mapping[int, str]) -> tuple[int, bool]:
    registry = _validate_slot_registry(claimed_slots)
    proposal = _require_str(proposal_hash, name="proposal_hash")
    for slot, bound in sorted(registry.items()):
        if bound == proposal:
            return int(slot), True
    if len(registry) > (_MAX_SLOT + 1):
        raise ValueError("claimed_slots over capacity")
    preferred = preferred_proposal_slot(proposal)
    for offset in range(_MAX_SLOT + 1):
        candidate = (preferred + offset) % (_MAX_SLOT + 1)
        if candidate not in registry:
            return int(candidate), False
    raise ValueError("no free proposal slots")


def snapshot_to_kernel_state(snapshot: ProofMiningManagerSnapshot) -> dict[str, Any]:
    registry = _validate_slot_registry(snapshot.claimed_slots)
    epoch = _require_int(snapshot.epoch, name="snapshot.epoch")
    base_reward = _require_int(snapshot.base_reward, name="snapshot.base_reward")
    initial_pool = _require_int(snapshot.initial_pool, name="snapshot.initial_pool")
    reward_pool_balance = _require_int(snapshot.reward_pool_balance, name="snapshot.reward_pool_balance")
    total_paid = _require_int(snapshot.total_paid, name="snapshot.total_paid")
    if epoch < 0 or epoch > _MAX_SLOT:
        raise ValueError("snapshot.epoch out of range")
    if base_reward < 1 or base_reward > 128:
        raise ValueError("snapshot.base_reward out of range")
    if initial_pool < 0 or reward_pool_balance < 0 or total_paid < 0:
        raise ValueError("snapshot balances must be non-negative")
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


def load_proof_mining_manager_ir() -> CandidateIR:
    if yaml is None:
        raise RuntimeError("ESSO runtime is unavailable")
    obj = yaml.safe_load(_PROOF_MINING_MANAGER_MODEL.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise TypeError("proof_mining_manager_v1.yaml must decode to a mapping")
    return CandidateIR.from_json_dict(obj, path=str(_PROOF_MINING_MANAGER_MODEL)).canonicalized()


def _apply_submit_proof_packet_python_v0(
    *,
    trusted_packet: ProofMiningManagerPacket,
    snapshot: ProofMiningManagerSnapshot,
) -> ProofMiningManagerApplyResult:
    """Deterministic fallback for the submit_proof kernel on minimal installs."""

    state_before = snapshot_to_kernel_state(snapshot)
    args = dict(_deep_thaw_jsonish(trusted_packet.command_args))
    slot = _require_int(args.get("proposal_slot"), name="command_args.proposal_slot")
    prover_id = _require_int(args.get("prover_id"), name="command_args.prover_id")
    flags_ok = all(
        _require_bool(args.get(name), name=f"command_args.{name}") is True
        for name in ("proof_ok", "binding_ok", "policy_ok", "nonce_ok")
    )
    reward_amount = schedule_reward_amount(base_reward=snapshot.base_reward, epoch=snapshot.epoch)
    slot_key = f"claimed_{slot}"
    if not flags_ok:
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=trusted_packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code="StepError",
            error_message="verification flags rejected",
        )
    if bool(state_before.get(slot_key)) is True:
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=trusted_packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code="StepError",
            error_message="proposal slot already claimed",
        )
    if _require_int(state_before.get("reward_pool_balance"), name="reward_pool_balance") < reward_amount:
        return ProofMiningManagerApplyResult(
            ok=False,
            packet=trusted_packet,
            state_after=None,
            effects=None,
            claimed_slots_after=dict(snapshot.claimed_slots),
            error_code="StepError",
            error_message="insufficient reward pool balance",
        )
    state_after = dict(state_before)
    state_after["reward_pool_balance"] = int(state_after["reward_pool_balance"]) - reward_amount
    state_after["total_paid"] = int(state_after["total_paid"]) + reward_amount
    state_after[slot_key] = True
    effects = {
        "proposal_slot": slot,
        "prover_id": prover_id,
        "reward_amount": reward_amount,
        "reward_kind": "TreasuryTransfer",
        "paid": True,
    }
    claimed_after = dict(_validate_slot_registry(snapshot.claimed_slots))
    claimed_after[int(trusted_packet.assigned_slot)] = str(trusted_packet.proposal_hash)
    return ProofMiningManagerApplyResult(
        ok=True,
        packet=trusted_packet,
        state_after=state_after,
        effects=effects,
        claimed_slots_after=claimed_after,
    )


def build_submit_proof_packet(
    *,
    claim_artifact: Mapping[str, Any],
    snapshot: ProofMiningManagerSnapshot,
    verification_flags: Mapping[str, Any],
) -> ProofMiningManagerPacket:
    claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=False)
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
    command_args = {
        "proposal_slot": int(assigned_slot),
        "prover_id": _require_int(claim.get("prover_id"), name="claim.prover_id"),
        "proof_ok": _require_bool(verification_flags.get("proof_ok"), name="verification_flags.proof_ok"),
        "binding_ok": _require_bool(verification_flags.get("binding_ok"), name="verification_flags.binding_ok"),
        "policy_ok": _require_bool(verification_flags.get("policy_ok"), name="verification_flags.policy_ok"),
        "nonce_ok": _require_bool(verification_flags.get("nonce_ok"), name="verification_flags.nonce_ok"),
    }
    return ProofMiningManagerPacket(
        claim=_deep_thaw_jsonish(claim_artifact),
        state_before=snapshot_to_kernel_state(snapshot),
        command_tag="submit_proof",
        command_args=command_args,
        assigned_slot=int(assigned_slot),
        proposal_hash=_require_str(claim.get("proposal_hash"), name="claim.proposal_hash"),
    )


def apply_submit_proof_packet(
    *,
    packet: ProofMiningManagerPacket,
    snapshot: ProofMiningManagerSnapshot,
    verification_flags: Mapping[str, Any],
    ir: CandidateIR | None = None,
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
    if prepare_step_context is None or step_ctx is None or Command is None:
        return _apply_submit_proof_packet_python_v0(
            trusted_packet=trusted_packet,
            snapshot=snapshot,
        )
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
    claimed_after = dict(_validate_slot_registry(snapshot.claimed_slots))
    claimed_after[int(trusted_packet.assigned_slot)] = str(trusted_packet.proposal_hash)
    return ProofMiningManagerApplyResult(
        ok=True,
        packet=trusted_packet,
        state_after=dict(res.state),
        effects=dict(res.effects),
        claimed_slots_after=claimed_after,
    )
