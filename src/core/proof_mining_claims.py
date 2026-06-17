from __future__ import annotations

from typing import Any, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

U32_MAX = 0xFFFFFFFF
MAX_EPOCH = 7
MAX_PROPOSAL_SLOT = 7
MAX_PROVER_ID = 3


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_flag(value: Any, *, name: str) -> int:
    flag = _require_int(value, name=name)
    if flag not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return int(flag)


def fallback_proposal_hash(*, round_id: str, job_digest: str, witness_hash: str) -> str:
    binding = {
        "mode": "round_fallback_v1",
        "round_id": _require_str(round_id, name="round_id"),
        "job_digest": _require_str(job_digest, name="job_digest"),
        "witness_hash": _require_str(witness_hash, name="witness_hash"),
    }
    return sha256_hex(domain_sep_bytes("permissionless_solver_proposal_fallback", version=1) + canonical_json_bytes(binding))


def explicit_proposal_hash(
    *,
    chain_id: str,
    prev_state_hash: str,
    batch_hash: str,
    witness_hash: str,
    dex_hash_after: str,
) -> str:
    binding = {
        "mode": "explicit_v1",
        "chain_id": _require_str(chain_id, name="chain_id"),
        "prev_state_hash": _require_str(prev_state_hash, name="prev_state_hash"),
        "batch_hash": _require_str(batch_hash, name="batch_hash"),
        "witness_hash": _require_str(witness_hash, name="witness_hash"),
        "dex_hash_after": _require_str(dex_hash_after, name="dex_hash_after"),
    }
    return sha256_hex(domain_sep_bytes("proof_mining_proposal", version=1) + canonical_json_bytes(binding))


def proof_mining_claim_hash(body: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("permissionless_solver_proof_mining_claim", version=1) + canonical_json_bytes(dict(body)))


def schedule_reward_amount(*, base_reward: int, epoch: int) -> int:
    base = _require_int(base_reward, name="base_reward")
    ep = _require_int(epoch, name="epoch")
    if base <= 0:
        raise ValueError("base_reward must be > 0")
    if base > U32_MAX:
        raise ValueError("base_reward out of u32 range")
    if ep < 0 or ep > MAX_EPOCH:
        raise ValueError("epoch out of range")
    shifted = int(base) >> int(ep)
    if shifted > 0:
        return int(shifted)
    return 1


def build_proof_mining_claim(
    *,
    round_obj: Mapping[str, Any],
    round_id: str,
    reward_pool_before: int,
    base_reward: int,
    epoch: int,
    proposal_slot: int,
    prover_id: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    policy_ok: int = 1,
    nonce_ok: int = 1,
    unclaimed_ok: int = 1,
    chain_id: str = "",
    prev_state_hash: str = "",
    batch_hash: str = "",
    dex_hash_after: str = "",
    allow_rejected: bool = False,
) -> dict[str, Any]:
    if bool(round_obj.get("ok")) is not True:
        raise ValueError("round must be ok")
    if not isinstance(round_id, str) or not round_id:
        raise ValueError("round_id must be non-empty")

    reward_pool = _require_int(reward_pool_before, name="reward_pool_before")
    if reward_pool < 0 or reward_pool > U32_MAX:
        raise ValueError("reward_pool_before out of u32 range")
    slot = _require_int(proposal_slot, name="proposal_slot")
    if slot < 0 or slot > MAX_PROPOSAL_SLOT:
        raise ValueError("proposal_slot out of range")
    prover = _require_int(prover_id, name="prover_id")
    if prover < 0 or prover > MAX_PROVER_ID:
        raise ValueError("prover_id out of range")

    winner = _require_mapping(round_obj.get("winner"), name="winner")
    miner_id = _require_str(winner.get("miner_id"), name="winner.miner_id")
    witness_sha256 = _require_str(winner.get("witness_sha256"), name="winner.witness_sha256")
    improvement_u64 = _require_int(winner.get("improvement_u64"), name="winner.improvement_u64")
    if improvement_u64 <= 0:
        raise ValueError("winner improvement must be positive")
    if improvement_u64 > 0xFFFFFFFFFFFFFFFF:
        raise ValueError("winner improvement out of u64 range")

    job_digest = _require_str(round_obj.get("job_digest"), name="round.job_digest")
    witness_hash = witness_sha256
    explicit_binding_fields = [chain_id, prev_state_hash, batch_hash, dex_hash_after]
    explicit_count = sum(1 for value in explicit_binding_fields if str(value).strip())
    if 0 < explicit_count < len(explicit_binding_fields):
        raise ValueError("explicit proposal binding requires chain_id, prev_state_hash, batch_hash, and dex_hash_after together")
    if explicit_count == len(explicit_binding_fields):
        proposal_binding = {
            "mode": "explicit_v1",
            "chain_id": _require_str(chain_id, name="chain_id"),
            "prev_state_hash": _require_str(prev_state_hash, name="prev_state_hash"),
            "batch_hash": _require_str(batch_hash, name="batch_hash"),
            "witness_hash": witness_hash,
            "dex_hash_after": _require_str(dex_hash_after, name="dex_hash_after"),
        }
        proposal_hash = explicit_proposal_hash(
            chain_id=proposal_binding["chain_id"],
            prev_state_hash=proposal_binding["prev_state_hash"],
            batch_hash=proposal_binding["batch_hash"],
            witness_hash=proposal_binding["witness_hash"],
            dex_hash_after=proposal_binding["dex_hash_after"],
        )
    else:
        proposal_binding = {
            "mode": "round_fallback_v1",
            "round_id": str(round_id),
            "job_digest": job_digest,
            "witness_hash": witness_hash,
        }
        proposal_hash = fallback_proposal_hash(
            round_id=str(round_id),
            job_digest=job_digest,
            witness_hash=witness_hash,
        )
    reward_amount = schedule_reward_amount(base_reward=base_reward, epoch=epoch)
    reward_pool_after = int(reward_pool) - int(reward_amount)

    flags = {
        "proof_ok": _require_flag(proof_ok, name="proof_ok"),
        "binding_ok": _require_flag(binding_ok, name="binding_ok"),
        "policy_ok": _require_flag(policy_ok, name="policy_ok"),
        "nonce_ok": _require_flag(nonce_ok, name="nonce_ok"),
        "unclaimed_ok": _require_flag(unclaimed_ok, name="unclaimed_ok"),
    }
    budget_ok = bool(reward_pool >= reward_amount)
    flags_ok = all(value == 1 for value in flags.values())
    tau_gate_expected_ok = bool(flags_ok and budget_ok)
    if not bool(tau_gate_expected_ok) and not bool(allow_rejected):
        raise ValueError("proof-mining claim would fail Tau gate")

    tau_inputs = {
        "i1": int(base_reward),
        "i2": int(epoch),
        "i3": int(reward_amount),
        "i4": int(reward_pool),
        "i5": int(flags["proof_ok"]),
        "i6": int(flags["binding_ok"]),
        "i7": int(flags["policy_ok"]),
        "i8": int(flags["nonce_ok"]),
        "i9": int(flags["unclaimed_ok"]),
    }

    body = {
        "schema": "zenodex/permissionless_solver_proof_mining_claim/v1",
        "round_id": str(round_id),
        "job_digest": job_digest,
        "proposal_hash": proposal_hash,
        "proposal_binding": proposal_binding,
        "winner": {
            "miner_id": miner_id,
            "witness_sha256": witness_sha256,
            "improvement_u64": int(improvement_u64),
        },
        "bounded_model": {
            "proposal_slot": int(slot),
            "prover_id": int(prover),
            "base_reward": int(base_reward),
            "epoch": int(epoch),
            "reward_amount": int(reward_amount),
            "reward_kind": "TreasuryTransfer",
        },
        "budget": {
            "reward_pool_before": int(reward_pool),
            "reward_pool_after": int(reward_pool_after),
        },
        "verification_flags": dict(flags),
        "tau_inputs": tau_inputs,
        "conditions": {
            "round_ok": True,
            "positive_improvement": True,
            "budget_ok": bool(budget_ok),
            "tau_gate_expected_ok": bool(tau_gate_expected_ok),
        },
    }
    claim_hash = proof_mining_claim_hash(body)
    return {"body": body, "claim_hash": claim_hash}


def validate_proof_mining_claim_artifact(
    claim_artifact: Mapping[str, Any], *, require_admissible: bool = True
) -> dict[str, Any]:
    body = _require_mapping(claim_artifact.get("body"), name="claim.body")
    if _require_str(body.get("schema"), name="claim.body.schema") != "zenodex/permissionless_solver_proof_mining_claim/v1":
        raise ValueError("unsupported proof-mining claim schema")
    claim_hash = _require_str(claim_artifact.get("claim_hash"), name="claim.claim_hash")
    if claim_hash != proof_mining_claim_hash(body):
        raise ValueError("claim_hash mismatch")

    winner = _require_mapping(body.get("winner"), name="claim.body.winner")
    witness_hash = _require_str(winner.get("witness_sha256"), name="claim.body.winner.witness_sha256")
    improvement_u64 = _require_int(winner.get("improvement_u64"), name="claim.body.winner.improvement_u64")
    if improvement_u64 <= 0:
        raise ValueError("winner improvement must be positive")
    if improvement_u64 > 0xFFFFFFFFFFFFFFFF:
        raise ValueError("winner improvement out of u64 range")

    proposal_binding = _require_mapping(body.get("proposal_binding"), name="claim.body.proposal_binding")
    binding_mode = _require_str(proposal_binding.get("mode"), name="claim.body.proposal_binding.mode")
    if binding_mode == "explicit_v1":
        expected_proposal_hash = explicit_proposal_hash(
            chain_id=_require_str(proposal_binding.get("chain_id"), name="claim.body.proposal_binding.chain_id"),
            prev_state_hash=_require_str(proposal_binding.get("prev_state_hash"), name="claim.body.proposal_binding.prev_state_hash"),
            batch_hash=_require_str(proposal_binding.get("batch_hash"), name="claim.body.proposal_binding.batch_hash"),
            witness_hash=_require_str(proposal_binding.get("witness_hash"), name="claim.body.proposal_binding.witness_hash"),
            dex_hash_after=_require_str(proposal_binding.get("dex_hash_after"), name="claim.body.proposal_binding.dex_hash_after"),
        )
    elif binding_mode == "round_fallback_v1":
        binding_round_id = _require_str(proposal_binding.get("round_id"), name="claim.body.proposal_binding.round_id")
        binding_job_digest = _require_str(proposal_binding.get("job_digest"), name="claim.body.proposal_binding.job_digest")
        expected_proposal_hash = fallback_proposal_hash(
            round_id=binding_round_id,
            job_digest=binding_job_digest,
            witness_hash=_require_str(proposal_binding.get("witness_hash"), name="claim.body.proposal_binding.witness_hash"),
        )
        if binding_round_id != _require_str(body.get("round_id"), name="claim.body.round_id"):
            raise ValueError("proposal binding round_id mismatch")
        if binding_job_digest != _require_str(body.get("job_digest"), name="claim.body.job_digest"):
            raise ValueError("proposal binding job_digest mismatch")
    else:
        raise ValueError("unsupported proposal binding mode")
    if _require_str(body.get("proposal_hash"), name="claim.body.proposal_hash") != expected_proposal_hash:
        raise ValueError("proposal_hash mismatch")
    if _require_str(proposal_binding.get("witness_hash"), name="claim.body.proposal_binding.witness_hash") != witness_hash:
        raise ValueError("proposal binding witness mismatch")

    bounded_model = _require_mapping(body.get("bounded_model"), name="claim.body.bounded_model")
    if _require_str(bounded_model.get("reward_kind"), name="claim.body.bounded_model.reward_kind") != "TreasuryTransfer":
        raise ValueError("unsupported reward kind")
    proposal_slot = _require_int(bounded_model.get("proposal_slot"), name="claim.body.bounded_model.proposal_slot")
    if proposal_slot < 0 or proposal_slot > MAX_PROPOSAL_SLOT:
        raise ValueError("proposal_slot out of range")
    prover_id = _require_int(bounded_model.get("prover_id"), name="claim.body.bounded_model.prover_id")
    if prover_id < 0 or prover_id > MAX_PROVER_ID:
        raise ValueError("prover_id out of range")
    base_reward = _require_int(bounded_model.get("base_reward"), name="claim.body.bounded_model.base_reward")
    epoch = _require_int(bounded_model.get("epoch"), name="claim.body.bounded_model.epoch")
    reward_amount = _require_int(bounded_model.get("reward_amount"), name="claim.body.bounded_model.reward_amount")
    if reward_amount != schedule_reward_amount(base_reward=base_reward, epoch=epoch):
        raise ValueError("reward schedule mismatch")

    budget = _require_mapping(body.get("budget"), name="claim.body.budget")
    reward_pool_before = _require_int(budget.get("reward_pool_before"), name="claim.body.budget.reward_pool_before")
    reward_pool_after = _require_int(budget.get("reward_pool_after"), name="claim.body.budget.reward_pool_after")
    budget_ok = bool(reward_pool_before >= reward_amount and reward_pool_before - reward_amount == reward_pool_after and reward_pool_after >= 0)

    flags = _require_mapping(body.get("verification_flags"), name="claim.body.verification_flags")
    flag_values = {
        "proof_ok": _require_flag(flags.get("proof_ok"), name="claim.body.verification_flags.proof_ok"),
        "binding_ok": _require_flag(flags.get("binding_ok"), name="claim.body.verification_flags.binding_ok"),
        "policy_ok": _require_flag(flags.get("policy_ok"), name="claim.body.verification_flags.policy_ok"),
        "nonce_ok": _require_flag(flags.get("nonce_ok"), name="claim.body.verification_flags.nonce_ok"),
        "unclaimed_ok": _require_flag(flags.get("unclaimed_ok"), name="claim.body.verification_flags.unclaimed_ok"),
    }
    tau_inputs = _require_mapping(body.get("tau_inputs"), name="claim.body.tau_inputs")
    expected_tau_inputs = {
        "i1": int(base_reward),
        "i2": int(epoch),
        "i3": int(reward_amount),
        "i4": int(reward_pool_before),
        "i5": int(flag_values["proof_ok"]),
        "i6": int(flag_values["binding_ok"]),
        "i7": int(flag_values["policy_ok"]),
        "i8": int(flag_values["nonce_ok"]),
        "i9": int(flag_values["unclaimed_ok"]),
    }
    if {key: _require_int(tau_inputs.get(key), name=f"claim.body.tau_inputs.{key}") for key in expected_tau_inputs} != expected_tau_inputs:
        raise ValueError("tau_inputs mismatch")

    conditions = _require_mapping(body.get("conditions"), name="claim.body.conditions")
    if _require_bool(conditions.get("round_ok"), name="claim.body.conditions.round_ok") is not True:
        raise ValueError("round_ok must be true")
    if _require_bool(conditions.get("positive_improvement"), name="claim.body.conditions.positive_improvement") is not True:
        raise ValueError("positive_improvement must be true")
    if _require_bool(conditions.get("budget_ok"), name="claim.body.conditions.budget_ok") != budget_ok:
        raise ValueError("budget_ok mismatch")
    tau_gate_expected_ok = bool(budget_ok and all(value == 1 for value in flag_values.values()))
    if _require_bool(
        conditions.get("tau_gate_expected_ok"),
        name="claim.body.conditions.tau_gate_expected_ok",
    ) != tau_gate_expected_ok:
        raise ValueError("tau_gate_expected_ok mismatch")
    if require_admissible and not tau_gate_expected_ok:
        raise ValueError("proof-mining claim inadmissible")

    return {
        "schema": "zenodex/permissionless_solver_proof_mining_claim/v1",
        "artifact_hash": claim_hash,
        "round_id": _require_str(body.get("round_id"), name="claim.body.round_id"),
        "job_digest": _require_str(body.get("job_digest"), name="claim.body.job_digest"),
        "winner": winner,
        "base_reward": base_reward,
        "epoch": epoch,
        "payout_amount": reward_amount,
        "reward_pool_before": reward_pool_before,
        "reward_pool_after": reward_pool_after,
        "proposal_slot": proposal_slot,
        "prover_id": prover_id,
        "proposal_hash": expected_proposal_hash,
    }
