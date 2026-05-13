from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

CLAIM_SCHEMA = "zenodex/permissionless_solver_proof_mining_claim/v2"
VERIFIER_EVIDENCE_SCHEMA = "zenodex/proof_mining_verifier_evidence/v1"
U32_MAX = 0xFFFFFFFF
U64_MAX = 0xFFFFFFFFFFFFFFFF
MAX_EPOCH = 7
MAX_PROPOSAL_SLOT = 7
MAX_PROVER_ID = 3
MAX_VERIFIER_ID = 7
MAX_VERIFIER_DOMAIN_ID = 7
MAX_VERIFIER_COUNT = 8
MAX_VERIFIER_QUORUM = 8
MAX_VERIFIER_DOMAIN_DIVERSITY = 8
DEFAULT_MIN_VERIFIER_QUORUM = 2
DEFAULT_MIN_VERIFIER_DOMAIN_DIVERSITY = 2


@dataclass(frozen=True)
class _WinnerFacts:
    witness_hash: str
    improvement_u64: int


@dataclass(frozen=True)
class _ProposalFacts:
    binding: dict[str, Any]
    proposal_hash: str


@dataclass(frozen=True)
class _BoundedModelFacts:
    proposal_slot: int
    prover_id: int
    base_reward: int
    epoch: int
    reward_amount: int


@dataclass(frozen=True)
class _BudgetFacts:
    reward_pool_before: int
    reward_pool_after: int
    budget_ok: bool


@dataclass(frozen=True)
class _VerifierEvidenceFacts:
    min_quorum: int
    min_domain_diversity: int
    verifier_count: int
    distinct_domain_count: int
    quorum_ok: bool
    diversity_ok: bool

    @property
    def evidence_ok(self) -> bool:
        return bool(self.quorum_ok and self.diversity_ok)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_round_id(value: Any) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError("round_id must be non-empty")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_flag(value: Any, *, name: str) -> int:
    flag = _require_int(value, name=name)
    if flag not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return int(flag)


def _require_reward_pool_before(value: Any) -> int:
    reward_pool = _require_int(value, name="reward_pool_before")
    if reward_pool < 0 or reward_pool > U32_MAX:
        raise ValueError("reward_pool_before out of u32 range")
    return reward_pool


def _require_proposal_slot(value: Any, *, name: str) -> int:
    slot = _require_int(value, name=name)
    if slot < 0 or slot > MAX_PROPOSAL_SLOT:
        raise ValueError("proposal_slot out of range")
    return slot


def _require_prover_id(value: Any, *, name: str) -> int:
    prover = _require_int(value, name=name)
    if prover < 0 or prover > MAX_PROVER_ID:
        raise ValueError("prover_id out of range")
    return prover


def _require_verifier_id(value: Any, *, name: str) -> int:
    verifier_id = _require_int(value, name=name)
    if verifier_id < 0 or verifier_id > MAX_VERIFIER_ID:
        raise ValueError("verifier_id out of range")
    return verifier_id


def _require_verifier_domain_id(value: Any, *, name: str) -> int:
    domain_id = _require_int(value, name=name)
    if domain_id < 0 or domain_id > MAX_VERIFIER_DOMAIN_ID:
        raise ValueError("verifier domain_id out of range")
    return domain_id


def _require_verifier_threshold(value: Any, *, name: str, maximum: int) -> int:
    threshold = _require_int(value, name=name)
    if threshold <= 0 or threshold > maximum:
        raise ValueError(f"{name} out of range")
    return threshold


def _require_winner_facts(winner: Mapping[str, Any], *, name: str) -> _WinnerFacts:
    witness_hash = _require_str(winner.get("witness_sha256"), name=f"{name}.witness_sha256")
    improvement_u64 = _require_int(winner.get("improvement_u64"), name=f"{name}.improvement_u64")
    if improvement_u64 <= 0:
        raise ValueError("winner improvement must be positive")
    if improvement_u64 > U64_MAX:
        raise ValueError("winner improvement out of u64 range")
    return _WinnerFacts(witness_hash=witness_hash, improvement_u64=improvement_u64)


def _require_build_flags(
    *,
    proof_ok: int,
    binding_ok: int,
    policy_ok: int,
    nonce_ok: int,
    unclaimed_ok: int,
) -> dict[str, int]:
    return {
        "proof_ok": _require_flag(proof_ok, name="proof_ok"),
        "binding_ok": _require_flag(binding_ok, name="binding_ok"),
        "policy_ok": _require_flag(policy_ok, name="policy_ok"),
        "nonce_ok": _require_flag(nonce_ok, name="nonce_ok"),
        "unclaimed_ok": _require_flag(unclaimed_ok, name="unclaimed_ok"),
    }


def _canonical_verifier_evidence(
    *,
    verifier_evidence: Any,
    min_verifier_quorum: int,
    min_verifier_domain_diversity: int,
) -> tuple[dict[str, Any], _VerifierEvidenceFacts]:
    min_quorum = _require_verifier_threshold(
        min_verifier_quorum,
        name="min_verifier_quorum",
        maximum=MAX_VERIFIER_QUORUM,
    )
    min_domain_diversity = _require_verifier_threshold(
        min_verifier_domain_diversity,
        name="min_verifier_domain_diversity",
        maximum=MAX_VERIFIER_DOMAIN_DIVERSITY,
    )
    if min_domain_diversity > min_quorum:
        raise ValueError("min_verifier_domain_diversity cannot exceed min_verifier_quorum")

    if verifier_evidence is None:
        raw_entries: list[Any] = []
    elif isinstance(verifier_evidence, Mapping):
        raise TypeError("verifier_evidence must be a sequence")
    else:
        raw_entries = list(verifier_evidence)
    if len(raw_entries) > MAX_VERIFIER_COUNT:
        raise ValueError("too many verifier evidence entries")

    entries: list[dict[str, int]] = []
    seen_verifier_ids: set[int] = set()
    accepted_domains: set[int] = set()
    accepted_count = 0
    for index, raw_entry in enumerate(raw_entries):
        entry = _require_mapping(raw_entry, name=f"verifier_evidence[{index}]")
        verifier_id = _require_verifier_id(
            entry.get("verifier_id"),
            name=f"verifier_evidence[{index}].verifier_id",
        )
        if verifier_id in seen_verifier_ids:
            raise ValueError("duplicate verifier_id")
        seen_verifier_ids.add(verifier_id)
        domain_id = _require_verifier_domain_id(
            entry.get("domain_id"),
            name=f"verifier_evidence[{index}].domain_id",
        )
        accepted = _require_flag(
            entry.get("accepted"),
            name=f"verifier_evidence[{index}].accepted",
        )
        if accepted == 1:
            accepted_count += 1
            accepted_domains.add(domain_id)
        entries.append(
            {
                "verifier_id": int(verifier_id),
                "domain_id": int(domain_id),
                "accepted": int(accepted),
            }
        )

    entries.sort(key=lambda item: item["verifier_id"])
    distinct_domain_count = len(accepted_domains)
    facts = _VerifierEvidenceFacts(
        min_quorum=int(min_quorum),
        min_domain_diversity=int(min_domain_diversity),
        verifier_count=int(accepted_count),
        distinct_domain_count=int(distinct_domain_count),
        quorum_ok=bool(accepted_count >= min_quorum),
        diversity_ok=bool(distinct_domain_count >= min_domain_diversity),
    )
    evidence = {
        "schema": VERIFIER_EVIDENCE_SCHEMA,
        "min_quorum": int(min_quorum),
        "min_domain_diversity": int(min_domain_diversity),
        "verifiers": entries,
    }
    return evidence, facts


def _tau_gate_expected_ok(*, flags: Mapping[str, int], budget_ok: bool) -> bool:
    return bool(budget_ok and all(value == 1 for value in flags.values()))


def _tau_inputs(
    *,
    base_reward: int,
    epoch: int,
    reward_amount: int,
    reward_pool_before: int,
    flags: Mapping[str, int],
) -> dict[str, int]:
    return {
        "i1": int(base_reward),
        "i2": int(epoch),
        "i3": int(reward_amount),
        "i4": int(reward_pool_before),
        "i5": int(flags["proof_ok"]),
        "i6": int(flags["binding_ok"]),
        "i7": int(flags["policy_ok"]),
        "i8": int(flags["nonce_ok"]),
        "i9": int(flags["unclaimed_ok"]),
    }


def fallback_proposal_hash(*, round_id: str, job_digest: str, witness_hash: str) -> str:
    binding = {
        "mode": "round_fallback_v1",
        "round_id": _require_str(round_id, name="round_id"),
        "job_digest": _require_str(job_digest, name="job_digest"),
        "witness_hash": _require_str(witness_hash, name="witness_hash"),
    }
    return sha256_hex(
        domain_sep_bytes("permissionless_solver_proposal_fallback", version=1)
        + canonical_json_bytes(binding)
    )


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
    return sha256_hex(
        domain_sep_bytes("proof_mining_proposal", version=1) + canonical_json_bytes(binding)
    )


def proof_mining_claim_hash(body: Mapping[str, Any]) -> str:
    return sha256_hex(
        domain_sep_bytes("permissionless_solver_proof_mining_claim", version=1)
        + canonical_json_bytes(dict(body))
    )


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


def _build_proposal_facts(
    *,
    round_id: str,
    job_digest: str,
    witness_hash: str,
    chain_id: str,
    prev_state_hash: str,
    batch_hash: str,
    dex_hash_after: str,
) -> _ProposalFacts:
    explicit_binding_fields = [chain_id, prev_state_hash, batch_hash, dex_hash_after]
    explicit_count = sum(1 for value in explicit_binding_fields if str(value).strip())
    if 0 < explicit_count < len(explicit_binding_fields):
        raise ValueError(
            "explicit proposal binding requires chain_id, prev_state_hash, batch_hash, and dex_hash_after together"
        )
    if explicit_count == len(explicit_binding_fields):
        binding = {
            "mode": "explicit_v1",
            "chain_id": _require_str(chain_id, name="chain_id"),
            "prev_state_hash": _require_str(prev_state_hash, name="prev_state_hash"),
            "batch_hash": _require_str(batch_hash, name="batch_hash"),
            "witness_hash": witness_hash,
            "dex_hash_after": _require_str(dex_hash_after, name="dex_hash_after"),
        }
        proposal_hash = explicit_proposal_hash(
            chain_id=binding["chain_id"],
            prev_state_hash=binding["prev_state_hash"],
            batch_hash=binding["batch_hash"],
            witness_hash=binding["witness_hash"],
            dex_hash_after=binding["dex_hash_after"],
        )
        return _ProposalFacts(binding=binding, proposal_hash=proposal_hash)

    binding = {
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
    return _ProposalFacts(binding=binding, proposal_hash=proposal_hash)


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
    verifier_evidence: Any = None,
    min_verifier_quorum: int = DEFAULT_MIN_VERIFIER_QUORUM,
    min_verifier_domain_diversity: int = DEFAULT_MIN_VERIFIER_DOMAIN_DIVERSITY,
) -> dict[str, Any]:
    if bool(round_obj.get("ok")) is not True:
        raise ValueError("round must be ok")

    round_id_str = _require_round_id(round_id)
    reward_pool = _require_reward_pool_before(reward_pool_before)
    slot = _require_proposal_slot(proposal_slot, name="proposal_slot")
    prover = _require_prover_id(prover_id, name="prover_id")

    winner = _require_mapping(round_obj.get("winner"), name="winner")
    miner_id = _require_str(winner.get("miner_id"), name="winner.miner_id")
    winner_facts = _require_winner_facts(winner, name="winner")
    job_digest = _require_str(round_obj.get("job_digest"), name="round.job_digest")
    proposal = _build_proposal_facts(
        round_id=round_id_str,
        job_digest=job_digest,
        witness_hash=winner_facts.witness_hash,
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        dex_hash_after=dex_hash_after,
    )

    reward_amount = schedule_reward_amount(base_reward=base_reward, epoch=epoch)
    reward_pool_after = int(reward_pool) - int(reward_amount)
    flags = _require_build_flags(
        proof_ok=proof_ok,
        binding_ok=binding_ok,
        policy_ok=policy_ok,
        nonce_ok=nonce_ok,
        unclaimed_ok=unclaimed_ok,
    )
    budget_ok = bool(reward_pool >= reward_amount)
    tau_gate_ok = _tau_gate_expected_ok(flags=flags, budget_ok=budget_ok)
    verifier_evidence_obj, verifier_evidence_facts = _canonical_verifier_evidence(
        verifier_evidence=verifier_evidence,
        min_verifier_quorum=min_verifier_quorum,
        min_verifier_domain_diversity=min_verifier_domain_diversity,
    )
    if not bool(tau_gate_ok) and not bool(allow_rejected):
        raise ValueError("proof-mining claim would fail Tau gate")
    if not bool(verifier_evidence_facts.evidence_ok) and not bool(allow_rejected):
        raise ValueError("proof-mining claim would fail verifier evidence gate")

    body = {
        "schema": CLAIM_SCHEMA,
        "round_id": str(round_id_str),
        "job_digest": job_digest,
        "proposal_hash": proposal.proposal_hash,
        "proposal_binding": proposal.binding,
        "winner": {
            "miner_id": miner_id,
            "witness_sha256": winner_facts.witness_hash,
            "improvement_u64": int(winner_facts.improvement_u64),
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
        "verifier_evidence": verifier_evidence_obj,
        "verification_flags": dict(flags),
        "tau_inputs": _tau_inputs(
            base_reward=base_reward,
            epoch=epoch,
            reward_amount=reward_amount,
            reward_pool_before=reward_pool,
            flags=flags,
        ),
        "conditions": {
            "round_ok": True,
            "positive_improvement": True,
            "budget_ok": bool(budget_ok),
            "tau_gate_expected_ok": bool(tau_gate_ok),
            "verifier_quorum_ok": bool(verifier_evidence_facts.quorum_ok),
            "verifier_diversity_ok": bool(verifier_evidence_facts.diversity_ok),
            "admissible_expected_ok": bool(
                tau_gate_ok and verifier_evidence_facts.evidence_ok
            ),
        },
    }
    claim_hash = proof_mining_claim_hash(body)
    return {"body": body, "claim_hash": claim_hash}


def _require_claim_body(claim_artifact: Mapping[str, Any]) -> tuple[Mapping[str, Any], str]:
    body = _require_mapping(claim_artifact.get("body"), name="claim.body")
    if _require_str(body.get("schema"), name="claim.body.schema") != CLAIM_SCHEMA:
        raise ValueError("unsupported proof-mining claim schema")
    claim_hash = _require_str(claim_artifact.get("claim_hash"), name="claim.claim_hash")
    if claim_hash != proof_mining_claim_hash(body):
        raise ValueError("claim_hash mismatch")
    return body, claim_hash


def _expected_proposal_hash(
    *, body: Mapping[str, Any], proposal_binding: Mapping[str, Any], binding_mode: str
) -> str:
    if binding_mode == "explicit_v1":
        return explicit_proposal_hash(
            chain_id=_require_str(
                proposal_binding.get("chain_id"),
                name="claim.body.proposal_binding.chain_id",
            ),
            prev_state_hash=_require_str(
                proposal_binding.get("prev_state_hash"),
                name="claim.body.proposal_binding.prev_state_hash",
            ),
            batch_hash=_require_str(
                proposal_binding.get("batch_hash"),
                name="claim.body.proposal_binding.batch_hash",
            ),
            witness_hash=_require_str(
                proposal_binding.get("witness_hash"),
                name="claim.body.proposal_binding.witness_hash",
            ),
            dex_hash_after=_require_str(
                proposal_binding.get("dex_hash_after"),
                name="claim.body.proposal_binding.dex_hash_after",
            ),
        )

    if binding_mode == "round_fallback_v1":
        binding_round_id = _require_str(
            proposal_binding.get("round_id"),
            name="claim.body.proposal_binding.round_id",
        )
        binding_job_digest = _require_str(
            proposal_binding.get("job_digest"),
            name="claim.body.proposal_binding.job_digest",
        )
        expected_proposal_hash = fallback_proposal_hash(
            round_id=binding_round_id,
            job_digest=binding_job_digest,
            witness_hash=_require_str(
                proposal_binding.get("witness_hash"),
                name="claim.body.proposal_binding.witness_hash",
            ),
        )
        if binding_round_id != _require_str(body.get("round_id"), name="claim.body.round_id"):
            raise ValueError("proposal binding round_id mismatch")
        if binding_job_digest != _require_str(body.get("job_digest"), name="claim.body.job_digest"):
            raise ValueError("proposal binding job_digest mismatch")
        return expected_proposal_hash

    raise ValueError("unsupported proposal binding mode")


def _validate_proposal_binding(*, body: Mapping[str, Any], witness_hash: str) -> str:
    proposal_binding = _require_mapping(
        body.get("proposal_binding"),
        name="claim.body.proposal_binding",
    )
    binding_mode = _require_str(
        proposal_binding.get("mode"),
        name="claim.body.proposal_binding.mode",
    )
    expected_proposal_hash = _expected_proposal_hash(
        body=body,
        proposal_binding=proposal_binding,
        binding_mode=binding_mode,
    )
    if (
        _require_str(body.get("proposal_hash"), name="claim.body.proposal_hash")
        != expected_proposal_hash
    ):
        raise ValueError("proposal_hash mismatch")
    if (
        _require_str(
            proposal_binding.get("witness_hash"),
            name="claim.body.proposal_binding.witness_hash",
        )
        != witness_hash
    ):
        raise ValueError("proposal binding witness mismatch")
    return expected_proposal_hash


def _validate_bounded_model(body: Mapping[str, Any]) -> _BoundedModelFacts:
    bounded_model = _require_mapping(body.get("bounded_model"), name="claim.body.bounded_model")
    if (
        _require_str(bounded_model.get("reward_kind"), name="claim.body.bounded_model.reward_kind")
        != "TreasuryTransfer"
    ):
        raise ValueError("unsupported reward kind")

    proposal_slot = _require_proposal_slot(
        bounded_model.get("proposal_slot"),
        name="claim.body.bounded_model.proposal_slot",
    )
    prover_id = _require_prover_id(
        bounded_model.get("prover_id"),
        name="claim.body.bounded_model.prover_id",
    )
    base_reward = _require_int(
        bounded_model.get("base_reward"),
        name="claim.body.bounded_model.base_reward",
    )
    epoch = _require_int(bounded_model.get("epoch"), name="claim.body.bounded_model.epoch")
    reward_amount = _require_int(
        bounded_model.get("reward_amount"),
        name="claim.body.bounded_model.reward_amount",
    )
    if reward_amount != schedule_reward_amount(base_reward=base_reward, epoch=epoch):
        raise ValueError("reward schedule mismatch")

    return _BoundedModelFacts(
        proposal_slot=proposal_slot,
        prover_id=prover_id,
        base_reward=base_reward,
        epoch=epoch,
        reward_amount=reward_amount,
    )


def _validate_budget(*, body: Mapping[str, Any], reward_amount: int) -> _BudgetFacts:
    budget = _require_mapping(body.get("budget"), name="claim.body.budget")
    reward_pool_before = _require_int(
        budget.get("reward_pool_before"),
        name="claim.body.budget.reward_pool_before",
    )
    reward_pool_after = _require_int(
        budget.get("reward_pool_after"),
        name="claim.body.budget.reward_pool_after",
    )
    budget_ok = bool(
        reward_pool_before >= reward_amount
        and reward_pool_before - reward_amount == reward_pool_after
        and reward_pool_after >= 0
    )
    return _BudgetFacts(
        reward_pool_before=reward_pool_before,
        reward_pool_after=reward_pool_after,
        budget_ok=budget_ok,
    )


def _validate_flags(body: Mapping[str, Any]) -> dict[str, int]:
    flags = _require_mapping(body.get("verification_flags"), name="claim.body.verification_flags")
    return {
        "proof_ok": _require_flag(
            flags.get("proof_ok"),
            name="claim.body.verification_flags.proof_ok",
        ),
        "binding_ok": _require_flag(
            flags.get("binding_ok"),
            name="claim.body.verification_flags.binding_ok",
        ),
        "policy_ok": _require_flag(
            flags.get("policy_ok"),
            name="claim.body.verification_flags.policy_ok",
        ),
        "nonce_ok": _require_flag(
            flags.get("nonce_ok"),
            name="claim.body.verification_flags.nonce_ok",
        ),
        "unclaimed_ok": _require_flag(
            flags.get("unclaimed_ok"),
            name="claim.body.verification_flags.unclaimed_ok",
        ),
    }


def _validate_verifier_evidence(body: Mapping[str, Any]) -> _VerifierEvidenceFacts:
    verifier_evidence_obj = _require_mapping(
        body.get("verifier_evidence"),
        name="claim.body.verifier_evidence",
    )
    if (
        _require_str(verifier_evidence_obj.get("schema"), name="claim.body.verifier_evidence.schema")
        != VERIFIER_EVIDENCE_SCHEMA
    ):
        raise ValueError("unsupported verifier evidence schema")
    canonical, facts = _canonical_verifier_evidence(
        verifier_evidence=verifier_evidence_obj.get("verifiers"),
        min_verifier_quorum=verifier_evidence_obj.get("min_quorum"),
        min_verifier_domain_diversity=verifier_evidence_obj.get("min_domain_diversity"),
    )
    if dict(verifier_evidence_obj) != canonical:
        raise ValueError("verifier_evidence not canonical")
    return facts


def _validate_tau_inputs(
    *,
    body: Mapping[str, Any],
    bounded_model: _BoundedModelFacts,
    budget: _BudgetFacts,
    flags: Mapping[str, int],
) -> None:
    tau_inputs = _require_mapping(body.get("tau_inputs"), name="claim.body.tau_inputs")
    expected_tau_inputs = _tau_inputs(
        base_reward=bounded_model.base_reward,
        epoch=bounded_model.epoch,
        reward_amount=bounded_model.reward_amount,
        reward_pool_before=budget.reward_pool_before,
        flags=flags,
    )
    actual_tau_inputs = {
        key: _require_int(tau_inputs.get(key), name=f"claim.body.tau_inputs.{key}")
        for key in expected_tau_inputs
    }
    if actual_tau_inputs != expected_tau_inputs:
        raise ValueError("tau_inputs mismatch")


def _validate_conditions(
    *,
    body: Mapping[str, Any],
    budget_ok: bool,
    flags: Mapping[str, int],
    verifier_evidence: _VerifierEvidenceFacts,
) -> tuple[bool, bool]:
    conditions = _require_mapping(body.get("conditions"), name="claim.body.conditions")
    if bool(conditions.get("round_ok")) is not True:
        raise ValueError("round_ok must be true")
    if bool(conditions.get("positive_improvement")) is not True:
        raise ValueError("positive_improvement must be true")
    if bool(conditions.get("budget_ok")) != budget_ok:
        raise ValueError("budget_ok mismatch")

    tau_gate_ok = _tau_gate_expected_ok(flags=flags, budget_ok=budget_ok)
    if bool(conditions.get("tau_gate_expected_ok")) != tau_gate_ok:
        raise ValueError("tau_gate_expected_ok mismatch")
    if bool(conditions.get("verifier_quorum_ok")) != verifier_evidence.quorum_ok:
        raise ValueError("verifier_quorum_ok mismatch")
    if bool(conditions.get("verifier_diversity_ok")) != verifier_evidence.diversity_ok:
        raise ValueError("verifier_diversity_ok mismatch")
    admissible_ok = bool(tau_gate_ok and verifier_evidence.evidence_ok)
    if bool(conditions.get("admissible_expected_ok")) != admissible_ok:
        raise ValueError("admissible_expected_ok mismatch")
    return tau_gate_ok, admissible_ok


def validate_proof_mining_claim_artifact(
    claim_artifact: Mapping[str, Any], *, require_admissible: bool = True
) -> dict[str, Any]:
    body, claim_hash = _require_claim_body(claim_artifact)
    winner = _require_mapping(body.get("winner"), name="claim.body.winner")
    winner_facts = _require_winner_facts(winner, name="claim.body.winner")
    expected_proposal_hash = _validate_proposal_binding(
        body=body,
        witness_hash=winner_facts.witness_hash,
    )
    bounded_model = _validate_bounded_model(body)
    budget = _validate_budget(body=body, reward_amount=bounded_model.reward_amount)
    verifier_evidence = _validate_verifier_evidence(body)
    flags = _validate_flags(body)
    _validate_tau_inputs(body=body, bounded_model=bounded_model, budget=budget, flags=flags)
    _, admissible_ok = _validate_conditions(
        body=body,
        budget_ok=budget.budget_ok,
        flags=flags,
        verifier_evidence=verifier_evidence,
    )
    if require_admissible and not admissible_ok:
        raise ValueError("proof-mining claim inadmissible")

    return {
        "schema": CLAIM_SCHEMA,
        "artifact_hash": claim_hash,
        "round_id": _require_str(body.get("round_id"), name="claim.body.round_id"),
        "job_digest": _require_str(body.get("job_digest"), name="claim.body.job_digest"),
        "winner": winner,
        "base_reward": bounded_model.base_reward,
        "epoch": bounded_model.epoch,
        "payout_amount": bounded_model.reward_amount,
        "reward_pool_before": budget.reward_pool_before,
        "reward_pool_after": budget.reward_pool_after,
        "proposal_slot": bounded_model.proposal_slot,
        "prover_id": bounded_model.prover_id,
        "proposal_hash": expected_proposal_hash,
        "verifier_count": verifier_evidence.verifier_count,
        "verifier_domain_count": verifier_evidence.distinct_domain_count,
        "min_verifier_quorum": verifier_evidence.min_quorum,
        "min_verifier_domain_diversity": verifier_evidence.min_domain_diversity,
    }
