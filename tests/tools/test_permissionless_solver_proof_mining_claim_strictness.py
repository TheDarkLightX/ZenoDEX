from __future__ import annotations

import re

import pytest

from tools.permissionless_solver_proof_mining_claim import (
    build_proof_mining_claim,
    proof_mining_claim_hash,
    validate_proof_mining_claim_artifact,
)


def _round_obj() -> dict:
    return {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": "job1",
        "winner": {
            "miner_id": "alice",
            "witness_sha256": "sha:a",
            "improvement_u64": 7,
        },
        "candidates": [],
        "argmax_certificate": None,
    }


@pytest.mark.parametrize(
    "field",
    [
        "round_ok",
        "positive_improvement",
        "budget_ok",
        "tau_gate_expected_ok",
    ],
)
def test_validate_proof_mining_claim_rejects_string_condition_flags(field: str) -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(),
        round_id="round-proof-condition-strictness",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["conditions"][field] = "yes"
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])

    with pytest.raises(
        TypeError,
        match=re.escape(f"claim.body.conditions.{field} must be a bool"),
    ):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)
