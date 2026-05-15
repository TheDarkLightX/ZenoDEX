from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from tools.permissionless_solver_proof_mining_claim import (
    build_proof_mining_claim as _build_proof_mining_claim,
    explicit_proposal_hash,
    fallback_proposal_hash,
    proof_mining_claim_hash,
    schedule_reward_amount,
    validate_proof_mining_claim_artifact,
)

SPEC_PATH = (
    Path(__file__).resolve().parents[2] / "src" / "tau_specs" / "proof_mining_reward_32_v1.tau"
)
U32_MAX = 0xFFFFFFFF


def _verifier_evidence() -> list[dict[str, int]]:
    return [
        {"verifier_id": 0, "domain_id": 0, "accepted": 1},
        {"verifier_id": 1, "domain_id": 1, "accepted": 1},
    ]


def build_proof_mining_claim(**kwargs):
    kwargs.setdefault("verifier_evidence", _verifier_evidence())
    return _build_proof_mining_claim(**kwargs)


def _round_obj(
    *,
    miner_id: str = "alice",
    witness_sha256: str = "sha:a",
    improvement_u64: int = 7,
    job_digest: str = "job1",
) -> dict:
    return {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": job_digest,
        "winner": {
            "miner_id": miner_id,
            "witness_sha256": witness_sha256,
            "improvement_u64": improvement_u64,
        },
        "candidates": [],
        "argmax_certificate": None,
    }


@pytest.mark.parametrize(
    ("base_reward", "epoch", "expected"),
    [
        (64, 0, 64),
        (64, 1, 32),
        (64, 6, 1),
        (1, 7, 1),
    ],
)
def test_schedule_reward_amount_bva(base_reward: int, epoch: int, expected: int) -> None:
    assert schedule_reward_amount(base_reward=base_reward, epoch=epoch) == expected


@settings(max_examples=64, deadline=None)
@given(
    base_reward=st.integers(min_value=1, max_value=U32_MAX),
    epoch=st.integers(min_value=0, max_value=7),
)
def test_schedule_reward_amount_matches_shift_floor(base_reward: int, epoch: int) -> None:
    expected = max(int(base_reward) >> int(epoch), 1)

    assert schedule_reward_amount(base_reward=base_reward, epoch=epoch) == expected


@pytest.mark.parametrize(
    ("base_reward", "epoch"),
    [
        (0, 0),
        (1, -1),
        (1, 8),
        (0x1_0000_0000, 0),
    ],
)
def test_schedule_reward_amount_rejects_invalid_inputs(base_reward: int, epoch: int) -> None:
    with pytest.raises((TypeError, ValueError)):
        schedule_reward_amount(base_reward=base_reward, epoch=epoch)


def test_build_proof_mining_claim_matches_tau_gate_inputs() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-1",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=2,
        prover_id=1,
    )
    body = claim["body"]
    assert body["schema"] == "zenodex/permissionless_solver_proof_mining_claim/v2"
    assert body["budget"]["reward_pool_after"] == 16
    assert body["bounded_model"]["reward_amount"] == 4
    assert body["conditions"]["tau_gate_expected_ok"] is True
    assert body["conditions"]["admissible_expected_ok"] is True
    assert body["verifier_evidence"]["min_quorum"] == 2
    assert body["verifier_evidence"]["min_domain_diversity"] == 2
    assert body["proposal_hash"] == fallback_proposal_hash(
        round_id="round-proof-1",
        job_digest="job1",
        witness_hash="sha:a",
    )
    assert claim["claim_hash"]

    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[dict(body["tau_inputs"])],
        timeout_s=30.0,
    )
    assert outputs[0]["o4"] == 1


def test_build_proof_mining_claim_detects_budget_failure() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=5),
        round_id="round-proof-2",
        reward_pool_before=3,
        base_reward=8,
        epoch=0,
        proposal_slot=0,
        prover_id=0,
        allow_rejected=True,
    )
    body = claim["body"]
    assert body["bounded_model"]["reward_amount"] == 8
    assert body["budget"]["reward_pool_after"] == -5
    assert body["conditions"]["budget_ok"] is False
    assert body["conditions"]["tau_gate_expected_ok"] is False
    with pytest.raises(ValueError, match="inadmissible"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_build_proof_mining_claim_requires_positive_improvement() -> None:
    with pytest.raises(ValueError, match="winner improvement must be positive"):
        build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=0),
            round_id="round-proof-3",
            reward_pool_before=20,
            base_reward=8,
            epoch=0,
            proposal_slot=0,
            prover_id=0,
        )


def test_build_proof_mining_claim_fails_closed_by_default_on_budget_failure() -> None:
    with pytest.raises(ValueError, match="would fail Tau gate"):
        build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=5),
            round_id="round-proof-4",
            reward_pool_before=3,
            base_reward=8,
            epoch=0,
            proposal_slot=0,
            prover_id=0,
        )


def test_build_proof_mining_claim_fails_closed_on_insufficient_verifier_quorum() -> None:
    with pytest.raises(ValueError, match="verifier evidence gate"):
        _build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=5),
            round_id="round-proof-verifier-1",
            reward_pool_before=20,
            base_reward=8,
            epoch=1,
            proposal_slot=0,
            prover_id=0,
            verifier_evidence=[{"verifier_id": 0, "domain_id": 0, "accepted": 1}],
        )


@pytest.mark.parametrize(
    ("verifier_evidence", "min_quorum", "min_domain_diversity", "expected_error"),
    [
        (
            [{"verifier_id": 0, "domain_id": 0, "accepted": 1}],
            1,
            1,
            "min_verifier_quorum out of range",
        ),
        (
            [
                {"verifier_id": 0, "domain_id": 0, "accepted": 1},
                {"verifier_id": 1, "domain_id": 0, "accepted": 1},
            ],
            2,
            1,
            "min_verifier_domain_diversity out of range",
        ),
    ],
)
def test_validate_proof_mining_claim_rejects_claim_controlled_verifier_thresholds(
    verifier_evidence: list[dict[str, int]],
    min_quorum: int,
    min_domain_diversity: int,
    expected_error: str,
) -> None:
    claim = _build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=5),
        round_id="round-proof-verifier-threshold-downgrade",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
        verifier_evidence=verifier_evidence,
        allow_rejected=True,
    )
    claim["body"]["verifier_evidence"]["min_quorum"] = min_quorum
    claim["body"]["verifier_evidence"]["min_domain_diversity"] = min_domain_diversity
    claim["body"]["conditions"]["verifier_quorum_ok"] = True
    claim["body"]["conditions"]["verifier_diversity_ok"] = True
    claim["body"]["conditions"]["admissible_expected_ok"] = True
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])

    with pytest.raises(ValueError, match=expected_error):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_validate_proof_mining_claim_rejects_verifier_domain_collapse() -> None:
    claim = _build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=5),
        round_id="round-proof-verifier-2",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
        verifier_evidence=[
            {"verifier_id": 0, "domain_id": 0, "accepted": 1},
            {"verifier_id": 1, "domain_id": 0, "accepted": 1},
        ],
        allow_rejected=True,
    )
    assert claim["body"]["conditions"]["verifier_quorum_ok"] is True
    assert claim["body"]["conditions"]["verifier_diversity_ok"] is False
    with pytest.raises(ValueError, match="inadmissible"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_validate_proof_mining_claim_rejects_duplicate_verifier_id() -> None:
    with pytest.raises(ValueError, match="duplicate verifier_id"):
        _build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=5),
            round_id="round-proof-verifier-3",
            reward_pool_before=20,
            base_reward=8,
            epoch=1,
            proposal_slot=0,
            prover_id=0,
            verifier_evidence=[
                {"verifier_id": 0, "domain_id": 0, "accepted": 1},
                {"verifier_id": 0, "domain_id": 1, "accepted": 1},
            ],
            allow_rejected=True,
        )


def test_validate_proof_mining_claim_rejects_tampered_verifier_condition() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=5),
        round_id="round-proof-verifier-4",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["conditions"]["verifier_quorum_ok"] = False
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="verifier_quorum_ok mismatch"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_validate_proof_mining_claim_rejects_noncanonical_verifier_order() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=5),
        round_id="round-proof-verifier-5",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["verifier_evidence"]["verifiers"] = list(
        reversed(claim["body"]["verifier_evidence"]["verifiers"])
    )
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="verifier_evidence not canonical"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_validate_proof_mining_claim_rejects_reward_schedule_mismatch() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-5",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["bounded_model"]["reward_amount"] = 5
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="reward schedule mismatch"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_build_proof_mining_claim_golden_hash_is_stable() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(
            miner_id="miner-golden",
            witness_sha256="witness-golden",
            improvement_u64=17,
            job_digest="job-golden",
        ),
        round_id="round-golden",
        reward_pool_before=42,
        base_reward=16,
        epoch=2,
        proposal_slot=3,
        prover_id=2,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev-golden",
        batch_hash="sha256:batch-golden",
        dex_hash_after="sha256:after-golden",
    )

    assert (
        claim["claim_hash"] == "0x87ff6026781c476bb33e747a821c1609c7dc229b8ae07985810fa28f7454a0c4"
    )
    assert (
        claim["body"]["proposal_hash"]
        == "0x2f895d190716d06e619c79c53599084d968977bf1bb8853c0446cd5eb42c51e7"
    )
    assert (
        validate_proof_mining_claim_artifact(claim, require_admissible=True)["payout_amount"] == 4
    )


@settings(max_examples=48, deadline=None)
@given(
    reward_pool_before=st.integers(min_value=1, max_value=128),
    base_reward=st.integers(min_value=1, max_value=32),
    epoch=st.integers(min_value=0, max_value=5),
    proposal_slot=st.integers(min_value=0, max_value=7),
    prover_id=st.integers(min_value=0, max_value=3),
    explicit_binding=st.booleans(),
)
def test_build_validate_claim_roundtrips_generated_admissible_inputs(
    reward_pool_before: int,
    base_reward: int,
    epoch: int,
    proposal_slot: int,
    prover_id: int,
    explicit_binding: bool,
) -> None:
    reward_amount = schedule_reward_amount(base_reward=base_reward, epoch=epoch)
    reward_pool_before = max(reward_pool_before, reward_amount)
    kwargs = {
        "chain_id": "tau-testnet-alpha",
        "prev_state_hash": "sha256:prev-property",
        "batch_hash": "sha256:batch-property",
        "dex_hash_after": "sha256:after-property",
    }
    if not explicit_binding:
        kwargs = {}
    claim = build_proof_mining_claim(
        round_obj=_round_obj(
            improvement_u64=1 + proposal_slot, job_digest=f"job-{proposal_slot}-{prover_id}"
        ),
        round_id=f"round-{proposal_slot}-{prover_id}-{epoch}",
        reward_pool_before=reward_pool_before,
        base_reward=base_reward,
        epoch=epoch,
        proposal_slot=proposal_slot,
        prover_id=prover_id,
        **kwargs,
    )

    validated = validate_proof_mining_claim_artifact(claim, require_admissible=True)

    assert validated["payout_amount"] == reward_amount
    assert validated["reward_pool_before"] == reward_pool_before
    assert validated["reward_pool_after"] == reward_pool_before - reward_amount
    assert validated["proposal_hash"] == claim["body"]["proposal_hash"]


def test_build_proof_mining_claim_supports_explicit_proposal_binding() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-6",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev",
        batch_hash="sha256:batch",
        dex_hash_after="sha256:after",
    )
    body = claim["body"]
    assert body["proposal_binding"]["mode"] == "explicit_v1"
    assert body["proposal_hash"] == explicit_proposal_hash(
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev",
        batch_hash="sha256:batch",
        witness_hash="sha:a",
        dex_hash_after="sha256:after",
    )


def test_build_proof_mining_claim_rejects_partial_explicit_binding() -> None:
    with pytest.raises(ValueError, match="explicit proposal binding requires"):
        build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=9),
            round_id="round-proof-7",
            reward_pool_before=20,
            base_reward=8,
            epoch=1,
            proposal_slot=0,
            prover_id=0,
            chain_id="tau-testnet-alpha",
        )


def test_validate_proof_mining_claim_rejects_fallback_binding_round_mismatch() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-8",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["proposal_binding"]["round_id"] = "other-round"
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="proposal binding round_id mismatch"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_validate_proof_mining_claim_rejects_out_of_range_bounded_model_fields() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-9",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["bounded_model"]["proposal_slot"] = 8
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="proposal_slot out of range"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_validate_proof_mining_claim_rejects_improvement_u64_overflow() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-10",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["winner"]["improvement_u64"] = 0x1_0000_0000_0000_0000
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="winner improvement out of u64 range"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_claim_cli_emits_output(tmp_path: Path) -> None:
    round_path = tmp_path / "round.json"
    out_path = tmp_path / "claim.json"
    round_path.write_text(
        json.dumps(_round_obj(improvement_u64=6), indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_solver_proof_mining_claim.py",
            "--round",
            str(round_path),
            "--output",
            str(out_path),
            "--round-id",
            "cli-round-1",
            "--reward-pool-before",
            "12",
            "--base-reward",
            "8",
            "--epoch",
            "1",
            "--proposal-slot",
            "0",
            "--prover-id",
            "0",
            "--verifier",
            "0:0",
            "--verifier",
            "1:1",
        ]
    )

    claim = json.loads(out_path.read_text(encoding="utf-8"))
    assert claim["body"]["bounded_model"]["reward_amount"] == 4
    assert claim["body"]["conditions"]["tau_gate_expected_ok"] is True


def test_claim_cli_fails_closed_when_tau_gate_would_reject(tmp_path: Path) -> None:
    round_path = tmp_path / "round.json"
    out_path = tmp_path / "claim.json"
    round_path.write_text(
        json.dumps(_round_obj(improvement_u64=6), indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    with pytest.raises(subprocess.CalledProcessError):
        subprocess.check_call(
            [
                "python3",
                "tools/permissionless_solver_proof_mining_claim.py",
                "--round",
                str(round_path),
                "--output",
                str(out_path),
                "--round-id",
                "cli-round-2",
                "--reward-pool-before",
                "3",
                "--base-reward",
                "8",
                "--epoch",
                "0",
                "--proposal-slot",
                "0",
                "--prover-id",
                "0",
                "--verifier",
                "0:0",
                "--verifier",
                "1:1",
            ]
        )
