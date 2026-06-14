"""Session-head pin: fork refusal needs one live head; genesis needs a quorum.

Two tiers, mirroring the policy-pin tests:

- BLS-real (skipped without py_ecc): opening a session under an actual 2-of-2
  quorum, payload cross-binding refusal, and the full lifecycle including the
  FORK case — two verified continuations of the same parent, only one of which
  can advance the head, with the archived forked lineage refused.
- BLS-independent fail-closed paths: synthetic (hash-valid) genesis records
  drive the advance/chain machinery — every boundary forgery the session
  verifier refuses must also be refused by the head pin, plus pin-record
  tamper/shape/kind discipline.
"""

from __future__ import annotations

from typing import Any, Callable, TypeVar, cast

import pytest

import src.integration.zeno_ledger_signature as sig
from src.integration.autonomous_governance_policy_pin import (
    build_genesis_policy_pin_v1,
)
from src.integration.autonomous_governance_q_policy import (
    policy_content_hash_v1,
)
from src.integration.autonomous_governance_session import (
    continue_autonomous_governance_surface_trajectory_v1,
)
from src.integration.autonomous_governance_session_pin import (
    AUTONOMOUS_GOVERNANCE_SESSION_PIN_SCHEMA_V1,
    PIN_KIND_ADVANCE,
    PIN_KIND_GENESIS,
    SESSION_OPEN_ACTION_ID_V1,
    _session_pin_body_hash,
    advance_autonomous_governance_session_v1,
    open_autonomous_governance_session_v1,
    session_genesis_payload_v1,
    session_registry_hash_v1,
    verify_session_pin_chain_v1,
)
from src.integration.autonomous_governance_trajectory import (
    run_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_governance_authority import (
    GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
    governance_action_payload_hash_v0,
)
from src.integration.zeno_key_manager_v0 import BACKEND_TAU_BLS_IMPORT, KeyBackendDescriptor
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0

ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32
SK1 = "0x" + ("01" * 32)
SK2 = "0x" + ("02" * 32)
SURROGATE = "ev\ud800il"
_TestFunc = TypeVar("_TestFunc", bound=Callable[..., Any])

_BUDGET = {"fee_bps": 50, "funding_cap_bps": 25, "buyburn_bps": 200, "reserve_bps": 200}


def _policy(policy_id: str = "session_pin_policy_a") -> dict[str, Any]:
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": policy_id,
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "selection": {
            "mode": "first_admissible",
            "anti_oscillation": {"enabled": True, "parameters": ["fee_bps"]},
            "trajectory_budget": {"enabled": True, "limits": dict(_BUDGET)},
        },
        "state_bins": {"deviation_bps": [25, 100, 300]},
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
        ],
        "q_layers": [
            {
                "id": "price_deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"hold": 3},
                    "1": {"hold": 3},
                    "2": {"raise_fee_10": 5, "hold": 1},
                    "3": {"raise_fee_10": 8, "hold": 1},
                },
            },
        ],
    }
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def _surface_state() -> dict[str, int]:
    return {
        "fee_bps": 30, "buyburn_bps": 6_000, "stakers_bps": 0,
        "reserve_bps": 2_000, "hosts_bps": 2_000, "mcr_bps": 11_000,
        "ccr_bps": 15_000, "staker_bps": 5_000, "funding_cap_bps": 120,
    }


def _steps(count: int, first_epoch: int) -> list[dict[str, Any]]:
    return [
        {
            "observation": {
                "observed_price_bps": 10_400, "target_price_bps": 10_000,
                "volatility_bps": 100, "divergence_bps": 10,
                "freshness_lag_epochs": 0, "liquidity_depth_bps": 5_000,
            },
            "current_epoch": first_epoch + index,
            "proposal_epoch": first_epoch + index - 24,
        }
        for index in range(count)
    ]


def _genesis_receipt(policy: dict[str, Any], *, steps: int = 3) -> dict[str, Any]:
    return run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_steps(steps, 100),
        expected_policy_hash=str(policy["policy_hash"]),
    )


def _continue(policy: dict[str, Any], parent: dict[str, Any], *, first_epoch: int, steps: int = 3) -> dict[str, Any]:
    receipt = continue_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        previous_receipt=parent,
        steps=_steps(steps, first_epoch),
        expected_policy_hash=str(policy["policy_hash"]),
    )
    return cast(dict[str, Any], receipt)


def _last_epoch(receipt: dict[str, Any]) -> int:
    return max(int(step["current_epoch"]) for step in receipt["input_steps"])


def _synthetic_genesis_pin(policy: dict[str, Any], receipt: dict[str, Any]) -> dict[str, Any]:
    """Hash-valid genesis record without authority (advance is BLS-free)."""

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_PIN_SCHEMA_V1,
        "kind": PIN_KIND_GENESIS,
        "policy_id": str(receipt["policy_id"]),
        "policy_hash": str(receipt["policy_hash"]),
        "policy_pin_hash": ROOT_B,
        "registry_hash": ROOT_C,
        "advance_index": 0,
        "previous_session_pin_hash": "",
        "session_genesis_pin_hash": "",
        "trajectory_hash": str(receipt["trajectory_hash"]),
        "trajectory_chain_head": str(receipt["chain_head"]),
        "session_initial_state": dict(receipt["initial_state"]),
        "segment_initial_state": dict(receipt["initial_state"]),
        "final_state": dict(receipt["final_state"]),
        "trajectory_used_final": dict(receipt["trajectory_used_final"]),
        "previous_approved_deltas_final": dict(receipt["previous_approved_deltas_final"]),
        "last_update_epoch_final": receipt["last_update_epoch_final"],
        "last_input_epoch": _last_epoch(receipt),
        "trajectory_budget": dict(receipt["trajectory_budget"]),
        "authority_receipt_hash": ROOT_B,
        "pinned_at_epoch": 20,
    }
    return {**body, "pin_hash": _session_pin_body_hash(body)}


def _registry() -> dict[str, Any]:
    registry = build_signer_registry_v0(
        registry_id="autogov-session-registry",
        payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
        threshold=2,
        signers=[
            {
                "signer_id": "alice", "key_id": "key-a",
                "public_key": sig.bls_public_key_hex_from_private_key_v0(SK1),
                "weight": 1, "status": "active",
            },
            {
                "signer_id": "bob", "key_id": "key-b",
                "public_key": sig.bls_public_key_hex_from_private_key_v0(SK2),
                "weight": 1, "status": "active",
            },
        ],
    )
    return cast(dict[str, Any], registry)


def _tau_receipt() -> dict[str, Any]:
    return {
        "schema": "zenodex/tau_policy/host_verified_receipt/v0",
        "ok": True,
        "policy_hash": ROOT_B,
        "production_security_claim": True,
    }


def _backend() -> KeyBackendDescriptor:
    return KeyBackendDescriptor(
        key_id="autogov-session-key",
        backend_kind=BACKEND_TAU_BLS_IMPORT,
        backend_id="tau-bls-import-backend",
        policy_hash=ROOT_C,
        active=True,
        no_raw_private_key_exposure=True,
        metadata={"threshold": 2, "participants": 2},
    )


def _envelopes_for(payload_hash: str) -> list[dict[str, Any]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
            payload_hash=payload_hash,
            signer_id="alice", key_id="key-a", private_key_hex=SK1,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
            payload_hash=payload_hash,
            signer_id="bob", key_id="key-b", private_key_hex=SK2,
        ),
    ]


def _policy_pin(policy: dict[str, Any], registry: dict[str, Any]) -> dict[str, Any]:
    from src.integration.autonomous_governance_policy_pin import (
        GENESIS_PREVIOUS_PIN_HASH,
        rotation_action_payload_v1,
        signer_registry_hash_v1,
    )

    payload = rotation_action_payload_v1(
        new_policy_hash=str(policy["policy_hash"]),
        previous_pin_hash=GENESIS_PREVIOUS_PIN_HASH,
        rotation_index=0,
        registry_hash=signer_registry_hash_v1(registry),
        proposal_epoch=10,
    )
    rotation = build_genesis_policy_pin_v1(
        policy=policy,
        registry=registry,
        signature_envelopes=_envelopes_for(governance_action_payload_hash_v0(payload)),
        current_epoch=20,
        proposal_epoch=10,
        min_delay_epochs=3,
        tau_policy_receipt=_tau_receipt(),
        backend_descriptors=[_backend()],
    )
    assert rotation["ok"] is True, rotation["errors"]
    return dict(rotation["pin"])


def _open_session(
    policy: dict[str, Any],
    policy_pin: dict[str, Any],
    receipt: dict[str, Any],
    registry: dict[str, Any],
    **overrides: Any,
) -> dict[str, Any]:
    payload = session_genesis_payload_v1(
        policy_hash=str(policy["policy_hash"]),
        policy_pin_hash=str(policy_pin["pin_hash"]),
        genesis_trajectory_hash=str(receipt["trajectory_hash"]),
        genesis_chain_head=str(receipt["chain_head"]),
        registry_hash=session_registry_hash_v1(registry),
        proposal_epoch=10,
    )
    kwargs: dict[str, Any] = {
        "policy": policy,
        "policy_pin": policy_pin,
        "genesis_receipt": receipt,
        "registry": registry,
        "signature_envelopes": _envelopes_for(governance_action_payload_hash_v0(payload)),
        "current_epoch": 20,
        "proposal_epoch": 10,
        "min_delay_epochs": 3,
        "tau_policy_receipt": _tau_receipt(),
        "backend_descriptors": [_backend()],
        "production_mode": True,
    }
    kwargs.update(overrides)
    return open_autonomous_governance_session_v1(**kwargs)


def _bls_test(fn: _TestFunc) -> _TestFunc:
    return cast(
        _TestFunc,
        pytest.mark.skipif(
            not sig._BLS_AVAILABLE,
            reason="py_ecc BLS dependency unavailable",
        )(fn),
    )


# --------------------------------------------------------------------------- #
# BLS-real: opening a session is an authority decision
# --------------------------------------------------------------------------- #
@_bls_test
def test_open_session_requires_and_records_real_quorum() -> None:
    policy = _policy()
    registry = _registry()
    policy_pin = _policy_pin(policy, registry)
    receipt = _genesis_receipt(policy)

    opened = _open_session(policy, policy_pin, receipt, registry)
    assert opened["ok"] is True, opened["errors"]
    pin = opened["pin"]
    assert pin["kind"] == PIN_KIND_GENESIS
    assert pin["advance_index"] == 0
    assert pin["policy_pin_hash"] == policy_pin["pin_hash"]
    assert pin["trajectory_chain_head"] == receipt["chain_head"]
    assert opened["open_payload"]["action_id"] == SESSION_OPEN_ACTION_ID_V1
    assert opened["authority_receipt"]["quorum_report"]["accepted_weight"] == 2

    chain = verify_session_pin_chain_v1([pin], policy=policy)
    assert chain["ok"] is True, chain["errors"]
    assert chain["head_pin_hash"] == pin["pin_hash"]
    assert chain["session_genesis_pin_hash"] == pin["pin_hash"]


@_bls_test
def test_open_session_refuses_non_fresh_genesis_receipt() -> None:
    policy = _policy()
    registry = _registry()
    policy_pin = _policy_pin(policy, registry)
    genesis = _genesis_receipt(policy)
    continuation = _continue(policy, genesis, first_epoch=103)
    assert continuation["ok"] is True

    opened = _open_session(policy, policy_pin, continuation, registry)
    assert opened["ok"] is False
    assert opened["pin"] == {}
    assert "session_genesis_carries_chain_head" in opened["errors"]


@_bls_test
def test_quorum_signed_for_other_genesis_cannot_open_this_one() -> None:
    policy = _policy()
    registry = _registry()
    policy_pin = _policy_pin(policy, registry)
    receipt_a = _genesis_receipt(policy, steps=3)
    receipt_b = _genesis_receipt(policy, steps=4)
    assert receipt_a["trajectory_hash"] != receipt_b["trajectory_hash"]

    payload_a = session_genesis_payload_v1(
        policy_hash=str(policy["policy_hash"]),
        policy_pin_hash=str(policy_pin["pin_hash"]),
        genesis_trajectory_hash=str(receipt_a["trajectory_hash"]),
        genesis_chain_head=str(receipt_a["chain_head"]),
        registry_hash=session_registry_hash_v1(registry),
        proposal_epoch=10,
    )
    opened = _open_session(
        policy, policy_pin, receipt_b, registry,
        signature_envelopes=_envelopes_for(governance_action_payload_hash_v0(payload_a)),
    )
    assert opened["ok"] is False
    assert "authority_rejected" in opened["errors"]
    assert any(
        str(error).startswith("authority:signature_quorum_invalid")
        for error in opened["errors"]
    )


@_bls_test
def test_open_session_refuses_policy_pin_for_other_policy() -> None:
    policy = _policy()
    other = _policy("session_pin_policy_b")
    registry = _registry()
    other_pin = _policy_pin(other, registry)
    receipt = _genesis_receipt(policy)

    opened = _open_session(policy, other_pin, receipt, registry)
    assert opened["ok"] is False
    assert "session_policy_pin_unverified" in opened["errors"]


@_bls_test
def test_lifecycle_advances_head_and_refuses_the_fork() -> None:
    policy = _policy()
    registry = _registry()
    policy_pin = _policy_pin(policy, registry)
    genesis_receipt = _genesis_receipt(policy)
    opened = _open_session(policy, policy_pin, genesis_receipt, registry)
    assert opened["ok"] is True, opened["errors"]
    head = opened["pin"]

    first = _continue(policy, genesis_receipt, first_epoch=103)
    advanced = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=first, policy=policy
    )
    assert advanced["ok"] is True, advanced["errors"]
    head_1 = advanced["pin"]
    assert head_1["kind"] == PIN_KIND_ADVANCE
    assert head_1["advance_index"] == 1
    assert head_1["previous_session_pin_hash"] == head["pin_hash"]
    assert head_1["session_genesis_pin_hash"] == head["pin_hash"]

    second = _continue(policy, first, first_epoch=106)
    advanced_2 = advance_autonomous_governance_session_v1(
        current_pin=head_1, receipt=second, policy=policy
    )
    assert advanced_2["ok"] is True, advanced_2["errors"]
    head_2 = advanced_2["pin"]

    chain = verify_session_pin_chain_v1([head, head_1, head_2], policy=policy)
    assert chain["ok"] is True, chain["errors"]
    assert chain["head_pin_hash"] == head_2["pin_hash"]
    assert chain["scope"] == "integrity_only"
    assert chain["authenticity_verified"] is False

    replayed = verify_session_pin_chain_v1(
        [head, head_1, head_2],
        policy=policy,
        receipts=[genesis_receipt, first, second],
    )
    assert replayed["ok"] is True, replayed["errors"]
    assert replayed["scope"] == "receipts_replayed"
    assert replayed["authenticity_verified"] is True

    # THE FORK: a second verified continuation of the SAME parent (different
    # steps). It verifies as a receipt, but the head has moved: it can no
    # longer advance, and an archived lineage containing both is refused.
    fork = _continue(policy, genesis_receipt, first_epoch=120)
    assert fork["ok"] is True
    forked_advance = advance_autonomous_governance_session_v1(
        current_pin=head_1, receipt=fork, policy=policy
    )
    assert forked_advance["ok"] is False
    assert "advance_chain_head_mismatch" in forked_advance["errors"]

    # Forked archive: replaying the fork as if it followed head_1 fails the
    # chain walk on segment threading (and on links if hashes are forged).
    fork_as_advance = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=fork, policy=policy
    )
    assert fork_as_advance["ok"] is True  # extends genesis: a true fork
    forked_chain = verify_session_pin_chain_v1(
        [head, head_1, fork_as_advance["pin"]], policy=policy
    )
    assert forked_chain["ok"] is False
    assert any("chain_link_mismatch" in str(error) or "advance_index_mismatch" in str(error) for error in forked_chain["errors"])


# --------------------------------------------------------------------------- #
# BLS-independent fail-closed paths
# --------------------------------------------------------------------------- #
def test_zero_envelopes_cannot_open_a_session() -> None:
    policy = _policy()
    receipt = _genesis_receipt(policy)
    opened = open_autonomous_governance_session_v1(
        policy=policy,
        policy_pin={"schema": "junk"},
        genesis_receipt=receipt,
        registry={"payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0},
        signature_envelopes=[],
        current_epoch=20,
        proposal_epoch=10,
        min_delay_epochs=3,
        tau_policy_receipt=_tau_receipt(),
        backend_descriptors=[_backend()],
        production_mode=False,
    )
    assert opened["ok"] is False
    assert opened["pin"] == {}
    assert "session_policy_pin_unverified" in opened["errors"]
    assert "authority_rejected" in opened["errors"]
    assert "authority:signature_quorum_missing" in opened["errors"]


def test_authority_evidence_inputs_are_gated_before_session_open() -> None:
    policy = _policy()
    receipt = _genesis_receipt(policy)
    surrogate_claim = {
        "claim_kind": SURROGATE,
        "evidence_hash": "0x" + "00" * 32,
        "ok": True,
    }
    cases: list[tuple[str, dict[str, Any], str]] = [
        (
            "required",
            {"required_evidence_claims": (SURROGATE,)},
            "required_evidence_claims_not_canonically_encodable",
        ),
        (
            "claim_kind",
            {"evidence_claims": (surrogate_claim,)},
            "evidence_claims_not_canonically_encodable",
        ),
    ]

    for name, overrides, expected_error in cases:
        opened = open_autonomous_governance_session_v1(
            policy=policy,
            policy_pin={"schema": "junk"},
            genesis_receipt=receipt,
            registry={"payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0},
            signature_envelopes=[],
            current_epoch=20,
            proposal_epoch=10,
            min_delay_epochs=3,
            tau_policy_receipt=_tau_receipt(),
            backend_descriptors=[_backend()],
            production_mode=False,
            **overrides,
        )
        assert opened["ok"] is False, name
        assert opened["pin"] == {}, name
        assert expected_error in opened["errors"], opened["errors"]


def test_advance_is_deterministic_and_math_gated() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)

    continuation = _continue(policy, genesis_receipt, first_epoch=103)
    first = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=continuation, policy=policy
    )
    second = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=continuation, policy=policy
    )
    assert first["ok"] is True, first["errors"]
    assert first == second
    assert first["pin"]["segment_initial_state"] == head["final_state"]
    assert first["pin"]["session_initial_state"] == head["session_initial_state"]
    assert first["pin"]["authority_receipt_hash"] == ""


def test_advance_refuses_naive_receipt_without_head_linkage() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)

    naive = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis_receipt["final_state"]),
        steps=_steps(3, 103),
        expected_policy_hash=str(policy["policy_hash"]),
    )
    result = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=naive, policy=policy
    )
    assert result["ok"] is False
    assert "advance_chain_head_mismatch" in result["errors"]
    assert "advance_carry_used_mismatch" in result["errors"]


def test_advance_refuses_linkage_without_carry() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy, steps=6)  # spends the full budget
    head = _synthetic_genesis_pin(policy, genesis_receipt)

    forged = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis_receipt["final_state"]),
        steps=_steps(6, 106),
        expected_policy_hash=str(policy["policy_hash"]),
        previous_chain_head=str(genesis_receipt["chain_head"]),
    )
    result = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=forged, policy=policy
    )
    assert result["ok"] is False
    assert "advance_carry_used_mismatch" in result["errors"]
    assert "advance_session_drift_exceeds_used:fee_bps" in result["errors"]


def test_advance_refuses_epoch_replay_and_budget_swap() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)

    replay = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis_receipt["final_state"]),
        steps=_steps(3, 100),  # reuses the genesis window
        expected_policy_hash=str(policy["policy_hash"]),
        last_update_epoch=genesis_receipt["last_update_epoch_final"],
        trajectory_used=dict(genesis_receipt["trajectory_used_final"]),
        previous_approved_deltas=dict(genesis_receipt["previous_approved_deltas_final"]),
        previous_chain_head=str(genesis_receipt["chain_head"]),
    )
    result = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=replay, policy=policy
    )
    assert result["ok"] is False
    assert "advance_epochs_not_strictly_increasing" in result["errors"]

    inflated = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis_receipt["final_state"]),
        steps=_steps(3, 103),
        expected_policy_hash=str(policy["policy_hash"]),
        last_update_epoch=genesis_receipt["last_update_epoch_final"],
        trajectory_budget={**dict(genesis_receipt["trajectory_budget"]), "fee_bps": 5_000},
        trajectory_used=dict(genesis_receipt["trajectory_used_final"]),
        previous_approved_deltas=dict(genesis_receipt["previous_approved_deltas_final"]),
        previous_chain_head=str(genesis_receipt["chain_head"]),
    )
    result = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=inflated, policy=policy
    )
    assert result["ok"] is False
    assert "advance_budget_mismatch" in result["errors"]


def test_advance_refuses_current_head_budget_above_policy_limit() -> None:
    policy = _policy()
    inflated_budget = {**dict(_BUDGET), "fee_bps": 5_000}
    genesis_receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_steps(20, 100),
        expected_policy_hash=str(policy["policy_hash"]),
        trajectory_budget=inflated_budget,
    )
    assert genesis_receipt["trajectory_used_final"]["fee_bps"] > _BUDGET["fee_bps"]
    head = _synthetic_genesis_pin(policy, genesis_receipt)
    continuation = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis_receipt["final_state"]),
        steps=_steps(2, 120),
        expected_policy_hash=str(policy["policy_hash"]),
        last_update_epoch=genesis_receipt["last_update_epoch_final"],
        trajectory_budget=inflated_budget,
        trajectory_used=dict(genesis_receipt["trajectory_used_final"]),
        previous_approved_deltas=dict(genesis_receipt["previous_approved_deltas_final"]),
        previous_chain_head=str(genesis_receipt["chain_head"]),
    )

    result = advance_autonomous_governance_session_v1(
        current_pin=head,
        receipt=continuation,
        policy=policy,
    )

    assert result["ok"] is False
    assert "current_trajectory_budget_policy_mismatch" in result["errors"]

    replayed = verify_session_pin_chain_v1(
        [head],
        policy=policy,
        receipts=[genesis_receipt],
    )
    assert replayed["ok"] is False
    assert "pin[0]_trajectory_budget_policy_mismatch" in replayed["errors"]


def test_advance_refuses_wrong_policy_and_tampered_pin() -> None:
    policy = _policy()
    other = _policy("session_pin_policy_b")
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)
    continuation = _continue(policy, genesis_receipt, first_epoch=103)

    wrong_policy = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=continuation, policy=other
    )
    assert wrong_policy["ok"] is False
    assert "advance_policy_hash_mismatch" in wrong_policy["errors"]

    tampered = dict(head)
    tampered["trajectory_used_final"] = {
        **dict(head["trajectory_used_final"]), "fee_bps": 0,
    }
    result = advance_autonomous_governance_session_v1(
        current_pin=tampered, receipt=continuation, policy=policy
    )
    assert result["ok"] is False
    assert "current_session_pin_hash_mismatch" in result["errors"]


def test_advance_refuses_structural_and_junk_receipts() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)

    structural = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=[],
        expected_policy_hash=str(policy["policy_hash"]),
    )
    for bad in (structural, None, 42, "receipt"):
        result = advance_autonomous_governance_session_v1(
            current_pin=head, receipt=bad, policy=policy
        )
        assert result["ok"] is False
        assert "advance_receipt_unverified" in result["errors"]


def test_chain_walk_refuses_gaps_splices_and_non_genesis_start() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)
    first = _continue(policy, genesis_receipt, first_epoch=103)
    advance_1 = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=first, policy=policy
    )["pin"]
    second = _continue(policy, first, first_epoch=106)
    advance_2 = advance_autonomous_governance_session_v1(
        current_pin=advance_1, receipt=second, policy=policy
    )["pin"]

    assert verify_session_pin_chain_v1([head, advance_1, advance_2])["ok"] is True

    assert verify_session_pin_chain_v1([])["ok"] is False
    assert verify_session_pin_chain_v1("nope")["ok"] is False

    gap = verify_session_pin_chain_v1([head, advance_2])
    assert gap["ok"] is False
    assert any("advance_index_mismatch" in str(error) for error in gap["errors"])

    headless = verify_session_pin_chain_v1([advance_1, advance_2])
    assert headless["ok"] is False
    assert any("session_chain_must_start_at_genesis" in str(error) for error in headless["errors"])

    # Cross-session splice: an advance from a DIFFERENT session lineage.
    other_genesis_receipt = _genesis_receipt(policy, steps=4)
    other_head = _synthetic_genesis_pin(policy, other_genesis_receipt)
    other_first = _continue(policy, other_genesis_receipt, first_epoch=110)
    other_advance = advance_autonomous_governance_session_v1(
        current_pin=other_head, receipt=other_first, policy=policy
    )["pin"]
    spliced = verify_session_pin_chain_v1([head, other_advance])
    assert spliced["ok"] is False
    assert any(
        "chain_link_mismatch" in str(error) or "session_anchor_mismatch" in str(error)
        for error in spliced["errors"]
    )

    bound = verify_session_pin_chain_v1([head, advance_1], policy=_policy("session_pin_policy_b"))
    assert bound["ok"] is False
    assert any("session_policy_hash_mismatch" in str(error) for error in bound["errors"])


def test_pin_kind_discipline_is_enforced() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)

    unauthorized = dict(head)
    unauthorized.pop("pin_hash")
    unauthorized["authority_receipt_hash"] = ""
    unauthorized = {**unauthorized, "pin_hash": _session_pin_body_hash(unauthorized)}
    result = advance_autonomous_governance_session_v1(
        current_pin=unauthorized,
        receipt=_continue(policy, genesis_receipt, first_epoch=103),
        policy=policy,
    )
    assert result["ok"] is False
    assert "current_session_pin_genesis_requires_authority_receipt" in result["errors"]

    first = _continue(policy, genesis_receipt, first_epoch=103)
    advance_1 = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=first, policy=policy
    )["pin"]
    claiming = dict(advance_1)
    claiming.pop("pin_hash")
    claiming["authority_receipt_hash"] = ROOT_B
    claiming = {**claiming, "pin_hash": _session_pin_body_hash(claiming)}
    chain = verify_session_pin_chain_v1([head, claiming])
    assert chain["ok"] is False
    assert any(
        "session_pin_advance_must_not_claim_authority" in str(error)
        for error in chain["errors"]
    )


def test_forged_lineage_passes_integrity_only_but_fails_receipt_replay() -> None:
    """The Codex r1 P1 case: pin records are self-hashed summaries, so an
    internally consistent lineage can be forged wholesale. The integrity-only
    scope must say so about itself, and the receipts-replayed scope must
    refuse the forgery."""

    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)
    first = _continue(policy, genesis_receipt, first_epoch=103)
    advance_1 = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=first, policy=policy
    )["pin"]
    second = _continue(policy, first, first_epoch=106)
    advance_2 = advance_autonomous_governance_session_v1(
        current_pin=advance_1, receipt=second, policy=policy
    )["pin"]

    # Forge the head move: keep every summary field coherent but invent the
    # trajectory that supposedly produced it. No verified continuation exists.
    forged = dict(advance_2)
    forged.pop("pin_hash")
    forged["trajectory_hash"] = ROOT_B
    forged["trajectory_chain_head"] = ROOT_C
    forged = {**forged, "pin_hash": _session_pin_body_hash(forged)}

    integrity = verify_session_pin_chain_v1([head, advance_1, forged], policy=policy)
    assert integrity["ok"] is True  # internally consistent: the forgery "passes"
    assert integrity["scope"] == "integrity_only"
    assert integrity["authenticity_verified"] is False  # ...and says so

    replayed = verify_session_pin_chain_v1(
        [head, advance_1, forged],
        policy=policy,
        receipts=[genesis_receipt, first, second],
    )
    assert replayed["ok"] is False
    assert replayed["authenticity_verified"] is False
    assert any(
        "pin_receipt_binding_mismatch:trajectory_hash" in str(error)
        for error in replayed["errors"]
    )


def test_receipt_replay_mode_is_fail_closed_about_its_inputs() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)
    first = _continue(policy, genesis_receipt, first_epoch=103)
    advance_1 = advance_autonomous_governance_session_v1(
        current_pin=head, receipt=first, policy=policy
    )["pin"]

    missing_policy = verify_session_pin_chain_v1(
        [head, advance_1], receipts=[genesis_receipt, first]
    )
    assert missing_policy["ok"] is False
    assert "session_pin_chain_policy_required_for_replay" in missing_policy["errors"]

    count = verify_session_pin_chain_v1(
        [head, advance_1], policy=policy, receipts=[genesis_receipt]
    )
    assert count["ok"] is False
    assert any(
        "session_pin_chain_receipt_count_mismatch" in str(error)
        for error in count["errors"]
    )

    swapped = verify_session_pin_chain_v1(
        [head, advance_1], policy=policy, receipts=[first, genesis_receipt]
    )
    assert swapped["ok"] is False
    assert any("pin_receipt_binding_mismatch" in str(error) for error in swapped["errors"])

    tampered_receipt = dict(first)
    tampered_receipt["final_state"] = {
        **dict(first["final_state"]),
        "fee_bps": int(first["final_state"]["fee_bps"]) + 10,
    }
    tampered = verify_session_pin_chain_v1(
        [head, advance_1], policy=policy, receipts=[genesis_receipt, tampered_receipt]
    )
    assert tampered["ok"] is False
    assert any(
        "session_pin_receipt_unverified" in str(error) for error in tampered["errors"]
    )


def test_session_genesis_pin_hash_threads_through_long_chains() -> None:
    policy = _policy()
    genesis_receipt = _genesis_receipt(policy)
    head = _synthetic_genesis_pin(policy, genesis_receipt)
    chain = [head]
    receipt = genesis_receipt
    for index in range(3):
        receipt = _continue(policy, receipt, first_epoch=103 + 3 * index)
        advanced = advance_autonomous_governance_session_v1(
            current_pin=chain[-1], receipt=receipt, policy=policy
        )
        assert advanced["ok"] is True, advanced["errors"]
        chain.append(advanced["pin"])
        assert advanced["pin"]["session_genesis_pin_hash"] == head["pin_hash"]

    verification = verify_session_pin_chain_v1(chain, policy=policy)
    assert verification["ok"] is True, verification["errors"]
    assert verification["session_genesis_pin_hash"] == head["pin_hash"]
    assert verification["length"] == 4
