"""Teeth for the WS2 imperative shell: head-advance enforcement + host multiplicity.

The pure core was already adversarially tested; what must be proven HERE is the
part the core cannot enforce about itself:
  - ACCEPT applies the head-advance obligation atomically (anti-double-accept),
  - REFUSE mutates nothing (reject-is-no-op extends to the shell),
  - two racing submissions of the same valid proof yield EXACTLY ONE accept,
  - multiplicity: a withholding/corrupting host is routed around, never trusted
    harder; running out of hosts is a liveness failure, never an acceptance.
"""

from __future__ import annotations

import threading
from typing import Any, Mapping

import pytest

from src.integration.client_admission_decision import (
    ConsensusContract,
    OperationPins,
    PinnedRegistry,
    ReceiptVerifyResult,
    RefuseCode,
    RequestedOperation,
    VerifierIdentity,
    VerifyStatus,
)
from src.integration.client_admission_loop import (
    ClientAdmissionLoop,
    ClientAdmissionLoopError,
    MultiHostAdmissionClient,
)

SURFACE, OPERATION = "perps_np", "deposit_collateral"
PROOF_TYPE = "risc0.zenodex_perps_np_transition.v1"
IMAGE = (1, 2, 3, 4, 5, 6, 7, 8)
HEAD0 = b"H" * 32
POST1 = b"P" * 32
POST2 = b"Q" * 32
OP_HASH = b"O" * 32
COLLAT_H = b"C" * 32
ORACLE_H = b"R" * 32

CLAIM = "live_replay_authority_equivalent"
CLAIM_ORDER = (
    "core_equivalent",
    "modeled_envelope_equivalent",
    "live_replay_authority_equivalent",
    "live_equivalent",
)


def _journal(pre: bytes, post: bytes) -> dict[str, Any]:
    return {
        "proof_type": PROOF_TYPE,
        "risc0_image_id": list(IMAGE),
        "chain_id": "devnet",
        "pre_app_hash_present": True,
        "pre_app_hash": pre,
        "post_app_hash": post,
        "operation_hash": OP_HASH,
        "collateral_binding_hash": COLLAT_H,
        "oracle_binding_hash": ORACLE_H,
    }


class _ScriptedVerifier:
    """Returns VERIFIED with a journal derived from the submitted proof bytes:
    proof b"proof:<pre>:<post>" -> journal binding pre->post. Lets multi-step
    chains be exercised without real receipts (the real port has its own corpus
    + the opt-in real-STARK e2e)."""

    def verify_receipt(self, proof_bytes, pinned_image_id, *, blessed_verifier):
        try:
            _tag, pre_hex, post_hex = proof_bytes.decode("ascii").split(":")
            journal = _journal(bytes.fromhex(pre_hex), bytes.fromhex(post_hex))
            return ReceiptVerifyResult(status=VerifyStatus.VERIFIED, journal=journal, error=None)
        except Exception:  # noqa: BLE001 - garbage proof bytes fail closed
            return ReceiptVerifyResult(status=VerifyStatus.FAILED, journal=None, error="bad proof")


def _proof(pre: bytes, post: bytes) -> bytes:
    return f"proof:{pre.hex()}:{post.hex()}".encode("ascii")


def _rebind(_op: RequestedOperation) -> Mapping[str, bytes]:
    return {
        "operation_hash": OP_HASH,
        "collateral_binding_hash": COLLAT_H,
        "oracle_binding_hash": ORACLE_H,
    }


def _pins() -> OperationPins:
    return OperationPins(
        surface=SURFACE,
        operation=OPERATION,
        pinned_image_id=IMAGE,
        pinned_proof_type=PROOF_TYPE,
        pinned_chain_id="devnet",
        blessed_verifier=VerifierIdentity(
            expected_cmd_hash="ab" * 32, binary_path="/usr/bin/r0vm", allow_path_lookup=False
        ),
        required_journal_fields=("collateral_binding_hash", "oracle_binding_hash"),
        expected_static={},
        recomputed_fields=("collateral_binding_hash", "oracle_binding_hash"),
        cross_field_equal=(),
        head_equal_fields=(),
        claim_level=CLAIM,
        ceiling_level=CLAIM,
        admission_threshold_level=CLAIM,
        admission_proof_gated_statuses=("bound_proof_required",),
    )


def _contract() -> ConsensusContract:
    return ConsensusContract(
        claim_levels_order=CLAIM_ORDER,
        required_level_by_op={(SURFACE, OPERATION): CLAIM},
        admission_binding_status_by_op={(SURFACE, OPERATION): "bound_proof_required"},
        level_by_proof_type={PROOF_TYPE: CLAIM},
    )


def _loop(initial_head: bytes = HEAD0) -> ClientAdmissionLoop:
    return ClientAdmissionLoop(
        SURFACE,
        initial_head,
        registry=PinnedRegistry(by_op={(SURFACE, OPERATION): _pins()}),
        contract=_contract(),
        verifier_by_operation={OPERATION: _ScriptedVerifier()},
        rebind_by_operation={OPERATION: _rebind},
    )


def _fields() -> dict[str, Any]:
    return {"pubkey": "wallet-aa", "asset": "zUSD", "amount_e8": 5, "nonce": 1}


def test_accept_advances_head_and_retires_preroot() -> None:
    loop = _loop()
    decision = loop.submit(OPERATION, {"zk_proof": _proof(HEAD0, POST1)}, _fields())
    assert decision.accepted
    assert loop.current_head() == POST1
    assert HEAD0 in loop.retired_roots()


def test_same_proof_cannot_be_accepted_twice() -> None:
    loop = _loop()
    proof = {"zk_proof": _proof(HEAD0, POST1)}
    assert loop.submit(OPERATION, proof, _fields()).accepted
    replay = loop.submit(OPERATION, proof, _fields())
    assert not replay.accepted
    assert replay.refuse_code == RefuseCode.PRESTATE_MISMATCH
    assert loop.current_head() == POST1


def test_chained_proofs_advance_in_order() -> None:
    loop = _loop()
    assert loop.submit(OPERATION, {"zk_proof": _proof(HEAD0, POST1)}, _fields()).accepted
    assert loop.submit(OPERATION, {"zk_proof": _proof(POST1, POST2)}, _fields()).accepted
    assert loop.current_head() == POST2
    assert loop.retired_roots() == frozenset({HEAD0, POST1})


def test_noop_transition_refused_and_not_replayable() -> None:
    # post == pre: the core (gate 12) refuses a non-advancing transition rather
    # than accepting-then-sticking (which would let the same proof replay forever).
    loop = _loop()
    decision = loop.submit(OPERATION, {"zk_proof": _proof(HEAD0, HEAD0)}, _fields())
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.HEAD_NONPROGRESS
    assert loop.current_head() == HEAD0
    assert loop.retired_roots() == frozenset()
    # Stays refused; nothing was mutated to make a second attempt behave differently.
    again = loop.submit(OPERATION, {"zk_proof": _proof(HEAD0, HEAD0)}, _fields())
    assert not again.accepted
    assert again.refuse_code == RefuseCode.HEAD_NONPROGRESS
    assert loop.current_head() == HEAD0


def test_cycle_into_retired_root_refused() -> None:
    # H0 -> POST1 (accept), then a real proof POST1 -> H0 would move the head back
    # into the retired H0 and re-open H0's consumed proof. The shell refuses it.
    loop = _loop()
    assert loop.submit(OPERATION, {"zk_proof": _proof(HEAD0, POST1)}, _fields()).accepted
    assert loop.current_head() == POST1
    cyc = loop.submit(OPERATION, {"zk_proof": _proof(POST1, HEAD0)}, _fields())
    assert not cyc.accepted
    assert cyc.refuse_code == RefuseCode.HEAD_NONPROGRESS
    assert loop.current_head() == POST1
    assert loop.retired_roots() == frozenset({HEAD0})
    # The audit trace must carry a first-false gate for the shell refusal, not the
    # core's all-true results (otherwise a refused submission logs as all-passed).
    assert cyc.gate_results.get("g13_head_not_retired") is False
    assert any(v is False for v in cyc.gate_results.values())


def test_refuse_is_shell_noop() -> None:
    loop = _loop()
    decision = loop.submit(OPERATION, {"ok": True, "proof_status": "verified"}, _fields())
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.NO_PROOF
    assert loop.current_head() == HEAD0
    assert loop.retired_roots() == frozenset()


def test_unmapped_operation_refuses() -> None:
    loop = _loop()
    decision = loop.submit("withdraw_collateral", {"zk_proof": _proof(HEAD0, POST1)}, _fields())
    assert not decision.accepted
    assert decision.refuse_code == RefuseCode.UNMAPPED_OPERATION
    assert loop.current_head() == HEAD0


def test_concurrent_same_proof_exactly_one_accept() -> None:
    loop = _loop()
    proof = {"zk_proof": _proof(HEAD0, POST1)}
    barrier = threading.Barrier(2)
    outcomes: list[bool] = []
    lock = threading.Lock()

    def run() -> None:
        barrier.wait()
        decision = loop.submit(OPERATION, proof, _fields())
        with lock:
            outcomes.append(decision.accepted)

    threads = [threading.Thread(target=run) for _ in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert sorted(outcomes) == [False, True]
    assert loop.current_head() == POST1


def test_constructor_fails_closed() -> None:
    with pytest.raises(ClientAdmissionLoopError):
        ClientAdmissionLoop(
            "",
            HEAD0,
            registry=PinnedRegistry(by_op={}),
            contract=_contract(),
            verifier_by_operation={OPERATION: _ScriptedVerifier()},
            rebind_by_operation={OPERATION: _rebind},
        )
    with pytest.raises(ClientAdmissionLoopError):
        ClientAdmissionLoop(
            SURFACE,
            b"",
            registry=PinnedRegistry(by_op={}),
            contract=_contract(),
            verifier_by_operation={OPERATION: _ScriptedVerifier()},
            rebind_by_operation={OPERATION: _rebind},
        )
    with pytest.raises(ClientAdmissionLoopError):
        ClientAdmissionLoop(
            SURFACE,
            HEAD0,
            registry=PinnedRegistry(by_op={}),
            contract=_contract(),
            verifier_by_operation={OPERATION: _ScriptedVerifier()},
            rebind_by_operation={"other_op": _rebind},
        )


# --------------------------------------------------------------------------- #
# Multiplicity: liveness from many hosts, trust from none
# --------------------------------------------------------------------------- #
def test_multiplicity_routes_around_bad_hosts() -> None:
    loop = _loop()

    def withholding(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        raise TimeoutError("host unreachable")

    def fake_green(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        return {"ok": True, "proof_status": "verified", "production_security_claim": True}

    def honest(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        return {"zk_proof": _proof(HEAD0, POST1)}

    client = MultiHostAdmissionClient(
        loop, [("h1", withholding), ("h2", fake_green), ("h3", honest)]
    )
    outcome = client.fetch_and_admit(OPERATION, _fields(), {"op": OPERATION})
    assert outcome.accepted and outcome.served_by == "h3"
    assert [a.host_id for a in outcome.attempts] == ["h1", "h2", "h3"]
    assert outcome.attempts[0].transport_error is not None
    assert outcome.attempts[1].refuse_code == RefuseCode.NO_PROOF
    assert loop.current_head() == POST1


def test_multiplicity_never_accepts_when_all_hosts_fail() -> None:
    loop = _loop()

    def withholding(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        raise ConnectionError("down")

    def corrupting(_req: Mapping[str, Any]) -> Mapping[str, Any]:
        return {"zk_proof": b"not-a-receipt", "ok": True}

    def non_object(_req: Mapping[str, Any]):
        return "200 OK"

    client = MultiHostAdmissionClient(
        loop, [("h1", withholding), ("h2", corrupting), ("h3", non_object)]
    )
    outcome = client.fetch_and_admit(OPERATION, _fields(), {"op": OPERATION})
    assert not outcome.accepted
    assert outcome.decision is None and outcome.served_by is None
    assert len(outcome.attempts) == 3
    assert outcome.attempts[1].refuse_code == RefuseCode.RECEIPT_VERIFY_FAILED
    assert loop.current_head() == HEAD0


def test_multiplicity_constructor_fails_closed() -> None:
    loop = _loop()
    with pytest.raises(ClientAdmissionLoopError):
        MultiHostAdmissionClient(loop, [])
    with pytest.raises(ClientAdmissionLoopError):
        MultiHostAdmissionClient(
            loop, [("h1", lambda r: {}), ("h1", lambda r: {})]
        )
