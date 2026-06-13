"""Executable BDD front door for consensus semantics.

The `.feature` file is the human-readable front door. These tests bind its
scenario ids to live code or to explicit open obligations.
"""

from __future__ import annotations

import json
from copy import deepcopy
from dataclasses import replace
from pathlib import Path

import pytest

from src.core import perp_np_clearinghouse as C
from src.core.perp_np_matching import E8
from src.integration import orderbook_api
from tools.runtime import perps_np_guest_differential as perps_np_diff
from tools.semantics import check_consensus_semantic_contract as semantic_check

ALICE = "0x" + "11" * 48


def _account(state: C.MarketState, pubkey: str = ALICE) -> C.Account:
    account = state.by_pubkey().get(pubkey)
    assert account is not None
    return account


def _state_with_account_nonce(nonce: int) -> C.MarketState:
    state = C.deposit(C.init_market(100 * E8), ALICE, 0)
    accts = state.by_pubkey()
    accts[ALICE] = replace(accts[ALICE], nonce=nonce)
    return state.with_accounts(accts)


def scenario_zero_deposit_joins_account() -> None:
    state = C.init_market(100 * E8)

    post = C.deposit(state, ALICE, 0)

    account = _account(post)
    assert account.collateral_e8 == 0
    assert account.nonce == 0
    assert post.net_deposited_e8 == state.net_deposited_e8


def scenario_core_deposit_does_not_consume_nonce() -> None:
    state = _state_with_account_nonce(7)

    post = C.deposit(state, ALICE, 100)

    account = _account(post)
    assert account.collateral_e8 == 100
    assert account.nonce == 7


def scenario_negative_rejects_without_mutation() -> None:
    state = C.deposit(C.init_market(100 * E8), ALICE, 25)

    with pytest.raises(ValueError, match="deposit must be non-negative"):
        C.deposit(state, ALICE, -1)

    assert state == C.deposit(C.init_market(100 * E8), ALICE, 25)


def scenario_claim_scoped_to_live_replay_authority() -> None:
    # P0-3b CLOSED: the guest envelope is bound to the live replay authority
    # (replay_guard.admit), and the claim is live_replay_authority_equivalent --
    # scoped to that strict-sequential replay authority/model, NOT the deployed node.
    report = semantic_check.validate()
    assert report["ok"], report["errors"]

    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    deposit = contract["operations"]["perps_np.deposit_collateral"]
    assert deposit["guest"]["envelope_binding"] == "live_replay_guard_admit_strict_sequential"
    assert deposit["guest"]["live_equivalence_claim_level"] == "live_replay_authority_equivalent"
    assert deposit["envelope"]["live_binding_status"] == "bound_to_replay_guard"
    assert deposit["envelope"]["chain_replay_layer"]["enforced_at"] == "tau_node_tx_sequence"

    docstring = perps_np_diff.__doc__ or ""
    # honest scoping tokens -- must match the contract overclaim_guards required_tokens
    assert "replay_guard" in docstring
    assert "strict-sequential" in docstring
    assert "chain tx_sequence" in docstring
    # must not overclaim: bound to the replay authority/model, not the deployed node
    assert "verified 1:1" not in docstring
    assert "production 1:1" not in docstring
    assert "live_equivalent" not in docstring


def scenario_duplicate_tx_rejects_before_core() -> None:
    # Drive the LIVE replay authority replay_guard.admit (the strict-sequential
    # policy the chain enforces via tx_sequence). A duplicate OR gap nonce is
    # rejected by the admission gate -- which, in the composed flow, runs BEFORE
    # the core deposit, so the core never executes on a replay.
    from src.core import replay_guard as rg

    accepted = rg.admit(state=rg.ReplayGuardState(), sender=ALICE, nonce=1)
    assert isinstance(accepted, rg.AdmitAccepted)
    after_one = accepted.state

    duplicate = rg.admit(state=after_one, sender=ALICE, nonce=1)
    assert isinstance(duplicate, rg.AdmitRejected) and duplicate.reason == "duplicate_nonce"

    gap = rg.admit(state=after_one, sender=ALICE, nonce=3)
    assert isinstance(gap, rg.AdmitRejected) and gap.reason == "nonce_gap"

    # The rejected admits did not advance state: the correct next nonce still admits.
    next_ok = rg.admit(state=after_one, sender=ALICE, nonce=2)
    assert isinstance(next_ok, rg.AdmitAccepted)


def scenario_clob_guest_claim_scoped_to_matching_core() -> None:
    # REVIEW(Codex 2026-06-07, grade A after fix): the CLOB guest now proves the
    # matching/book-root kernel, but the deployed Stage-0 API still calls
    # apply_order directly and labels responses proof_pending. This scenario keeps
    # that claim at core_equivalent until the live API admission path invokes and
    # requires the proof.
    report = semantic_check.validate()
    assert report["ok"], report["errors"]

    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    op = contract["operations"]["clob.place_limit_order"]
    assert op["core"]["live_authority_ref"] == "src/core/clob_matching.py::apply_order"
    assert op["guest"]["proof_type"] == "risc0.zenodex_clob_transition.v1"
    assert op["guest"]["live_equivalence_claim_level"] == "core_equivalent"
    assert op["guest"]["strongest_allowed_claim"] == "core_equivalent"
    assert (
        op["guest"]["deployed_api_admission_binding_status"]
        == "not_bound_stage0_api_does_not_invoke_guest"
    )
    assert op["api"]["proof_invocation"] == "none_stage0"

    store = orderbook_api.new_demo_store()
    status, policy = orderbook_api.handle_orderbook_request(
        "GET", "/api/orderbook/proof-policy", None, store=store
    )
    assert status == 200
    assert policy["proof_mode"] == "pending"
    assert policy["accepted_verifier_ids"] == []
    assert policy["latest_proven_height"] is None

    order_req = {
        "market_id": "ZENO-USD",
        "client_order_id": "semantic-clob-1",
        "side": "BUY",
        "order_type": "limit",
        "price": "1000",
        "quantity": "5",
        "time_in_force": "GTC",
        "expires_at": 0,
        "nonce": 1,
        "deadline": 0,
        "agent_key_id": "0x" + "ab" * 48,
        "signature": "0x" + "ff" * 8,
    }
    status, resp = orderbook_api.handle_orderbook_request(
        "POST",
        "/api/orderbook/orders",
        json.dumps(order_req).encode("utf-8"),
        store=store,
    )
    assert status == 201, resp
    assert resp["order"]["status"] == "executed"
    assert resp["order"]["proof_status"] == "proof_pending"
    assert resp["order"]["latest_proven_height"] is None

    source = Path(orderbook_api.__file__).read_text(encoding="utf-8")
    assert "apply_order(book, built.order)" in source
    assert "execute_clob_transition_v1" not in source
    assert "ProofStatus.PROOF_VERIFIED.value" not in source


SCENARIOS = {
    "clob.place_limit_order.guest.claim_scoped_to_matching_core": scenario_clob_guest_claim_scoped_to_matching_core,
    "perps_np.deposit_collateral.core.zero_deposit_joins_account": scenario_zero_deposit_joins_account,
    "perps_np.deposit_collateral.core.deposit_does_not_consume_nonce": scenario_core_deposit_does_not_consume_nonce,
    "perps_np.deposit_collateral.core.negative_rejects_without_mutation": scenario_negative_rejects_without_mutation,
    "perps_np.deposit_collateral.guest.claim_scoped_to_live_replay_authority": scenario_claim_scoped_to_live_replay_authority,
    "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core": scenario_duplicate_tx_rejects_before_core,
}


def test_consensus_semantic_contract_lints() -> None:
    report = semantic_check.validate()

    assert report["ok"], report["errors"]
    assert report["scenario_count"] == 6
    # P0-3b plus the CLOB core-proof scope are executable; no open obligations.
    assert report["executable_scenarios"] == 6
    assert report["open_obligations"] == []


def test_scoped_replay_claim_level_is_required_by_shape_gate() -> None:
    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    mutated = deepcopy(contract)
    mutated["claim_levels"].pop("live_replay_authority_equivalent")

    errors = semantic_check._validate_contract_shape(mutated)

    # REVIEW(Codex 2026-06-07, grade A after fix): P0-3b introduced this scoped
    # claim level to avoid overstating replay-authority equivalence as full live
    # node equivalence. The shape gate must fail if the vocabulary is removed,
    # otherwise operation metadata can cite an undefined claim and still lint.
    assert "claim_levels missing live_replay_authority_equivalent" in errors


def test_clob_guest_live_equivalent_overclaim_is_rejected() -> None:
    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    mutated = deepcopy(contract)
    mutated["operations"]["clob.place_limit_order"]["guest"][
        "live_equivalence_claim_level"
    ] = "live_equivalent"
    mutated["operations"]["clob.place_limit_order"]["guest"][
        "strongest_allowed_claim"
    ] = "live_equivalent"

    errors = semantic_check._validate_clob_contract(mutated)

    # REVIEW(Codex 2026-06-07, grade A after fix): the deployed orderbook API is
    # Stage-0 and proof-pending, so the CLOB guest cannot be promoted to a
    # live-equivalent admission claim by editing JSON alone.
    assert "CLOB guest live_equivalence_claim_level must be core_equivalent" in errors
    assert "CLOB guest strongest_allowed_claim must be core_equivalent" in errors


@pytest.mark.parametrize("scenario_id", sorted(SCENARIOS))
def test_executable_bdd_scenarios(scenario_id: str) -> None:
    SCENARIOS[scenario_id]()


def test_every_executable_feature_scenario_has_a_pytest_binding() -> None:
    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    required = contract["bdd"]["required_scenarios"]
    executable = {
        scenario_id
        for scenario_id, meta in required.items()
        if meta["status"] == "executable"
    }

    assert executable == set(SCENARIOS)


def test_tx_envelope_replay_binding_is_closed_and_bound() -> None:
    # P0-3b CLOSED: the tx-envelope replay obligation is bound to the live replay
    # authority, and the chain_replay_layer records where production replay lives.
    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    envelope = contract["operations"]["perps_np.deposit_collateral"]["envelope"]
    required = contract["bdd"]["required_scenarios"][
        "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core"
    ]

    assert envelope["live_binding_status"] == "bound_to_replay_guard"
    assert envelope["closed_obligation_id"] == "P0-3b"
    assert envelope["chain_replay_layer"]["python_authority_model"] == "src/core/replay_guard.py::admit"
    assert required["status"] == "executable"
    assert required["layer"] == "tx_envelope"
