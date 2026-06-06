"""Executable BDD front door for consensus semantics.

The `.feature` file is the human-readable front door. These tests bind its
scenario ids to live code or to explicit open obligations.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import perp_np_clearinghouse as C
from src.core.perp_np_matching import E8
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
    # (replay_guard.admit), and the claim is live_equivalent -- scoped honestly to
    # that strict-sequential replay authority, not to the deployed node.
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


SCENARIOS = {
    "perps_np.deposit_collateral.core.zero_deposit_joins_account": scenario_zero_deposit_joins_account,
    "perps_np.deposit_collateral.core.deposit_does_not_consume_nonce": scenario_core_deposit_does_not_consume_nonce,
    "perps_np.deposit_collateral.core.negative_rejects_without_mutation": scenario_negative_rejects_without_mutation,
    "perps_np.deposit_collateral.guest.claim_scoped_to_live_replay_authority": scenario_claim_scoped_to_live_replay_authority,
    "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core": scenario_duplicate_tx_rejects_before_core,
}


def test_consensus_semantic_contract_lints() -> None:
    report = semantic_check.validate()

    assert report["ok"], report["errors"]
    assert report["scenario_count"] == 5
    # P0-3b CLOSED: all five scenarios are now executable; no open obligations.
    assert report["executable_scenarios"] == 5
    assert report["open_obligations"] == []


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
