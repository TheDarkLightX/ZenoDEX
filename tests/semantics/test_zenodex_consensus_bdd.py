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


def scenario_modeled_envelope_claim_is_scoped() -> None:
    report = semantic_check.validate()
    assert report["ok"], report["errors"]

    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    deposit = contract["operations"]["perps_np.deposit_collateral"]
    assert deposit["guest"]["modeled_envelope_claim_level"] == "modeled_envelope_equivalent"
    assert deposit["guest"]["live_equivalence_claim_level"] == "open_obligation"
    assert deposit["envelope"]["open_obligation_id"] == "P0-3b"

    docstring = perps_np_diff.__doc__ or ""
    assert "MODELS that envelope" in docstring
    assert "does NOT prove" in docstring
    assert "live TX replay path" in docstring
    assert "verified 1:1" not in docstring


SCENARIOS = {
    "perps_np.deposit_collateral.core.zero_deposit_joins_account": scenario_zero_deposit_joins_account,
    "perps_np.deposit_collateral.core.deposit_does_not_consume_nonce": scenario_core_deposit_does_not_consume_nonce,
    "perps_np.deposit_collateral.core.negative_rejects_without_mutation": scenario_negative_rejects_without_mutation,
    "perps_np.deposit_collateral.guest.modeled_envelope_claim_is_scoped": scenario_modeled_envelope_claim_is_scoped,
}


def test_consensus_semantic_contract_lints() -> None:
    report = semantic_check.validate()

    assert report["ok"], report["errors"]
    assert report["scenario_count"] == 5
    assert report["executable_scenarios"] == 4
    assert report["open_obligations"] == [
        "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core"
    ]


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


def test_tx_envelope_replay_binding_is_explicitly_open() -> None:
    contract = semantic_check._load_json(semantic_check.DEFAULT_CONTRACT)
    envelope = contract["operations"]["perps_np.deposit_collateral"]["envelope"]
    required = contract["bdd"]["required_scenarios"][
        "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core"
    ]

    assert envelope["live_binding_status"] == "open_obligation"
    assert envelope["open_obligation_id"] == "P0-3b"
    assert required["status"] == "open_obligation"
    assert required["layer"] == "tx_envelope"
