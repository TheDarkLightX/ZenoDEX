"""One canonical pool identity across creation, state, and scheduling surfaces."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

from src.core.dex import DexState
from src.core.intent_access import access_for_intent, intents_conflict
from src.core.liquidity import create_pool
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.zeno_ledger_conflict_graph_v0 import build_conflict_graph_v0
from src.state.balances import BalanceTable
from src.state.intents import CreatePoolIntent, Intent, IntentKind, SwapIntent
from src.state.lp import LPTable
from src.state.state_root import compute_state_root

_FIXTURE_PATH = Path(__file__).resolve().parents[1] / "fixtures" / "pool_identity_conformance_v1.json"


@pytest.fixture(scope="module")
def conformance_fixture() -> dict[str, Any]:
    value = json.loads(_FIXTURE_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    assert value["schema"] == "zenodex.pool_identity_conformance.v1"
    return value


def _intent_from_spec(spec: dict[str, Any]) -> Intent:
    kind = IntentKind(spec["kind"])
    intent_type = CreatePoolIntent if kind is IntentKind.CREATE_POOL else SwapIntent
    return intent_type(
        module=spec["module"],
        version=spec["version"],
        kind=kind,
        intent_id=spec["intent_id"],
        sender_pubkey=spec["sender_pubkey"],
        deadline=spec["deadline"],
        fields=copy.deepcopy(spec["fields"]),
    )


def _sorted_access_keys(keys: set[tuple[str, str, str]]) -> list[list[str]]:
    return [list(key) for key in sorted(keys)]


def _ledger_transaction(intent_spec: dict[str, Any]) -> dict[str, Any]:
    wire_intent = {
        "kind": intent_spec["kind"],
        "sender_pubkey": intent_spec["sender_pubkey"],
        **copy.deepcopy(intent_spec["fields"]),
    }
    return {"kind": "ZENODEX_BATCH", "operations": {"dex": [wire_intent]}}


def test_parameter_bound_identity_matches_pool_creation_and_strict_snapshot(
    conformance_fixture: dict[str, Any],
) -> None:
    identity = conformance_fixture["pool_identity"]
    creation = conformance_fixture["creation"]
    pool_id, pool, lp_minted = create_pool(
        identity["asset0"],
        identity["asset1"],
        creation["amount0"],
        creation["amount1"],
        identity["fee_bps"],
        creation["creator_pubkey"],
        created_at=creation["created_at"],
        curve_tag=identity["curve_tag"],
        curve_params=identity["curve_params"],
    )

    assert pool_id == identity["pool_id"]
    assert pool.pool_id == identity["pool_id"]
    assert lp_minted == creation["expected_lp_minted"]
    assert pool.lp_supply == creation["expected_lp_supply"]

    created_state = DexState(
        balances=BalanceTable(),
        pools={pool_id: pool},
        lp_balances=LPTable(),
    )
    assert snapshot_from_state(created_state).data == conformance_fixture["dex_snapshot_v4"]

    restored = state_from_snapshot(conformance_fixture["dex_snapshot_v4"])
    assert restored.pools[pool_id] == pool
    assert snapshot_from_state(restored).data == conformance_fixture["dex_snapshot_v4"]
    assert (
        compute_state_root(
            balances=restored.balances,
            pools=restored.pools,
            lp_balances=restored.lp_balances,
            nonces=restored.nonces,
            fee_accumulator=restored.fee_accumulator,
        )
        == conformance_fixture["expected"]["state_root_v5"]
    )


def test_pool_parameter_mutation_rejects_before_snapshot_authority(
    conformance_fixture: dict[str, Any],
) -> None:
    mutated = copy.deepcopy(conformance_fixture["dex_snapshot_v4"])
    mutated["pools"][0]["fee_bps"] += 1

    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        state_from_snapshot(mutated)


def test_symbolic_compatibility_is_explicit_and_cannot_enter_state_root_authority(
    conformance_fixture: dict[str, Any],
) -> None:
    claim_boundary = conformance_fixture["claim_boundary"]
    assert claim_boundary["symbolic_pool_id_compatibility"] == "local_test_only_non_authoritative"
    assert claim_boundary["settlement_authority"] is False
    assert claim_boundary["risc0_proof_generated"] is False

    symbolic = copy.deepcopy(conformance_fixture["dex_snapshot_v4"])
    symbolic["pools"][0]["pool_id"] = "local-pool-a"
    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        state_from_snapshot(symbolic)

    restored = state_from_snapshot(symbolic, allow_symbolic_pool_ids=True)
    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        compute_state_root(
            balances=restored.balances,
            pools=restored.pools,
            lp_balances=restored.lp_balances,
            nonces=restored.nonces,
            fee_accumulator=restored.fee_accumulator,
        )


def test_parameter_bound_identity_is_shared_by_intent_access_and_conflict_graph(
    conformance_fixture: dict[str, Any],
) -> None:
    restored = state_from_snapshot(conformance_fixture["dex_snapshot_v4"])
    identity = conformance_fixture["pool_identity"]
    intent_specs = conformance_fixture["intents"]
    create_intent = _intent_from_spec(intent_specs["create_pool"])
    swap_intent = _intent_from_spec(intent_specs["swap_exact_in"])
    created_pools = {identity["pool_id"]: (identity["asset0"], identity["asset1"])}

    create_access = access_for_intent(
        create_intent,
        pools=restored.pools,
        created_pools=created_pools,
    )
    swap_access = access_for_intent(
        swap_intent,
        pools=restored.pools,
        created_pools=created_pools,
    )
    expected_access = conformance_fixture["expected"]["intent_access"]
    assert _sorted_access_keys(create_access.reads) == expected_access["create_pool"]["reads"]
    assert _sorted_access_keys(create_access.writes) == expected_access["create_pool"]["writes"]
    assert _sorted_access_keys(swap_access.reads) == expected_access["swap_exact_in"]["reads"]
    assert _sorted_access_keys(swap_access.writes) == expected_access["swap_exact_in"]["writes"]
    assert intents_conflict(create_access, swap_access)

    transactions = [
        _ledger_transaction(intent_specs["create_pool"]),
        _ledger_transaction(intent_specs["swap_exact_in"]),
    ]
    assert build_conflict_graph_v0(transactions) == conformance_fixture["expected"][
        "conflict_graph_v0"
    ]
