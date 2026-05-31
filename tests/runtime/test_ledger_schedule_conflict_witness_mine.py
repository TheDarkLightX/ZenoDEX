"""Symbolic disaster-witness mines for two more unowned ZenoLedger safety surfaces.

Both modules had only example-based tests. These use `hypothesis` to search for
disaster witnesses across thousands of generated inputs; a clean run is a bounded
NEGATIVE receipt.

A. validator_schedule (`build_proposer_duty_v0`) — weighted round-robin proposer
   selection. Disaster classes mined:
     - non-determinism            (same set+height -> different proposer)
     - out-of-set / revoked proposer
     - proportional unfairness    (over one full cycle, an active validator is
       NOT selected exactly voting_power times -> censorship / over-weight)

B. conflict_graph (`transactions_conflict_v0` / `build_conflict_graph_v0`) — the
   parallel-execution conflict relation. Disaster class = UNDER-CONFLICT: two txs
   that share state are scheduled into different components and executed in
   parallel (double-spend / nondeterministic state). Mined invariants:
     - global-cell wildcard: a tx with unknown state access conflicts with ALL
     - symmetry of the conflict relation
     - graph edge present  <=>  pairwise relation true   (completeness)
     - component separation: txs in different components do NOT conflict
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_conflict_graph_v0 as cg  # noqa: E402
from src.integration import zeno_ledger_validator_schedule_v0 as vs  # noqa: E402

PK = lambda i: "0x" + f"{i:096x}"  # noqa: E731


# ============================ A. validator_schedule ============================

# (active?, voting_power 1..4); identity i fixed by position; <=5 validators.
_validators = st.lists(
    st.tuples(st.booleans(), st.integers(min_value=1, max_value=4)),
    min_size=1,
    max_size=5,
)


@settings(max_examples=1500)
@given(specs=_validators)
def test_proposer_schedule_has_no_selection_witness(specs):
    active = [(i, w) for i, (a, w) in enumerate(specs) if a]
    if not active:
        return  # build rejects a set with no active validator
    start_height = 1000
    validators = [
        {
            "validator_id": f"val-{i}",
            "key_id": f"key-{i}",
            "public_key": PK(i + 1),
            "voting_power": w,
            "status": "active" if a else "revoked",
        }
        for i, (a, w) in enumerate(specs)
    ]
    vset = vs.build_validator_set_v0(
        chain_id="chain-1", epoch=0, start_height=start_height, validators=validators
    )
    active_ids = {(f"val-{i}", f"key-{i}") for i, _w in active}
    expected_power = {(f"val-{i}", f"key-{i}"): w for i, w in active}
    cycle_len = vset["active_slot_count"]  # == sum of active voting_power

    counts: dict[tuple[str, str], int] = {}
    for h in range(start_height, start_height + cycle_len):
        duty = vs.build_proposer_duty_v0(validator_set=vset, height=h)
        p = (duty["proposer"]["validator_id"], duty["proposer"]["key_id"])
        # (1) proposer is an ACTIVE, registered validator — never revoked/out-of-set
        assert p in active_ids, f"out-of-set/revoked proposer {p} at height {h}"
        # (2) determinism: recompute -> identical duty certificate
        duty2 = vs.build_proposer_duty_v0(validator_set=vset, height=h)
        assert duty2["duty_hash"] == duty["duty_hash"]
        counts[p] = counts.get(p, 0) + 1

    # (3) proportional fairness: over one full cycle each active validator is the
    # proposer EXACTLY voting_power times (no censorship, no over-representation).
    assert counts == expected_power, (
        f"unfair schedule over cycle: got {counts} expected {expected_power}"
    )


def test_proposer_schedule_rejects_height_before_start():
    vset = vs.build_validator_set_v0(
        chain_id="c",
        epoch=0,
        start_height=10,
        validators=[{"validator_id": "v", "key_id": "k", "public_key": PK(1), "voting_power": 1}],
    )
    with pytest.raises(ValueError, match="precedes validator set start_height"):
        vs.build_proposer_duty_v0(validator_set=vset, height=9)


# ============================== B. conflict_graph ==============================

# A tiny tx vocabulary that produces overlapping touched-cell sets so the conflict
# relation is genuinely exercised (faucet shares the faucet cell; specific
# balance cells overlap on (to,asset); GLOBAL is the wildcard case).
_PUB = [PK(1), PK(2)]
_ASSET = ["0x" + "aa" * 32, "0x" + "bb" * 32]


def _faucet(to, asset):
    return {"kind": "ZENODEX_TESTNET_FAUCET", "to_pubkey": to, "asset": asset}


def _global_tx():
    # An unknown-kind operation-bearing tx -> maps to the GLOBAL_DEX_CELL wildcard.
    return {"kind": "ZENODEX_OP", "operations": {"ops": [{"kind": "MYSTERY"}]}}


_tx = st.one_of(
    st.builds(_faucet, st.sampled_from(_PUB), st.sampled_from(_ASSET)),
    st.just(_global_tx()),
    st.just({"kind": "ZENODEX_TESTNET_TOKEN_CREATE", "symbol": "AAA", "asset": _ASSET[0]}),
)


def test_conflict_graph_mine_is_non_vacuous():
    """Teeth: prove the two real branches the mine relies on actually fire — a
    global-cell tx DOES conflict with a specific-cell tx (wildcard branch), and
    two disjoint txs land in DIFFERENT components (cross-component branch). If
    these were unreachable, the negative receipt above would be vacuous."""
    g, faucet = _global_tx(), _faucet(_PUB[0], _ASSET[0])
    assert cg.GLOBAL_DEX_CELL_V0 in cg.touched_cells_for_transaction_v0(g)
    assert cg.transactions_conflict_v0(g, faucet)  # wildcard branch is live

    token = {"kind": "ZENODEX_TESTNET_TOKEN_CREATE", "symbol": "AAA", "asset": _ASSET[0]}
    assert not cg.transactions_conflict_v0(faucet, token)  # disjoint -> no conflict
    graph = cg.build_conflict_graph_v0([faucet, token])
    comp = {i: c["component_id"] for c in graph["components"] for i in c["transaction_indices"]}
    assert comp[0] != comp[1]  # cross-component branch is live


@settings(max_examples=1500)
@given(txs=st.lists(_tx, min_size=1, max_size=6))
def test_conflict_graph_has_no_underconflict_witness(txs):
    graph = cg.build_conflict_graph_v0(list(txs))
    n = len(txs)

    # (1) symmetry + (2) global-cell wildcard, over every ordered pair
    for i in range(n):
        ci = cg.touched_cells_for_transaction_v0(txs[i])
        for j in range(n):
            cij = cg.transactions_conflict_v0(txs[i], txs[j])
            assert cij == cg.transactions_conflict_v0(txs[j], txs[i]), "asymmetric conflict"
            if i != j and cg.GLOBAL_DEX_CELL_V0 in ci:
                assert cij, f"global-cell tx {i} did NOT conflict with {j} (under-conflict)"

    # (3) graph edge present  <=>  pairwise relation true (edge completeness)
    edge_pairs = {(e["left_index"], e["right_index"]) for e in graph["edges"]}
    for i in range(n):
        for j in range(i + 1, n):
            rel = cg.transactions_conflict_v0(txs[i], txs[j])
            assert ((i, j) in edge_pairs) == rel, f"edge/relation mismatch at ({i},{j})"

    # (4) component separation: txs in DIFFERENT components must NOT conflict
    comp_of: dict[int, int] = {}
    for comp in graph["components"]:
        for idx in comp["transaction_indices"]:
            comp_of[idx] = comp["component_id"]
    for i in range(n):
        for j in range(i + 1, n):
            if comp_of[i] != comp_of[j]:
                assert not cg.transactions_conflict_v0(txs[i], txs[j]), (
                    f"UNDER-CONFLICT: txs {i},{j} conflict but are in different components"
                )
