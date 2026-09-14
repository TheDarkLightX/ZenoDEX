"""LP coverage, canonical pool identity and defensive ownership of Spot state."""

from dataclasses import replace

import pytest

from src.core.cpmm import MIN_LP_LOCK
from src.core.global_settlement_resource_limits_v2 import StateResourceLimitExceededV2
from src.core.liquidity import create_pool
from src.core.spot_swap_plan_v2 import _snapshot_pool
from src.core.spot_swap_state_v2 import (
    SpotIntentNonceV2,
    SpotLPPositionV2,
    SpotSwapStateV2,
    snapshot_spot_swap_state_v2,
)
from src.state.support_root import LP_LOCK_PUBKEY
from tests.core.test_asset_lane_coordinator_v2 import _root

ALICE = "0x" + "aa" * 48
BOB = "0x" + "bb" * 48
CAROL = "0x" + "cc" * 48
MALLORY = "0x" + "dd" * 48

def spot_state(*, fee_bps=30):
    _, pool, minted = create_pool("A", "B", 10_000, 20_000, fee_bps, BOB, 7)
    return SpotSwapStateV2(_root("spot-release"), _snapshot_pool(pool), (
        SpotLPPositionV2(LP_LOCK_PUBKEY, MIN_LP_LOCK),
        SpotLPPositionV2(BOB, minted, 7, None, 2, 7),
        SpotLPPositionV2(CAROL, 0, 2, 6, 1, 6),
    ))


def test_genesis_donor_shares_and_dormant_metadata_are_fully_committed():
    state = spot_state()
    assert sum(row.shares for row in state.lp_positions) == state.pool.lp_supply
    assert state.lp_positions[0].owner == LP_LOCK_PUBKEY
    assert state.intent_nonce(ALICE) == 0
    for name in ("shares", "last_mint_timestamp", "last_remove_timestamp", "churn_tier",
                 "last_churn_update_timestamp"):
        row = state.lp_positions[-1]
        changes = {name: 3}
        # Moving shares requires a matching LP source; metadata alone does not.
        positions = (*state.lp_positions[:-1], replace(row, **changes))
        if name == "shares":
            positions = (positions[0], replace(positions[1], shares=positions[1].shares - 3), positions[2])
        candidate = SpotSwapStateV2(state.module_release_id, state.pool, positions)
        assert candidate.state_root != state.state_root


def test_input_and_getter_mutations_cannot_reassign_owned_lp_rights_or_nonces():
    original = spot_state()
    pool, owners, nonces = original.pool, original.lp_positions, (SpotIntentNonceV2(ALICE, 1),)
    state = SpotSwapStateV2(original.module_release_id, pool, owners, nonces)
    baseline = state.state_root
    for p, positions, ns in ((pool, owners, nonces), (state.pool, state.lp_positions, state.intent_nonces)):
        object.__setattr__(p, "reserve0", 1)
        object.__setattr__(positions[1], "owner", MALLORY)
        object.__setattr__(ns[0], "last_nonce", 200)
    canonical = state.to_canonical()
    canonical["pool"]["reserve0"] = 2
    object.__setattr__(canonical["lp_positions"][1], "owner", MALLORY)
    assert state.state_root == baseline
    assert snapshot_spot_swap_state_v2(state).state_root == baseline


@pytest.mark.parametrize("defect", ["missing", "duplicate", "unordered", "sum", "lock", "identity"])
def test_invalid_ownership_is_unrepresentable(defect):
    state = spot_state()
    pool, rows = state.pool, state.lp_positions
    if defect == "missing":
        rows = rows[:1]
    elif defect == "duplicate":
        rows = (rows[0], rows[1], rows[1])
    elif defect == "unordered":
        rows = rows[::-1]
    elif defect == "sum":
        rows = (rows[0], replace(rows[1], shares=rows[1].shares + 1), rows[2])
    elif defect == "lock":
        rows = (replace(rows[0], shares=999), replace(rows[1], shares=rows[1].shares + 1), rows[2])
    else:
        pool = replace(pool, pool_id=_root("another-pool"))
    with pytest.raises(ValueError):
        SpotSwapStateV2(state.module_release_id, pool, rows)


@pytest.mark.parametrize("nonce", [0, -1, 1 << 32, True])
def test_nonce_rows_are_positive_exact_u32(nonce):
    with pytest.raises((TypeError, ValueError)):
        SpotIntentNonceV2(ALICE, nonce)


def test_capacity_is_checked_before_traversing_foreign_rows():
    state = spot_state()
    with pytest.raises(StateResourceLimitExceededV2):
        SpotSwapStateV2(state.module_release_id, state.pool, (object(),) * 4097)
    with pytest.raises(TypeError):
        SpotSwapStateV2(state.module_release_id, state.pool, (object(),))
    forged = object.__new__(SpotLPPositionV2)
    for name, value in vars_with_slots(state.lp_positions[1]).items():
        object.__setattr__(forged, name, value)
    object.__setattr__(forged, "shares", True)
    with pytest.raises(TypeError):
        SpotSwapStateV2(state.module_release_id, state.pool, (state.lp_positions[0], forged))


def vars_with_slots(value):
    return {name: getattr(value, name) for name in value.__slots__}


@pytest.mark.parametrize("field", ["_lp_positions", "_intent_nonces"])
def test_snapshot_checks_raw_capacity_before_copying_forged_backing(field):
    state = spot_state()
    object.__setattr__(state, field, (object(),) * 4097)
    with pytest.raises(StateResourceLimitExceededV2):
        snapshot_spot_swap_state_v2(state)


@pytest.mark.parametrize("owner", [ALICE[2:], ALICE.upper(), "alice", " " + ALICE])
def test_owner_aliases_cannot_create_distinct_lp_or_nonce_identities(owner):
    for constructor, amount in ((SpotLPPositionV2, 1), (SpotIntentNonceV2, 1)):
        with pytest.raises(ValueError):
            constructor(owner, amount)
