from __future__ import annotations

import re
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from src.core.global_economic_lifecycle_plan_v2 import (
    derive_global_oracle_occurrence_plan_v2,
    derive_global_terminal_obligation_plan_v2,
)
from src.core.global_economic_state_v2 import (
    MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2,
    MAX_GLOBAL_ORACLE_ROWS_V2,
    MAX_GLOBAL_OUTBOX_ROWS_V2,
    MAX_GLOBAL_REPLAY_ROWS_V2,
    MAX_GLOBAL_SUPPLY_ROWS_V2,
    MAX_GLOBAL_TERMINAL_ROWS_V2,
    GlobalEconomicStateRootV2,
    GlobalEconomicStateV2,
    LaneStateRootV2,
    OutboxStateV2,
    OutboxStatusV2,
    ReplayStateV2,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    OracleOccurrenceStateV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
)


def _root(n: int) -> str:
    return f"0x{n:064x}"


def _lane_roots() -> tuple[LaneStateRootV2, ...]:
    return tuple(
        LaneStateRootV2(
            lane_id=lane_id,
            module_release_id=_root(index + 1),
            enabled=lane_id is LaneIdV2.ASSET_TRANSFER,
            state_root=_root(index + 101),
        )
        for index, lane_id in enumerate(ALL_LANE_IDS_V2)
    )


def _state(**overrides: object) -> GlobalEconomicStateV2:
    values: dict[str, object] = {
        "chain_id": "chain:test",
        "deployment_root": _root(201),
        "writer_epoch": 3,
        "height": 7,
        "profile_root": _root(202),
        "lane_roots": _lane_roots(),
        "balances": (
            EconomicAmountV2("alice", "asset:usd", "zenoledger:accounts", 7),
        ),
        "supplies": (AssetSupplyV2("asset:usd", 10),),
        "custody": (
            EconomicAmountV2("pool:one", "asset:usd", "zenoledger:pools", 2),
        ),
        "liabilities": (
            EconomicAmountV2("alice", "asset:usd", "zenoledger:claims", 1),
        ),
        "reserves": (
            EconomicAmountV2("reserve:fees", "asset:usd", "zenoledger:reserves", 1),
        ),
        "oracle_occurrences": (),
        "replay_state": (),
        "terminal_obligations": (),
        "history_root": ZERO_ROOT_V2,
        "outbox": (),
    }
    values.update(overrides)
    return GlobalEconomicStateV2(**values)


def _obligation(
    amount: int,
    status: TerminalObligationStatusV2 = TerminalObligationStatusV2.OPEN,
) -> TerminalObligationV2:
    return TerminalObligationV2(
        obligation_id="obligation:one",
        lane_id=LaneIdV2.PERPS_MARKET,
        claimant="alice",
        asset="asset:usd",
        liability_domain="zenoledger:claims",
        amount_atoms=amount,
        status=status,
    )


def test_global_state_commits_all_twelve_lanes_and_exact_economic_totals() -> None:
    state = _state()

    assert tuple(row.lane_id for row in state.lane_roots) == ALL_LANE_IDS_V2
    assert state.owned_atoms_by_asset() == {"asset:usd": 10}
    assert state.liability_atoms_by_asset() == {"asset:usd": 1}
    assert state.supply_atoms_by_asset() == {"asset:usd": 10}
    assert GlobalEconomicStateRootV2.from_state(state) == GlobalEconomicStateRootV2(
        root=state.state_root,
        profile_root=state.profile_root,
        writer_epoch=state.writer_epoch,
        height=state.height,
    )


@pytest.mark.parametrize(
    "lane_roots",
    [
        _lane_roots()[:-1],
        tuple(reversed(_lane_roots())),
        (_lane_roots()[0], *_lane_roots()[1:-1], _lane_roots()[0]),
    ],
)
def test_global_state_rejects_missing_reordered_or_duplicate_lane_ownership(
    lane_roots: tuple[LaneStateRootV2, ...],
) -> None:
    with pytest.raises(ValueError, match="every ABI V2 lane"):
        _state(lane_roots=lane_roots)


def test_global_state_rejects_noncanonical_sparse_rows_and_replay_aliases() -> None:
    with pytest.raises(ValueError, match="nonzero"):
        _state(
            balances=(
                EconomicAmountV2("alice", "asset:usd", "zenoledger:accounts", 0),
            )
        )
    with pytest.raises(ValueError, match="ordered and unique"):
        _state(
            balances=(
                EconomicAmountV2("bob", "asset:usd", "zenoledger:accounts", 1),
                EconomicAmountV2("alice", "asset:usd", "zenoledger:accounts", 1),
            )
        )
    with pytest.raises(ValueError, match="occurrence ids must be unique"):
        _state(
            replay_state=(
                ReplayStateV2("replay:a", _root(301)),
                ReplayStateV2("replay:b", _root(301)),
            )
        )


def test_global_state_rejects_future_oracle_observations() -> None:
    with pytest.raises(ValueError, match="observed height exceeds global state height"):
        _state(
            height=7,
            oracle_occurrences=(
                OracleOccurrenceStateV2("oracle:future", _root(303), 8, False),
            ),
        )


def test_global_state_checks_table_bound_before_deep_row_validation() -> None:
    invalid = AssetSupplyV2("asset:invalid", 1)
    object.__setattr__(invalid, "asset", "")
    invalid_at_limit = (invalid,) * MAX_GLOBAL_SUPPLY_ROWS_V2
    invalid_above_limit = (invalid,) * (MAX_GLOBAL_SUPPLY_ROWS_V2 + 1)

    with pytest.raises(ValueError, match="supply asset must not be empty"):
        _state(supplies=invalid_at_limit)
    with pytest.raises(ValueError, match="global state supplies exceeds.*bounded shape"):
        _state(supplies=invalid_above_limit)


def test_python_and_rust_global_collection_limits_are_frozen_and_equal() -> None:
    expected = {
        "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2": 65_536,
        "MAX_GLOBAL_ORACLE_ROWS_V2": 4_096,
        "MAX_GLOBAL_OUTBOX_ROWS_V2": 65_536,
        "MAX_GLOBAL_REPLAY_ROWS_V2": 65_536,
        "MAX_GLOBAL_SUPPLY_ROWS_V2": 4_096,
        "MAX_GLOBAL_TERMINAL_ROWS_V2": 65_536,
    }
    assert {
        "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2": MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2,
        "MAX_GLOBAL_ORACLE_ROWS_V2": MAX_GLOBAL_ORACLE_ROWS_V2,
        "MAX_GLOBAL_OUTBOX_ROWS_V2": MAX_GLOBAL_OUTBOX_ROWS_V2,
        "MAX_GLOBAL_REPLAY_ROWS_V2": MAX_GLOBAL_REPLAY_ROWS_V2,
        "MAX_GLOBAL_SUPPLY_ROWS_V2": MAX_GLOBAL_SUPPLY_ROWS_V2,
        "MAX_GLOBAL_TERMINAL_ROWS_V2": MAX_GLOBAL_TERMINAL_ROWS_V2,
    } == expected

    rust_source = (
        Path(__file__).resolve().parents[2]
        / "zk/global_settlement_abi_v2/src/global_state.rs"
    ).read_text(encoding="utf-8")
    rust_limits = {
        name: int(value.replace("_", ""))
        for name, value in re.findall(
            r"pub const (MAX_GLOBAL_[A-Z0-9_]+): usize = ([0-9_]+);",
            rust_source,
        )
    }
    assert {name: rust_limits[name] for name in expected} == expected


def test_global_state_root_owns_constructor_inputs() -> None:
    lanes = list(_lane_roots())
    balances = [EconomicAmountV2("alice", "asset:usd", "zenoledger:accounts", 7)]
    state = _state(lane_roots=tuple(lanes), balances=tuple(balances))
    root_before = state.state_root

    object.__setattr__(lanes[0], "state_root", _root(999))
    object.__setattr__(balances[0], "amount_atoms", MAX_ATOMS_V2)

    assert state.state_root == root_before
    assert state.lane_roots[0].state_root == _root(101)
    assert state.balances[0].amount_atoms == 7


def test_global_state_getters_and_canonical_projection_do_not_expose_backing() -> None:
    oracle = OracleOccurrenceStateV2("oracle:usd", _root(401), 4, False)
    replay = ReplayStateV2("replay:a", _root(402))
    obligation = _obligation(4)
    outbox = OutboxStateV2(
        effect_id=_root(403),
        destination_id="tau:testnet",
        payload_hash=_root(404),
        adapter_profile_root=_root(405),
        commit_id=_root(406),
        status=OutboxStatusV2.PENDING,
    )
    state = _state(
        oracle_occurrences=(oracle,),
        replay_state=(replay,),
        terminal_obligations=(obligation,),
        outbox=(outbox,),
    )
    root_before = state.state_root
    canonical_before = canonical_global_bytes_v2(state)

    assert root_before == (
        "0x34d4148cb4721a0a1fc33b0fec09cd343e310b6eddec12462cd129674296beac"
    )

    object.__setattr__(state.lane_roots[0], "state_root", _root(901))
    object.__setattr__(state.balances[0], "amount_atoms", 901)
    object.__setattr__(state.supplies[0], "amount_atoms", 902)
    object.__setattr__(state.custody[0], "amount_atoms", 903)
    object.__setattr__(state.liabilities[0], "amount_atoms", 904)
    object.__setattr__(state.reserves[0], "amount_atoms", 905)
    object.__setattr__(state.oracle_occurrences[0], "observed_height", 906)
    object.__setattr__(state.replay_state[0], "occurrence_id", _root(907))
    object.__setattr__(state.terminal_obligations[0], "amount_atoms", 908)
    object.__setattr__(state.outbox[0], "payload_hash", _root(909))
    projected = state.to_canonical()
    projected_balances = cast(tuple[EconomicAmountV2, ...], projected["balances"])
    object.__setattr__(projected_balances[0], "amount_atoms", 910)

    assert state.state_root == root_before
    assert canonical_global_bytes_v2(state) == canonical_before
    assert state.lane_roots[0].state_root == _root(101)
    assert state.balances[0].amount_atoms == 7
    assert state.supplies[0].amount_atoms == 10
    assert state.custody[0].amount_atoms == 2
    assert state.liabilities[0].amount_atoms == 1
    assert state.reserves[0].amount_atoms == 1
    assert state.oracle_occurrences[0].observed_height == 4
    assert state.replay_state[0].occurrence_id == _root(402)
    assert state.terminal_obligations[0].amount_atoms == 4
    assert state.outbox[0].payload_hash == _root(404)


def test_global_state_replace_preserves_owned_graph_and_public_field_updates() -> None:
    state = _state()
    minimal = GlobalEconomicStateV2(
        chain_id="chain:test",
        deployment_root=_root(201),
        writer_epoch=3,
        height=7,
        profile_root=_root(202),
        lane_roots=_lane_roots(),
    )

    unchanged = replace(state)
    updated = replace(
        state,
        balances=(
            EconomicAmountV2("alice", "asset:usd", "zenoledger:accounts", 8),
        ),
    )

    assert unchanged == state
    assert unchanged.state_root == state.state_root
    assert replace(minimal) == minimal
    assert minimal.balances == minimal.terminal_obligations == minimal.outbox == ()
    assert updated.balances[0].amount_atoms == 8
    assert updated.state_root != state.state_root


def test_lifecycle_derivation_owns_caller_rows() -> None:
    obligation_before = _obligation(4)
    obligation_after = _obligation(6)
    terminal_plan = derive_global_terminal_obligation_plan_v2(
        (obligation_before,),
        (obligation_after,),
    )
    terminal_root_before = terminal_plan.plan_root
    oracle_before = OracleOccurrenceStateV2("oracle:usd", _root(411), 4, False)
    oracle_after = OracleOccurrenceStateV2("oracle:usd", _root(412), 5, True)
    oracle_plan = derive_global_oracle_occurrence_plan_v2(
        (oracle_before,),
        (oracle_after,),
    )
    oracle_root_before = oracle_plan.plan_root

    object.__setattr__(obligation_before, "amount_atoms", 100)
    object.__setattr__(obligation_after, "amount_atoms", 101)
    object.__setattr__(oracle_before, "observed_height", 100)
    object.__setattr__(oracle_after, "observed_height", 101)

    assert terminal_plan.plan_root == terminal_root_before
    assert terminal_plan.deltas[0].pre_obligation == _obligation(4)
    assert terminal_plan.deltas[0].post_obligation == _obligation(6)
    assert oracle_plan.plan_root == oracle_root_before
    assert oracle_plan.deltas[0].pre_occurrence == OracleOccurrenceStateV2(
        "oracle:usd", _root(411), 4, False
    )
    assert oracle_plan.deltas[0].post_occurrence == OracleOccurrenceStateV2(
        "oracle:usd", _root(412), 5, True
    )


def test_terminal_plan_is_canonical_and_covers_create_update_and_drain() -> None:
    created = derive_global_terminal_obligation_plan_v2((), (_obligation(4),))
    updated = derive_global_terminal_obligation_plan_v2(
        (_obligation(4),),
        (_obligation(6),),
    )
    drained = derive_global_terminal_obligation_plan_v2(
        (_obligation(6),),
        (_obligation(6, TerminalObligationStatusV2.DRAINED),),
    )

    assert created.deltas[0].pre_obligation is None
    assert updated.deltas[0].post_obligation.amount_atoms == 6
    assert drained.deltas[0].post_obligation.status is TerminalObligationStatusV2.DRAINED
    assert len({created.plan_root, updated.plan_root, drained.plan_root}) == 3


def test_terminal_plan_rejects_deletion_and_identity_drift() -> None:
    with pytest.raises(ValueError, match="cannot be deleted"):
        derive_global_terminal_obligation_plan_v2((_obligation(4),), ())
    with pytest.raises(ValueError, match="identity fields are immutable"):
        derive_global_terminal_obligation_plan_v2(
            (_obligation(4),),
            (replace(_obligation(4), liability_domain="zenoledger:other"),),
        )


def test_oracle_plan_is_canonical_and_rejects_deletion_or_height_regression() -> None:
    before = OracleOccurrenceStateV2("oracle:usd", _root(401), 4, False)
    after = OracleOccurrenceStateV2("oracle:usd", _root(402), 5, True)
    plan = derive_global_oracle_occurrence_plan_v2((before,), (after,))

    assert plan.deltas[0].pre_occurrence == before
    assert plan.deltas[0].post_occurrence == after
    assert plan.plan_root != ZERO_ROOT_V2
    with pytest.raises(ValueError, match="cannot be deleted"):
        derive_global_oracle_occurrence_plan_v2((before,), ())
    with pytest.raises(ValueError, match="height cannot regress"):
        derive_global_oracle_occurrence_plan_v2(
            (after,),
            (OracleOccurrenceStateV2("oracle:usd", _root(401), 4, False),),
        )


def test_outbox_state_has_closed_status_and_commit_binding() -> None:
    row = OutboxStateV2(
        effect_id=_root(501),
        destination_id="tau:testnet",
        payload_hash=_root(502),
        adapter_profile_root=_root(503),
        commit_id=_root(504),
        status=OutboxStatusV2.PENDING,
    )

    state = _state(outbox=(row,))
    assert state.outbox == (row,)
    with pytest.raises(TypeError, match="status is not closed"):
        OutboxStateV2(
            effect_id=_root(501),
            destination_id="tau:testnet",
            payload_hash=_root(502),
            adapter_profile_root=_root(503),
            commit_id=_root(504),
            status="PENDING",
        )
