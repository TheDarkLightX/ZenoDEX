"""The derived custody successor must be the one global post-state that refines."""

from dataclasses import replace

import pytest

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_global_v2 import (
    derive_asset_lane_custody_global_post_v2,
    refine_asset_lane_custody_global_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_economic_state_v2 import (
    MAX_GLOBAL_REPLAY_ROWS_V2,
    GlobalEconomicStateV2,
    LaneStateRootV2,
    OutboxStateV2,
    OutboxStatusV2,
    ReplayStateV2,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    MAX_U64_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    OracleOccurrenceStateV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _root,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_global_v2 import global_case
from tests.core.test_asset_lane_custody_v2 import custody_state

RETAINED_LANE = LaneIdV2.SPOT_LIQUIDITY
RETAINED_LANE_ROOT = _root("retained-spot-liquidity")
RETAINED_HISTORY_ROOT = _root("retained-history")

# Every predecessor row the successor must carry through unchanged.
RETAINED_FRAME_FIELDS = (
    "chain_id",
    "deployment_root",
    "writer_epoch",
    "profile_root",
    "custody",
    "liabilities",
    "reserves",
    "oracle_occurrences",
    "terminal_obligations",
    "history_root",
    "outbox",
)

RETAINED_ORACLE_ROW = OracleOccurrenceStateV2("usd-mark", _root("oracle-occurrence"), 5, True)
RETAINED_OUTBOX_ROW = OutboxStateV2(
    _root("outbox-effect"),
    "bridge:alpha",
    _root("outbox-payload"),
    _root("outbox-adapter"),
    _root("outbox-commit"),
    OutboxStatusV2.PENDING,
)


def _claims(lane):
    """Mirror the retained claimant frame the existing global fixture commits."""

    if not lane.custody:
        return (), ()
    return (
        (EconomicAmountV2("alice", "USD", "escrow", 20),),
        (
            TerminalObligationV2(
                "alice-vault-claim",
                LaneIdV2.ASSET_TRANSFER,
                "alice",
                "USD",
                "escrow",
                20,
                TerminalObligationStatusV2.OPEN,
            ),
        ),
    )


def _lane_roots(lane, other_enabled):
    rows = []
    for lane_id in ALL_LANE_IDS_V2:
        if lane_id is LaneIdV2.ASSET_TRANSFER:
            row = LaneStateRootV2(
                lane_id, lane.transfer_state.module_release_id, True, lane.state_root
            )
        elif lane_id is RETAINED_LANE and other_enabled:
            row = LaneStateRootV2(lane_id, _root(lane_id.value), True, RETAINED_LANE_ROOT)
        else:
            row = LaneStateRootV2(lane_id, _root(lane_id.value), False, ZERO_ROOT_V2)
        rows.append(row)
    return tuple(rows)


def _case(
    lane=None,
    command=None,
    *,
    nonce=1,
    height=None,
    replay_state=(),
    other_enabled=False,
    lifecycle_rows=False,
):
    """Build an accepted custody command over an independently written predecessor."""

    lane = custody_state() if lane is None else lane
    command = _transfer_command(amount_atoms=10) if command is None else command
    context = _context(command, nonce=nonce)
    occurrence = context.occurrence
    liabilities, obligations = _claims(lane)
    pre = GlobalEconomicStateV2(
        occurrence.chain_id,
        occurrence.deployment_root,
        context.writer_epoch,
        occurrence.height - 1 if height is None else height,
        occurrence.profile_root,
        _lane_roots(lane, other_enabled),
        balances=lane.transfer_state.balances,
        supplies=tuple(row for row in lane.transfer_state.supplies if row.amount_atoms),
        custody=lane.custody,
        liabilities=liabilities,
        oracle_occurrences=(RETAINED_ORACLE_ROW,) if lifecycle_rows else (),
        replay_state=replay_state,
        terminal_obligations=obligations,
        history_root=RETAINED_HISTORY_ROOT if lifecycle_rows else ZERO_ROOT_V2,
        outbox=(RETAINED_OUTBOX_ROW,) if lifecycle_rows else (),
    )
    occurrence = replace(occurrence, pre_state_root=pre.state_root)
    context = AssetLaneContextV2(
        context.writer_epoch, context.module_release_id, pre.state_root, occurrence
    )
    accepted = transition_asset_lane_custody_v2(context, lane, command)
    assert isinstance(accepted, AssetLaneCustodyAcceptedV2)
    return lane, accepted, pre, occurrence


def _advance(lane, global_pre, command, nonce):
    """Chain one further accepted command onto a live derived predecessor."""

    context = _context(command, nonce=nonce)
    occurrence = replace(context.occurrence, pre_state_root=global_pre.state_root)
    context = AssetLaneContextV2(
        context.writer_epoch, context.module_release_id, global_pre.state_root, occurrence
    )
    accepted = transition_asset_lane_custody_v2(context, lane, command)
    assert isinstance(accepted, AssetLaneCustodyAcceptedV2)
    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, global_pre, occurrence)
    refine_asset_lane_custody_global_v2(lane, accepted, global_pre, derived, occurrence)
    return accepted.post_state, derived


def _inserted_replay(occurrence):
    return ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id)


def test_transfer_successor_equals_the_independently_written_admitted_post_state():
    lane, accepted, pre, post, occurrence = global_case()

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    assert type(derived) is GlobalEconomicStateV2
    assert not hasattr(derived, "production_authority")
    assert not hasattr(derived, "refinement_root")
    assert derived.to_canonical() == post.to_canonical()
    assert derived.state_root == post.state_root
    assert derived.balances == (
        EconomicAmountV2("alice", "USD", "accounts", 68),
        EconomicAmountV2("bob", "USD", "accounts", 10),
        EconomicAmountV2("treasury", "USD", "accounts", 2),
    )
    assert derived.custody == pre.custody == (EconomicAmountV2("vault", "USD", "escrow", 20),)
    assert derived.supplies == pre.supplies == (AssetSupplyV2("USD", 100),)
    assert sum(row.amount_atoms for row in (*derived.balances, *derived.custody)) == 100


def test_derived_successor_repasses_the_original_relation_and_is_deterministic():
    lane, accepted, pre, occurrence = _case(lifecycle_rows=True)

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)
    repeated = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)
    checked = refine_asset_lane_custody_global_v2(lane, accepted, pre, derived, occurrence)

    assert derived.state_root == repeated.state_root
    assert checked.pre_state_root == pre.state_root
    assert checked.post_state_root == derived.state_root
    assert checked.effect_plan_root == accepted.effects.effect_plan_root
    assert checked.production_authority == "NONE"


@pytest.mark.parametrize(
    "kind,accounts,vault,amount,supply",
    (
        ("managed_asset_issue", 80, 20, 7, 107),
        ("managed_asset_burn", 80, 20, 80, 20),
        ("managed_asset_issue", 0, 0, 1, 1),
        ("managed_asset_burn", 1, 0, 1, 0),
    ),
)
def test_issue_burn_and_dormant_successors_project_only_positive_supply(
    kind, accounts, vault, amount, supply
):
    lane, accepted, pre, post, occurrence = global_case(
        custody_state(accounts, vault), _managed_command(kind=kind, amount_atoms=amount)
    )

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    assert derived.to_canonical() == post.to_canonical()
    assert accepted.post_state.transfer_state.supply_atoms("USD") == supply
    assert derived.supplies == ((AssetSupplyV2("USD", supply),) if supply else ())
    assert derived.balances == accepted.post_state.transfer_state.balances
    assert derived.custody == pre.custody
    assert derived.liabilities == pre.liabilities
    assert derived.height == pre.height + 1


def test_every_unchanged_global_frame_field_is_carried_into_the_successor():
    lane, accepted, pre, occurrence = _case(lifecycle_rows=True)

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    for field_name in RETAINED_FRAME_FIELDS:
        assert getattr(derived, field_name) == getattr(pre, field_name), field_name
    assert derived.reserves == ()
    assert derived.oracle_occurrences == (RETAINED_ORACLE_ROW,)
    assert derived.outbox == (RETAINED_OUTBOX_ROW,)
    assert derived.history_root == RETAINED_HISTORY_ROOT
    assert derived.height == pre.height + 1
    assert derived.replay_state == (_inserted_replay(occurrence),)
    assert derived.balances != pre.balances


def test_other_enabled_lane_keeps_its_root_release_and_enabled_metadata():
    lane, accepted, pre, occurrence = _case(other_enabled=True)

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    retained = {row.lane_id: row for row in derived.lane_roots}
    for row in pre.lane_roots:
        if row.lane_id is LaneIdV2.ASSET_TRANSFER:
            continue
        assert retained[row.lane_id] == row, row.lane_id
    assert retained[RETAINED_LANE].enabled is True
    assert retained[RETAINED_LANE].state_root == RETAINED_LANE_ROOT
    assert retained[LaneIdV2.ASSET_TRANSFER] == LaneStateRootV2(
        LaneIdV2.ASSET_TRANSFER,
        lane.transfer_state.module_release_id,
        True,
        accepted.post_state.state_root,
    )


def test_prior_replay_rows_are_retained_canonically_around_the_inserted_identity():
    lower = ReplayStateV2("!prior-lower", _root("prior-occurrence-lower"))
    upper = ReplayStateV2("zz-prior-upper", _root("prior-occurrence-upper"))
    lane, accepted, pre, occurrence = _case(replay_state=(lower, upper))

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    inserted = _inserted_replay(occurrence)
    assert lower.replay_id < inserted.replay_id < upper.replay_id
    assert derived.replay_state == (lower, inserted, upper)
    refine_asset_lane_custody_global_v2(lane, accepted, pre, derived, occurrence)


def test_replay_identity_collisions_reject_instead_of_overwriting_a_prior_row():
    command = _transfer_command(amount_atoms=10)
    replayed = _context(command).occurrence.replay_id
    prior = ReplayStateV2(replayed, _root("prior-occurrence"))
    lane, accepted, pre, occurrence = _case(command=command, replay_state=(prior,))
    assert occurrence.replay_id == replayed

    with pytest.raises(ValueError, match="replay_state must be canonically ordered and unique"):
        derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    assert prior.occurrence_id != occurrence.occurrence_id
    assert pre.replay_state == (prior,)


def test_duplicate_occurrence_identity_rejects_before_the_relation_is_consulted():
    lane, accepted, pre, occurrence = _case()
    forged = replace(pre, replay_state=(ReplayStateV2("zz-other", occurrence.occurrence_id),))
    forged_root = forged.state_root

    with pytest.raises(ValueError, match="replay occurrence ids must be unique"):
        derive_asset_lane_custody_global_post_v2(lane, accepted, forged, occurrence)

    assert forged.state_root == forged_root
    assert pre.replay_state == ()


@pytest.mark.parametrize("source", ("foreign_lane", "post_lane"))
def test_wrong_predecessor_lane_rejects_and_returns_no_successor(source):
    lane, accepted, pre, occurrence = _case()
    wrong = custody_state(70, 30) if source == "foreign_lane" else accepted.post_state
    original_root = pre.state_root

    with pytest.raises(ValueError, match="complete projection mismatch"):
        derive_asset_lane_custody_global_post_v2(wrong, accepted, pre, occurrence)

    assert pre.state_root == original_root
    assert wrong.state_root != lane.state_root


def test_predecessor_that_the_occurrence_does_not_bind_is_rejected():
    lane, accepted, pre, occurrence = _case()
    stale = replace(pre, history_root=RETAINED_HISTORY_ROOT)
    assert stale.state_root != pre.state_root

    with pytest.raises(ValueError, match="occurrence context mismatch"):
        derive_asset_lane_custody_global_post_v2(lane, accepted, stale, occurrence)

    assert occurrence.pre_state_root == pre.state_root


def test_occurrence_height_that_is_not_the_successor_height_rejects():
    stale_height = _context(_transfer_command(amount_atoms=10)).occurrence.height
    lane, accepted, pre, occurrence = _case(height=stale_height)
    assert occurrence.height == pre.height

    with pytest.raises(ValueError, match="occurrence height mismatch"):
        derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    assert pre.height == stale_height


def test_height_ceiling_rejects_the_successor_at_the_maximum_predecessor_height():
    lane, accepted, pre, occurrence = _case(height=MAX_U64_V2)
    assert pre.height == MAX_U64_V2

    with pytest.raises(ValueError, match="height must fit an unsigned 64-bit integer"):
        derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    assert pre.height == MAX_U64_V2


def test_replay_row_ceiling_rejects_before_the_relation_is_consulted():
    lane, accepted, pre, occurrence = _case()
    full = tuple(
        ReplayStateV2(f"prior-{index:06d}", "0x" + f"{index + 1:064x}")
        for index in range(MAX_GLOBAL_REPLAY_ROWS_V2)
    )
    forged = replace(pre, replay_state=full)

    with pytest.raises(ValueError, match="replay_state exceeds the ABI V2 bounded shape"):
        derive_asset_lane_custody_global_post_v2(lane, accepted, forged, occurrence)

    assert len(full) == MAX_GLOBAL_REPLAY_ROWS_V2


def test_maximum_custody_rows_are_carried_into_the_admitted_successor():
    rows = tuple(
        EconomicAmountV2(f"vault-{index:04d}", "USD", "escrow", 1) for index in range(4096)
    )
    base = custody_state(80, 4096)
    lane = AssetLaneCustodyStateV2(
        base.transfer_state, base.origin_registry, base.managed_policies, rows
    )
    lane, accepted, pre, occurrence = _case(lane)

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)

    assert derived.custody == rows
    assert derived.supplies == (AssetSupplyV2("USD", 4176),)
    assert sum(row.amount_atoms for row in (*derived.balances, *derived.custody)) == 4176
    refine_asset_lane_custody_global_v2(lane, accepted, pre, derived, occurrence)


def test_repeated_issue_transfer_burn_sequence_chains_admitted_successors():
    issue = _managed_command(kind="managed_asset_issue", amount_atoms=7)
    transfer = _transfer_command(amount_atoms=10)
    burn = _managed_command(kind="managed_asset_burn", amount_atoms=5)
    lane, accepted, pre, occurrence = _case(custody_state(80, 20), issue)

    first = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)
    lane_two, second = _advance(accepted.post_state, first, transfer, 2)
    lane_three, third = _advance(lane_two, second, burn, 3)

    assert [state.height for state in (pre, first, second, third)] == [8, 9, 10, 11]
    assert [len(state.replay_state) for state in (first, second, third)] == [1, 2, 3]
    assert first.replay_state == (_inserted_replay(occurrence),)
    assert set(first.replay_state) < set(second.replay_state) < set(third.replay_state)
    assert third.replay_state == tuple(sorted(third.replay_state, key=lambda row: row.replay_id))
    for state in (first, second, third):
        assert state.custody == pre.custody
        assert state.liabilities == pre.liabilities
        assert state.terminal_obligations == pre.terminal_obligations
        assert state.reserves == ()
        owned = sum(row.amount_atoms for row in (*state.balances, *state.custody))
        assert owned == state.supplies[0].amount_atoms
    assert {row.owner: row.amount_atoms for row in third.balances} == {
        "alice": 70,
        "bob": 10,
        "treasury": 2,
    }
    assert third.supplies == (AssetSupplyV2("USD", 102),)
    assert lane_three.physical_atoms("USD") == 102


def test_successor_neither_aliases_the_predecessor_nor_exposes_mutable_rows():
    lane, accepted, pre, occurrence = _case()

    derived = derive_asset_lane_custody_global_post_v2(lane, accepted, pre, occurrence)
    derived_root = derived.state_root

    object.__setattr__(object.__getattribute__(pre, "_custody")[0], "amount_atoms", 999)
    object.__setattr__(object.__getattribute__(pre, "_liabilities")[0], "owner", "mallory")
    object.__setattr__(derived.custody[0], "amount_atoms", 999)
    object.__setattr__(derived.balances[0], "owner", "mallory")

    assert derived.state_root == derived_root
    assert derived.custody == (EconomicAmountV2("vault", "USD", "escrow", 20),)
    assert derived.liabilities == (EconomicAmountV2("alice", "USD", "escrow", 20),)
    assert derived.balances[0] == EconomicAmountV2("alice", "USD", "accounts", 68)
