"""Receipt-boundary byte closure; no cryptographic or publisher authority is tested."""

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v2 import (
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    PerpsMarginGlobalRejectCodeV2,
    PerpsMarginGlobalRejectedV2,
    transition_perps_margin_global_v2,
)
from src.core.perps_margin_receipt_v2 import (
    MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2,
    encode_perps_margin_frame_v2,
    prepare_perps_margin_statement_v2,
)
from src.core.perps_margin_types_v1 import PerpsMarginAccountStatusV1
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration.custody_publication_record_v2 import (
    decode_custody_global_state_v2,
    frame_joint_margin_publication_v2,
    replay_joint_margin_publication_v2,
)
from tests.core.test_perps_margin_global_v2 import (
    DEPOSIT,
    WITHDRAW,
    _command,
    _initial,
    _occurrence,
)


def _inputs_with_terminal_history(count):
    assets, margin, state = _initial()
    terminal = TerminalObligationV2(
        "old-000000" + "x" * 150,
        LaneIdV2.PERPS_MARKET,
        "z" * 160,
        "USD",
        "perps_margin",
        1,
        TerminalObligationStatusV2.DRAINED,
    )
    terminals = tuple(
        replace(terminal, obligation_id=f"old-{index:06d}" + "x" * 150)
        for index in range(count)
    )
    raw = canonical_global_bytes_v2(replace(state, terminal_obligations=terminals))
    # The predecessor must pass the real decoder, not merely a byte-count check.
    return assets, margin, decode_custody_global_state_v2(raw)


def _request(state, kind, nonce):
    command = _command(kind, 1, nonce)
    return PerpsMarginRequestV2(command, _occurrence(state, command, nonce))


def test_margin_successor_beyond_next_input_byte_limit_rejects_without_effects():
    inputs = _inputs_with_terminal_history(2252)
    assets, margin, state = inputs
    before = tuple(canonical_global_bytes_v2(value) for value in inputs)
    request = _request(state, DEPOSIT, 1)

    # Reachability control: unchanged economics accepts this valid one-atom
    # deposit. Its new claim/replay rows push only the global successor over cap.
    economic = transition_perps_margin_global_v2(
        assets, margin, state, request.command, request.occurrence,
    )
    assert type(economic) is PerpsMarginGlobalAcceptedV2
    assert len(before[2]) == 1_048_155
    assert len(canonical_global_bytes_v2(economic.post_state)) == 1_048_696
    assert len(before[2]) <= MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2
    assert economic.post_margin.economic_state.accounts[0].collateral_atoms == 1

    rejected = prepare_perps_margin_statement_v2(*inputs, request)
    assert type(rejected) is PerpsMarginGlobalRejectedV2
    assert rejected.code is PerpsMarginGlobalRejectCodeV2.SUCCESSOR_REJECTED
    assert rejected.pre_state_root == rejected.post_state_root == state.state_root
    assert rejected.effects.is_empty
    assert rejected.terminal_plan.deltas == ()
    assert rejected.oracle_plan.deltas == ()

    # An independently framed, individually admissible predecessor cannot
    # evade that same guard through the durable-record replay route.
    frame = frame_joint_margin_publication_v2(
        encode_perps_margin_frame_v2(*inputs, request), None,
    )
    with pytest.raises(ValueError, match="rejected.*SUCCESSOR_REJECTED"):
        replay_joint_margin_publication_v2(frame)
    assert tuple(canonical_global_bytes_v2(value) for value in inputs) == before


def test_margin_byte_capacity_neighbor_preserves_deposit_and_terminal_drain():
    inputs = _inputs_with_terminal_history(2251)
    before = tuple(canonical_global_bytes_v2(value) for value in inputs)
    initial_terminals = inputs[2].terminal_obligations
    claim_id = None

    for kind, nonce in ((DEPOSIT, 1), (WITHDRAW, 2)):
        request = _request(inputs[2], kind, nonce)
        frame = frame_joint_margin_publication_v2(
            encode_perps_margin_frame_v2(*inputs, request), None,
        )
        replay = replay_joint_margin_publication_v2(frame)
        inputs = replay.lane_post, replay.margin_post, replay.global_post
        assert all(
            len(canonical_global_bytes_v2(value)) <= MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2
            for value in inputs
        )
        if kind == DEPOSIT:
            assert len(canonical_global_bytes_v2(replay.global_post)) == 1_048_232
            claim_id = replay.margin_post.claim_id("margin-a")
            assert claim_id is not None
            assert replay.margin_post.economic_state.accounts[0].collateral_atoms == 1
            assert replay.global_post.custody[0].amount_atoms == 1
            assert replay.global_post.liabilities[0].amount_atoms == 1
            assert canonical_global_bytes_v2(replay.global_pre) == before[2]

    assets, margin, state = inputs
    assert margin.active_claims == ()
    account = margin.economic_state.accounts[0]
    assert account.collateral_atoms == 0
    assert account.status is PerpsMarginAccountStatusV1.OPEN
    assert assets.transfer_state.balances[0].amount_atoms == 100
    assert state.custody == state.liabilities == ()
    assert len(state.replay_state) == 2
    assert state.supplies == replay.global_pre.supplies
    assert tuple(row for row in state.terminal_obligations if row.obligation_id != claim_id) == initial_terminals
    terminal = next(row for row in state.terminal_obligations if row.obligation_id == claim_id)
    assert terminal.status is TerminalObligationStatusV2.DRAINED
    assert terminal.amount_atoms == 1
