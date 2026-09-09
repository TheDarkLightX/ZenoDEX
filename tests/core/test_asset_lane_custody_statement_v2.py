"""Native global-refinement evidence for custody statement preparation."""

from __future__ import annotations

import json
from dataclasses import replace
from types import SimpleNamespace
from typing import Any, cast

import pytest

import src.core.asset_lane_custody_statement_v2 as statement
from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
from src.core.asset_lane_custody_coordinator_v2 import transition_asset_lane_custody_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _root,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_global_v2 import global_case
from tests.core.test_asset_lane_custody_v2 import custody_state


def _case(lane=None, command=None):
    command = _transfer_command(amount_atoms=10) if command is None else command
    lane, accepted, before, after, occurrence = global_case(lane, command)
    context = AssetLaneContextV2(
        before.writer_epoch,
        lane.transfer_state.module_release_id,
        before.state_root,
        occurrence,
    )
    return context, lane, command, accepted, before, after


def _body(raw: bytes) -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(raw))


@pytest.mark.parametrize(
    ("name", "lane", "command"),
    (
        ("transfer", custody_state(), _transfer_command(amount_atoms=10)),
        (
            "managed_issue",
            custody_state(80, 20),
            _managed_command(kind="managed_asset_issue", amount_atoms=7),
        ),
        (
            "managed_full_burn",
            custody_state(80, 20),
            _managed_command(kind="managed_asset_burn", amount_atoms=80),
        ),
        (
            "dormant_issue",
            custody_state(0, 0),
            _managed_command(kind="managed_asset_issue", amount_atoms=1),
        ),
        (
            "dormant_burn",
            custody_state(1, 0),
            _managed_command(kind="managed_asset_burn", amount_atoms=1),
        ),
    ),
)
def test_accepted_custody_cases_emit_the_exact_four_field_global_statement(
    name: str, lane, command
) -> None:
    context, lane, command, accepted, before, after = _case(lane, command)

    produced = statement.prepare_asset_lane_custody_global_statement_v2(
        context, lane, command, before, after
    )

    assert type(produced) is bytes, name
    expected = canonical_global_bytes_v2(
        {
            "schema": statement.ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2,
            "module_journal": accepted.module_journal,
            "global_pre_state_root": before.state_root,
            "global_post_state_root": after.state_root,
        }
    )
    assert produced == expected, name
    assert _body(produced) == {
        "schema": statement.ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2,
        "module_journal": _body(canonical_global_bytes_v2(accepted.module_journal)),
        "global_pre_state_root": before.state_root,
        "global_post_state_root": after.state_root,
    }, name


def test_leaf_rejection_is_returned_verbatim_before_broken_globals_or_refinement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    lane = custody_state()
    command = _transfer_command(amount_atoms=10)
    context = _context(command, subject="mallory")
    rejected = transition_asset_lane_custody_v2(context, lane, command)
    assert type(rejected) is AssetLaneRejectedV2
    actual = statement.prepare_asset_lane_custody_global_statement_v2(
        context,
        lane,
        command,
        cast(GlobalEconomicStateV2, object()),
        cast(GlobalEconomicStateV2, object()),
    )
    assert type(actual) is AssetLaneRejectedV2
    assert actual.code is rejected.code
    assert actual.pre_state_root == actual.post_state_root == lane.state_root
    assert actual.effects.is_empty
    calls: list[object] = []

    def forbidden_refinement(*args: object) -> object:
        calls.append(args)
        raise AssertionError("rejected custody leaf reached global refinement")

    monkeypatch.setattr(statement, "transition_asset_lane_custody_v2", lambda *_: rejected)
    monkeypatch.setattr(statement, "refine_asset_lane_custody_global_v2", forbidden_refinement)

    produced = statement.prepare_asset_lane_custody_global_statement_v2(
        context,
        lane,
        command,
        cast(GlobalEconomicStateV2, object()),
        cast(GlobalEconomicStateV2, object()),
    )

    assert produced is rejected
    assert produced.code.value == "UNAUTHORIZED_SUBJECT"
    assert produced.pre_state_root == produced.post_state_root == lane.state_root
    assert produced.effects.is_empty
    assert calls == []


def test_statement_cannot_bypass_global_consumer_substitution_guards() -> None:
    context, lane, command, _, before, after = _case()
    claimant = replace(after, liabilities=(replace(after.liabilities[0], owner="mallory"),))
    custody = replace(after, custody=(replace(after.custody[0], owner="mallory"),))
    replay = replace(after, replay_state=())
    writer = AssetLaneContextV2(
        context.writer_epoch + 1,
        context.module_release_id,
        context.global_pre_state_root,
        context.occurrence,
    )
    stale_history = _root("stale-global-pre")
    stale_pre = replace(before, history_root=stale_history)
    stale_post = replace(after, history_root=stale_history)

    substitutions = (
        (context, before, claimant, "claimant or custody frame changed"),
        (context, before, custody, "complete projection mismatch"),
        (context, before, replay, "replay post-state mismatch"),
        (writer, before, after, "source journal binding mismatch"),
        (context, stale_pre, stale_post, "occurrence context mismatch"),
    )
    for substituted_context, substituted_pre, substituted_post, message in substitutions:
        with pytest.raises(ValueError, match=message):
            statement.prepare_asset_lane_custody_global_statement_v2(
                substituted_context,
                lane,
                command,
                substituted_pre,
                substituted_post,
            )


def test_statement_uses_refinement_returned_roots_and_actual_custody_journal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context, lane, command, accepted, before, after = _case()
    refined_pre = _root("refinement-pre")
    refined_post = _root("refinement-post")
    seen: list[tuple[object, ...]] = []

    def replacement_refinement(*args: object) -> SimpleNamespace:
        seen.append(args)
        return SimpleNamespace(pre_state_root=refined_pre, post_state_root=refined_post)

    monkeypatch.setattr(statement, "refine_asset_lane_custody_global_v2", replacement_refinement)
    produced = statement.prepare_asset_lane_custody_global_statement_v2(
        context, lane, command, before, after
    )

    assert type(produced) is bytes
    assert _body(produced)["global_pre_state_root"] == refined_pre
    assert _body(produced)["global_post_state_root"] == refined_post
    assert _body(produced)["module_journal"] == _body(
        canonical_global_bytes_v2(accepted.module_journal)
    )
    assert seen == [(lane, accepted, before, after, context.occurrence)]


def test_unexpected_accepted_result_without_occurrence_raises_before_refinement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context, lane, command, accepted, before, after = _case()
    missing_occurrence = AssetLaneContextV2(
        context.writer_epoch,
        context.module_release_id,
        context.global_pre_state_root,
        None,
    )

    def forbidden_refinement(*_: object) -> object:
        raise AssertionError("missing occurrence reached global refinement")

    monkeypatch.setattr(statement, "transition_asset_lane_custody_v2", lambda *_: accepted)
    monkeypatch.setattr(statement, "refine_asset_lane_custody_global_v2", forbidden_refinement)
    with pytest.raises(ValueError, match="accepted custody statement requires an occurrence"):
        statement.prepare_asset_lane_custody_global_statement_v2(
            missing_occurrence, lane, command, before, after
        )


def test_statement_bytes_remain_immutable_after_source_input_mutation() -> None:
    context, lane, command, _, before, after = _case()
    produced = statement.prepare_asset_lane_custody_global_statement_v2(
        context, lane, command, before, after
    )
    assert type(produced) is bytes

    object.__setattr__(context, "writer_epoch", context.writer_epoch + 1)
    object.__setattr__(lane, "_custody", ())
    object.__setattr__(command, "amount_atoms", 1)
    object.__setattr__(before, "height", before.height + 1)
    object.__setattr__(after, "height", after.height + 1)

    assert produced == bytes(produced)
    assert _body(produced)["global_pre_state_root"] != before.state_root
    assert _body(produced)["global_post_state_root"] != after.state_root
