"""Actual Python/Rust output correspondence for the pure joint margin successor.

The JSON-lines transport checks typed transitions; the separate frame executable
uses the strict ZDPM2 decoder intended for the guest. Accepted successor states
feed the next attempt. No cryptographic receipt or publication authority follows.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from copy import deepcopy
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    GlobalOracleOccurrencePlanV2,
    LaneIdV2,
    canonical_global_bytes_v2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    PerpsMarginGlobalRejectedV2,
    PerpsMarginOracleV2,
    transition_perps_margin_global_v2,
)
from src.core.perps_margin_receipt_v2 import (
    MAX_PERPS_MARGIN_FRAME_BYTES_V2,
    MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2,
    encode_perps_margin_frame_v2,
    replay_perps_margin_frame_v2,
)
from src.core.perps_margin_state_v2 import PerpsMarginStateV2
from src.core.perps_margin_types_v1 import PerpsMarginMarketStatusV1
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from tests.core.test_asset_lane_coordinator_v2 import _root, _transfer_command
from tests.core.test_perps_margin_global_bounds_v2 import (
    _full_asset_balance_inputs,
    _nonflat_inputs,
)
from tests.core.test_perps_margin_global_v2 import (
    CLOSE,
    DEPOSIT,
    WITHDRAW,
    _command,
    _initial,
    _occurrence,
)
from tests.core.test_perps_margin_receipt_v2 import _frame_from_parts, _frame_parts
from tests.integration.test_joint_margin_capacity_v2 import _inputs_with_terminal_history

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "zk" / "perps_margin_global_v2" / "Cargo.toml"
TARGET = Path(tempfile.gettempdir()) / "zenodex-perps-margin-global-v2-target"
MIN_FREE_BYTES = 4 * 1024**3
MAX_TARGET_BYTES = 1024**3
Case = tuple[str, dict[str, object], dict[str, object], bytes | None]


@pytest.fixture(scope="module")
def rust_margin_binary() -> Path:
    # The build target follows TMPDIR, which can be a separate filesystem.
    if shutil.disk_usage(TARGET.parent).free < MIN_FREE_BYTES:
        pytest.skip("disk guard: bounded native build requires four GiB free; parity unqualified")
    environment = {**os.environ, "CARGO_TARGET_DIR": str(TARGET)}
    result = subprocess.run(
        ["cargo", "build", "--offline", "--locked", "--manifest-path", str(MANIFEST),
         "--examples"],
        cwd=ROOT, env=environment, capture_output=True, text=True, timeout=180, check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    size = sum(path.stat().st_size for path in TARGET.rglob("*") if path.is_file())
    assert size <= MAX_TARGET_BYTES, "bounded Rust target exceeded one GiB"
    binary = TARGET / "debug" / "examples" / "parity"
    assert binary.is_file()
    return binary


def _json(value):
    return json.loads(canonical_global_bytes_v2(value))


def _observe(result):
    accepted = type(result) is PerpsMarginGlobalAcceptedV2
    assert accepted or type(result) is PerpsMarginGlobalRejectedV2
    effects, terminal = result.effects, result.terminal_plan
    oracle = GlobalOracleOccurrencePlanV2.empty() if accepted else result.oracle_plan
    refinement = None
    if accepted:
        fields = ("pre_state_root", "post_state_root", "effect_plan_root", "terminal_plan_root",
                  "oracle_plan_root", "state_delta_root", "production_authority", "refinement_root")
        refinement = {field: getattr(result.refinement, field) for field in fields}
    roots = {
        "pre_state_root": result.refinement.pre_state_root if accepted else result.pre_state_root,
        "post_state_root": result.refinement.post_state_root if accepted else result.post_state_root,
        "effect_plan_root": effects.effect_plan_root,
        "terminal_plan_root": terminal.plan_root,
        "oracle_plan_root": oracle.plan_root,
        "state_delta_root": result.refinement.state_delta_root if accepted else None,
        "refinement_root": result.refinement.refinement_root if accepted else None,
        "statement_root": result.statement_root if accepted else None,
    }
    observed = {
        "kind": "accepted" if accepted else "rejected", "effects": _json(effects),
        "terminal_plan": _json(terminal), "oracle_plan": _json(oracle),
        "refinement": refinement, "statement_root": roots["statement_root"], "roots": roots,
    }
    if accepted:
        observed.update(assets=_json(result.post_assets), margin=_json(result.post_margin),
                        state=_json(result.post_state))
    else:
        observed["code"] = result.code.value
    return observed


def _margin_case(cases, label, inputs, command, outer_nonce, code=None, *, occurrence=None, oracle=None):
    assets, margin, state = inputs
    occurrence = _occurrence(state, command, outer_nonce) if occurrence is None else occurrence
    before = _json(inputs)
    wire = _json({
        "op": "perps", "assets": assets, "state": state,
        "margin": {"economic_state": margin.economic_state, "active_claims": margin.active_claims},
        "command": command, "occurrence": occurrence, "oracle": oracle,
    })
    result = transition_perps_margin_global_v2(assets, margin, state, command, occurrence, oracle)
    assert _json(inputs) == before
    if code is None:
        assert type(result) is PerpsMarginGlobalAcceptedV2, (label, result)
        successor = result.post_assets, result.post_margin, result.post_state
        assert result.refinement.post_state_root == result.post_state.state_root
        assert result.refinement.production_authority == "NONE"
    else:
        assert type(result) is PerpsMarginGlobalRejectedV2, (label, result)
        assert result.code.value == code, label
        assert result.pre_state_root == result.post_state_root == state.state_root
        assert result.effects.is_empty and not result.terminal_plan.deltas and not result.oracle_plan.deltas
        successor = inputs
    frame = encode_perps_margin_frame_v2(*inputs, PerpsMarginRequestV2(command, occurrence, oracle))
    cases.append((label, wire, _observe(result), frame))
    return successor


def _transfer_case(cases, inputs):
    assets, margin, state = inputs
    command = _transfer_command(amount_atoms=5)
    occurrence = EconomicCommandOccurrenceV2(
        state.chain_id, state.deployment_root, state.height + 1, 0, 0, command.command_kind,
        command.command_body_hash, _root("asset-route"), "alice", _root("grant"), 4,
        state.profile_root, state.state_root, (),
    )
    context = AssetLaneContextV2(state.writer_epoch, assets.transfer_state.module_release_id,
                                 state.state_root, occurrence)
    result = transition_asset_lane_custody_v2(context, assets, command)
    assert type(result) is AssetLaneCustodyAcceptedV2
    post = derive_asset_lane_custody_global_post_v2(assets, result, state, occurrence)
    assert post.terminal_obligations == state.terminal_obligations
    assert next(row.state_root for row in post.lane_roots
                if row.lane_id is LaneIdV2.PERPS_MARKET) == margin.state_root
    wire = _json(dict(op="transfer", assets=assets, state=state, context=context,
                      command=command, occurrence=occurrence))
    expected = dict(kind="accepted", assets=_json(result.post_state), state=_json(post),
                    effects=_json(result.effects), roots={
                        "asset_state_root": result.post_state.state_root,
                        "state_root": post.state_root, "effect_plan_root": result.effects.effect_plan_root,
                    })
    cases.append(("ordinary-transfer-between-margin-episodes", wire, expected, None))
    return result.post_state, margin, post


def _compare(binary, cases):
    payload = "".join(json.dumps(wire, separators=(",", ":")) + "\n" for _, wire, _, _ in cases)
    completed = subprocess.run([str(binary)], input=payload, capture_output=True, text=True,
                               timeout=60, check=False)
    assert completed.returncode == 0, completed.stderr
    outputs = [json.loads(line) for line in completed.stdout.splitlines()]
    assert len(outputs) == len(cases)
    for (label, _, expected, frame), actual in zip(cases, outputs, strict=True):
        _assert_same_observation(actual, expected, label)
        if frame is not None:
            _compare_frame(binary, frame, expected["kind"] == "accepted", label)


def _compare_frame(binary, frame, accepted, label):
    result = subprocess.run([str(binary.with_name("receipt_frame"))], input=frame,
                            capture_output=True, timeout=15, check=False)
    if accepted:
        assert result.returncode == 0 and not result.stderr, (label, result.stderr)
        assert result.stdout == replay_perps_margin_frame_v2(frame).statement, label
    else:
        with pytest.raises(ValueError):
            replay_perps_margin_frame_v2(frame)
        assert result.returncode == 2 and not result.stdout, (label, result)
        assert result.stderr.startswith(b"perps margin global frame rejected:"), label
    return result


def _assert_same_observation(actual, expected, label):
    # Python structural equality aliases True, 1 and 1.0. Typed observations
    # must preserve boolean/integer distinctions and reject floats.
    assert canonical_global_bytes_v2(actual) == canonical_global_bytes_v2(expected), label


@pytest.mark.parametrize("height,error", [(True, AssertionError), (1.0, TypeError)])
def test_parity_observer_rejects_boolean_and_float_integer_aliases(height, error):
    cases: list[Case] = []
    _margin_case(cases, "observer-positive", _initial(), _command(DEPOSIT, 1, 1), 1)
    expected = cases[0][2]
    _assert_same_observation(expected, deepcopy(expected), "unchanged observation")
    actual = deepcopy(expected)
    state = actual["state"]
    assert isinstance(state, dict)
    state["height"] = height
    with pytest.raises(error):
        _assert_same_observation(actual, expected, "output corruption, not a Rust mutant")


def test_python_rust_connected_margin_transfer_refill_and_close(rust_margin_binary):
    cases: list[Case] = []
    inputs = _initial()
    for amount, nonce, kind in ((40, 1, DEPOSIT), (10, 2, WITHDRAW), (30, 3, WITHDRAW)):
        inputs = _margin_case(cases, f"first-episode-{nonce}", inputs, _command(kind, amount, nonce), nonce)
    first_claim = inputs[2].terminal_obligations[0]
    assert first_claim.amount_atoms == 30 and first_claim.status.value == "DRAINED"
    inputs = _transfer_case(cases, inputs)
    for amount, nonce, kind in ((20, 4, DEPOSIT), (20, 5, WITHDRAW), (0, 6, CLOSE)):
        inputs = _margin_case(cases, f"second-episode-{nonce}", inputs, _command(kind, amount, nonce), nonce + 1)
    assert first_claim in inputs[2].terminal_obligations
    assert len(inputs[2].terminal_obligations) == 2
    _margin_case(cases, "closed-account-cannot-reopen", inputs, _command(DEPOSIT, 1, 7), 8, "ACCOUNT_CLOSED")
    assert len(cases) == 8
    _compare(rust_margin_binary, cases)


def test_python_rust_same_owner_accounts_and_exact_replay(rust_margin_binary):
    cases: list[Case] = []
    inputs = _margin_case(cases, "deposit-a", _initial(), _command(DEPOSIT, 25, 1), 1)
    inputs = _margin_case(cases, "deposit-b-own-nonce-one", inputs, _command(DEPOSIT, 25, 1, "margin-b"), 2)
    assert len({row.obligation_id for row in inputs[1].active_claims}) == 2
    assert inputs[2].liabilities[0].amount_atoms == 50
    withdraw = _command(WITHDRAW, 25, 2)
    _margin_case(cases, "replay-valid-account-nonce-current-head", inputs, withdraw, 2, "REPLAY_ALREADY_CONSUMED")
    inputs = _margin_case(cases, "drain-a", inputs, withdraw, 3)
    assert inputs[1].claim_id("margin-b") is not None
    assert inputs[2].liabilities[0].amount_atoms == 25
    inputs = _margin_case(cases, "refill-a-fresh-claim", inputs, _command(DEPOSIT, 7, 3), 4)
    _margin_case(cases, "drain-b", inputs, _command(WITHDRAW, 25, 2, "margin-b"), 5)
    assert len(cases) == 6
    _compare(rust_margin_binary, cases)


def test_python_rust_ordered_rejections_and_finite_width_edges(rust_margin_binary):
    cases: list[Case] = []
    inputs = _initial()
    command = _command(DEPOSIT, 1, 1)
    occurrence = _occurrence(inputs[2], command, 1)
    for field, value, code in (
        ("pre_state_root", _root("stale"), "OCCURRENCE_CONTEXT_MISMATCH"),
        ("chain_id", "foreign-chain", "OCCURRENCE_CONTEXT_MISMATCH"),
        ("profile_root", _root("wrong-profile"), "OCCURRENCE_CONTEXT_MISMATCH"),
        ("command_body_hash", _root("wrong-body"), "OCCURRENCE_COMMAND_MISMATCH"),
        ("consumed_object_ids", ("foreign-object",), "OCCURRENCE_COMMAND_MISMATCH"),
        ("subject_id", "mallory", "UNAUTHORIZED_SUBJECT"),
    ):
        _margin_case(cases, field, inputs, command, 1, code,
                     occurrence=replace(occurrence, **{field: value}))
    for amount, code in ((0, "ZERO_AMOUNT"), (101, "INSUFFICIENT_BALANCE"),
                         (2**127, "EFFECT_DELTA_OVERFLOW"), (2**128 - 1, "EFFECT_DELTA_OVERFLOW")):
        _margin_case(cases, f"deposit-{amount}", inputs, _command(DEPOSIT, amount, 1), 1, code)
    state = replace(inputs[2], height=2**64 - 1)
    for height in (0, 2**64 - 2, 2**64 - 1):
        bounded_occurrence = replace(occurrence, height=height, pre_state_root=state.state_root,
                                     command_body_hash=_root("wrong-body"))
        _margin_case(cases, f"maximum-height-{height}", (inputs[0], inputs[1], state), command, 1,
                     "OCCURRENCE_CONTEXT_MISMATCH", occurrence=bounded_occurrence)
    # Actual production balance-row bound, with all complete physical rows retained.
    deposited = _margin_case(cases, "one-atom-deposit", inputs, command, 1)
    full = _full_asset_balance_inputs(deposited)
    _margin_case(cases, "4096-balances-absent-withdrawal-row", full, _command(WITHDRAW, 1, 2), 2,
                 "SUCCESSOR_REJECTED")
    assert len(cases) == 15
    _compare(rust_margin_binary, cases)


def test_python_rust_oracle_maintenance_and_market_lifecycle(rust_margin_binary):
    cases: list[Case] = []
    inputs = _nonflat_inputs()
    oracle = PerpsMarginOracleV2(_root("authority"), _root("oracle"), 1)
    for amount, value, code in (
        (24, oracle, None), (24, None, "ORACLE_AUTHORITY_MISSING"),
        (24, replace(oracle, price_e8=2), "ORACLE_PRICE_MISMATCH"),
        (25, oracle, "MAINTENANCE_BREACH"),
    ):
        _margin_case(cases, f"oracle-{amount}-{code}", inputs,
                     _command(WITHDRAW, amount, 2, "perps-account-1"), 2, code, oracle=value)
    flat = _margin_case(cases, "flat-deposit", _initial(), _command(DEPOSIT, 5, 1), 1)
    for status, kind, amount, code in (
        (PerpsMarginMarketStatusV1.DRAIN_ONLY, WITHDRAW, 5, None),
        (PerpsMarginMarketStatusV1.DRAIN_ONLY, DEPOSIT, 1, "MARKET_DRAIN_ONLY"),
        (PerpsMarginMarketStatusV1.HALTED, WITHDRAW, 5, "HALTED_MARKET"),
    ):
        assets, margin, state = flat
        successor_margin = PerpsMarginStateV2(replace(margin.economic_state, market_status=status), margin.active_claims)
        roots = tuple(replace(row, state_root=successor_margin.state_root)
                      if row.lane_id is LaneIdV2.PERPS_MARKET else row for row in state.lane_roots)
        _margin_case(cases, status.value + kind, (assets, successor_margin, replace(state, lane_roots=roots)),
                     _command(kind, amount, 2), 2, code)
    assert len(cases) == 8
    _compare(rust_margin_binary, cases)


def test_parity_transport_rejects_unknown_outer_fields_and_oversized_lines(rust_margin_binary):
    # This is a bound on a test tool, not production wire-decoding assurance.
    cases: list[Case] = []
    _margin_case(cases, "fixture", _initial(), _command(DEPOSIT, 1, 1), 1)
    wire = {**cases[0][1], "extra": 1}
    for payload in (json.dumps(wire) + "\n", "x" * (4 * 1024**2 + 1)):
        result = subprocess.run([str(rust_margin_binary)], input=payload, capture_output=True,
                                text=True, timeout=15, check=False)
        output = json.loads(result.stdout)
        assert output["kind"] == "error"


@pytest.mark.parametrize("part_index", range(4))
@pytest.mark.parametrize("mutation", ("whitespace", "unknown", "duplicate", "v1-schema"))
def test_python_rust_exact_frame_rejects_noncanonical_components(rust_margin_binary, part_index, mutation):
    inputs = _initial()
    command = _command(DEPOSIT, 1, 1)
    request = PerpsMarginRequestV2(command, _occurrence(inputs[2], command, 1))
    frame = encode_perps_margin_frame_v2(*inputs, request)
    parts = list(_frame_parts(frame))
    payload = json.loads(parts[part_index])
    if mutation == "whitespace":
        parts[part_index] += b" "
    elif mutation == "duplicate":
        key = next(iter(payload))
        duplicate = canonical_global_bytes_v2({key: payload[key]})[1:-1]
        parts[part_index] = parts[part_index][:-1] + b"," + duplicate + b"}"
    else:
        if mutation == "unknown":
            payload["extra"] = 1
        else:
            payload["schema"] = payload["schema"].replace("/v2", "/v1")
        parts[part_index] = canonical_global_bytes_v2(payload)
    _compare_frame(rust_margin_binary, _frame_from_parts(tuple(parts)), False, (part_index, mutation))


def test_python_rust_frame_bounds_and_scalar_types(rust_margin_binary):
    inputs = _initial()
    command = _command(DEPOSIT, 1, 1)
    request = PerpsMarginRequestV2(command, _occurrence(inputs[2], command, 1))
    frame = encode_perps_margin_frame_v2(*inputs, request)
    malformed = [b"", frame[:6], frame[:-1], frame + b"x", b"ZDPM1\0" + frame[6:],
                 b"x" * (MAX_PERPS_MARGIN_FRAME_BYTES_V2 + 1)]
    for size in (0, MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2 + 1, 2**32 - 1):
        malformed.append(frame[:6] + size.to_bytes(4, "little") + frame[10:])
    parts = _frame_parts(frame)
    for value in (True, -1, 2**128):
        payload = json.loads(parts[3])
        payload["command"]["amount_atoms"] = value
        malformed.append(_frame_from_parts((*parts[:3], canonical_global_bytes_v2(payload))))
    for raw_value in (b"1.0", b"1e0"):
        raw = parts[3].replace(b'"amount_atoms":1', b'"amount_atoms":' + raw_value, 1)
        malformed.append(_frame_from_parts((*parts[:3], raw)))
    payload = json.loads(parts[3])
    del payload["oracle"]
    malformed.append(_frame_from_parts((*parts[:3], canonical_global_bytes_v2(payload))))
    for index, value in enumerate(malformed):
        _compare_frame(rust_margin_binary, value, False, index)


@pytest.mark.parametrize("history_count", (2251, 2252))
def test_python_rust_frame_successor_byte_closure_and_terminal_neighbor(rust_margin_binary, history_count):
    inputs = _inputs_with_terminal_history(history_count)
    command = _command(DEPOSIT, 1, 1)
    request = PerpsMarginRequestV2(command, _occurrence(inputs[2], command, 1))
    frame = encode_perps_margin_frame_v2(*inputs, request)
    accepted = history_count == 2251
    result = _compare_frame(rust_margin_binary, frame, accepted, history_count)
    if not accepted:
        assert result.stderr.endswith(b"SuccessorTooLarge\n")
        return
    deposited = replay_perps_margin_frame_v2(frame).result
    inputs = deposited.post_assets, deposited.post_margin, deposited.post_state
    command = _command(WITHDRAW, 1, 2)
    request = PerpsMarginRequestV2(command, _occurrence(inputs[2], command, 2))
    _compare_frame(rust_margin_binary, encode_perps_margin_frame_v2(*inputs, request), True, "terminal-neighbor")
