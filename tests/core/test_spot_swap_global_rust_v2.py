"""Complete native Spot correspondence, with independent economic observations.

These tests compare canonical successor values, effects and roots. They do not
qualify a guest, cryptographic receipt, authentication or publication authority.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from copy import deepcopy
from dataclasses import fields, replace
from itertools import product
from pathlib import Path

import pytest

from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
)
from src.core.spot_swap_global_v2 import (
    SpotSwapGlobalAcceptedV2,
    SpotSwapGlobalRejectedV2,
    transition_spot_swap_global_v2,
)
from src.core.spot_swap_state_v2 import SpotIntentNonceV2, SpotLPPositionV2, SpotSwapStateV2
from src.kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.state.pools import PoolStatus, compute_pool_id
from tests.core.test_asset_lane_coordinator_v2 import _registry, _root
from tests.core.test_spot_swap_global_v2 import (
    command,
    initial,
    occurrence,
    transfer,
    with_spot_root,
)
from tests.core.test_spot_swap_state_v2 import ALICE, BOB, CAROL, MALLORY

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "zk" / "spot_swap_global_v2" / "Cargo.toml"
Case = tuple[str, dict, dict]


@pytest.fixture(scope="module")
def rust_spot_binary() -> Path:
    target = Path(os.environ.get("CARGO_TARGET_DIR", str(
        Path(tempfile.gettempdir()) / "zenodex-spot-swap-global-v2-target")))
    parent = target if target.exists() else target.parent
    if shutil.disk_usage(parent).free < 4 * 1024**3:
        pytest.skip("disk guard: four GiB required; native Spot parity remains unqualified")
    result = subprocess.run(
        ["cargo", "build", "--offline", "--locked", "--manifest-path", str(MANIFEST),
         "--examples", "-j", "2"],
        cwd=ROOT, env={**os.environ, "CARGO_TARGET_DIR": str(target)},
        capture_output=True, text=True, timeout=180, check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert sum(p.stat().st_size for p in target.rglob("*") if p.is_file()) <= 1024**3
    binary = target / "debug" / "examples" / "parity"
    assert binary.is_file()
    return binary


@pytest.fixture(scope="module")
def rust_mutant_target(rust_spot_binary):
    # Share dependency compilation within this run, then remove only this
    # fixture's own regeneratable directory. No stale cache grows across runs.
    with tempfile.TemporaryDirectory(prefix="semantic-mutants-", dir=rust_spot_binary.parents[2]) as target:
        yield Path(target)


def _json(value):
    return json.loads(canonical_global_bytes_v2(value))


def _unique_object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate native output key: {key}")
        value[key] = item
    return value


def _outputs(stdout):
    assert stdout.endswith("\n"), "native JSON-lines response must end at a record boundary"
    return [json.loads(line, object_pairs_hook=_unique_object) for line in stdout[:-1].split("\n")]


def _case(cases, label, inputs, cmd, outer_nonce=1, *, occ=None, timestamp=100, code=None):
    assets, spot, state = inputs
    occ = occurrence(state, cmd, outer_nonce) if occ is None else occ
    # Retain unsupported fields too: the command-body helper deliberately
    # refuses those, whereas the transition must produce its typed rejection.
    body = {f.name: cmd.to_wire_fields() if f.name == "fields" else getattr(cmd, f.name)
            for f in fields(cmd)}
    wire = _json(dict(assets=assets, spot=spot, state=state, intent=body,
                      occurrence=occ, block_timestamp=timestamp))
    before = canonical_global_bytes_v2(inputs)
    result = transition_spot_swap_global_v2(*inputs, cmd, occ, timestamp)
    assert canonical_global_bytes_v2(inputs) == before, label
    if type(result) is SpotSwapGlobalAcceptedV2:
        assert code is None, label
        assert result.refinement.production_authority == "NONE"
        assert result.post_spot.lp_positions == spot.lp_positions
        assert result.post_state.terminal_obligations == state.terminal_obligations
        assert result.post_state.liabilities == state.liabilities
        assert result.post_state.supplies == state.supplies
        expected = _json(dict(status="accepted", post_assets=result.post_assets,
            post_spot=result.post_spot, post_state=result.post_state, effects=result.effects,
            statement_root=result.statement_root, refinement_root=result.refinement.refinement_root))
        successor = result.post_assets, result.post_spot, result.post_state
    else:
        assert type(result) is SpotSwapGlobalRejectedV2, (label, result)
        assert result.code.value == code, (label, result.code, code)
        assert result.pre_state_root == result.post_state_root == state.state_root
        assert result.effects.is_empty
        expected = _json(dict(status="rejected", code=code, pre_state_root=state.state_root,
                             post_state_root=state.state_root, effects=result.effects))
        successor = inputs
    cases.append((label, wire, expected))
    return successor


def _compare(binary, cases):
    payload = "".join(json.dumps(wire, ensure_ascii=False, separators=(",", ":")) + "\n"
                      for _, wire, _ in cases)
    completed = subprocess.run([str(binary)], input=payload, capture_output=True,
                               encoding="utf-8", timeout=60, check=False)
    assert completed.returncode == 0, completed.stderr
    outputs = _outputs(completed.stdout)
    assert len(outputs) == len(cases)
    for (label, _, expected), actual in zip(cases, outputs, strict=True):
        # Python == conflates True, 1 and 1.0. Compare canonical typed bytes.
        if canonical_global_bytes_v2(actual) != canonical_global_bytes_v2(expected):
            raise AssertionError((label, actual, expected))


def _output(reserve_in, reserve_out, fee, gross):
    net = gross - (gross * fee + 9999) // 10000
    return reserve_out * net // (reserve_in + net)


def _minimum_gross(reserve_in, reserve_out, fee, wanted):
    # Independent monotone search over the full admitted gross-input domain;
    # production instead uses a closed-form inverse of the fee and curve.
    low, high = 1, 3_000_000_000
    if _output(reserve_in, reserve_out, fee, high) < wanted:
        return None
    while low < high:
        middle = (low + high) // 2
        if _output(reserve_in, reserve_out, fee, middle) >= wanted:
            high = middle
        else:
            low = middle + 1
    assert _output(reserve_in, reserve_out, fee, low) >= wanted
    assert low == 1 or _output(reserve_in, reserve_out, fee, low - 1) < wanted
    return low


def _economic_expectation(reserve_in, reserve_out, fee, amount, exact_out):
    gross = _minimum_gross(reserve_in, reserve_out, fee, amount) if exact_out else amount
    if gross is None:
        return None, 0, "QUOTE_REJECTED"
    quote = _output(reserve_in, reserve_out, fee, gross)
    gap = ((quote - amount) * 10000 + amount - 1) // amount if exact_out else 0
    if quote <= 0 or gap > 200 or reserve_in + gross > 3_000_000_000:
        return gross, quote, "QUOTE_REJECTED"
    if exact_out and gross > 1001:
        return gross, quote, "SLIPPAGE_LIMIT"
    if gross > 1000:
        return gross, quote, "INSUFFICIENT_BALANCE"
    return gross, amount if exact_out else quote, None


def _check_economic_success(observed, spot, reverse, gross, output, fee_bps):
    asset_in, asset_out = ("B", "A") if reverse else ("A", "B")
    fee = (gross * fee_bps + 9999) // 10000
    expected = {
        ("ACCOUNT_MOVEMENT", ALICE, asset_in, "accounts", -gross),
        ("ACCOUNT_MOVEMENT", BOB, asset_out, "accounts", output),
        ("CUSTODY", spot.pool.pool_id, asset_in, "spot_pool", gross),
        ("CUSTODY", spot.pool.pool_id, asset_out, "spot_pool", -output),
    }
    if fee:
        expected.add(("FEE_ALLOCATION", spot.pool.pool_id, asset_in, "spot_pool", fee))
    assert sorted(tuple(row[key] for key in ("kind", "principal", "asset", "custody_domain", "delta_atoms"))
                  for row in observed["effects"]["rows"]) == sorted(expected)
    pool = observed["post_spot"]["pool"]
    assert (pool["reserve0"], pool["reserve1"]) == (
        (spot.pool.reserve0 - output, spot.pool.reserve1 + gross) if reverse else
        (spot.pool.reserve0 + gross, spot.pool.reserve1 - output))
    expected_balances = {(ALICE, asset_in): 1000 - gross, (ALICE, asset_out): 1000, (BOB, asset_out): output}
    assert {(row["owner"], row["asset"]): row["amount_atoms"] for row in observed["post_state"]["balances"]} == {
        key: amount for key, amount in expected_balances.items() if amount}


def _economic_cases():
    cases: list[Case] = []
    for fee in (0, 1, 30, 1000, 9999, 10000):
        for reverse in (False, True):
            for exact_out in (False, True):
                for amount in (1, 2, 7, 999, 1000, 1001):
                    inputs = initial(fee_bps=fee)
                    reserve_in, reserve_out = (20_000, 10_000) if reverse else (10_000, 20_000)
                    amounts = dict(amount_out=amount, max_amount_in=1001) if exact_out else dict(
                        amount_in=amount, min_amount_out=0)
                    cmd = command(inputs[1], exact_out=exact_out, reverse=reverse, recipient=BOB, **amounts)
                    gross, output, code = _economic_expectation(reserve_in, reserve_out, fee, amount, exact_out)
                    _case(cases, f"math-{fee}-{reverse}-{exact_out}-{amount}", inputs, cmd, code=code)
                    if code is None:
                        _check_economic_success(cases[-1][2], inputs[1], reverse, gross, output, fee)
    outcomes = [expected.get("code", "accepted") for _, _, expected in cases]
    assert {code: outcomes.count(code) for code in set(outcomes)} == {
        "accepted": 61, "QUOTE_REJECTED": 52, "SLIPPAGE_LIMIT": 23, "INSUFFICIENT_BALANCE": 8}
    return cases


def _guard_cases():
    cases: list[Case] = []
    inputs = initial()
    cmd = command(inputs[1])
    good = occurrence(inputs[2], cmd, 1)
    for field, value in (("chain_id", "wrong"), ("deployment_root", _root("wrong")),
                         ("profile_root", _root("wrong")), ("pre_state_root", _root("wrong")), ("height", 2)):
        _case(cases, field, inputs, cmd, occ=replace(good, **{field: value}), code="OCCURRENCE_CONTEXT_MISMATCH")
    for field, value in (("command_body_hash", _root("wrong")), ("command_kind", "wrong"),
                         ("consumed_object_ids", (_root("object"),))):
        _case(cases, field, inputs, cmd, occ=replace(good, **{field: value}), code="OCCURRENCE_COMMAND_MISMATCH")
    _case(cases, "conserving-foreign-subject", inputs, cmd,
          occ=replace(good, subject_id=MALLORY), code="SUBJECT_MISMATCH")
    for updates, code in ((dict(nonce=0), "INVALID_NONCE"), (dict(nonce=2), "INVALID_NONCE"),
                          (dict(pool_id="wrong"), "POOL_MISMATCH"), (dict(asset_out="A"), "ASSET_MISMATCH"),
                          (dict(max_amount_in=1), "SLIPPAGE_LIMIT")):
        _case(cases, str(updates), inputs, replace(cmd, fields={**dict(cmd.fields), **updates}), code=code)
    _case(cases, "expired", inputs, cmd, timestamp=101, code="EXPIRED")
    _case(cases, "boundary-time", inputs, cmd, timestamp=99)
    _case(cases, "unicode-salt-at-character-limit", inputs, replace(cmd, salt="\u00e9" * 4096))
    _case(cases, "salt-json-escaping", inputs, replace(cmd, salt='"\\\n\x1f\x7f\u2028\U0001f642'))
    _case(cases, "u64-deadline-and-time", inputs, replace(cmd, deadline=(1 << 64) - 1), timestamp=(1 << 64) - 1)
    _case(cases, "unknown-fields-before-wrong-context", inputs, command(inputs[1], foreign="value"),
          occ=replace(good, chain_id="wrong"), code="UNSUPPORTED_FIELDS")
    for value in (True, {"nested": [True]}):
        _case(cases, f"foreign-nonscalar-{value}", inputs, command(inputs[1], foreign=value),
              occ=good, code="UNSUPPORTED_FIELDS")
    for metadata in (dict(intent_id=_root("new-intent")), dict(salt="different"), dict(deadline=101)):
        _case(cases, str(metadata), inputs, replace(cmd, **metadata), occ=good, code="OCCURRENCE_COMMAND_MISMATCH")
    assets, spot, state = inputs
    for status in (PoolStatus.FROZEN, PoolStatus.DISABLED):
        changed = SpotSwapStateV2(spot.module_release_id, replace(spot.pool, status=status), spot.lp_positions)
        _case(cases, status.value, (assets, changed, with_spot_root(state, changed)), cmd, code="POOL_INACTIVE")
    for field, value in (("owner", MALLORY), ("last_remove_timestamp", 99)):
        rows = spot.lp_positions
        changed = SpotSwapStateV2(spot.module_release_id, spot.pool, tuple(sorted(
            (rows[0], replace(rows[1], **{field: value}), rows[2]), key=lambda row: row.owner)))
        _case(cases, "uncommitted-lp-" + field, (assets, changed, state), cmd, code="PROJECTION_MISMATCH")
    for defect in ("disabled", "transfer-fee", "origin"):
        leaf = assets.transfer_state
        change = dict(enabled=False) if defect == "disabled" else dict(transfer_fee_atoms=1)
        policies = leaf.policies if defect == "origin" else (replace(leaf.policies[0], **change), leaf.policies[1])
        registry = _registry(policies, (), drift_transfer_asset="A" if defect == "origin" else None)
        changed = AssetLaneCustodyStateV2(AssetTransferStateV2(leaf.module_release_id, policies,
            leaf.balances, leaf.supplies), registry, (), assets.custody)
        global_state = replace(state, lane_roots=tuple(replace(row, state_root=changed.state_root)
            if row.lane_id is LaneIdV2.ASSET_TRANSFER else row for row in state.lane_roots))
        _case(cases, defect, (changed, spot, global_state), cmd,
              code="ASSET_ORIGIN_MISMATCH" if defect == "origin" else "UNSUPPORTED_ASSET_POLICY")
    pool = replace(spot.pool, curve_tag="UNSUPPORTED", pool_id=compute_pool_id(
        spot.pool.asset0, spot.pool.asset1, spot.pool.fee_bps,
        curve_tag="UNSUPPORTED", curve_params=spot.pool.curve_params))
    changed_spot = SpotSwapStateV2(spot.module_release_id, pool, spot.lp_positions)
    custody = tuple(sorted((replace(row, owner=pool.pool_id)
        if row.owner == spot.pool.pool_id and row.custody_domain == "spot_pool" else row
        for row in assets.custody), key=lambda row: row.key))
    changed = AssetLaneCustodyStateV2(assets.transfer_state, assets.origin_registry,
                                    assets.managed_policies, custody)
    global_state = with_spot_root(state, changed_spot)
    global_state = replace(global_state, custody=custody, lane_roots=tuple(
        replace(row, state_root=changed.state_root) if row.lane_id is LaneIdV2.ASSET_TRANSFER else row
        for row in global_state.lane_roots))
    _case(cases, "unsupported-curve-with-complete-projection", (changed, changed_spot, global_state),
          command(changed_spot), code="UNSUPPORTED_CURVE")
    return cases


def _history_cases():
    cases: list[Case] = []
    assets, spot, state = initial()
    state = replace(state, liabilities=(EconomicAmountV2(CAROL, "A", "escrow", 20),),
        terminal_obligations=(TerminalObligationV2("carol-claim", LaneIdV2.STRATEGY_ESCROW,
            CAROL, "A", "escrow", 20, TerminalObligationStatusV2.OPEN),))
    inputs = transfer((assets, spot, state), 1)
    for inner, outer, reverse in ((1, 2, False), (2, 4, True), (3, 6, False)):
        cmd = command(inputs[1], nonce=inner, reverse=reverse, amount_out=100, max_amount_in=250)
        inputs = _case(cases, f"swap-{inner}", inputs, cmd, outer)
        retry = command(inputs[1], nonce=inner + 1, amount_out=100, max_amount_in=250)
        _case(cases, f"outer-replay-{inner}", inputs, retry, outer, code="REPLAY_ALREADY_CONSUMED")
        _case(cases, f"inner-replay-{inner}", inputs, cmd, outer + 1, code="INVALID_NONCE")
        inputs = transfer(inputs, outer + 1)
    return cases


def _intent_boundary_cases():
    cases: list[Case] = []
    inputs = initial()
    cmd = command(inputs[1])
    for nonce in ("1", -1, 1 << 32, (1 << 256) - 1):
        _case(cases, f"nonce-{nonce}", inputs, command(inputs[1], nonce=nonce), code="INVALID_NONCE")
    _case(cases, "missing-nonce", inputs, replace(cmd, fields={
        key: value for key, value in cmd.fields.items() if key != "nonce"}), code="INVALID_NONCE")
    _case(cases, "u256-maximum-slippage-bound", inputs, command(inputs[1], max_amount_in=(1 << 256) - 1))
    _case(cases, "u256-minimum-unreachable", inputs, command(inputs[1], exact_out=False,
        min_amount_out=(1 << 256) - 1), code="SLIPPAGE_LIMIT")
    for amount in (1 << 64, 1 << 128):
        _case(cases, f"amount-over-domain-{amount}", inputs, command(inputs[1], exact_out=False,
            amount_in=amount), code="QUOTE_REJECTED")
    for limit, code in ((17, None), (18, "SLIPPAGE_LIMIT")):
        _case(cases, f"exact-in-slippage-{limit}", inputs,
              command(inputs[1], exact_out=False, amount_in=10, min_amount_out=limit), code=code)
    for limit, code in ((5, None), (4, "SLIPPAGE_LIMIT")):
        _case(cases, f"exact-out-slippage-{limit}", inputs, command(inputs[1], max_amount_in=limit), code=code)
    good = occurrence(inputs[2], cmd, 1)
    _case(cases, "all-occurrence-fields", inputs, cmd, occ=replace(good, tx_index=(1 << 64) - 1,
        op_index=17, route_release_id=_root("different-route"), grant_root=_root("different-grant")))
    _case(cases, "context-before-recipient-alias", inputs, command(inputs[1], recipient=BOB.upper()),
          occ=replace(good, chain_id="wrong"), code="OCCURRENCE_CONTEXT_MISMATCH")
    _case(cases, "subject-before-expiry", inputs, cmd, timestamp=101,
          occ=replace(good, subject_id=MALLORY), code="SUBJECT_MISMATCH")
    _case(cases, "slippage-before-sequence-nonce", inputs,
          command(inputs[1], nonce=2, max_amount_in=1), code="SLIPPAGE_LIMIT")
    assets, spot, state = inputs
    spot = SpotSwapStateV2(spot.module_release_id, spot.pool, spot.lp_positions, (SpotIntentNonceV2(MALLORY, 1),))
    _case(cases, "insert-nonce-before-existing-owner", (assets, spot, with_spot_root(state, spot)), command(spot))
    return cases


def _capacity_cases():
    cases: list[Case] = []
    assets, spot, state = initial()
    nonces = tuple(SpotIntentNonceV2("0x" + f"{i:096x}", 1) for i in range(4096))
    for label, rows, nonce, code in (
        ("new-owner-at-capacity", nonces, 1, "SUCCESSOR_REJECTED"),
        ("existing-owner-at-capacity", (*nonces[1:], SpotIntentNonceV2(ALICE, 1)), 2, None),
        ("nonce-exhausted", (SpotIntentNonceV2(ALICE, (1 << 32) - 1),), (1 << 32) - 1, "INVALID_NONCE"),
        ("nonce-successor-out-of-domain", (SpotIntentNonceV2(ALICE, (1 << 32) - 1),), 1 << 32, "INVALID_NONCE"),
    ):
        changed = SpotSwapStateV2(spot.module_release_id, spot.pool, spot.lp_positions, rows)
        _case(cases, label, (assets, changed, with_spot_root(state, changed)), command(changed, nonce=nonce), code=code)
    # Global supply can represent the u128 maximum. A recipient near that
    # bound must still preserve exact integer bytes and a conserving success.
    maximum = (1 << 128) - 1
    leaf = assets.transfer_state
    balances = (*leaf.balances, EconomicAmountV2(BOB, "B", "accounts", maximum - 21_000))
    supplies = (leaf.supplies[0], AssetSupplyV2("B", maximum))
    assets = AssetLaneCustodyStateV2(AssetTransferStateV2(leaf.module_release_id, leaf.policies,
        balances, supplies), assets.origin_registry, assets.managed_policies, assets.custody)
    state = replace(state, balances=balances, supplies=supplies, lane_roots=tuple(
        replace(row, state_root=assets.state_root) if row.lane_id is LaneIdV2.ASSET_TRANSFER else row
        for row in state.lane_roots))
    _case(cases, "u128-supply-and-recipient", (assets, spot, state), command(spot, recipient=BOB))
    return cases


def _balance_capacity_cases():
    cases: list[Case] = []
    assets, spot, state = initial()
    leaf = assets.transfer_state
    balances = tuple(sorted((*leaf.balances, *(
        EconomicAmountV2("0x" + f"{i:096x}", "A", "accounts", 1) for i in range(4094)
    )), key=lambda row: row.key))
    supplies = (replace(leaf.supplies[0], amount_atoms=leaf.supplies[0].amount_atoms + 4094), leaf.supplies[1])
    assets = AssetLaneCustodyStateV2(AssetTransferStateV2(leaf.module_release_id, leaf.policies,
        balances, supplies), assets.origin_registry, assets.managed_policies, assets.custody)
    state = replace(state, balances=balances, supplies=supplies, lane_roots=tuple(
        replace(row, state_root=assets.state_root) if row.lane_id is LaneIdV2.ASSET_TRANSFER else row
        for row in state.lane_roots))
    for amount, code in ((10, "SUCCESSOR_REJECTED"), (1000, None)):
        # Draining the sender removes its row before the new recipient is added.
        # A transient insertion-count check would reject this valid successor.
        cmd = command(spot, exact_out=False, amount_in=amount, min_amount_out=1, recipient=BOB)
        post = _case(cases, f"balance-capacity-debit-{amount}", (assets, spot, state), cmd, code=code)
        assert len(post[2].balances) == 4096
        if code is None:
            holdings = {(row.owner, row.asset): row.amount_atoms for row in post[2].balances}
            assert (ALICE, "A") not in holdings
            assert holdings[BOB, "B"] == _output(10_000, 20_000, 30, amount)
    return cases


def _byte_capacity_cases():
    cases: list[Case] = []
    assets, spot, state = initial()
    positions = tuple(sorted((*spot.lp_positions, *(
        SpotLPPositionV2("0x" + f"{i:096x}", 0) for i in range(1, 4094)
    )), key=lambda row: row.owner))
    empty_size = len(canonical_global_bytes_v2(dict(spot.to_canonical(), lp_positions=positions)))
    nonce = SpotIntentNonceV2("0x" + f"{1:096x}", 1)
    stride = len(canonical_global_bytes_v2(nonce)) + 1
    ceiling = 1_048_576
    maximum_count = (ceiling - empty_size + 1) // stride
    for count, code in ((maximum_count - 1, None), (maximum_count, "SUCCESSOR_REJECTED")):
        nonces = tuple(SpotIntentNonceV2("0x" + f"{i:096x}", 1) for i in range(1, count + 1))
        changed = SpotSwapStateV2(spot.module_release_id, spot.pool, positions, nonces)
        pre_size = len(canonical_global_bytes_v2(changed))
        assert pre_size <= ceiling and len(nonces) + 1 < 4096
        # The new sender nonce adds one fixed-width row. This isolates the
        # byte ceiling from row capacity, economics and nonce exhaustion.
        assert (pre_size + stride > ceiling) == (code is not None)
        post = _case(cases, f"byte-capacity-{pre_size}",
                     (assets, changed, with_spot_root(state, changed)), command(changed), code=code)
        if code is None:
            assert len(canonical_global_bytes_v2(post[1])) == pre_size + stride
    return cases


def _reserve_boundary_cases():
    cases: list[Case] = []
    for reserve0, reserve1, wanted, code in (
        (1000, 10_210_200, 10_000, None),  # gross 1 quotes 10200: gap exactly 200 bps.
        (1000, 10_211_201, 10_000, "QUOTE_REJECTED"),  # 10201: gap 201 bps.
        (2_999_999_998, 3_000_000_000, 1, None),
        (2_999_999_999, 3_000_000_000, 1, None),
        (3_000_000_000, 3_000_000_000, 1, "QUOTE_REJECTED"),
    ):
        assets, spot, state = initial(fee_bps=0)
        spot = SpotSwapStateV2(spot.module_release_id,
            replace(spot.pool, reserve0=reserve0, reserve1=reserve1), spot.lp_positions)
        holdings = dict(A=reserve0, B=reserve1)
        custody = tuple(replace(row, amount_atoms=holdings[row.asset])
            if row.custody_domain == "spot_pool" else row for row in assets.custody)
        leaf = assets.transfer_state
        supplies = (AssetSupplyV2("A", reserve0 + 1020), AssetSupplyV2("B", reserve1 + 1000))
        assets = AssetLaneCustodyStateV2(AssetTransferStateV2(leaf.module_release_id, leaf.policies,
            leaf.balances, supplies), assets.origin_registry, assets.managed_policies, custody)
        state = with_spot_root(state, spot)
        state = replace(state, custody=custody, supplies=supplies, lane_roots=tuple(
            replace(row, state_root=assets.state_root) if row.lane_id is LaneIdV2.ASSET_TRANSFER else row
            for row in state.lane_roots))
        post = _case(cases, f"reserves-{reserve0}-{reserve1}", (assets, spot, state),
                     command(spot, amount_out=wanted, max_amount_in=1000, recipient=BOB), code=code)
        if code is None:
            assert post[1].pool.reserve0 == reserve0 + 1
            assert post[1].pool.reserve1 == reserve1 - wanted
    return cases


@pytest.mark.parametrize("make_cases", [_economic_cases, _guard_cases, _history_cases, _capacity_cases,
                                       _balance_capacity_cases, _byte_capacity_cases,
                                       _reserve_boundary_cases, _intent_boundary_cases])
def test_python_rust_complete_spot_correspondence(rust_spot_binary, make_cases):
    _compare(rust_spot_binary, make_cases())


def test_parity_oracle_checks_required_success_reject_and_capacity_cases():
    # Runs without Cargo, making fixture/oracle failures distinct from a port
    # disagreement. The exact same cases feed the native correspondence check.
    assert len(_economic_cases()) == 144
    assert len(_guard_cases()) == 33
    assert len(_history_cases()) == 9
    assert len(_capacity_cases()) == 5
    assert len(_balance_capacity_cases()) == 2
    assert len(_byte_capacity_cases()) == 2
    assert len(_reserve_boundary_cases()) == 5
    assert len(_intent_boundary_cases()) == 18


def test_native_output_observer_preserves_unicode_records_and_rejects_duplicate_keys():
    assert _outputs('{"salt":"\u2028\x85"}\n') == [{"salt": "\u2028\x85"}]
    with pytest.raises(ValueError, match="duplicate native output key"):
        _outputs('{"post_state":{"height":1,"height":2}}\n')


def test_native_quote_arithmetic_matches_existing_kernel_on_bounded_grid_and_extremes(rust_spot_binary):
    domains = (range(1, 9), (0, 1, 2, 2_999_999_999, 3_000_000_000, 3_000_000_001))
    requests, expected = [], []
    for domain in domains:
        for reserve_in, reserve_out, amount, fee, exact_out in product(
                domain, domain, domain, (0, 1, 30, 1000, 9999, 10000), (False, True)):
            mode = "exact_out" if exact_out else "exact_in"
            requests.append(dict(mode=mode, reserve_in=reserve_in, reserve_out=reserve_out,
                                 amount=amount, fee_bps=fee))
            function = quote_cpmm_swap_exact_out if exact_out else quote_cpmm_swap_exact_in
            try:
                quote = function(reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee,
                                 **{"amount_out" if exact_out else "amount_in": amount})
            except ValueError:
                expected.append(None)
                continue
            gross, output = quote.amount_in, quote.amount_out
            # Independent forward arithmetic and predecessor minimality observe
            # more than Python/Rust agreement on the inverse formula.
            priced = _output(reserve_in, reserve_out, fee, gross)
            assert priced >= output and quote.fee_paid == (gross * fee + 9999) // 10000
            assert quote.k_after >= quote.k_before
            if exact_out:
                assert gross == 1 or _output(reserve_in, reserve_out, fee, gross - 1) < output
            else:
                assert priced == output
            expected.append(dict(status="quoted", mode=mode, amount_in=gross, amount_out=output,
                fee_paid=quote.fee_paid, net_in=quote.net_in_actual if exact_out else quote.net_in,
                reserve_in_after=quote.reserve_in_after, reserve_out_after=quote.reserve_out_after,
                k_before=quote.k_before, k_after=quote.k_after,
                amount_out_quote=quote.amount_out_quote if exact_out else output,
                overdelivery_gap_bps=quote.gap_bps if exact_out else 0))
    assert len(requests) == 8736
    result = subprocess.run([str(rust_spot_binary.with_name("quote"))],
        input="".join(json.dumps(row) + "\n" for row in requests),
        capture_output=True, encoding="utf-8", timeout=30, check=False)
    assert result.returncode == 0, result.stderr
    outputs = _outputs(result.stdout)
    assert len(outputs) == len(expected)
    for request, wanted, actual in zip(requests, expected, outputs, strict=True):
        if wanted is None:
            assert set(actual) == {"status", "reason"} and actual["status"] == "rejected", (request, actual)
        else:
            assert canonical_global_bytes_v2(actual) == canonical_global_bytes_v2(wanted), (request, actual, wanted)


@pytest.mark.parametrize("source,old,new,builder,label", [
    ("plan.rs", "if context.subject_id != intent.sender_pubkey() {",
     "if false && context.subject_id != intent.sender_pubkey() {",
     _guard_cases, "conserving-foreign-subject"),
    ("global.rs", "|| occurrence.command_body_hash != body_hash",
     "|| (false && occurrence.command_body_hash != body_hash)", _guard_cases, "command_body_hash"),
    ("global.rs", "if expected_nonce != Some(u64::from(plan.nonce())) {",
     "if false && expected_nonce != Some(u64::from(plan.nonce())) {", _history_cases, "inner-replay-1"),
    ("quote.rs", "ceil_div(checked_mul(gross_in, fee_bps)?, BPS_DENOM_V2)",
     "Ok(checked_mul(gross_in, fee_bps)? / BPS_DENOM_V2)", _economic_cases, "math-30-False-False-7"),
])
def test_native_semantic_mutants_are_detected(rust_spot_binary, rust_mutant_target, tmp_path,
                                            source, old, new, builder, label):
    cases = [row for row in builder() if row[0] == label]
    assert len(cases) == 1
    _compare(rust_spot_binary, cases)  # The unchanged control must pass first.
    candidate = tmp_path / "crate"
    shutil.copytree(MANIFEST.parent, candidate, ignore=shutil.ignore_patterns("target", ".git"))
    path = candidate / "src" / source
    original = path.read_text()
    assert original.count(old) == 1
    path.write_text(original.replace(old, new))
    manifest = candidate / "Cargo.toml"
    dependency = 'path = "../global_settlement_abi_v2"'
    manifest_text = manifest.read_text()
    assert manifest_text.count(dependency) == 1
    manifest.write_text(manifest_text.replace(dependency,
        "path = " + json.dumps(str(ROOT / "zk/global_settlement_abi_v2"))))
    target = rust_mutant_target
    result = subprocess.run(["cargo", "build", "--offline", "--locked", "--manifest-path",
        str(manifest), "--example", "parity", "-j", "2"],
        env={**os.environ, "CARGO_TARGET_DIR": str(target), "CARGO_INCREMENTAL": "0"}, capture_output=True,
        encoding="utf-8", timeout=180, check=False)
    assert result.returncode == 0, result.stdout + result.stderr  # Build errors never count as kills.
    assert sum(p.stat().st_size for p in target.rglob("*") if p.is_file()) <= 512 * 1024**2
    with pytest.raises(AssertionError) as detected:
        _compare(target / "debug/examples/parity", cases)
    assert detected.value.args[0][0] == label  # Require the intended semantic observation.


def _require_python_input_rejection(defect, inputs, wire):
    cmd = command(inputs[1])
    if defect in {"extra", "duplicate", "nested-duplicate", "escaped-duplicate"}:
        return  # Raw test-transport grammar has no typed Python equivalent.
    with pytest.raises((TypeError, ValueError)):
        if defect in {"float", "boolean", "negative", "oversized-integer", "number-object"}:
            transition_spot_swap_global_v2(*inputs, cmd, occurrence(inputs[2], cmd, 1), wire["block_timestamp"])
        elif defect in {"owner-alias", "lp-coverage"}:
            spot = inputs[1]
            SpotSwapStateV2(spot.module_release_id, spot.pool, tuple(
                SpotLPPositionV2(**row) for row in wire["spot"]["lp_positions"]))
        elif defect == "oversized-salt":
            replace(cmd, salt=wire["intent"]["salt"])
        elif defect in {"empty-field-key", "nested-nonce", "boolean-nonce"}:
            malformed = replace(cmd, fields=wire["intent"]["fields"])
            transition_spot_swap_global_v2(*inputs, malformed, occurrence(inputs[2], cmd, 1), 100)


@pytest.mark.parametrize("defect", ["extra", "duplicate", "nested-duplicate", "escaped-duplicate", "float", "boolean", "negative",
                                    "number-object", "nested-nonce", "boolean-nonce",
                                    "oversized-integer", "owner-alias", "lp-coverage", "oversized-salt", "empty-field-key"])
def test_native_decoder_rejects_malformed_inputs(rust_spot_binary, defect):
    cases: list[Case] = []
    inputs = initial()
    _case(cases, "positive", inputs, command(inputs[1]))
    wire = deepcopy(cases[0][1])
    if defect == "extra":
        wire["extra"] = 1
    elif defect in ("float", "boolean", "negative", "oversized-integer"):
        wire["block_timestamp"] = {"float": 100.0, "boolean": True, "negative": -1,
                                   "oversized-integer": 1 << 64}[defect]
    elif defect == "number-object":
        wire["block_timestamp"] = {"$serde_json::private::Number": "100"}
    elif defect in ("nested-nonce", "boolean-nonce"):
        wire["intent"]["fields"]["nonce"] = [] if defect == "nested-nonce" else True
    elif defect == "owner-alias":
        wire["spot"]["lp_positions"][1]["owner"] = "0x" + BOB[2:].upper()
    elif defect == "lp-coverage":
        wire["spot"]["lp_positions"][1]["shares"] += 1
    elif defect == "oversized-salt":
        wire["intent"]["salt"] = "\u00e9" * 4097
    elif defect == "empty-field-key":
        wire["intent"]["fields"][""] = 1
    _require_python_input_rejection(defect, inputs, wire)
    payload = json.dumps(wire, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    if defect == "duplicate":
        payload = payload.replace('"block_timestamp":100', '"block_timestamp":99,"block_timestamp":100')
    elif defect == "nested-duplicate":
        payload = payload.replace('"reserve0":10000', '"reserve0":9999,"reserve0":10000')
    elif defect == "escaped-duplicate":
        payload = payload.replace('"reserve0":10000', '"reserve\\u0030":9999,"reserve0":10000')
    positive = json.dumps(cases[0][1], ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    result = subprocess.run([str(rust_spot_binary)], input=payload + "\n" + positive + "\n",
                            capture_output=True, encoding="utf-8", timeout=15, check=False)
    assert result.returncode == 0, result.stderr
    outputs = _outputs(result.stdout)
    assert len(outputs) == 2
    observed = outputs[0]
    assert set(observed) == {"status", "code"} and observed["status"] == "input_error"
    assert type(observed["code"]) is str and observed["code"]
    assert canonical_global_bytes_v2(outputs[1]) == canonical_global_bytes_v2(cases[0][2])
