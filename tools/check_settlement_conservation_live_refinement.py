#!/usr/bin/env python3
# ruff: noqa: E402
"""Build/check the live-settlement conservation refinement receipt.

This receipt is the next balances-surface increment after
``Proofs.SettlementConservationLive``.  The Lean proof says every modeled
``AssetMove`` preserves ``balance + reserve`` for one asset.  This checker binds
the live Python settlement output to those constructors on a replayable corpus:
exact-in/out swaps, pool creation, add-liquidity, and remove-liquidity.

It intentionally does not flip any CBC registry column.  The receipt proves a
bounded refinement slice: live settlement deltas on the checked corpus match the
Lean constructor algebra.  A full balances proof_artifact flip still needs a
broader refinement review and matrix decision.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.core.batch_clearing import apply_settlement, compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import BalanceDelta, ReserveDelta, Settlement
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState

DEFAULT_RECEIPT = ROOT / "docs" / "assurance" / "settlement_conservation_live_refinement_receipt.json"

RECEIPT_SCHEMA = "zenodex.balances.live_settlement_conservation_refinement.v1"
CHECK_SCHEMA = "zenodex.balances.live_settlement_conservation_refinement_check.v1"
LEAN_MODULE = "Proofs.SettlementConservationLive"

A0 = "0x" + "01" * 32
A1 = "0x" + "02" * 32
PK = "0x" + "11" * 48
PK2 = "0x" + "12" * 48
FEE_RECIP = "0x" + "22" * 48
LP_LOCK = "0x" + "00" * 48

SOURCE_FILES = [
    "tools/check_settlement_conservation_live_refinement.py",
    "tests/test_check_settlement_conservation_live_refinement.py",
    "tests/runtime/test_settlement_conservation_live_binding.py",
    "tests/formal/test_lean_settlement_conservation_live.py",
    "lean-mathlib/Proofs/SettlementConservationLive.lean",
    "lean-mathlib/proof_receipts/settlement_conservation_live_v1.json",
    "src/core/batch_clearing.py",
    "src/core/settlement_strong_validator.py",
    "src/core/settlement.py",
    "src/core/liquidity.py",
]

EXPECTED_CLAIM = (
    "Bounded refinement: live Python settlement deltas in the checked corpus instantiate "
    "the Lean AssetMove constructors and preserve each asset's balance+reserve total."
)
EXPECTED_GRADE = "A-"
EXPECTED_GRADE_REASON = (
    "Strong replay binding with protocol-fee, bidirectional swap, create-pool, add-liquidity, "
    "remove-liquidity, and mixed-batch composition coverage. Still bounded and not a full "
    "proof_artifact flip."
)
EXPECTED_PRODUCTION_MATRIX_EFFECT = "No CBC registry column flips."
EXPECTED_COMMANDS = [
    ["lake", "--wfail", "build", LEAN_MODULE],
    ["python3", "-m", "pytest", "-q", "tests/formal/test_lean_settlement_conservation_live.py"],
    ["python3", "-m", "pytest", "-q", "tests/runtime/test_settlement_conservation_live_binding.py"],
]
EXPECTED_COMMAND_CWDS = ["lean-mathlib", ".", "."]
EXPECTED_COVERED_CONSTRUCTORS = [
    "addLiquidity",
    "createPool",
    "removeLiquidity",
    "swapInput",
    "swapOutput",
]


class RefinementError(ValueError):
    pass


@dataclass(frozen=True)
class Scenario:
    case_id: str
    intents: list[Intent]
    pools: dict[str, PoolState]
    balances: BalanceTable
    lp_balances: LPTable
    settlement: Settlement
    protocol_fee_share_bps: int = 0
    protocol_fee_recipient_pubkey: str | None = None


@dataclass(frozen=True)
class AssetMoveWitness:
    asset: str
    constructor: str
    balance_delta: int
    reserve_delta: int
    params: dict[str, int]


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _run(command: list[str], *, cwd: Path = ROOT) -> dict[str, Any]:
    proc = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=240)
    return {
        "cmd": command,
        "cwd": str(cwd.relative_to(ROOT) if cwd != ROOT else "."),
        "returncode": proc.returncode,
        "stdout_tail": proc.stdout[-2000:],
        "stderr_tail": proc.stderr[-2000:],
    }


def _net_balance_by_asset(deltas: Iterable[BalanceDelta]) -> dict[str, int]:
    out: dict[str, int] = defaultdict(int)
    for delta in deltas:
        out[delta.asset] += int(delta.net_delta())
    return dict(out)


def _net_reserve_by_asset(deltas: Iterable[ReserveDelta]) -> dict[str, int]:
    out: dict[str, int] = defaultdict(int)
    for delta in deltas:
        out[delta.asset] += int(delta.net_delta())
    return dict(out)


def _witness(asset: str, constructor: str, balance_delta: int, reserve_delta: int, **params: int) -> AssetMoveWitness:
    if balance_delta + reserve_delta != 0:
        raise RefinementError(
            f"internal witness is not conservative: {constructor} {asset} "
            f"balance={balance_delta} reserve={reserve_delta}"
        )
    return AssetMoveWitness(
        asset=asset,
        constructor=constructor,
        balance_delta=int(balance_delta),
        reserve_delta=int(reserve_delta),
        params={k: int(v) for k, v in params.items()},
    )


def _pool_for(intent: Intent, pools: Mapping[str, PoolState]) -> PoolState:
    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or pool_id not in pools:
        raise RefinementError(f"pool not found for intent {intent.intent_id}: {pool_id!r}")
    return pools[pool_id]


def _expected_witnesses(scenario: Scenario) -> list[AssetMoveWitness]:
    intents_by_id = {intent.intent_id: intent for intent in scenario.intents}
    witnesses: list[AssetMoveWitness] = []
    for fill in scenario.settlement.fills:
        if fill.action.value != "FILL":
            continue
        intent = intents_by_id.get(fill.intent_id)
        if intent is None:
            raise RefinementError(f"fill has no matching intent: {fill.intent_id}")

        if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            if fill.reason == "COW_NETTED":
                raise RefinementError("COW_NETTED is outside the SettlementConservationLive constructor scope")
            asset_in = intent.get_field("asset_in")
            asset_out = intent.get_field("asset_out")
            amount_in = int(fill.amount_in_filled or 0)
            amount_out = int(fill.amount_out_filled or 0)
            protocol_fee = int(fill.protocol_fee_paid or 0)
            witnesses.append(
                _witness(
                    str(asset_in),
                    "swapInput",
                    -amount_in + protocol_fee,
                    amount_in - protocol_fee,
                    amount=amount_in,
                    protocol_fee=protocol_fee,
                )
            )
            witnesses.append(
                _witness(str(asset_out), "swapOutput", amount_out, -amount_out, amount_out=amount_out)
            )
            continue

        if intent.kind == IntentKind.CREATE_POOL:
            amount0 = int(intent.get_field("amount0"))
            amount1 = int(intent.get_field("amount1"))
            asset0 = str(intent.get_field("asset0"))
            asset1 = str(intent.get_field("asset1"))
            witnesses.append(_witness(asset0, "createPool", -amount0, amount0, amount=amount0))
            witnesses.append(_witness(asset1, "createPool", -amount1, amount1, amount=amount1))
            continue

        if intent.kind == IntentKind.ADD_LIQUIDITY:
            pool = _pool_for(intent, scenario.pools)
            amount0 = int(fill.amount0_used or 0)
            amount1 = int(fill.amount1_used or 0)
            witnesses.append(_witness(pool.asset0, "addLiquidity", -amount0, amount0, amount_used=amount0))
            witnesses.append(_witness(pool.asset1, "addLiquidity", -amount1, amount1, amount_used=amount1))
            continue

        if intent.kind == IntentKind.REMOVE_LIQUIDITY:
            pool = _pool_for(intent, scenario.pools)
            amount0 = int(fill.amount0_out or 0)
            amount1 = int(fill.amount1_out or 0)
            witnesses.append(_witness(pool.asset0, "removeLiquidity", amount0, -amount0, amount_out=amount0))
            witnesses.append(_witness(pool.asset1, "removeLiquidity", amount1, -amount1, amount_out=amount1))
            continue

        raise RefinementError(f"unsupported intent kind in refinement corpus: {intent.kind}")
    return witnesses


def verify_scenario(scenario: Scenario) -> dict[str, Any]:
    ok, err = validate_settlement_strong(
        settlement=scenario.settlement,
        intents=scenario.intents,
        pre_balances=scenario.balances,
        pre_pools=scenario.pools,
        pre_lp_balances=scenario.lp_balances,
        protocol_fee_share_bps=scenario.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=scenario.protocol_fee_recipient_pubkey,
    )
    if not ok:
        raise RefinementError(f"{scenario.case_id}: strong validation failed: {err}")

    expected = _expected_witnesses(scenario)
    if not expected:
        raise RefinementError(f"{scenario.case_id}: no filled witnesses; corpus case is vacuous")
    expected_balance = _sum_witnesses(expected, field="balance_delta")
    expected_reserve = _sum_witnesses(expected, field="reserve_delta")
    actual_balance = _net_balance_by_asset(scenario.settlement.balance_deltas)
    actual_reserve = _net_reserve_by_asset(scenario.settlement.reserve_deltas)
    if expected_balance != actual_balance:
        raise RefinementError(
            f"{scenario.case_id}: balance deltas do not refine to Lean AssetMove constructors: "
            f"expected={expected_balance} actual={actual_balance}"
        )
    if expected_reserve != actual_reserve:
        raise RefinementError(
            f"{scenario.case_id}: reserve deltas do not refine to Lean AssetMove constructors: "
            f"expected={expected_reserve} actual={actual_reserve}"
        )
    for asset in set(actual_balance) | set(actual_reserve):
        if actual_balance.get(asset, 0) + actual_reserve.get(asset, 0) != 0:
            raise RefinementError(f"{scenario.case_id}: nonzero total delta for {asset}")

    pre_totals = _asset_totals(scenario.balances, scenario.pools)
    post_balances = _copy_balances(scenario.balances)
    post_pools = {pool_id: dataclasses.replace(pool) for pool_id, pool in scenario.pools.items()}
    post_lp = _copy_lp(scenario.lp_balances)
    apply_settlement(scenario.settlement, post_balances, post_pools, post_lp)
    post_totals = _asset_totals(post_balances, post_pools)
    if pre_totals != post_totals:
        raise RefinementError(f"{scenario.case_id}: state totals changed: pre={pre_totals} post={post_totals}")

    return {
        "case_id": scenario.case_id,
        "filled_intents": sum(1 for _intent_id, action in scenario.settlement.included_intents if action.value == "FILL"),
        "constructors": sorted({w.constructor for w in expected}),
        "assets": sorted(set(actual_balance) | set(actual_reserve)),
        "witnesses": [dataclasses.asdict(w) for w in expected],
        "pre_post_totals_ok": True,
    }


def _sum_witnesses(witnesses: Iterable[AssetMoveWitness], *, field: str) -> dict[str, int]:
    out: dict[str, int] = defaultdict(int)
    for witness in witnesses:
        out[witness.asset] += int(getattr(witness, field))
    return dict(out)


def _copy_balances(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, amount)
    return copied


def _copy_lp(lp_balances: LPTable) -> LPTable:
    copied = LPTable()
    for (pubkey, pool_id), amount in lp_balances.get_all_balances().items():
        copied.set(pubkey, pool_id, amount)
    for (pubkey, pool_id), timestamp in lp_balances.get_all_last_mint_timestamps().items():
        if copied.get(pubkey, pool_id) > 0:
            copied.set_last_mint_timestamp(pubkey, pool_id, timestamp)
    return copied


def _asset_totals(balances: BalanceTable, pools: Mapping[str, PoolState]) -> dict[str, int]:
    totals: dict[str, int] = defaultdict(int)
    for (_pubkey, asset), amount in balances.get_all_balances().items():
        totals[asset] += int(amount)
    for pool in pools.values():
        totals[pool.asset0] += int(pool.reserve0)
        totals[pool.asset1] += int(pool.reserve1)
    return dict(totals)


def _base_pool() -> tuple[str, PoolState, BalanceTable, LPTable]:
    pool_id, pool, lp_minted = create_pool(
        asset0=A0,
        asset1=A1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=PK,
    )
    balances = BalanceTable()
    balances.set(PK, A0, 10_000_000)
    balances.set(PK, A1, 10_000_000)
    balances.set(PK2, A0, 10_000_000)
    balances.set(PK2, A1, 10_000_000)
    lp = LPTable()
    lp.set(PK, pool_id, lp_minted)
    lp.set(LP_LOCK, pool_id, pool.lp_supply - lp_minted)
    return pool_id, pool, balances, lp


def _swap_scenario(
    *,
    case_id: str,
    kind: IntentKind,
    asset_in: str,
    asset_out: str,
    amount: int,
    protocol_fee_share_bps: int = 0,
) -> Scenario:
    pool_id, pool, balances, lp = _base_pool()
    if kind == IntentKind.SWAP_EXACT_IN:
        fields = {
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount,
            "min_amount_out": 1,
        }
    elif kind == IntentKind.SWAP_EXACT_OUT:
        fields = {
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount,
            "max_amount_in": 10_000_000,
        }
    else:
        raise AssertionError(kind)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_iid(100 + len(case_id)),
        sender_pubkey=PK,
        deadline=9999999999,
        fields=fields,
    )
    settlement = compute_settlement(
        [intent],
        {pool_id: pool},
        balances,
        lp,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=FEE_RECIP if protocol_fee_share_bps else None,
    )
    return Scenario(
        case_id=case_id,
        intents=[intent],
        pools={pool_id: pool},
        balances=balances,
        lp_balances=lp,
        settlement=settlement,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=FEE_RECIP if protocol_fee_share_bps else None,
    )


def _create_pool_scenario() -> Scenario:
    balances = BalanceTable()
    balances.set(PK, A0, 10_000_000)
    balances.set(PK, A1, 10_000_000)
    lp = LPTable()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(201),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"asset0": A0, "asset1": A1, "fee_bps": 30, "amount0": 2_000_000, "amount1": 3_000_000},
    )
    settlement = compute_settlement([intent], {}, balances, lp)
    return Scenario("create_pool", [intent], {}, balances, lp, settlement)


def _add_liquidity_scenario() -> Scenario:
    pool_id, pool, balances, lp = _base_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(301),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 250_000,
            "amount1_desired": 125_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp)
    return Scenario("add_liquidity", [intent], {pool_id: pool}, balances, lp, settlement)


def _remove_liquidity_scenario() -> Scenario:
    pool_id, pool, balances, lp = _base_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(401),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "lp_amount": 123_456, "amount0_min": 0, "amount1_min": 0},
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp)
    return Scenario("remove_liquidity", [intent], {pool_id: pool}, balances, lp, settlement)


def _mixed_existing_pool_batch_scenario() -> Scenario:
    pool_id, pool, balances, lp = _base_pool()
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(501),
            sender_pubkey=PK,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": A0,
                "asset_out": A1,
                "amount_in": 20_000,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(502),
            sender_pubkey=PK2,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": A1,
                "asset_out": A0,
                "amount_out": 10_000,
                "max_amount_in": 100_000,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.ADD_LIQUIDITY,
            intent_id=_iid(503),
            sender_pubkey=PK,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "amount0_desired": 100_000,
                "amount1_desired": 100_000,
                "amount0_min": 0,
                "amount1_min": 0,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.REMOVE_LIQUIDITY,
            intent_id=_iid(504),
            sender_pubkey=PK,
            deadline=9999999999,
            fields={"pool_id": pool_id, "lp_amount": 50_000, "amount0_min": 0, "amount1_min": 0},
        ),
    ]
    settlement = compute_settlement(
        intents,
        {pool_id: pool},
        balances,
        lp,
        protocol_fee_share_bps=1_000,
        protocol_fee_recipient_pubkey=FEE_RECIP,
    )
    return Scenario(
        "mixed_existing_pool_batch",
        intents,
        {pool_id: pool},
        balances,
        lp,
        settlement,
        protocol_fee_share_bps=1_000,
        protocol_fee_recipient_pubkey=FEE_RECIP,
    )


def build_scenarios() -> list[Scenario]:
    return [
        _swap_scenario(
            case_id="swap_exact_in_a0_to_a1",
            kind=IntentKind.SWAP_EXACT_IN,
            asset_in=A0,
            asset_out=A1,
            amount=1_000,
        ),
        _swap_scenario(
            case_id="swap_exact_in_a1_to_a0_with_protocol_fee",
            kind=IntentKind.SWAP_EXACT_IN,
            asset_in=A1,
            asset_out=A0,
            amount=250_000,
            protocol_fee_share_bps=2_500,
        ),
        _swap_scenario(
            case_id="swap_exact_out_a0_to_a1",
            kind=IntentKind.SWAP_EXACT_OUT,
            asset_in=A0,
            asset_out=A1,
            amount=50_000,
        ),
        _swap_scenario(
            case_id="swap_exact_out_a1_to_a0_with_protocol_fee",
            kind=IntentKind.SWAP_EXACT_OUT,
            asset_in=A1,
            asset_out=A0,
            amount=50_000,
            protocol_fee_share_bps=2_500,
        ),
        _create_pool_scenario(),
        _add_liquidity_scenario(),
        _remove_liquidity_scenario(),
        _mixed_existing_pool_batch_scenario(),
    ]


def run_refinement_checks() -> list[dict[str, Any]]:
    return [verify_scenario(scenario) for scenario in build_scenarios()]


def _source_hashes() -> dict[str, str]:
    return {rel: _sha256_file(ROOT / rel) for rel in SOURCE_FILES}


def build_receipt(path: Path) -> dict[str, Any]:
    lean = _run(EXPECTED_COMMANDS[0], cwd=ROOT / "lean-mathlib")
    if lean["returncode"] != 0:
        raise RefinementError(f"Lean build failed: {lean}")
    formal = _run(EXPECTED_COMMANDS[1])
    if formal["returncode"] != 0:
        raise RefinementError(f"formal smoke failed: {formal}")
    runtime = _run(EXPECTED_COMMANDS[2])
    if runtime["returncode"] != 0:
        raise RefinementError(f"runtime binding failed: {runtime}")
    cases = run_refinement_checks()
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "source_hashes": _source_hashes(),
        "lean_module": LEAN_MODULE,
        "commands": [lean, formal, runtime],
        "cases": cases,
        "covered_constructors": sorted({ctor for case in cases for ctor in case["constructors"]}),
        "claim": EXPECTED_CLAIM,
        "grade": EXPECTED_GRADE,
        "grade_reason": EXPECTED_GRADE_REASON,
        "production_matrix_effect": EXPECTED_PRODUCTION_MATRIX_EFFECT,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return receipt


def _receipt_object(value: Any, field: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{field} must be an object")
        return {}
    return value


def _receipt_list(value: Any, field: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{field} must be a list")
        return []
    return value


def check_receipt(path: Path) -> dict[str, Any]:
    receipt = json.loads(path.read_text(encoding="utf-8"))
    errors: list[str] = []
    if not isinstance(receipt, Mapping):
        return {
            "schema": CHECK_SCHEMA,
            "ok": False,
            "errors": ["receipt must be an object"],
            "receipt": str(path),
            "covered_constructors": [],
        }
    if receipt.get("schema") != RECEIPT_SCHEMA:
        errors.append("bad schema")
    if receipt.get("lean_module") != LEAN_MODULE:
        errors.append("lean_module mismatch")
    if receipt.get("claim") != EXPECTED_CLAIM:
        errors.append("claim mismatch")
    if receipt.get("grade") != EXPECTED_GRADE:
        errors.append("grade mismatch")
    if receipt.get("grade_reason") != EXPECTED_GRADE_REASON:
        errors.append("grade_reason mismatch")
    if receipt.get("production_matrix_effect") != EXPECTED_PRODUCTION_MATRIX_EFFECT:
        errors.append("production_matrix_effect must keep the no-flip boundary explicit")
    source_hashes = _receipt_object(receipt.get("source_hashes"), "source_hashes", errors)
    for rel, pinned in source_hashes.items():
        if not isinstance(rel, str) or not isinstance(pinned, str):
            errors.append("source_hashes entries must map string paths to string sha256 values")
            continue
        try:
            actual = _sha256_file(ROOT / rel)
        except OSError as exc:
            errors.append(f"source file unreadable: {rel}: {exc}")
            continue
        if actual != pinned:
            errors.append(f"source hash mismatch: {rel}")
    if sorted(source_hashes.keys()) != sorted(SOURCE_FILES):
        errors.append("source hash file set mismatch")
    try:
        cases = run_refinement_checks()
    except Exception as exc:  # pragma: no cover - surfaced in result envelope
        errors.append(f"refinement replay failed: {exc}")
        cases = []
    got_cases = _receipt_list(receipt.get("cases"), "cases", errors)
    if got_cases != cases:
        errors.append("case replay mismatch")
    covered = sorted({ctor for case in cases for ctor in case.get("constructors", [])})
    if covered != EXPECTED_COVERED_CONSTRUCTORS:
        errors.append("internal constructor coverage mismatch")
    got_covered = _receipt_list(receipt.get("covered_constructors"), "covered_constructors", errors)
    if got_covered != covered:
        errors.append("covered constructor set mismatch")
    commands = _receipt_list(receipt.get("commands"), "commands", errors)
    command_entries: list[Mapping[str, Any]] = []
    for index, command in enumerate(commands):
        if not isinstance(command, Mapping):
            errors.append(f"commands[{index}] must be an object")
            continue
        command_entries.append(command)
    got_commands = [cmd.get("cmd") for cmd in command_entries]
    got_returncodes = [cmd.get("returncode") for cmd in command_entries]
    got_cwds = [cmd.get("cwd") for cmd in command_entries]
    if got_commands != EXPECTED_COMMANDS or got_returncodes != [0, 0, 0] or got_cwds != EXPECTED_COMMAND_CWDS:
        errors.append("command receipt mismatch")
    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "receipt": str(path),
        "covered_constructors": covered,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build/check live settlement conservation refinement receipt.")
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_build = sub.add_parser("build")
    p_build.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    p_build.add_argument("--pretty", action="store_true")
    p_check = sub.add_parser("check")
    p_check.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    p_check.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        if args.cmd == "build":
            result = build_receipt(args.receipt)
        else:
            result = check_receipt(args.receipt)
    except Exception as exc:
        result = {"schema": CHECK_SCHEMA, "ok": False, "errors": [str(exc)]}
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if result.get("ok", args.cmd == "build") else 1


if __name__ == "__main__":
    raise SystemExit(main())
