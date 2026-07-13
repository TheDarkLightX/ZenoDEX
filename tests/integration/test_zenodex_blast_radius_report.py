from __future__ import annotations

import json
import subprocess
from pathlib import Path

from src.agents.intent_signer import (
    create_swap_intent_from_quote_receipt,
    create_swap_intents_from_quote_receipt,
)
from src.core.dex import DexState
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.operations import (
    SignedIntentEnvelope,
    create_intent_operation,
    create_signed_intent_operation,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from tools.zenodex_blast_radius_report import build_blast_radius_report


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pk(n: int) -> str:
    return "0x" + f"{n:096x}"


def _asset(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pool(*, pid: str, asset0: str, asset1: str, reserve0: int, reserve1: int, fee_bps: int = 30) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=asset0,
        asset1=asset1,
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag="CPMM",
        curve_params="",
    )


def test_build_blast_radius_report_uses_snapshot_for_exact_scope() -> None:
    sender1 = _pk(1)
    sender2 = _pk(2)
    asset_a = _asset(1)
    asset_b = _asset(2)
    asset_c = _asset(3)
    asset_d = _asset(4)
    pool_ab = compute_pool_id(asset_a, asset_b, 30)
    pool_cd = compute_pool_id(asset_c, asset_d, 30)

    balances = BalanceTable()
    balances.set(sender1, asset_a, 10_000)
    balances.set(sender1, asset_b, 0)
    balances.set(sender2, asset_c, 10_000)
    balances.set(sender2, asset_d, 0)

    state = DexState(
        balances=balances,
        pools={
            pool_ab: _pool(pid=pool_ab, asset0=asset_a, asset1=asset_b, reserve0=1_000, reserve1=2_000),
            pool_cd: _pool(pid=pool_cd, asset0=asset_c, asset1=asset_d, reserve0=2_000, reserve1=1_000),
        },
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )
    snapshot = snapshot_from_state(state).data

    swap1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=sender1,
        deadline=9999999999,
        fields={
            "pool_id": pool_ab,
            "asset_in": asset_a,
            "asset_out": asset_b,
            "amount_in": 100,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    swap2 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=sender2,
        deadline=9999999999,
        fields={
            "pool_id": pool_cd,
            "asset_in": asset_c,
            "asset_out": asset_d,
            "amount_in": 200,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )

    report = build_blast_radius_report(
        operations=create_intent_operation([swap1, swap2]),
        snapshot=snapshot,
    )

    assert report["schema"] == "zenodex/blast-radius-report/v1"
    assert report["summary"]["intent_count"] == 2
    assert report["summary"]["conflict_component_count"] == 2
    assert report["summary"]["pool_count"] == 2
    assert report["exact_scope"]["full_state_root"]
    assert report["exact_scope"]["support_root"]
    assert report["exact_scope"]["state_support_ratio"] is not None
    assert report["heuristic_scope"]["state_surfaces"] == ["balances", "nonces", "pools"]


def test_blast_radius_cli_reports_conflict_component_for_shared_pool(tmp_path: Path) -> None:
    sender1 = _pk(1)
    sender2 = _pk(2)
    asset_a = _asset(1)
    asset_b = _asset(2)
    pool_ab = compute_pool_id(asset_a, asset_b, 30)

    balances = BalanceTable()
    balances.set(sender1, asset_a, 10_000)
    balances.set(sender2, asset_a, 10_000)

    state = DexState(
        balances=balances,
        pools={pool_ab: _pool(pid=pool_ab, asset0=asset_a, asset1=asset_b, reserve0=1_000, reserve1=2_000)},
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )

    swap1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=sender1,
        deadline=9999999999,
        fields={
            "pool_id": pool_ab,
            "asset_in": asset_a,
            "asset_out": asset_b,
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
    swap2 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=sender2,
        deadline=9999999999,
        fields={
            "pool_id": pool_ab,
            "asset_in": asset_a,
            "asset_out": asset_b,
            "amount_in": 150,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xabc",
        },
    )

    operations_path = tmp_path / "ops.json"
    snapshot_path = tmp_path / "snapshot.json"
    out_path = tmp_path / "report.json"
    operations_path.write_text(
        json.dumps(create_intent_operation([swap1, swap2]), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    snapshot_path.write_text(json.dumps(snapshot_from_state(state).data, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    proc = subprocess.run(
        [
            "python3",
            "tools/zenodex_blast_radius_report.py",
            "--operations",
            str(operations_path),
            "--snapshot",
            str(snapshot_path),
            "--output",
            str(out_path),
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(out_path.read_text(encoding="utf-8"))
    assert report["summary"]["conflict_component_count"] == 1
    assert report["summary"]["largest_conflict_component_size"] == 2
    assert "quote_receipt_binding_present_runtime_enforcement_partial" in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_hash_only_present" in report["heuristic_scope"]["heuristic_flags"]
    assert report["intents"][0]["quote_receipt_binding_status"] == "none"
    assert report["intents"][1]["quote_receipt_binding_status"] == "hash_only"
    assert report["evidence"]["functional_core_modules"]


def test_build_blast_radius_report_marks_attached_quote_receipt_witness_as_full() -> None:
    sender = _pk(7)
    asset_a = _asset(10)
    asset_b = _asset(11)
    pool_id = compute_pool_id(asset_a, asset_b, 10)
    balances = BalanceTable()
    balances.set(sender, asset_a, 10_000)
    balances.set(sender, asset_b, 0)
    pools = {
        pool_id: PoolState(
            pool_id=pool_id,
            asset0=asset_a,
            asset1=asset_b,
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )
    snapshot = snapshot_from_state(state).data

    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in=asset_a, asset_out=asset_b, amount_in=123)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    operations = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    report = build_blast_radius_report(
        operations=operations,
        snapshot=snapshot,
    )

    assert "quote_receipt_binding_present_runtime_enforcement_full" in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_present_runtime_enforcement_partial" not in report["heuristic_scope"]["heuristic_flags"]
    assert report["intents"][0]["has_quote_receipt_hash"] is True
    assert report["intents"][0]["has_quote_receipt_witness"] is True
    assert report["intents"][0]["quote_receipt_binding_status"] == "attached_verified"
    assert report["quote_receipt_groups"] == [
        {
            "quote_receipt_hash": receipt["receipt_hash"],
            "intent_ids": [intent.intent_id],
            "intent_count": 1,
            "attached_witness_count": 1,
            "observed_leg_indices": [0],
            "expected_leg_indices": [0],
            "missing_leg_index_intent_ids": [],
            "duplicate_leg_indices": [],
            "status": "complete",
        }
    ]


def test_build_blast_radius_report_keeps_invalid_attached_quote_receipt_witness_partial() -> None:
    sender = _pk(8)
    asset_a = _asset(12)
    asset_b = _asset(13)
    pool_id = compute_pool_id(asset_a, asset_b, 10)
    balances = BalanceTable()
    balances.set(sender, asset_a, 10_000)
    balances.set(sender, asset_b, 0)
    pools = {
        pool_id: PoolState(
            pool_id=pool_id,
            asset0=asset_a,
            asset1=asset_b,
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )
    snapshot = snapshot_from_state(state).data

    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in=asset_a, asset_out=asset_b, amount_in=123)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    bad_receipt = {
        **receipt,
        "receipt_hash": "0xdeadbeef",
    }
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    operations = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=bad_receipt)])

    report = build_blast_radius_report(
        operations=operations,
        snapshot=snapshot,
    )

    assert "quote_receipt_binding_present_runtime_enforcement_partial" in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_present_runtime_enforcement_full" not in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_invalid_witness_present" in report["heuristic_scope"]["heuristic_flags"]
    assert report["intents"][0]["quote_receipt_binding_status"] == "attached_invalid"


def test_build_blast_radius_report_marks_attached_quote_receipt_without_snapshot_unverified() -> None:
    sender = _pk(9)
    asset_a = _asset(14)
    asset_b = _asset(15)
    pool_id = compute_pool_id(asset_a, asset_b, 10)
    pools = {
        pool_id: PoolState(
            pool_id=pool_id,
            asset0=asset_a,
            asset1=asset_b,
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }

    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in=asset_a, asset_out=asset_b, amount_in=123)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    operations = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    report = build_blast_radius_report(operations=operations, snapshot=None)

    assert "quote_receipt_binding_present_runtime_enforcement_partial" in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_attached_witness_unverified" in report["heuristic_scope"]["heuristic_flags"]
    assert report["intents"][0]["quote_receipt_binding_status"] == "attached_unverified"


def test_build_blast_radius_report_marks_snapshot_only_quote_binding() -> None:
    sender = _pk(10)
    asset_a = _asset(16)
    asset_b = _asset(17)
    pool_id = compute_pool_id(asset_a, asset_b, 10)
    fingerprint = "0x" + "12" * 32

    balances = BalanceTable()
    balances.set(sender, asset_a, 10_000)
    pools = {
        pool_id: PoolState(
            pool_id=pool_id,
            asset0=asset_a,
            asset1=asset_b,
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )
    snapshot = snapshot_from_state(state).data

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(10),
        sender_pubkey=sender,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset_a,
            "asset_out": asset_b,
            "amount_in": 123,
            "min_amount_out": 1,
            "quote_pool_fingerprint": fingerprint,
        },
    )

    report = build_blast_radius_report(
        operations=create_intent_operation([intent]),
        snapshot=snapshot,
    )

    assert "quote_receipt_binding_snapshot_only_present" in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_present_runtime_enforcement_full" not in report["heuristic_scope"]["heuristic_flags"]
    assert "quote_receipt_binding_present_runtime_enforcement_partial" not in report["heuristic_scope"]["heuristic_flags"]
    assert report["intents"][0]["quote_receipt_binding_status"] == "snapshot_only"


def test_build_blast_radius_report_flags_incomplete_split_quote_receipt_group() -> None:
    sender = _pk(11)
    asset_a = _asset(18)
    asset_b = _asset(19)
    pool_1 = compute_pool_id(asset_a, asset_b, 30)
    pool_2 = compute_pool_id(asset_a, asset_b, 31)
    pools = {
        pool_1: _pool(pid=pool_1, asset0=asset_a, asset1=asset_b, reserve0=1_000, reserve1=1_000),
        pool_2: _pool(pid=pool_2, asset0=asset_a, asset1=asset_b, reserve0=1_000, reserve1=1_000, fee_bps=31),
    }
    balances = BalanceTable()
    balances.set(sender, asset_a, 10_000)
    balances.set(sender, asset_b, 0)
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )
    snapshot = snapshot_from_state(state).data

    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in=asset_a, asset_out=asset_b, amount_in=600)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    report = build_blast_radius_report(
        operations=create_signed_intent_operation([SignedIntentEnvelope(intent=intents[0], quote_receipt=receipt)]),
        snapshot=snapshot,
    )

    assert "quote_receipt_binding_incomplete_group_present" in report["heuristic_scope"]["heuristic_flags"]
    assert report["quote_receipt_groups"][0]["status"] == "incomplete"
    assert report["quote_receipt_groups"][0]["expected_leg_indices"] == [0, 1]
    assert report["quote_receipt_groups"][0]["observed_leg_indices"] == [0]


def test_build_blast_radius_report_flags_duplicate_split_quote_receipt_leg() -> None:
    sender = _pk(12)
    asset_a = _asset(20)
    asset_b = _asset(21)
    pool_1 = compute_pool_id(asset_a, asset_b, 30)
    pool_2 = compute_pool_id(asset_a, asset_b, 31)
    pools = {
        pool_1: _pool(pid=pool_1, asset0=asset_a, asset1=asset_b, reserve0=1_000, reserve1=1_000),
        pool_2: _pool(pid=pool_2, asset0=asset_a, asset1=asset_b, reserve0=1_000, reserve1=1_000, fee_bps=31),
    }
    balances = BalanceTable()
    balances.set(sender, asset_a, 10_000)
    balances.set(sender, asset_b, 0)
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )
    snapshot = snapshot_from_state(state).data

    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in=asset_a, asset_out=asset_b, amount_in=600)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    duplicate_intent = Intent(
        module=intents[0].module,
        version=intents[0].version,
        kind=intents[0].kind,
        intent_id=_iid(1200),
        sender_pubkey=intents[0].sender_pubkey,
        deadline=intents[0].deadline,
        salt=intents[0].salt,
        fields=dict(intents[0].fields or {}),
    )
    duplicate_intent.set_field("nonce", 99)
    report = build_blast_radius_report(
        operations=create_signed_intent_operation(
            [
                SignedIntentEnvelope(intent=intents[0], quote_receipt=receipt),
                SignedIntentEnvelope(intent=intents[1], quote_receipt=receipt),
                SignedIntentEnvelope(intent=duplicate_intent, quote_receipt=receipt),
            ]
        ),
        snapshot=snapshot,
    )

    assert "quote_receipt_binding_duplicate_leg_present" in report["heuristic_scope"]["heuristic_flags"]
    assert report["quote_receipt_groups"][0]["status"] == "duplicate_leg"
    assert report["quote_receipt_groups"][0]["duplicate_leg_indices"] == [0]
