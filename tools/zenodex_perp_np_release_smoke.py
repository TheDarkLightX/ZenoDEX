#!/usr/bin/env python3
"""Release smoke: N-party perps clearinghouse, 3+ independent wallets, through the engine.

Proves the participation the fixed 2-party market cannot give, end to end through the
real transaction entrypoint ``apply_perp_ops`` (NOT the ZK guest — that has its own
smoke). For each scenario it:

  1. operator opens an NP market (``init_market_np``),
  2. 3+ INDEPENDENT wallets each deposit collateral (single-signed, sender-bound),
  3. wallets submit single-signed long AND short intents,
  4. the oracle publishes an oracle-signed (real BLS) clearing price,
  5. the operator runs the epoch (settle + largest-remainder match).

Then it asserts the release-relevant invariants and emits an evidence bundle:
  - >= 3 participants actually took positions,
  - both a long and a short position exist (real two-sided participation),
  - net-zero positions (sum of position_base == 0) by construction,
  - two-ledger conservation + insurance identity (recomputed here AND enforced
    fail-closed by the market-state __post_init__ that ran on commit),
  - state-header agreement: re-running the identical op sequence from scratch
    yields a byte-identical canonical snapshot root (deterministic settlement),
  - snapshot roundtrip preserves accounts / pending buffer / global_state.

Fake-value public testnet. ``production_security_claim`` stays false.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.dex import DexState  # noqa: E402
from src.integration.bls_intent_signing import (  # noqa: E402
    bls_pubkey_hex_from_privkey,
    sign_perp_op_for_engine,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot  # noqa: E402
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.lp import LPTable  # noqa: E402

E8 = 100_000_000
CHAIN = "zenodex-perp-np-release-smoke-v0"
MKT = "perp:chnp:RELEASE"
FUTURE = 4_102_444_800
OPERATOR = "0x" + "0f" * 48
ORACLE_SK = 7
ORACLE = bls_pubkey_hex_from_privkey(ORACLE_SK)
CFG = PerpEngineConfig(chain_id=CHAIN, operator_pubkey=OPERATOR, oracle_pubkey=ORACLE)


def log(msg: str, *, json_only: bool = False) -> None:
    if not json_only:
        print(msg, file=sys.stderr)


def _wallet(i: int) -> str:
    # Distinct, deterministic 48-byte pubkeys for independent wallets.
    return "0x" + f"{i:02x}" * 48


def _op(action: str, **fields: object) -> dict[str, object]:
    return {"module": "TauPerp", "version": "1.2", "market_id": MKT, "action": action, **fields}


def _apply(state: DexState, op: dict, sender: str, ts: int = 1):
    res = apply_perp_ops(
        config=CFG, state=state, operations={"5": [op]},
        tx_sender_pubkey=sender, block_timestamp=ts,
    )
    if not res.ok:
        raise RuntimeError(f"engine rejected {op.get('action')} from {sender[:10]}: {res.error}")
    return res.state


def _signed_publish(price_e8: int, nonce: int = 1) -> dict:
    op = _op("publish_clearing_price", price_e8=price_e8, deadline=FUTURE, oracle_nonce=nonce)
    op["oracle_sig"] = sign_perp_op_for_engine(
        op, privkey=ORACLE_SK, chain_id=CHAIN, signer_pubkey=ORACLE, nonce=nonce)
    return op


def _canonical_root(state: DexState) -> str:
    snap = snapshot_from_state(state).data
    blob = json.dumps(snap, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def _run_sequence(wallets: list[str], targets: list[int], *, deposit: int, index_e8: int, clearing_e8: int) -> DexState:
    """Deterministically drive one full NP epoch through the engine."""
    bt = BalanceTable()
    for pk in wallets:
        bt.set(pk, "zUSD", 10_000)
    state = DexState(balances=bt, pools={}, lp_balances=LPTable())
    state = _apply(state, _op("init_market_np", quote_asset="zUSD", index_price_e8=index_e8), OPERATOR)
    for pk in wallets:
        state = _apply(state, _op("deposit_collateral", account_pubkey=pk, amount=deposit), pk)
    for pk, tgt in zip(wallets, targets):
        state = _apply(state, _op("submit_intent", account_pubkey=pk, target_base=tgt), pk)
    state = _apply(state, _signed_publish(clearing_e8), ORACLE)
    state = _apply(state, _op("run_epoch", funding_rate_bps=0), OPERATOR)
    return state


def _scenarios() -> dict[str, dict[str, Any]]:
    return {
        # 3 wallets: one long, two short; buys 10 == sells 10 (exact two-sided match).
        "three_wallet": {
            "wallets": [_wallet(0xa1), _wallet(0xb2), _wallet(0xc3)],
            "targets": [10, -6, -4],
            "deposit": 1000, "index_e8": 100 * E8, "clearing_e8": 100 * E8,
        },
        # 4 wallets: two long, two short; buys 20 == sells 20.
        "four_wallet": {
            "wallets": [_wallet(0xa1), _wallet(0xb2), _wallet(0xc3), _wallet(0xd4)],
            "targets": [12, 8, -15, -5],
            "deposit": 2000, "index_e8": 100 * E8, "clearing_e8": 100 * E8,
        },
        # 5 wallets: oracle moves the clearing price within bound; still net-zero.
        "five_wallet": {
            "wallets": [_wallet(0xa1), _wallet(0xb2), _wallet(0xc3), _wallet(0xd4), _wallet(0xe5)],
            "targets": [10, 5, -7, -5, -3],
            "deposit": 3000, "index_e8": 100 * E8, "clearing_e8": 101 * E8,
        },
    }


def _run_scenario(name: str, scn: dict[str, Any]) -> dict[str, Any]:
    wallets = scn["wallets"]
    targets = scn["targets"]
    log(f"[{name}] {len(wallets)} wallets, targets={targets}")

    state = _run_sequence(wallets, targets, deposit=scn["deposit"], index_e8=scn["index_e8"], clearing_e8=scn["clearing_e8"])
    mkt = state.perps.get_market(MKT)
    pos = {a.pubkey: a.position_base for a in mkt.accounts}
    coll = {a.pubkey: a.collateral_e8 for a in mkt.accounts}
    gs = dict(mkt.global_state)

    # --- release assertions -------------------------------------------------
    participants = [pk for pk, p in pos.items() if p != 0]
    longs = [pk for pk, p in pos.items() if p > 0]
    shorts = [pk for pk, p in pos.items() if p < 0]
    assert len(pos) >= 3, f"need >=3 accounts, got {len(pos)}"
    assert len(participants) >= 3, f"need >=3 active participants, got {len(participants)}"
    assert longs and shorts, "need both a long and a short position (two-sided)"
    net = sum(pos.values())
    assert net == 0, f"net position must be zero, got {net}"
    for pk, tgt in zip(wallets, targets):
        assert pos.get(pk) == tgt, f"{pk[:10]} position {pos.get(pk)} != target {tgt}"

    # Two-ledger conservation (II) + insurance identity (IV), recomputed independently.
    net_deposited = int(gs["net_deposited_e8"])
    fee_pool = int(gs["fee_pool_e8"])
    insurance = int(gs["insurance_e8"])
    insurance_ext = int(gs.get("insurance_ext_e8", gs.get("initial_insurance_e8", 0)))
    claims_paid = int(gs.get("claims_paid_e8", 0))
    coll_sum = sum(coll.values())
    conserved = (net_deposited + insurance_ext) == (coll_sum + fee_pool + insurance)
    insurance_ok = insurance == (insurance_ext - claims_paid) and insurance >= 0
    assert conserved, f"conservation: {net_deposited}+{insurance_ext} != {coll_sum}+{fee_pool}+{insurance}"
    assert insurance_ok, f"insurance ledger: {insurance} != {insurance_ext}-{claims_paid}"

    # State-header agreement: deterministic replay yields a byte-identical root.
    root_a = _canonical_root(state)
    state_b = _run_sequence(wallets, targets, deposit=scn["deposit"], index_e8=scn["index_e8"], clearing_e8=scn["clearing_e8"])
    root_b = _canonical_root(state_b)
    assert root_a == root_b, f"non-deterministic settlement: {root_a} != {root_b}"

    # Snapshot roundtrip preserves dynamic accounts + global state.
    reloaded = state_from_snapshot(snapshot_from_state(state).data)
    rmkt = reloaded.perps.get_market(MKT)
    roundtrip_ok = (
        rmkt.accounts == mkt.accounts
        and rmkt.pending_intents == mkt.pending_intents
        and dict(rmkt.global_state) == gs
    )
    assert roundtrip_ok, "snapshot roundtrip changed market state"
    assert mkt.pending_intents == (), "pending intent buffer must be cleared after match"

    log(f"[{name}] OK  participants={len(participants)} longs={len(longs)} shorts={len(shorts)} root={root_a[:16]}")
    return {
        "scenario": name,
        "ok": True,
        "accounts": len(pos),
        "active_participants": len(participants),
        "longs": len(longs),
        "shorts": len(shorts),
        "net_position": net,
        "positions": pos,
        "now_epoch_after": int(gs.get("now_epoch", -1)),
        "conservation_ok": conserved,
        "insurance_ledger_ok": insurance_ok,
        "deterministic_replay_ok": root_a == root_b,
        "snapshot_roundtrip_ok": roundtrip_ok,
        "state_header_root": root_a,
    }


def run_smoke(*, out_dir: Path, scenario: str) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    scns = _scenarios()
    selected = list(scns) if scenario == "all" else [scenario]
    unknown = [s for s in selected if s not in scns]
    if unknown:
        raise ValueError(f"unknown scenario(s): {', '.join(unknown)}")
    cases = [_run_scenario(name, scns[name]) for name in selected]
    report = {
        "schema": "zenodex.perp_np_release_smoke.v1",
        "ok": all(c["ok"] for c in cases),
        "engine_entrypoint": "apply_perp_ops",
        "market_kind": "clearinghouse_np_v1",
        "oracle_signed_clearing_price": True,
        "production_security_claim": False,
        "case_count": len(cases),
        "cases": cases,
    }
    report_path = out_dir / "perp_np_release_smoke_report.json"
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    report["report_path"] = str(report_path)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/zenodex_perp_np_release_smoke"))
    parser.add_argument("--scenario", choices=("three_wallet", "four_wallet", "five_wallet", "all"), default="all")
    parser.add_argument("--json", action="store_true", help="emit only the JSON report to stdout")
    args = parser.parse_args(argv)
    report = run_smoke(out_dir=args.out_dir.resolve(), scenario=args.scenario)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
