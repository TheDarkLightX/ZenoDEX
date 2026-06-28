#!/usr/bin/env python3
"""Replay the AB compressed subset-DP refutation witness."""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import (  # noqa: E402
    _AbDpRecord,
    _best_order_by_objective_bruteforce,
    _best_order_by_objective_subset_dp,
    _debit_balance_key,
    _is_better_ab_dp_record,
    _objective_exact_in_contribution,
    _objective_for_order,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.pools import PoolState  # noqa: E402
from tools.zenodex_ab_cow_algorithm_breakthrough_20260627 import (  # noqa: E402
    ASSET0,
    ASSET1,
    _ab_context,
    _exact_in_intent,
    _pool,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_compressed_dp_refuter_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_COMPRESSED_DP_REFUTER_20260628.md"


@dataclass(frozen=True)
class WitnessSwap:
    intent_no: int
    sender_no: int
    amount_in: int
    min_amount_out: int


WITNESS_SWAPS = (
    WitnessSwap(intent_no=1000, sender_no=2, amount_in=32, min_amount_out=32),
    WitnessSwap(intent_no=1001, sender_no=2, amount_in=119, min_amount_out=81),
    WitnessSwap(intent_no=1002, sender_no=3, amount_in=96, min_amount_out=130),
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _witness_pool() -> PoolState:
    base = _pool()
    return PoolState(
        pool_id=base.pool_id,
        asset0=base.asset0,
        asset1=base.asset1,
        reserve0=85,
        reserve1=561,
        fee_bps=5,
        lp_supply=base.lp_supply,
        status=base.status,
        created_at=base.created_at,
    )


def _witness_inputs() -> tuple[PoolState, list[Any], BalanceTable]:
    balances = BalanceTable()
    balances.set("0x" + "02" * 48, ASSET0, 209)
    balances.set("0x" + "03" * 48, ASSET0, 203)
    intents = [
        _exact_in_intent(
            swap.intent_no,
            sender_no=swap.sender_no,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_in=swap.amount_in,
            min_amount_out=swap.min_amount_out,
        )
        for swap in WITNESS_SWAPS
    ]
    return _witness_pool(), intents, balances


def _short_ids(order: tuple[Any, ...] | None) -> tuple[str, ...]:
    if order is None:
        return tuple()
    return tuple(intent.intent_id[-4:] for intent in order)


def _key(order: tuple[Any, ...] | None, context: Any) -> tuple[int, int, tuple[str, ...]]:
    if order is None:
        return (-1, -1, tuple())
    amount_a, surplus_b, order_ids = _objective_for_order(order, context)
    return int(amount_a), int(surplus_b), tuple(str(intent_id) for intent_id in order_ids)


def _compressed_subset_only_dp(intents: list[Any], context: Any) -> tuple[Any, ...] | None:
    """Unsafe reference algorithm: keep only one state per processed subset.

    This intentionally drops reserves and per-sender balances from the DP key.
    The witness report uses it only as a falsification target.
    """
    n = len(intents)
    intent_by_id = {intent.intent_id: intent for intent in intents}
    senders = tuple(sorted(context.sender_bal_in))
    sender_index = {sender: idx for idx, sender in enumerate(senders)}
    initial_balances = tuple(int(context.sender_bal_in[sender]) for sender in senders)
    dp: dict[int, tuple[_AbDpRecord, int, int, tuple[int, ...]]] = {
        0: (_AbDpRecord(0, 0, tuple()), int(context.r_in0), int(context.r_out0), initial_balances)
    }

    for mask in range(1 << n):
        state = dp.get(mask)
        if state is None:
            continue
        record, r_in, r_out, balance_key = state
        balances = {sender: int(balance_key[idx]) for sender, idx in sender_index.items()}
        for idx, intent in enumerate(intents):
            bit = 1 << idx
            if mask & bit:
                continue
            next_r_in = int(r_in)
            next_r_out = int(r_out)
            next_balance_key = balance_key
            next_a = int(record.amount_a)
            next_b = int(record.surplus_b)
            contribution = _objective_exact_in_contribution(
                intent,
                context,
                r_in=next_r_in,
                r_out=next_r_out,
                bal_in=balances,
            )
            if contribution is not None:
                amount_in, surplus, next_r_in, next_r_out = contribution
                next_a += int(amount_in)
                next_b += int(surplus)
                next_balance_key = _debit_balance_key(
                    next_balance_key,
                    sender_index=sender_index,
                    sender=intent.sender_pubkey,
                    amount=int(amount_in),
                )

            next_mask = mask | bit
            next_record = _AbDpRecord(next_a, next_b, (*record.order_ids, intent.intent_id))
            current = dp.get(next_mask)
            if current is None or _is_better_ab_dp_record(next_record, current[0], context):
                dp[next_mask] = (next_record, next_r_in, next_r_out, next_balance_key)

    final = dp.get((1 << n) - 1)
    if final is None:
        return None
    return tuple(intent_by_id[intent_id] for intent_id in final[0].order_ids)


def _build_report() -> dict[str, Any]:
    pool, intents, balances = _witness_inputs()
    context = _ab_context(pool, intents, balances)
    brute = _best_order_by_objective_bruteforce(intents, context)
    full_state = _best_order_by_objective_subset_dp(intents, context)
    compressed = _compressed_subset_only_dp(intents, context)
    brute_key = _key(brute, context)
    full_key = _key(full_state, context)
    compressed_key = _key(compressed, context)
    objective_loss_amount = int(brute_key[0]) - int(compressed_key[0])
    ok = (
        brute is not None
        and full_state is not None
        and compressed is not None
        and brute_key == full_key
        and objective_loss_amount > 0
    )
    return {
        "schema": "zenodex.ab_compressed_dp_refuter_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "witness": {
            "pool": {
                "reserve0": int(pool.reserve0),
                "reserve1": int(pool.reserve1),
                "fee_bps": int(pool.fee_bps),
            },
            "sender_balances": {
                "sender_2_asset0": int(balances.get("0x" + "02" * 48, ASSET0)),
                "sender_3_asset0": int(balances.get("0x" + "03" * 48, ASSET0)),
            },
            "swaps": [
                {
                    "intent_id": intent.intent_id,
                    "short_id": intent.intent_id[-4:],
                    "sender": intent.sender_pubkey,
                    "amount_in": int(intent.get_field("amount_in")),
                    "min_amount_out": int(intent.get_field("min_amount_out")),
                }
                for intent in intents
            ],
        },
        "results": {
            "bruteforce": {"order": _short_ids(brute), "key": brute_key},
            "full_state_subset_dp": {"order": _short_ids(full_state), "key": full_key},
            "compressed_subset_only_dp": {"order": _short_ids(compressed), "key": compressed_key},
            "objective_loss_amount_a": objective_loss_amount,
            "surplus_delta_compressed_minus_optimal": int(compressed_key[1]) - int(brute_key[1]),
        },
        "claim": {
            "falsified": "A one-record-per-subset Held-Karp DP is not sound for the current AB objective under integer CPMM semantics.",
            "supported_boundary": "The existing full-state subset DP keeps reserves and sender balances in the state key.",
        },
        "non_claims": [
            "This does not refute the existing full-state subset DP.",
            "This does not refute compressed-state results for different cross-pool routing models with separate conservation proofs.",
            "The witness is a bounded deterministic counterexample, not a distributional performance benchmark.",
        ],
        "replay_command": "python3 tools/zenodex_ab_compressed_dp_refuter_20260628.py",
    }


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX AB Compressed-DP Refuter - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(report["claim"]["falsified"])
    lines.append(report["claim"]["supported_boundary"])
    lines.append("")
    lines.append("## Witness")
    lines.append("")
    pool = report["witness"]["pool"]
    lines.append(f"- Pool: reserve0 `{pool['reserve0']}`, reserve1 `{pool['reserve1']}`, fee_bps `{pool['fee_bps']}`")
    for swap in report["witness"]["swaps"]:
        lines.append(
            f"- `{swap['short_id']}`: sender `{swap['sender'][-6:]}`, amount_in `{swap['amount_in']}`, min_amount_out `{swap['min_amount_out']}`"
        )
    lines.append("")
    lines.append("## Oracle Comparison")
    lines.append("")
    lines.append("| solver | order | AB key |")
    lines.append("| --- | --- | --- |")
    for name, result in report["results"].items():
        if not isinstance(result, dict) or "order" not in result:
            continue
        short_key = (result["key"][0], result["key"][1], tuple(result["order"]))
        lines.append(f"| `{name}` | `{', '.join(result['order'])}` | `{short_key}` |")
    lines.append("")
    lines.append(
        f"The unsafe compressed subset-only DP loses `{report['results']['objective_loss_amount_a']}` units of primary AB amount while gaining surplus that the objective ranks second."
    )
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = _build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "objective_loss_amount_a": report["results"]["objective_loss_amount_a"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
