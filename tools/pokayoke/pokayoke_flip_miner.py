#!/usr/bin/env python3
from __future__ import annotations

"""Bounded Pokayoke falsifier miner for adjacent amount action flips."""

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.pokayoke_swap_suggest import _action_severity, _eval_amount


SCHEMA = "zenodex/pokayoke-flip-miner/v1"


@dataclass(frozen=True)
class EvalOutcome:
    action: str
    severity: int
    reasons: tuple[str, ...]


@dataclass(frozen=True)
class FlipWitness:
    kind: str
    reserve_in: int
    reserve_out: int
    fee_bps: int
    pending_volume_same_direction: int
    confidence_bps: int
    user_slippage_bps: int
    max_attacker_amount_in: int
    slippage_options_bps: tuple[int, ...]
    amount_before: int
    amount_after: int
    action_before: str
    action_after: str
    severity_before: int
    severity_after: int
    reasons_before: tuple[str, ...]
    reasons_after: tuple[str, ...]

    def transition_key(self) -> str:
        return f"{self.action_before}->{self.action_after}|{','.join(self.reasons_before)}=>{','.join(self.reasons_after)}"

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "reserve_in": self.reserve_in,
            "reserve_out": self.reserve_out,
            "fee_bps": self.fee_bps,
            "pending_volume_same_direction": self.pending_volume_same_direction,
            "confidence_bps": self.confidence_bps,
            "user_slippage_bps": self.user_slippage_bps,
            "max_attacker_amount_in": self.max_attacker_amount_in,
            "slippage_options_bps": list(self.slippage_options_bps),
            "amount_before": self.amount_before,
            "amount_after": self.amount_after,
            "action_before": self.action_before,
            "action_after": self.action_after,
            "severity_before": self.severity_before,
            "severity_after": self.severity_after,
            "reasons_before": list(self.reasons_before),
            "reasons_after": list(self.reasons_after),
            "transition_key": self.transition_key(),
        }


def _parse_int_list(raw: str) -> list[int]:
    return [int(part.strip()) for part in str(raw).split(",") if part.strip()]


def _kind(before: EvalOutcome, after: EvalOutcome) -> str:
    delta = int(after.severity) - int(before.severity)
    if delta < 0:
        return "severity_drop_adjacent"
    if delta > 0:
        return "severity_rise_adjacent"
    return "reason_flip_adjacent"


def _eval(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    pending_volume_same_direction: int,
    confidence_bps: int,
    slippage_options_bps: list[int],
    max_attacker_amount_in: int,
    user_slippage_bps: int,
) -> EvalOutcome:
    _, decision = _eval_amount(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        fee_bps=int(fee_bps),
        amount_in=int(amount_in),
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
        slippage_options_bps=list(slippage_options_bps),
        max_attacker_amount_in=int(max_attacker_amount_in),
        user_slippage_bps=int(user_slippage_bps),
    )
    return EvalOutcome(
        action=str(decision.action),
        severity=int(_action_severity(decision.action)),
        reasons=tuple(str(r) for r in decision.reasons),
    )


def mine_pokayoke_adjacent_amount_flips(
    *,
    reserve_in_values: list[int],
    reserve_out_values: list[int],
    fee_bps_values: list[int],
    pending_volume_values: list[int],
    confidence_bps_values: list[int],
    user_slippage_bps_values: list[int],
    max_attacker_amount_in_values: list[int],
    slippage_options_bps: list[int],
    amount_min: int,
    amount_max: int,
    max_witnesses: int = 64,
) -> dict[str, Any]:
    if amount_min <= 0:
        raise ValueError("amount_min must be positive")
    if amount_max <= amount_min:
        raise ValueError("amount_max must be greater than amount_min")
    if max_witnesses <= 0:
        raise ValueError("max_witnesses must be positive")

    witnesses: list[FlipWitness] = []
    transition_counts: Counter[str] = Counter()
    kind_counts: Counter[str] = Counter()
    eval_count = 0

    for reserve_in in reserve_in_values:
        for reserve_out in reserve_out_values:
            for fee_bps in fee_bps_values:
                for pending_volume_same_direction in pending_volume_values:
                    for confidence_bps in confidence_bps_values:
                        for user_slippage_bps in user_slippage_bps_values:
                            for max_attacker_amount_in in max_attacker_amount_in_values:
                                prev = _eval(
                                    reserve_in=reserve_in,
                                    reserve_out=reserve_out,
                                    fee_bps=fee_bps,
                                    amount_in=amount_min,
                                    pending_volume_same_direction=pending_volume_same_direction,
                                    confidence_bps=confidence_bps,
                                    slippage_options_bps=slippage_options_bps,
                                    max_attacker_amount_in=max_attacker_amount_in,
                                    user_slippage_bps=user_slippage_bps,
                                )
                                eval_count += 1
                                for amount_before in range(amount_min, amount_max):
                                    amount_after = amount_before + 1
                                    curr = _eval(
                                        reserve_in=reserve_in,
                                        reserve_out=reserve_out,
                                        fee_bps=fee_bps,
                                        amount_in=amount_after,
                                        pending_volume_same_direction=pending_volume_same_direction,
                                        confidence_bps=confidence_bps,
                                        slippage_options_bps=slippage_options_bps,
                                        max_attacker_amount_in=max_attacker_amount_in,
                                        user_slippage_bps=user_slippage_bps,
                                    )
                                    eval_count += 1
                                    if curr.action != prev.action or curr.reasons != prev.reasons:
                                        witness = FlipWitness(
                                            kind=_kind(prev, curr),
                                            reserve_in=int(reserve_in),
                                            reserve_out=int(reserve_out),
                                            fee_bps=int(fee_bps),
                                            pending_volume_same_direction=int(pending_volume_same_direction),
                                            confidence_bps=int(confidence_bps),
                                            user_slippage_bps=int(user_slippage_bps),
                                            max_attacker_amount_in=int(max_attacker_amount_in),
                                            slippage_options_bps=tuple(int(x) for x in slippage_options_bps),
                                            amount_before=int(amount_before),
                                            amount_after=int(amount_after),
                                            action_before=prev.action,
                                            action_after=curr.action,
                                            severity_before=int(prev.severity),
                                            severity_after=int(curr.severity),
                                            reasons_before=tuple(prev.reasons),
                                            reasons_after=tuple(curr.reasons),
                                        )
                                        witnesses.append(witness)
                                        transition_counts[witness.transition_key()] += 1
                                        kind_counts[witness.kind] += 1
                                    prev = curr

    witnesses.sort(
        key=lambda w: (
            {"severity_drop_adjacent": 0, "severity_rise_adjacent": 1, "reason_flip_adjacent": 2}.get(w.kind, 9),
            w.amount_before,
            w.reserve_in,
            w.reserve_out,
            w.fee_bps,
            w.pending_volume_same_direction,
            w.confidence_bps,
            w.user_slippage_bps,
            w.max_attacker_amount_in,
            w.transition_key(),
        )
    )
    truncated = witnesses[:max_witnesses]

    return {
        "schema": SCHEMA,
        "search": {
            "reserve_in_values": list(reserve_in_values),
            "reserve_out_values": list(reserve_out_values),
            "fee_bps_values": list(fee_bps_values),
            "pending_volume_values": list(pending_volume_values),
            "confidence_bps_values": list(confidence_bps_values),
            "user_slippage_bps_values": list(user_slippage_bps_values),
            "max_attacker_amount_in_values": list(max_attacker_amount_in_values),
            "slippage_options_bps": list(slippage_options_bps),
            "amount_min": int(amount_min),
            "amount_max": int(amount_max),
            "max_witnesses": int(max_witnesses),
        },
        "eval_count": int(eval_count),
        "witness_count_total": int(len(witnesses)),
        "witness_count_returned": int(len(truncated)),
        "kind_counts": dict(sorted(kind_counts.items())),
        "transition_counts": [{"transition_key": key, "count": int(count)} for key, count in sorted(transition_counts.items())],
        "witnesses": [w.to_json() for w in truncated],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Bounded Pokayoke falsifier miner for adjacent amount action flips.")
    ap.add_argument("--reserve-in-values", default="500")
    ap.add_argument("--reserve-out-values", default="500")
    ap.add_argument("--fee-bps-values", default="0")
    ap.add_argument("--pending-volume-values", default="0")
    ap.add_argument("--confidence-bps-values", default="9000")
    ap.add_argument("--user-slippage-bps-values", default="10")
    ap.add_argument("--max-attacker-amount-in-values", default="500")
    ap.add_argument("--slippage-options-bps", default="10,50,100,300,500")
    ap.add_argument("--amount-min", type=int, default=1)
    ap.add_argument("--amount-max", type=int, default=128)
    ap.add_argument("--max-witnesses", type=int, default=64)
    ap.add_argument("--out", default="")
    args = ap.parse_args()

    report = mine_pokayoke_adjacent_amount_flips(
        reserve_in_values=_parse_int_list(args.reserve_in_values),
        reserve_out_values=_parse_int_list(args.reserve_out_values),
        fee_bps_values=_parse_int_list(args.fee_bps_values),
        pending_volume_values=_parse_int_list(args.pending_volume_values),
        confidence_bps_values=_parse_int_list(args.confidence_bps_values),
        user_slippage_bps_values=_parse_int_list(args.user_slippage_bps_values),
        max_attacker_amount_in_values=_parse_int_list(args.max_attacker_amount_in_values),
        slippage_options_bps=_parse_int_list(args.slippage_options_bps),
        amount_min=int(args.amount_min),
        amount_max=int(args.amount_max),
        max_witnesses=int(args.max_witnesses),
    )

    payload = json.dumps(report, sort_keys=True, indent=2)
    if args.out:
        out_path = Path(args.out).resolve()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(payload + "\n", encoding="utf-8")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
