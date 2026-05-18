#!/usr/bin/env python3
"""Generate synthetic AutoTraderEnergy candidate-action datasets."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from random import Random
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.autotrader_energy import (  # noqa: E402
    ACTION_KINDS,
    AutoTraderCandidate,
    AutoTraderContext,
    rows_for_candidate_set,
    save_jsonl,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contexts", type=int, default=400)
    parser.add_argument("--candidates-per-context", type=int, default=10)
    parser.add_argument("--seed", type=int, default=20260518)
    parser.add_argument("--profile", choices=("easy", "hard"), default="easy")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--metadata-output", type=Path)
    args = parser.parse_args()

    rows = list(generate_rows(
        contexts=args.contexts,
        candidates_per_context=args.candidates_per_context,
        seed=args.seed,
        profile=args.profile,
    ))
    save_jsonl(rows, args.output)
    metadata = _metadata(
        rows,
        contexts=args.contexts,
        candidates_per_context=args.candidates_per_context,
        seed=args.seed,
        profile=args.profile,
    )
    if args.metadata_output is not None:
        args.metadata_output.parent.mkdir(parents=True, exist_ok=True)
        args.metadata_output.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(metadata, indent=2, sort_keys=True))
    return 0


def generate_rows(
    *,
    contexts: int,
    candidates_per_context: int,
    seed: int,
    profile: str = "easy",
) -> Iterable[dict[str, object]]:
    rng = Random(seed)
    for index in range(contexts):
        context = _generate_context(rng, index, profile=profile)
        candidates = _generate_candidates(rng, context, candidates_per_context, profile=profile)
        yield from rows_for_candidate_set(context, candidates)


def _generate_context(rng: Random, index: int, *, profile: str) -> AutoTraderContext:
    window_budget = rng.randint(500, 5_000)
    window_used = rng.randint(0, int(window_budget * 0.85))
    lifetime_limit = rng.randint(5_000, 50_000)
    lifetime_spent = rng.randint(0, int(lifetime_limit * 0.85))
    max_live_orders = rng.randint(1, 6)
    live_order_high = max_live_orders if profile == "easy" else max(0, max_live_orders - 1)
    return AutoTraderContext(
        context_id=f"synthetic-autotrader-{index:08d}",
        budget_remaining=rng.randint(50, max(100, window_budget - window_used + 100)),
        window_budget=window_budget,
        window_budget_used=window_used,
        lifetime_limit=lifetime_limit,
        lifetime_spent=lifetime_spent,
        live_orders=rng.randint(0, live_order_high),
        max_live_orders=max_live_orders,
        max_quote_age_s=rng.choice((15, 30, 60, 120)),
        max_slippage_bps=rng.choice((25, 50, 100, 150, 250)),
        volatility_bps=rng.randint(0, 500),
        inventory_skew_bps=rng.randint(-750, 750),
        trust_bps=rng.randint(5_000, 10_000),
        kill_switch_active=rng.random() < (0.08 if profile == "easy" else 0.02),
        session_nonce_expected=rng.randint(1, 1_000_000),
    )


def _generate_candidates(
    rng: Random,
    context: AutoTraderContext,
    count: int,
    *,
    profile: str,
) -> tuple[AutoTraderCandidate, ...]:
    candidates = [
        AutoTraderCandidate(
            candidate_id=f"{context.context_id}:noop",
            kind="no_op",
            requested=True,
            admissible_hint=True,
            wallet_capability_ok=True,
            signal_provenance_ok=True,
            route_sanity_ok=True,
            oracle_freshness_ok=True,
            execution_window_ok=True,
            nonce=context.session_nonce_expected,
            order_size=0,
            quote_age_s=0,
            slippage_bps=0,
            edge_bps=0,
            gas_bps=0,
            risk_bps=0,
            action_priority=0,
        )
    ]
    if profile == "hard":
        candidates.extend(_hard_seed_candidates(rng, context))
    safe_size = max(1, min(context.budget_remaining, context.window_budget - context.window_budget_used, 300))
    candidates.append(
        AutoTraderCandidate(
            candidate_id=f"{context.context_id}:safe_submit",
            kind="submit",
            requested=True,
            admissible_hint=True,
            wallet_capability_ok=True,
            signal_provenance_ok=True,
            route_sanity_ok=True,
            oracle_freshness_ok=True,
            execution_window_ok=True,
            nonce=context.session_nonce_expected,
            order_size=safe_size,
            quote_age_s=min(5, context.max_quote_age_s),
            slippage_bps=max(1, context.max_slippage_bps // 3),
            edge_bps=context.max_slippage_bps + 220 + context.volatility_bps // 3,
            gas_bps=10,
            risk_bps=20,
            action_priority=1,
        )
    )
    while len(candidates) < count:
        kind = rng.choice(ACTION_KINDS[1:])
        valid_hint = profile == "hard" and rng.random() < 0.45
        candidate = AutoTraderCandidate(
            candidate_id=f"{context.context_id}:candidate:{len(candidates)}",
            kind=kind,
            requested=rng.random() > 0.03,
            admissible_hint=rng.random() > 0.12,
            wallet_capability_ok=True if valid_hint else rng.random() > 0.08,
            signal_provenance_ok=True if valid_hint else rng.random() > 0.12,
            route_sanity_ok=True if valid_hint else rng.random() > 0.10,
            oracle_freshness_ok=True if valid_hint else rng.random() > 0.10,
            execution_window_ok=True if valid_hint else rng.random() > 0.08,
            nonce=context.session_nonce_expected
            if valid_hint
            else context.session_nonce_expected + (0 if rng.random() > 0.12 else rng.choice((-2, -1, 1, 2))),
            order_size=rng.randint(1, _max_valid_order_size(context) if valid_hint else max(1, context.window_budget)),
            quote_age_s=rng.randint(0, context.max_quote_age_s if valid_hint else context.max_quote_age_s * 3),
            slippage_bps=rng.randint(0, context.max_slippage_bps if valid_hint else context.max_slippage_bps * 3),
            edge_bps=rng.randint(-150, context.max_slippage_bps * 4 + 500),
            gas_bps=rng.randint(0, 180),
            risk_bps=rng.randint(0, 350),
            action_priority=len(candidates),
        )
        candidates.append(candidate)
    return tuple(candidates[:count])


def _hard_seed_candidates(rng: Random, context: AutoTraderContext) -> list[AutoTraderCandidate]:
    max_size = _max_valid_order_size(context)
    small_size = max(1, min(max_size, 80 + rng.randint(0, 60)))
    large_size = max(1, min(max_size, 650 + rng.randint(0, 450)))
    fresh_age = min(context.max_quote_age_s, rng.randint(0, max(1, context.max_quote_age_s // 3)))
    base_slippage = max(1, context.max_slippage_bps // 3)
    return [
        AutoTraderCandidate(
            candidate_id=f"{context.context_id}:hard_valid_low_gas",
            kind=rng.choice(("submit", "reduce", "reroute")),
            requested=True,
            admissible_hint=True,
            wallet_capability_ok=True,
            signal_provenance_ok=True,
            route_sanity_ok=True,
            oracle_freshness_ok=True,
            execution_window_ok=True,
            nonce=context.session_nonce_expected,
            order_size=large_size,
            quote_age_s=fresh_age,
            slippage_bps=base_slippage,
            edge_bps=context.max_slippage_bps + 260 + rng.randint(0, 120),
            gas_bps=rng.randint(0, 12),
            risk_bps=rng.randint(0, 40),
            action_priority=1,
        ),
        AutoTraderCandidate(
            candidate_id=f"{context.context_id}:hard_valid_high_edge_high_cost",
            kind=rng.choice(("submit", "hedge", "reroute")),
            requested=True,
            admissible_hint=True,
            wallet_capability_ok=True,
            signal_provenance_ok=True,
            route_sanity_ok=True,
            oracle_freshness_ok=True,
            execution_window_ok=True,
            nonce=context.session_nonce_expected,
            order_size=small_size,
            quote_age_s=fresh_age,
            slippage_bps=base_slippage,
            edge_bps=context.max_slippage_bps + 430 + rng.randint(0, 170),
            gas_bps=rng.randint(180, 380),
            risk_bps=rng.randint(90, 220),
            action_priority=2,
        ),
        AutoTraderCandidate(
            candidate_id=f"{context.context_id}:hard_invalid_attractive",
            kind=rng.choice(("submit", "hedge", "reroute")),
            requested=True,
            admissible_hint=True,
            wallet_capability_ok=True,
            signal_provenance_ok=False,
            route_sanity_ok=True,
            oracle_freshness_ok=True,
            execution_window_ok=True,
            nonce=context.session_nonce_expected,
            order_size=max(1, min(max_size, 500 + rng.randint(0, 500))),
            quote_age_s=fresh_age,
            slippage_bps=0,
            edge_bps=context.max_slippage_bps + 700 + rng.randint(0, 500),
            gas_bps=0,
            risk_bps=0,
            action_priority=3,
        ),
    ]


def _max_valid_order_size(context: AutoTraderContext) -> int:
    return max(
        1,
        min(
            context.budget_remaining,
            context.window_budget - context.window_budget_used,
            context.lifetime_limit - context.lifetime_spent,
        ),
    )


def _metadata(
    rows: list[dict[str, object]],
    *,
    contexts: int,
    candidates_per_context: int,
    seed: int,
    profile: str,
) -> dict[str, object]:
    winners = [row for row in rows if row["label"]["is_winner"]]  # type: ignore[index]
    valid = [row for row in rows if row["label"]["valid"]]  # type: ignore[index]
    by_kind: dict[str, int] = {}
    for row in rows:
        by_kind[str(row["candidate_kind"])] = by_kind.get(str(row["candidate_kind"]), 0) + 1
    return {
        "schema": "zenodex/energy/autotrader_dataset_metadata/v1",
        "source": "synthetic",
        "seed": seed,
        "profile": profile,
        "contexts_requested": contexts,
        "candidates_per_context": candidates_per_context,
        "rows": len(rows),
        "valid_rows": len(valid),
        "invalid_rows": len(rows) - len(valid),
        "winner_rows": len(winners),
        "candidate_kind_counts": by_kind,
        "synthetic_only": True,
    }


if __name__ == "__main__":
    raise SystemExit(main())
