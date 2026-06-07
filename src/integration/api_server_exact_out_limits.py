from __future__ import annotations

DEX_API_MAX_ROUTE_AMOUNT_IN = 50_000
DEX_API_EXACT_OUT_CANDIDATE_EVAL_BUDGET = 4_096

DEX_API_EXACT_OUT_SEARCH_CAPS = {
    "amount_out_total": (1, DEX_API_MAX_ROUTE_AMOUNT_IN),
    "max_legs": (1, 3),
    "max_candidate_pools": (1, 5),
    "max_candidates": (1, 12),
    "max_iters": (1, 4_096),
    "window": (0, 64),
    "brute_force_max": (0, 512),
    "max_full_domain_pools": (1, 16),
    "max_enumerated_candidates": (1, 50_000),
}
