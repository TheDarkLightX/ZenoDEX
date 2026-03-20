from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.exact_out_many_pool_repaired_replacement_shadow_benchmark_v1 import (
    benchmark_exact_out_many_pool_repaired_replacement_shadow_on_curve_templates,
)


def _parse_reserve_pair(text: str) -> tuple[int, int]:
    left, sep, right = text.partition(",")
    if not sep:
        raise argparse.ArgumentTypeError("reserve templates must look like '20,10'")
    try:
        reserve0 = int(left)
        reserve1 = int(right)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc
    if reserve0 <= 0 or reserve1 <= 0:
        raise argparse.ArgumentTypeError("reserve template values must be positive")
    return reserve0, reserve1


def _parse_curve_template(text: str) -> tuple[tuple[int, int], str, object | None]:
    reserve_text, sep, remainder = text.partition("|")
    if not sep:
        raise argparse.ArgumentTypeError(
            "curve templates must look like '20,10|CPMM' or '20,10|SUM_BOOST_V1|{\"mu_num\":1,\"mu_den\":2}'"
        )
    reserve_pair = _parse_reserve_pair(reserve_text)
    curve_tag, sep, curve_params_text = remainder.partition("|")
    if not curve_tag.strip():
        raise argparse.ArgumentTypeError("curve template curve_tag must be non-empty")
    if not sep:
        return reserve_pair, curve_tag.strip(), None
    try:
        curve_params = json.loads(curve_params_text)
    except json.JSONDecodeError as exc:
        raise argparse.ArgumentTypeError(f"invalid curve template JSON params: {exc}") from exc
    return reserve_pair, curve_tag.strip(), curve_params


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Benchmark current default many-pool policy against the repaired selected-domain replacement candidate."
    )
    parser.add_argument(
        "--curve-template",
        action="append",
        dest="curve_templates",
        required=True,
        help=(
            "Curve template in the form reserve_in,reserve_out|CURVE_TAG or "
            "reserve_in,reserve_out|CURVE_TAG|<json-params>. Repeat to add more templates."
        ),
    )
    parser.add_argument("--num-pools", type=int, default=3)
    parser.add_argument("--amount-out", type=int, action="append", dest="amount_out_values", required=True)
    parser.add_argument("--max-legs", type=int, default=3)
    parser.add_argument("--max-candidate-pools", type=int, default=3)
    parser.add_argument("--max-candidates", type=int, default=12)
    parser.add_argument("--max-iters", type=int, default=4096)
    parser.add_argument("--window", type=int, default=64)
    parser.add_argument("--brute-force-max", type=int, default=512)
    parser.add_argument("--max-full-domain-pools", type=int, default=8)
    parser.add_argument("--max-enumerated-candidates", type=int, default=20_000)
    parser.add_argument(
        "--require-non-cpmm-pool",
        action="store_true",
        help="Keep only cases whose ordered pool tuple contains at least one non-CPMM pool.",
    )
    args = parser.parse_args()

    result = benchmark_exact_out_many_pool_repaired_replacement_shadow_on_curve_templates(
        curve_templates=tuple(_parse_curve_template(text) for text in args.curve_templates),
        num_pools=int(args.num_pools),
        amount_out_values=tuple(int(value) for value in args.amount_out_values),
        max_legs=int(args.max_legs),
        max_candidate_pools=int(args.max_candidate_pools),
        max_candidates=int(args.max_candidates),
        max_iters=int(args.max_iters),
        window=int(args.window),
        brute_force_max=int(args.brute_force_max),
        max_full_domain_pools=int(args.max_full_domain_pools),
        max_enumerated_candidates=int(args.max_enumerated_candidates),
        require_non_cpmm_pool=bool(args.require_non_cpmm_pool),
    )
    payload = {
        "curve_templates": result.curve_templates,
        "num_pools": result.num_pools,
        "amount_out_values": result.amount_out_values,
        "require_non_cpmm_pool": result.require_non_cpmm_pool,
        "total_cases": result.total_cases,
        "infeasible_cases": result.infeasible_cases,
        "evaluated_cases": result.evaluated_cases,
        "shadow_packet_ok_cases": result.shadow_packet_ok_cases,
        "default_packet_ok_cases": result.default_packet_ok_cases,
        "replacement_available_cases": result.replacement_available_cases,
        "replacement_quote_matches_full_canonical_cases": result.replacement_quote_matches_full_canonical_cases,
        "replacement_quote_matches_selected_runtime_quote_cases": result.replacement_quote_matches_selected_runtime_quote_cases,
        "effective_quote_matches_replacement_quote_cases": result.effective_quote_matches_replacement_quote_cases,
        "default_effective_quote_matches_full_domain_canonical_cases": (
            result.default_effective_quote_matches_full_domain_canonical_cases
        ),
        "default_uses_repaired_advisory_cases": result.default_uses_repaired_advisory_cases,
        "strict_replacement_cases": result.strict_replacement_cases,
        "strict_replacement_case_ids": result.strict_replacement_case_ids,
        "shadow_packet_failure_case_ids": result.shadow_packet_failure_case_ids,
        "default_packet_failure_case_ids": result.default_packet_failure_case_ids,
        "replacement_unavailable_case_ids": result.replacement_unavailable_case_ids,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
