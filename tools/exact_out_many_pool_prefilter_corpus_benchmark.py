from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.kernels.python.exact_out_many_pool_prefilter_corpus_benchmark_v1 import (
    benchmark_exact_out_many_pool_prefilter_cover_search,
    benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates,
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
        description="Benchmark current exact-out many-pool prefilter vs bounded cover-search repair."
    )
    template_group = parser.add_mutually_exclusive_group(required=True)
    template_group.add_argument(
        "--reserve-template",
        action="append",
        dest="reserve_templates",
        help="Reserve template in the form reserve_in,reserve_out. Repeat to add more templates.",
    )
    template_group.add_argument(
        "--curve-template",
        action="append",
        dest="curve_templates",
        help=(
            "Curve template in the form reserve_in,reserve_out|CURVE_TAG or "
            "reserve_in,reserve_out|CURVE_TAG|<json-params>. Repeat to add more templates."
        ),
    )
    parser.add_argument("--num-pools", type=int, default=4)
    parser.add_argument("--amount-out", type=int, action="append", dest="amount_out_values", required=True)
    parser.add_argument("--max-legs", type=int, default=3)
    parser.add_argument("--max-candidate-pools", type=int, default=3)
    parser.add_argument("--max-full-domain-pools", type=int, default=8)
    parser.add_argument("--max-enumerated-candidates", type=int, default=20_000)
    parser.add_argument(
        "--require-non-cpmm-pool",
        action="store_true",
        help="When used with --curve-template, keep only cases whose ordered pool tuple contains at least one non-CPMM pool.",
    )
    args = parser.parse_args()

    if args.curve_templates:
        result = benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
            curve_templates=tuple(_parse_curve_template(text) for text in args.curve_templates),
            num_pools=int(args.num_pools),
            amount_out_values=tuple(int(value) for value in args.amount_out_values),
            max_legs=int(args.max_legs),
            max_candidate_pools=int(args.max_candidate_pools),
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
            "current_matches_full_canonical_cases": result.current_matches_full_canonical_cases,
            "cover_matches_full_canonical_cases": result.cover_matches_full_canonical_cases,
            "current_contraction_holds_cases": result.current_contraction_holds_cases,
            "cover_contraction_holds_cases": result.cover_contraction_holds_cases,
            "strict_improvement_cases": result.strict_improvement_cases,
            "cover_never_worse_cases": result.cover_never_worse_cases,
            "bounded_cover_search_cases": result.bounded_cover_search_cases,
            "max_searched_subset_count": result.max_searched_subset_count,
            "strict_improvement_case_ids": result.strict_improvement_case_ids,
            "current_mismatch_case_ids": result.current_mismatch_case_ids,
            "cover_mismatch_case_ids": result.cover_mismatch_case_ids,
        }
    else:
        result = benchmark_exact_out_many_pool_prefilter_cover_search(
            reserve_templates=tuple(_parse_reserve_pair(text) for text in args.reserve_templates),
            num_pools=int(args.num_pools),
            amount_out_values=tuple(int(value) for value in args.amount_out_values),
            max_legs=int(args.max_legs),
            max_candidate_pools=int(args.max_candidate_pools),
            max_full_domain_pools=int(args.max_full_domain_pools),
            max_enumerated_candidates=int(args.max_enumerated_candidates),
        )
        payload = {
            "reserve_templates": result.reserve_templates,
            "num_pools": result.num_pools,
            "amount_out_values": result.amount_out_values,
            "total_cases": result.total_cases,
            "infeasible_cases": result.infeasible_cases,
            "evaluated_cases": result.evaluated_cases,
            "current_matches_full_canonical_cases": result.current_matches_full_canonical_cases,
            "cover_matches_full_canonical_cases": result.cover_matches_full_canonical_cases,
            "current_contraction_holds_cases": result.current_contraction_holds_cases,
            "cover_contraction_holds_cases": result.cover_contraction_holds_cases,
            "strict_improvement_cases": result.strict_improvement_cases,
            "cover_never_worse_cases": result.cover_never_worse_cases,
            "bounded_cover_search_cases": result.bounded_cover_search_cases,
            "max_searched_subset_count": result.max_searched_subset_count,
            "strict_improvement_case_ids": result.strict_improvement_case_ids,
            "current_mismatch_case_ids": result.current_mismatch_case_ids,
        }
    print(
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
