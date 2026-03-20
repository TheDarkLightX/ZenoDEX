from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Sequence

from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus, normalize_curve_config
from .exact_out_route_certificate import build_exact_out_many_pool_repaired_replacement_shadow_packet


CurveTemplate = tuple[tuple[int, int], str, object | None]


@dataclass(frozen=True)
class ExactOutManyPoolRepairedReplacementShadowBenchmarkCase:
    case_id: str
    pool_templates: tuple[str, ...]
    amount_out_total: int
    shadow_packet_ok: bool
    default_packet_ok: bool
    default_effective_quote_source: str | None
    replacement_available: bool
    replacement_quote_matches_full_canonical: bool
    replacement_quote_matches_selected_runtime_quote: bool
    effective_quote_matches_replacement_quote: bool
    default_effective_quote_matches_full_domain_canonical: bool | None
    default_uses_repaired_advisory: bool
    strict_replacement: bool


@dataclass(frozen=True)
class ExactOutManyPoolRepairedReplacementShadowBenchmarkResult:
    curve_templates: tuple[str, ...]
    num_pools: int
    amount_out_values: tuple[int, ...]
    require_non_cpmm_pool: bool
    total_cases: int
    infeasible_cases: int
    evaluated_cases: int
    shadow_packet_ok_cases: int
    default_packet_ok_cases: int
    replacement_available_cases: int
    replacement_quote_matches_full_canonical_cases: int
    replacement_quote_matches_selected_runtime_quote_cases: int
    effective_quote_matches_replacement_quote_cases: int
    default_effective_quote_matches_full_domain_canonical_cases: int
    default_uses_repaired_advisory_cases: int
    strict_replacement_cases: int
    strict_replacement_case_ids: tuple[str, ...]
    shadow_packet_failure_case_ids: tuple[str, ...]
    default_packet_failure_case_ids: tuple[str, ...]
    replacement_unavailable_case_ids: tuple[str, ...]
    cases: tuple[ExactOutManyPoolRepairedReplacementShadowBenchmarkCase, ...]


def _curve_template_text(curve_template: CurveTemplate) -> str:
    reserve_pair, curve_tag, curve_params = curve_template
    reserve0, reserve1 = reserve_pair
    tag, params = normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)
    if params:
        return f"({int(reserve0)},{int(reserve1)})/{tag}:{params}"
    return f"({int(reserve0)},{int(reserve1)})/{tag}"


def _pool_from_curve_template(pid: str, curve_template: CurveTemplate) -> PoolState:
    reserve_pair, curve_tag, curve_params = curve_template
    reserve0, reserve1 = reserve_pair
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=curve_tag,
        curve_params=curve_params,
    )


def _curve_case_id(curve_templates: Sequence[CurveTemplate], amount_out_total: int) -> str:
    template_text = ",".join(_curve_template_text(curve_template) for curve_template in curve_templates)
    return f"q={int(amount_out_total)};pools=[{template_text}]"


def benchmark_exact_out_many_pool_repaired_replacement_shadow_on_curve_templates(
    *,
    curve_templates: Sequence[CurveTemplate],
    num_pools: int,
    amount_out_values: Sequence[int],
    asset_in: str = "A",
    asset_out: str = "B",
    max_legs: int = 3,
    max_candidate_pools: int = 3,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
    require_non_cpmm_pool: bool = False,
    capture_case_limit: int = 128,
) -> ExactOutManyPoolRepairedReplacementShadowBenchmarkResult:
    if not curve_templates:
        raise ValueError("curve_templates must be non-empty")
    if int(num_pools) <= 0:
        raise ValueError("num_pools must be positive")
    if not amount_out_values:
        raise ValueError("amount_out_values must be non-empty")
    if int(capture_case_limit) <= 0:
        raise ValueError("capture_case_limit must be positive")

    total_cases = 0
    infeasible_cases = 0
    shadow_packet_ok_cases = 0
    default_packet_ok_cases = 0
    replacement_available_cases = 0
    replacement_quote_matches_full_canonical_cases = 0
    replacement_quote_matches_selected_runtime_quote_cases = 0
    effective_quote_matches_replacement_quote_cases = 0
    default_effective_quote_matches_full_domain_canonical_cases = 0
    default_uses_repaired_advisory_cases = 0
    strict_replacement_cases = 0
    strict_replacement_case_ids: list[str] = []
    shadow_packet_failure_case_ids: list[str] = []
    default_packet_failure_case_ids: list[str] = []
    replacement_unavailable_case_ids: list[str] = []
    captured_cases: list[ExactOutManyPoolRepairedReplacementShadowBenchmarkCase] = []

    normalized_templates = tuple(
        (
            (int(reserve_pair[0]), int(reserve_pair[1])),
            normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)[0],
            curve_params,
        )
        for reserve_pair, curve_tag, curve_params in curve_templates
    )

    for selected_templates in product(normalized_templates, repeat=int(num_pools)):
        if bool(require_non_cpmm_pool) and all(
            normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)[0] == CURVE_TAG_CPMM
            for _reserve_pair, curve_tag, curve_params in selected_templates
        ):
            continue
        pools = tuple(
            _pool_from_curve_template(f"p{idx}", curve_template)
            for idx, curve_template in enumerate(selected_templates)
        )
        for amount_out_total in amount_out_values:
            total_cases += 1
            case_id = _curve_case_id(selected_templates, int(amount_out_total))
            try:
                packet = build_exact_out_many_pool_repaired_replacement_shadow_packet(
                    pools,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
            except ValueError:
                infeasible_cases += 1
                continue

            payload = packet.to_dict()
            default_payload = packet.default_packet.to_dict()

            shadow_packet_ok = bool(packet.packet_ok)
            default_packet_ok = bool(packet.default_packet.packet_ok)
            replacement_available = bool(packet.replacement_available)
            replacement_quote_matches_full_canonical = bool(payload["replacement_quote_matches_full_canonical"])
            replacement_quote_matches_selected_runtime_quote = bool(packet.replacement_quote_matches_selected_runtime_quote)
            effective_quote_matches_replacement_quote = bool(packet.effective_quote_matches_replacement_quote)
            default_effective_quote_matches_full_domain_canonical = default_payload[
                "effective_quote_matches_full_domain_canonical"
            ]
            default_effective_quote_source = default_payload["effective_quote_source"]
            default_uses_repaired_advisory = default_effective_quote_source == "repaired_bounded_advisory"
            strict_replacement = bool(
                replacement_available
                and replacement_quote_matches_full_canonical
                and not effective_quote_matches_replacement_quote
            )

            shadow_packet_ok_cases += int(shadow_packet_ok)
            default_packet_ok_cases += int(default_packet_ok)
            replacement_available_cases += int(replacement_available)
            replacement_quote_matches_full_canonical_cases += int(replacement_quote_matches_full_canonical)
            replacement_quote_matches_selected_runtime_quote_cases += int(
                replacement_quote_matches_selected_runtime_quote
            )
            effective_quote_matches_replacement_quote_cases += int(effective_quote_matches_replacement_quote)
            default_effective_quote_matches_full_domain_canonical_cases += int(
                bool(default_effective_quote_matches_full_domain_canonical)
            )
            default_uses_repaired_advisory_cases += int(default_uses_repaired_advisory)
            strict_replacement_cases += int(strict_replacement)

            if strict_replacement:
                strict_replacement_case_ids.append(case_id)
            if not shadow_packet_ok:
                shadow_packet_failure_case_ids.append(case_id)
            if not default_packet_ok:
                default_packet_failure_case_ids.append(case_id)
            if not replacement_available:
                replacement_unavailable_case_ids.append(case_id)
            if len(captured_cases) < int(capture_case_limit):
                captured_cases.append(
                    ExactOutManyPoolRepairedReplacementShadowBenchmarkCase(
                        case_id=case_id,
                        pool_templates=tuple(_curve_template_text(curve_template) for curve_template in selected_templates),
                        amount_out_total=int(amount_out_total),
                        shadow_packet_ok=shadow_packet_ok,
                        default_packet_ok=default_packet_ok,
                        default_effective_quote_source=default_effective_quote_source,
                        replacement_available=replacement_available,
                        replacement_quote_matches_full_canonical=replacement_quote_matches_full_canonical,
                        replacement_quote_matches_selected_runtime_quote=replacement_quote_matches_selected_runtime_quote,
                        effective_quote_matches_replacement_quote=effective_quote_matches_replacement_quote,
                        default_effective_quote_matches_full_domain_canonical=(
                            None
                            if default_effective_quote_matches_full_domain_canonical is None
                            else bool(default_effective_quote_matches_full_domain_canonical)
                        ),
                        default_uses_repaired_advisory=bool(default_uses_repaired_advisory),
                        strict_replacement=strict_replacement,
                    )
                )

    evaluated_cases = total_cases - infeasible_cases
    return ExactOutManyPoolRepairedReplacementShadowBenchmarkResult(
        curve_templates=tuple(
            _curve_template_text(curve_template)
            for curve_template in normalized_templates
        ),
        num_pools=int(num_pools),
        amount_out_values=tuple(int(value) for value in amount_out_values),
        require_non_cpmm_pool=bool(require_non_cpmm_pool),
        total_cases=total_cases,
        infeasible_cases=infeasible_cases,
        evaluated_cases=evaluated_cases,
        shadow_packet_ok_cases=shadow_packet_ok_cases,
        default_packet_ok_cases=default_packet_ok_cases,
        replacement_available_cases=replacement_available_cases,
        replacement_quote_matches_full_canonical_cases=replacement_quote_matches_full_canonical_cases,
        replacement_quote_matches_selected_runtime_quote_cases=replacement_quote_matches_selected_runtime_quote_cases,
        effective_quote_matches_replacement_quote_cases=effective_quote_matches_replacement_quote_cases,
        default_effective_quote_matches_full_domain_canonical_cases=(
            default_effective_quote_matches_full_domain_canonical_cases
        ),
        default_uses_repaired_advisory_cases=default_uses_repaired_advisory_cases,
        strict_replacement_cases=strict_replacement_cases,
        strict_replacement_case_ids=tuple(strict_replacement_case_ids),
        shadow_packet_failure_case_ids=tuple(shadow_packet_failure_case_ids),
        default_packet_failure_case_ids=tuple(default_packet_failure_case_ids),
        replacement_unavailable_case_ids=tuple(replacement_unavailable_case_ids),
        cases=tuple(captured_cases),
    )
