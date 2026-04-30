#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from itertools import product
from pathlib import Path

BPS = 10_000


@dataclass(frozen=True)
class RevenueSurface:
    name: str
    kind: str
    notional_units: int
    value_created_units: int
    protocol_surplus_units: int = 0
    ops_cost_units: int = 0
    recurring: bool = True
    washable: bool = False
    user_no_worse_required: bool = True
    primary_revenue: bool = True


@dataclass(frozen=True)
class SinkSplit:
    name: str
    burn_bps: int
    treasury_bps: int
    proof_security_bps: int
    liquidity_bps: int
    lock_reward_bps: int
    user_rebate_bps: int


@dataclass(frozen=True)
class RevenuePolicy:
    name: str
    base_notional_fee_bps: int
    value_capture_bps: int
    pro_notional_fee_bps: int
    bot_profit_share_bps: int
    insurance_premium_bps: int
    exit_penalty_bps: int
    solver_reward_bps: int
    fee_rebate_bps: int
    usage_reward_bps: int
    subsidy_emission_units: int
    sink: SinkSplit


@dataclass(frozen=True)
class SurfaceResult:
    surface: str
    kind: str
    user_value_created: int
    user_fee_paid: int
    solver_reward: int
    protocol_revenue_gross: int
    protocol_revenue_net: int
    user_net_value: int
    recurring: bool
    primary_revenue: bool
    washable: bool


@dataclass(frozen=True)
class PolicyScore:
    policy: str
    rails_ok: bool
    survivor: bool
    total_user_value_created: int
    total_user_fee_paid: int
    total_user_net_value: int
    gross_protocol_revenue: int
    net_protocol_revenue: int
    recurring_revenue: int
    primary_recurring_revenue: int
    penalty_revenue: int
    solver_rewards: int
    burn_budget: int
    treasury_budget: int
    proof_security_budget: int
    liquidity_budget: int
    lock_reward_budget: int
    user_rebate_budget: int
    subsidy_emission_units: int
    deflation_margin: int
    negative_user_surface_count: int
    wash_profit_max: int
    recurring_revenue_bps: int
    primary_recurring_revenue_bps: int
    penalty_dependency_bps: int
    passive_reward_over_burn_bps: int
    rail_violation_count: int
    score: float
    surfaces: tuple[SurfaceResult, ...]


SURFACES = (
    RevenueSurface(
        "swap_base_protocol_rake",
        "base_notional",
        notional_units=200_000,
        value_created_units=180,
        ops_cost_units=4,
        recurring=True,
        washable=True,
    ),
    RevenueSurface(
        "route_surplus_capture",
        "value_capture",
        notional_units=200_000,
        value_created_units=1_200,
        ops_cost_units=15,
        recurring=True,
        washable=True,
    ),
    RevenueSurface(
        "exact_out_savings_capture",
        "value_capture",
        notional_units=140_000,
        value_created_units=700,
        ops_cost_units=12,
        recurring=True,
        washable=True,
    ),
    RevenueSurface(
        "cow_batch_solver_surplus",
        "solver_value_capture",
        notional_units=240_000,
        value_created_units=1_500,
        ops_cost_units=20,
        recurring=True,
        washable=False,
    ),
    RevenueSurface(
        "mev_protection_receipt",
        "base_notional",
        notional_units=150_000,
        value_created_units=160,
        ops_cost_units=10,
        recurring=True,
        washable=True,
    ),
    RevenueSurface(
        "automation_orders",
        "pro_notional",
        notional_units=120_000,
        value_created_units=300,
        ops_cost_units=12,
        recurring=True,
        washable=False,
    ),
    RevenueSurface(
        "pro_certificate_api",
        "pro_notional",
        notional_units=500_000,
        value_created_units=1_000,
        ops_cost_units=35,
        recurring=True,
        washable=False,
    ),
    RevenueSurface(
        "integrator_router_surface",
        "pro_notional",
        notional_units=400_000,
        value_created_units=900,
        ops_cost_units=30,
        recurring=True,
        washable=True,
    ),
    RevenueSurface(
        "treasury_market_maker_bot",
        "bot_profit_share",
        notional_units=0,
        value_created_units=0,
        protocol_surplus_units=850,
        ops_cost_units=60,
        recurring=True,
        washable=False,
        user_no_worse_required=False,
    ),
    RevenueSurface(
        "arbitrage_recapture_auction",
        "auction_surplus_capture",
        notional_units=0,
        value_created_units=0,
        protocol_surplus_units=1_100,
        ops_cost_units=50,
        recurring=True,
        washable=False,
        user_no_worse_required=False,
    ),
    RevenueSurface(
        "lp_loss_cover_premium",
        "insurance_premium",
        notional_units=100_000,
        value_created_units=550,
        protocol_surplus_units=250,
        ops_cost_units=15,
        recurring=True,
        washable=False,
    ),
    RevenueSurface(
        "staking_early_exit_penalty",
        "exit_penalty",
        notional_units=50_000,
        value_created_units=0,
        ops_cost_units=0,
        recurring=False,
        washable=False,
        user_no_worse_required=False,
        primary_revenue=False,
    ),
)


SINK_SPLITS = (
    SinkSplit("fire_revenue_backed", 4500, 1500, 1500, 1000, 1000, 500),
    SinkSplit("max_burn_guarded", 8000, 500, 500, 500, 300, 200),
    SinkSplit("growth_balanced", 3500, 1500, 1500, 1500, 1000, 1000),
    SinkSplit("passive_reward_heavy", 2000, 1000, 1000, 1000, 4000, 1000),
)


NAMED_POLICIES = (
    RevenuePolicy("zero_fee", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, SINK_SPLITS[0]),
    RevenuePolicy("fee_surface_launch", 3, 2500, 8, 5000, 30, 0, 5000, 5000, 0, 0, SINK_SPLITS[0]),
    RevenuePolicy("surplus_bot_heavy", 0, 5000, 5, 8000, 30, 0, 3000, 2500, 0, 0, SINK_SPLITS[1]),
    RevenuePolicy("extractive_notional", 45, 7000, 45, 8000, 90, 2500, 7000, 8000, 2500, 0, SINK_SPLITS[1]),
    RevenuePolicy("wash_rebate_farm", 5, 2500, 10, 5000, 30, 500, 5000, 12_000, 8000, 0, SINK_SPLITS[2]),
    RevenuePolicy("penalty_dependency", 0, 0, 0, 0, 0, 2500, 0, 0, 0, 0, SINK_SPLITS[0]),
    RevenuePolicy("subsidized_passive_yield", 3, 2500, 8, 5000, 30, 500, 5000, 5000, 0, 900, SINK_SPLITS[3]),
)


def floor_bps(amount: int, bps: int) -> int:
    return int(amount) * int(bps) // BPS


def sink_sum(sink: SinkSplit) -> int:
    return (
        int(sink.burn_bps)
        + int(sink.treasury_bps)
        + int(sink.proof_security_bps)
        + int(sink.liquidity_bps)
        + int(sink.lock_reward_bps)
        + int(sink.user_rebate_bps)
    )


def recurring_bps(amount: int, gross: int) -> int:
    if gross <= 0:
        return 0
    return floor_bps(BPS, 0) + int(amount) * BPS // int(gross)


def rail_violations(policy: RevenuePolicy) -> list[str]:
    out: list[str] = []
    if not 0 <= policy.base_notional_fee_bps <= 25:
        out.append("base_notional_fee_bps")
    if not 0 <= policy.value_capture_bps <= 7000:
        out.append("value_capture_bps")
    if not 0 <= policy.pro_notional_fee_bps <= 30:
        out.append("pro_notional_fee_bps")
    if not 0 <= policy.bot_profit_share_bps <= 8000:
        out.append("bot_profit_share_bps")
    if not 0 <= policy.insurance_premium_bps <= 80:
        out.append("insurance_premium_bps")
    if not 0 <= policy.exit_penalty_bps <= 2500:
        out.append("exit_penalty_bps")
    if not 0 <= policy.solver_reward_bps <= 7000:
        out.append("solver_reward_bps")
    if policy.solver_reward_bps + policy.value_capture_bps > BPS:
        out.append("solver_plus_protocol_capture")
    if not 0 <= policy.fee_rebate_bps <= 10_000:
        out.append("fee_rebate_bps")
    if not 0 <= policy.usage_reward_bps <= 5000:
        out.append("usage_reward_bps")
    if policy.fee_rebate_bps + policy.usage_reward_bps > BPS:
        out.append("wash_reward_above_fee")
    if policy.subsidy_emission_units < 0:
        out.append("subsidy_emission_units")
    if sink_sum(policy.sink) != BPS:
        out.append("sink_sum")
    if policy.sink.burn_bps < 3000:
        out.append("burn_floor")
    if policy.sink.treasury_bps < 500:
        out.append("treasury_floor")
    if policy.sink.proof_security_bps < 500:
        out.append("proof_security_floor")
    if policy.sink.liquidity_bps < 500:
        out.append("liquidity_floor")
    if policy.sink.lock_reward_bps > 2500:
        out.append("passive_lock_reward_cap")
    return out


def evaluate_surface(policy: RevenuePolicy, surface: RevenueSurface) -> SurfaceResult:
    if surface.kind == "base_notional":
        user_fee = floor_bps(surface.notional_units, policy.base_notional_fee_bps)
        solver_reward = 0
        protocol_gross = user_fee
    elif surface.kind == "value_capture":
        user_fee = floor_bps(surface.value_created_units, policy.value_capture_bps)
        solver_reward = 0
        protocol_gross = user_fee
    elif surface.kind == "solver_value_capture":
        solver_reward = floor_bps(surface.value_created_units, policy.solver_reward_bps)
        protocol_gross = floor_bps(surface.value_created_units, policy.value_capture_bps)
        user_fee = solver_reward + protocol_gross
    elif surface.kind == "pro_notional":
        user_fee = floor_bps(surface.notional_units, policy.pro_notional_fee_bps)
        solver_reward = 0
        protocol_gross = user_fee
    elif surface.kind == "bot_profit_share":
        user_fee = 0
        solver_reward = 0
        protocol_gross = floor_bps(surface.protocol_surplus_units, policy.bot_profit_share_bps)
    elif surface.kind == "auction_surplus_capture":
        user_fee = 0
        solver_reward = 0
        protocol_gross = floor_bps(surface.protocol_surplus_units, policy.value_capture_bps)
    elif surface.kind == "insurance_premium":
        user_fee = floor_bps(surface.notional_units, policy.insurance_premium_bps)
        solver_reward = 0
        protocol_gross = user_fee
    elif surface.kind == "exit_penalty":
        user_fee = floor_bps(surface.notional_units, policy.exit_penalty_bps)
        solver_reward = 0
        protocol_gross = user_fee
    else:
        raise ValueError(f"unknown surface kind: {surface.kind}")

    direct_cost = int(surface.ops_cost_units)
    if surface.kind == "insurance_premium":
        direct_cost += int(surface.protocol_surplus_units)
    net = int(protocol_gross) - direct_cost
    user_net = int(surface.value_created_units) - int(user_fee)
    return SurfaceResult(
        surface=surface.name,
        kind=surface.kind,
        user_value_created=int(surface.value_created_units),
        user_fee_paid=int(user_fee),
        solver_reward=int(solver_reward),
        protocol_revenue_gross=int(protocol_gross),
        protocol_revenue_net=int(net),
        user_net_value=int(user_net),
        recurring=bool(surface.recurring),
        primary_revenue=bool(surface.primary_revenue),
        washable=bool(surface.washable),
    )


def wash_profit(policy: RevenuePolicy, result: SurfaceResult, surface: RevenueSurface) -> int:
    if not surface.washable or result.user_fee_paid <= 0:
        return -1
    execution_drag = floor_bps(surface.notional_units, 2) + 1
    reward = floor_bps(result.user_fee_paid, policy.fee_rebate_bps + policy.usage_reward_bps)
    return int(reward) - int(result.user_fee_paid) - int(execution_drag)


def evaluate_policy(policy: RevenuePolicy) -> PolicyScore:
    surfaces = tuple(evaluate_surface(policy, surface) for surface in SURFACES)
    violations = rail_violations(policy)

    total_user_value = sum(s.user_value_created for s in surfaces)
    total_user_fee = sum(s.user_fee_paid for s in surfaces)
    total_user_net = sum(
        s.user_net_value
        for s, surface in zip(surfaces, SURFACES)
        if surface.user_no_worse_required
    )
    gross = sum(s.protocol_revenue_gross for s in surfaces)
    net = sum(s.protocol_revenue_net for s in surfaces)
    recurring = sum(s.protocol_revenue_gross for s in surfaces if s.recurring)
    primary_recurring = sum(s.protocol_revenue_gross for s in surfaces if s.recurring and s.primary_revenue)
    penalty_revenue = sum(s.protocol_revenue_gross for s in surfaces if s.kind == "exit_penalty")
    solver_rewards = sum(s.solver_reward for s in surfaces)
    negative_user_count = sum(
        1
        for s, surface in zip(surfaces, SURFACES)
        if surface.user_no_worse_required and s.user_net_value < 0
    )
    wash_max = max(wash_profit(policy, s, surface) for s, surface in zip(surfaces, SURFACES))

    burn = max(0, floor_bps(net, policy.sink.burn_bps))
    treasury = max(0, floor_bps(net, policy.sink.treasury_bps))
    proof_security = max(0, floor_bps(net, policy.sink.proof_security_bps))
    liquidity = max(0, floor_bps(net, policy.sink.liquidity_bps))
    lock_reward = max(0, floor_bps(net, policy.sink.lock_reward_bps))
    user_rebate = max(0, floor_bps(net, policy.sink.user_rebate_bps))
    deflation_margin = burn - int(policy.subsidy_emission_units)

    recurring_share = recurring_bps(recurring, gross)
    primary_recurring_share = recurring_bps(primary_recurring, gross)
    penalty_dependency = recurring_bps(penalty_revenue, gross)
    passive_reward_over_burn = recurring_bps(lock_reward, burn)

    survivor = bool(
        not violations
        and negative_user_count == 0
        and gross > 0
        and net > 0
        and recurring_share >= 9000
        and primary_recurring_share >= 8500
        and penalty_dependency <= 1000
        and wash_max <= 0
        and burn > 0
        and treasury > 0
        and proof_security > 0
        and liquidity > 0
        and lock_reward <= burn
        and deflation_margin > 0
    )

    score = (
        float(net)
        + 1.50 * float(burn)
        + 0.60 * float(total_user_net)
        + 0.25 * float(primary_recurring)
        - 3.00 * float(max(0, wash_max))
        - 2_000.0 * float(negative_user_count)
        - 0.20 * float(penalty_revenue)
        - 0.50 * float(policy.subsidy_emission_units)
    )

    return PolicyScore(
        policy=policy.name,
        rails_ok=not violations,
        survivor=survivor,
        total_user_value_created=total_user_value,
        total_user_fee_paid=total_user_fee,
        total_user_net_value=total_user_net,
        gross_protocol_revenue=gross,
        net_protocol_revenue=net,
        recurring_revenue=recurring,
        primary_recurring_revenue=primary_recurring,
        penalty_revenue=penalty_revenue,
        solver_rewards=solver_rewards,
        burn_budget=burn,
        treasury_budget=treasury,
        proof_security_budget=proof_security,
        liquidity_budget=liquidity,
        lock_reward_budget=lock_reward,
        user_rebate_budget=user_rebate,
        subsidy_emission_units=int(policy.subsidy_emission_units),
        deflation_margin=deflation_margin,
        negative_user_surface_count=negative_user_count,
        wash_profit_max=wash_max,
        recurring_revenue_bps=recurring_share,
        primary_recurring_revenue_bps=primary_recurring_share,
        penalty_dependency_bps=penalty_dependency,
        passive_reward_over_burn_bps=passive_reward_over_burn,
        rail_violation_count=len(violations),
        score=round(score, 6),
        surfaces=surfaces,
    )


def survivor_condition_failures(score: PolicyScore) -> list[str]:
    failures: list[str] = []
    if not score.rails_ok:
        failures.append("rails")
    if score.negative_user_surface_count != 0:
        failures.append("user_no_worse")
    if score.gross_protocol_revenue <= 0:
        failures.append("gross_revenue")
    if score.net_protocol_revenue <= 0:
        failures.append("net_revenue")
    if score.recurring_revenue_bps < 9000:
        failures.append("recurring_revenue")
    if score.primary_recurring_revenue_bps < 8500:
        failures.append("primary_recurring_revenue")
    if score.penalty_dependency_bps > 1000:
        failures.append("penalty_dependency")
    if score.wash_profit_max > 0:
        failures.append("wash_profit")
    if score.burn_budget <= 0:
        failures.append("burn_budget")
    if score.treasury_budget <= 0:
        failures.append("treasury_budget")
    if score.proof_security_budget <= 0:
        failures.append("proof_security_budget")
    if score.liquidity_budget <= 0:
        failures.append("liquidity_budget")
    if score.lock_reward_budget > score.burn_budget:
        failures.append("passive_reward_over_burn")
    if score.deflation_margin <= 0:
        failures.append("deflation_margin")
    return failures


def audit_scores(scores: list[PolicyScore]) -> dict[str, object]:
    surface_by_name = {surface.name: surface for surface in SURFACES}
    gross_negative_count = 0
    user_net_identity_failures = 0
    net_identity_failures = 0
    sink_budget_overallocations = 0
    survivor_rule_failures = 0

    for score in scores:
        if score.survivor and survivor_condition_failures(score):
            survivor_rule_failures += 1
        if score.net_protocol_revenue >= 0:
            sink_total = (
                score.burn_budget
                + score.treasury_budget
                + score.proof_security_budget
                + score.liquidity_budget
                + score.lock_reward_budget
                + score.user_rebate_budget
            )
            if sink_total > score.net_protocol_revenue:
                sink_budget_overallocations += 1
        for result in score.surfaces:
            surface = surface_by_name[result.surface]
            if result.protocol_revenue_gross < 0:
                gross_negative_count += 1
            if result.user_net_value != result.user_value_created - result.user_fee_paid:
                user_net_identity_failures += 1
            expected_cost = int(surface.ops_cost_units)
            if surface.kind == "insurance_premium":
                expected_cost += int(surface.protocol_surplus_units)
            if result.protocol_revenue_net != result.protocol_revenue_gross - expected_cost:
                net_identity_failures += 1

    named = {score.policy: score for score in scores if score.policy in {policy.name for policy in NAMED_POLICIES}}
    named_expectations = {
        "zero_fee_not_revenue_generating": (
            named["zero_fee"].gross_protocol_revenue == 0
            and not named["zero_fee"].survivor
        ),
        "launch_policy_survives": named["fee_surface_launch"].survivor,
        "extractive_notional_rejected": (
            not named["extractive_notional"].survivor
            and named["extractive_notional"].negative_user_surface_count > 0
        ),
        "wash_rebate_farm_rejected": (
            not named["wash_rebate_farm"].survivor
            and (named["wash_rebate_farm"].wash_profit_max > 0 or named["wash_rebate_farm"].rail_violation_count > 0)
        ),
        "penalty_dependency_rejected": (
            not named["penalty_dependency"].survivor
            and named["penalty_dependency"].penalty_dependency_bps >= 9000
        ),
        "subsidized_passive_yield_rejected": not named["subsidized_passive_yield"].survivor,
    }

    return {
        "gross_negative_count": gross_negative_count,
        "user_net_identity_failures": user_net_identity_failures,
        "net_identity_failures": net_identity_failures,
        "sink_budget_overallocations": sink_budget_overallocations,
        "survivor_rule_failures": survivor_rule_failures,
        "named_expectations": named_expectations,
        "all_named_expectations_passed": all(named_expectations.values()),
        "total_model_invariant_failures": (
            gross_negative_count
            + user_net_identity_failures
            + net_identity_failures
            + sink_budget_overallocations
            + survivor_rule_failures
            + sum(0 if ok else 1 for ok in named_expectations.values())
        ),
    }


def iter_grid_policies() -> list[RevenuePolicy]:
    policies = list(NAMED_POLICIES)
    base_values = (0, 2, 5, 10, 25)
    capture_values = (0, 2500, 5000, 7000)
    pro_values = (0, 5, 15, 30)
    bot_values = (0, 5000, 8000)
    insurance_values = (0, 30, 60)
    exit_values = (0, 500)
    solver_values = (0, 5000, 7000)
    rebate_values = (0, 5000, 12_000)
    usage_values = (0, 2500, 8000)
    subsidy_values = (0,)
    idx = 0
    for (
        base,
        capture,
        pro,
        bot,
        insurance,
        exit_penalty,
        solver,
        rebate,
        usage,
        subsidy,
        sink,
    ) in product(
        base_values,
        capture_values,
        pro_values,
        bot_values,
        insurance_values,
        exit_values,
        solver_values,
        rebate_values,
        usage_values,
        subsidy_values,
        SINK_SPLITS,
    ):
        policies.append(
            RevenuePolicy(
                name=f"grid_{idx:06d}_{sink.name}",
                base_notional_fee_bps=base,
                value_capture_bps=capture,
                pro_notional_fee_bps=pro,
                bot_profit_share_bps=bot,
                insurance_premium_bps=insurance,
                exit_penalty_bps=exit_penalty,
                solver_reward_bps=solver,
                fee_rebate_bps=rebate,
                usage_reward_bps=usage,
                subsidy_emission_units=subsidy,
                sink=sink,
            )
        )
        idx += 1
    return policies


def serialize_score(score: PolicyScore, include_surfaces: bool = False) -> dict[str, object]:
    out = asdict(score)
    if not include_surfaces:
        out.pop("surfaces", None)
    return out


def main() -> None:
    policies = iter_grid_policies()
    scores = [evaluate_policy(policy) for policy in policies]
    survivors = [score for score in scores if score.survivor]
    best = max(survivors or scores, key=lambda item: item.score)
    named = {score.policy: serialize_score(score, include_surfaces=True) for score in scores if score.policy in {p.name for p in NAMED_POLICIES}}
    best_by_net = max(scores, key=lambda item: item.net_protocol_revenue)
    best_by_user = max(scores, key=lambda item: item.total_user_net_value)

    best_surface_revenue = {
        result.surface: {
            "kind": result.kind,
            "gross_revenue": result.protocol_revenue_gross,
            "net_revenue": result.protocol_revenue_net,
            "user_fee_paid": result.user_fee_paid,
            "user_net_value": result.user_net_value,
        }
        for result in best.surfaces
    }

    report = {
        "cycle": "v190",
        "object": "revenue_surface_atlas_v1",
        "tier": "descriptive_oracle",
        "oracle_dependent": True,
        "discovery_domain": {
            "surface_count": len(SURFACES),
            "policy_count": len(scores),
            "sink_split_count": len(SINK_SPLITS),
            "surfaces": [asdict(surface) for surface in SURFACES],
        },
        "holdout_domain": "not included; next step is replay on real quote/action corpora",
        "candidate_policy_count": len(scores),
        "survivor_count": len(survivors),
        "model_audit": audit_scores(scores),
        "best_survivor": serialize_score(best, include_surfaces=True),
        "best_by_net_protocol_revenue": serialize_score(best_by_net),
        "best_by_total_user_net_value": serialize_score(best_by_user),
        "named_policies": named,
        "best_survivor_surface_revenue": best_surface_revenue,
        "strongest_claim": (
            "Within this bounded fee-surface corpus, revenue-backed staking is viable only when most revenue "
            "comes from recurring value-capture, bot/auction surplus, insurance premiums, and low-friction "
            "notional services; policies depending on penalties, excessive passive subsidy, extractive notional "
            "fees, or rebate farming fail the explicit rails."
        ),
        "non_claims": [
            "This is not a production fee engine.",
            "This does not forecast market demand or token price.",
            "This does not prove legal status or regulatory treatment.",
            "This does not prove wash trading impossible outside the bounded cost model.",
        ],
    }

    out = Path(__file__).resolve().parent / "generated" / "report.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("candidate_policy_count", "survivor_count", "strongest_claim")}, indent=2))


if __name__ == "__main__":
    main()
