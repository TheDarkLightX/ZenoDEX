from __future__ import annotations

import pytest

from src.core.zeno_ux_certificate import (
    CERT_SCHEMA,
    MINIMAX_REGRET_CERT_SCHEMA,
    MINIMAX_REGRET_POLICY_SCHEMA,
    POLICY_SCHEMA,
    REGRET_CERT_SCHEMA,
    REGRET_POLICY_SCHEMA,
    ZenoUXCertificate,
    ZenoUXMinimaxRegretCertificate,
    ZenoUXMinimaxRegretPolicy,
    ZenoUXPolicy,
    ZenoUXRegretCertificate,
    ZenoUXRegretPolicy,
    build_zeno_ux_minimax_regret_certificate,
    build_zeno_ux_regret_certificate,
    choose_min_regret_zeno_ux_certificate,
    choose_minimax_regret_zeno_ux_certificate,
    choose_zeno_ux_certificate,
    compare_zeno_ux,
    pareto_frontier_zeno_ux,
    zeno_ux_certificate_from_payload,
    zeno_ux_certificate_hash,
    zeno_ux_certificate_to_payload,
    zeno_ux_from_cow_quality,
    zeno_ux_minimax_regret_certificate_from_payload,
    zeno_ux_minimax_regret_certificate_hash,
    zeno_ux_minimax_regret_certificate_to_payload,
    zeno_ux_minimax_regret_policy_from_payload,
    zeno_ux_minimax_regret_policy_to_payload,
    zeno_ux_regret_certificate_from_payload,
    zeno_ux_regret_certificate_hash,
    zeno_ux_regret_certificate_to_payload,
    zeno_ux_regret_policy_from_payload,
    zeno_ux_regret_policy_to_payload,
    zeno_ux_regret_score,
    zeno_ux_status_label,
)


def _cert(
    certificate_id: str,
    *,
    decision_class: str = "certified_approx",
    latency_bound_ms: int = 1_000,
    value_loss_bound_bps: int = 10,
    mev_exposure_bound_bps: int = 5,
    finality_bound_blocks: int = 2,
    capital_at_risk_bps: int = 0,
    privacy_leakage_bits: int = 0,
    cognitive_steps: int = 2,
    surface: str = "cow_trade",
    scenario_id: str = "high_load_cow",
    explanation_code: str = "cow_certified_approx_quality",
    next_action: str = "show_quality_floor",
    evidence_refs: tuple[str, ...] = ("sha256:abc",),
) -> ZenoUXCertificate:
    return ZenoUXCertificate(
        schema=CERT_SCHEMA,
        certificate_id=certificate_id,
        surface=surface,
        scenario_id=scenario_id,
        decision_class=decision_class,
        latency_bound_ms=latency_bound_ms,
        value_loss_bound_bps=value_loss_bound_bps,
        mev_exposure_bound_bps=mev_exposure_bound_bps,
        finality_bound_blocks=finality_bound_blocks,
        capital_at_risk_bps=capital_at_risk_bps,
        privacy_leakage_bits=privacy_leakage_bits,
        cognitive_steps=cognitive_steps,
        explanation_code=explanation_code,
        next_action=next_action,
        evidence_refs=evidence_refs,
    )


def test_exact_certificate_requires_zero_value_loss() -> None:
    with pytest.raises(ValueError, match="exact decision requires zero"):
        _cert(
            "bad_exact",
            decision_class="exact",
            value_loss_bound_bps=1,
            explanation_code="cow_exact_quality",
            next_action="settle",
        )


def test_verifier_backed_decision_requires_evidence_refs() -> None:
    with pytest.raises(ValueError, match="requires evidence_refs"):
        _cert("missing_evidence", evidence_refs=())


def test_payload_roundtrip_and_hash_are_stable() -> None:
    certificate = _cert("approx_a")
    payload = zeno_ux_certificate_to_payload(certificate)
    parsed = zeno_ux_certificate_from_payload(payload)

    assert parsed == certificate
    assert payload["evidence_refs"] == ["sha256:abc"]
    assert zeno_ux_certificate_hash(parsed) == zeno_ux_certificate_hash(certificate)
    assert zeno_ux_status_label(certificate) == "CERTIFIED_APPROX"


def test_dominance_means_no_worse_on_all_axes_and_better_on_one() -> None:
    better = _cert(
        "better",
        latency_bound_ms=500,
        value_loss_bound_bps=0,
        decision_class="exact",
        explanation_code="cow_exact_quality",
        next_action="settle",
    )
    worse = _cert("worse", latency_bound_ms=1_000, value_loss_bound_bps=10)

    comparison = compare_zeno_ux(better, worse)

    assert comparison.relation == "dominates"
    assert "decision_rank" in comparison.better_axes
    assert "latency_bound_ms" in comparison.better_axes
    assert "value_loss_bound_bps" in comparison.better_axes


def test_tradeoff_is_incomparable_until_product_policy_selects() -> None:
    fast_lossy = _cert(
        "fast_lossy",
        latency_bound_ms=100,
        value_loss_bound_bps=100,
    )
    slow_tight = _cert(
        "slow_tight",
        latency_bound_ms=1_000,
        value_loss_bound_bps=1,
    )

    comparison = compare_zeno_ux(fast_lossy, slow_tight)

    assert comparison.relation == "incomparable"
    assert comparison.reasons == ("tradeoff",)
    assert comparison.better_axes == ("latency_bound_ms",)
    assert comparison.worse_axes == ("value_loss_bound_bps",)


def test_pareto_frontier_removes_dominated_options_but_keeps_tradeoffs() -> None:
    dominated = _cert("dominated", latency_bound_ms=2_000, value_loss_bound_bps=100)
    fast_lossy = _cert("fast_lossy", latency_bound_ms=100, value_loss_bound_bps=100)
    slow_tight = _cert("slow_tight", latency_bound_ms=1_000, value_loss_bound_bps=1)

    frontier = pareto_frontier_zeno_ux([dominated, fast_lossy, slow_tight])

    assert tuple(c.certificate_id for c in frontier) == ("fast_lossy", "slow_tight")


def test_policy_choice_is_symbolic_and_deterministic() -> None:
    fast_lossy = _cert("fast_lossy", latency_bound_ms=100, value_loss_bound_bps=100)
    slow_tight = _cert("slow_tight", latency_bound_ms=1_000, value_loss_bound_bps=1)
    value_first = ZenoUXPolicy(
        schema=POLICY_SCHEMA,
        policy_id="value_first",
        priority_axes=("value_loss_bound_bps", "latency_bound_ms"),
    )
    speed_first = ZenoUXPolicy(
        schema=POLICY_SCHEMA,
        policy_id="speed_first",
        priority_axes=("latency_bound_ms", "value_loss_bound_bps"),
    )

    assert choose_zeno_ux_certificate(
        [fast_lossy, slow_tight],
        policy=value_first,
    ).certificate_id == "slow_tight"
    assert choose_zeno_ux_certificate(
        [fast_lossy, slow_tight],
        policy=speed_first,
    ).certificate_id == "fast_lossy"


def test_mixed_scope_certificates_cannot_be_compared_or_optimized() -> None:
    left = _cert("left", scenario_id="cow")
    right = _cert("right", scenario_id="perp")

    assert compare_zeno_ux(left, right).relation == "incomparable"
    assert compare_zeno_ux(left, right).reasons == ("different_scope",)
    with pytest.raises(ValueError, match="must share surface"):
        choose_zeno_ux_certificate([left, right])


def test_cow_quality_mapping_turns_volume_bound_into_value_loss_bound() -> None:
    certificate = zeno_ux_from_cow_quality(
        certificate_id="cow_bad_family",
        scenario_id="large_coupled_cow",
        achieved_netted_volume=12,
        upper_bound=2_000_000,
        latency_bound_ms=1_000,
        finality_bound_blocks=2,
        evidence_refs=("generated/cow_large_coupled_greedy_gap/report.json",),
    )

    assert certificate.decision_class == "certified_approx"
    assert certificate.value_loss_bound_bps == 10_000
    assert certificate.explanation_code == "cow_certified_approx_quality"
    assert zeno_ux_status_label(certificate) == "CERTIFIED_APPROX"


def test_cow_quality_exact_when_achieved_matches_upper_bound() -> None:
    certificate = zeno_ux_from_cow_quality(
        certificate_id="cow_exact",
        scenario_id="small_coupled_cow",
        achieved_netted_volume=2_000,
        upper_bound=2_000,
        latency_bound_ms=50,
        finality_bound_blocks=1,
        evidence_refs=("sha256:exact",),
    )

    assert certificate.decision_class == "exact"
    assert certificate.value_loss_bound_bps == 0
    assert certificate.next_action == "settle"


def test_regret_policy_rejects_degenerate_zero_weights() -> None:
    with pytest.raises(ValueError, match="at least one regret weight"):
        ZenoUXRegretPolicy(
            schema=REGRET_POLICY_SCHEMA,
            policy_id="degenerate",
            weights={"value_loss_bound_bps": 0},
        )


def test_min_regret_choice_is_policy_owned() -> None:
    fast_lossy = _cert("fast_lossy", latency_bound_ms=100, value_loss_bound_bps=100)
    slow_tight = _cert("slow_tight", latency_bound_ms=1_000, value_loss_bound_bps=1)
    speed_policy = ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="speed_regret",
        weights={"latency_bound_ms": 1},
    )
    value_policy = ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="value_regret",
        weights={"value_loss_bound_bps": 1_000},
    )

    assert zeno_ux_regret_score(fast_lossy, policy=speed_policy) == 100
    assert choose_min_regret_zeno_ux_certificate(
        [fast_lossy, slow_tight],
        policy=speed_policy,
    ).certificate_id == "fast_lossy"
    assert choose_min_regret_zeno_ux_certificate(
        [fast_lossy, slow_tight],
        policy=value_policy,
    ).certificate_id == "slow_tight"


def test_regret_certificate_records_best_action_and_top_terms() -> None:
    fast_lossy = _cert("fast_lossy", latency_bound_ms=100, value_loss_bound_bps=100)
    slow_tight = _cert("slow_tight", latency_bound_ms=1_000, value_loss_bound_bps=1)
    policy = ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="value_regret",
        weights={"value_loss_bound_bps": 1_000, "latency_bound_ms": 1},
        max_regret_score=99_000,
    )

    certificate = build_zeno_ux_regret_certificate(
        [fast_lossy, slow_tight],
        chosen_certificate_id="fast_lossy",
        policy=policy,
        evidence_refs=("sha256:policy",),
    )

    assert certificate.schema == REGRET_CERT_SCHEMA
    assert certificate.chosen_certificate_id == "fast_lossy"
    assert certificate.best_certificate_id == "slow_tight"
    assert certificate.regret_score == 98_100
    assert certificate.regret_ok is True
    assert certificate.top_regret_terms == (("value_loss_bound_bps", 99_000),)
    assert len(certificate.candidate_hashes) == 2


def test_regret_certificate_can_fail_threshold_without_rejecting_payload() -> None:
    fast_lossy = _cert("fast_lossy", latency_bound_ms=100, value_loss_bound_bps=100)
    slow_tight = _cert("slow_tight", latency_bound_ms=1_000, value_loss_bound_bps=1)
    policy = ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="tight_threshold",
        weights={"value_loss_bound_bps": 1_000},
        max_regret_score=10,
    )

    certificate = build_zeno_ux_regret_certificate(
        [fast_lossy, slow_tight],
        chosen_certificate_id="fast_lossy",
        policy=policy,
    )

    assert certificate.regret_score == 99_000
    assert certificate.regret_ok is False


def test_regret_policy_and_certificate_payloads_are_stable() -> None:
    fast_lossy = _cert("fast_lossy", latency_bound_ms=100, value_loss_bound_bps=100)
    slow_tight = _cert("slow_tight", latency_bound_ms=1_000, value_loss_bound_bps=1)
    policy = ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="value_regret",
        weights={"value_loss_bound_bps": 1_000},
        max_regret_score=100_000,
    )
    parsed_policy = zeno_ux_regret_policy_from_payload(
        zeno_ux_regret_policy_to_payload(policy),
    )
    certificate = build_zeno_ux_regret_certificate(
        [fast_lossy, slow_tight],
        chosen_certificate_id="fast_lossy",
        policy=parsed_policy,
    )
    payload = zeno_ux_regret_certificate_to_payload(certificate)
    parsed_certificate = zeno_ux_regret_certificate_from_payload(payload)

    assert parsed_policy == policy
    assert parsed_certificate == certificate
    assert zeno_ux_regret_certificate_hash(parsed_certificate) == (
        zeno_ux_regret_certificate_hash(certificate)
    )


def test_regret_certificate_rejects_inconsistent_math() -> None:
    candidate_hash = zeno_ux_certificate_hash(_cert("candidate"))

    with pytest.raises(ValueError, match="regret_score must equal"):
        ZenoUXRegretCertificate(
            schema=REGRET_CERT_SCHEMA,
            certificate_id="bad_regret_math",
            policy_id="value_regret",
            surface="cow_trade",
            scenario_id="high_load_cow",
            chosen_certificate_id="fast_lossy",
            best_certificate_id="slow_tight",
            chosen_score=100,
            best_score=10,
            regret_score=91,
            regret_threshold=100,
            regret_ok=True,
            top_regret_terms=(("value_loss_bound_bps", 90),),
            candidate_hashes=(candidate_hash,),
            evidence_refs=(),
        )


def test_weighted_linear_regret_can_choose_smoother_high_mev_witness() -> None:
    smooth_high_mev = _cert(
        "smooth_high_mev",
        mev_exposure_bound_bps=500,
        cognitive_steps=0,
        latency_bound_ms=50,
    )
    safer_typed_confirm = _cert(
        "safer_typed_confirm",
        mev_exposure_bound_bps=50,
        cognitive_steps=5,
        latency_bound_ms=500,
    )
    miscalibrated = ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="friction_over_safety",
        weights={"mev_exposure_bound_bps": 1, "cognitive_steps": 1_000},
    )

    assert choose_min_regret_zeno_ux_certificate(
        [smooth_high_mev, safer_typed_confirm],
        policy=miscalibrated,
    ).certificate_id == "smooth_high_mev"


def test_minimax_regret_prioritizes_worst_safety_axis_before_friction() -> None:
    smooth_high_mev = _cert(
        "smooth_high_mev",
        mev_exposure_bound_bps=500,
        cognitive_steps=0,
        latency_bound_ms=50,
    )
    safer_typed_confirm = _cert(
        "safer_typed_confirm",
        mev_exposure_bound_bps=50,
        cognitive_steps=5,
        latency_bound_ms=500,
    )
    policy = ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id="safety_then_friction",
        safety_axes=("mev_exposure_bound_bps", "capital_at_risk_bps"),
        friction_weights={"cognitive_steps": 1_000, "latency_bound_ms": 1},
    )

    assert choose_minimax_regret_zeno_ux_certificate(
        [smooth_high_mev, safer_typed_confirm],
        policy=policy,
    ).certificate_id == "safer_typed_confirm"


def test_minimax_regret_filters_candidates_outside_safety_budget() -> None:
    high_mev = _cert("high_mev", mev_exposure_bound_bps=301)
    budget_ok = _cert("budget_ok", mev_exposure_bound_bps=300, latency_bound_ms=5_000)
    policy = ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id="mev_budget",
        safety_axes=("mev_exposure_bound_bps",),
        safety_budgets={"mev_exposure_bound_bps": 300},
        friction_weights={"latency_bound_ms": 1},
    )

    assert choose_minimax_regret_zeno_ux_certificate(
        [high_mev, budget_ok],
        policy=policy,
    ).certificate_id == "budget_ok"

    with pytest.raises(ValueError, match="no admissible"):
        choose_minimax_regret_zeno_ux_certificate([high_mev], policy=policy)


def test_minimax_regret_certificate_records_safety_delta_and_budget_rejects() -> None:
    smooth_high_mev = _cert(
        "smooth_high_mev",
        mev_exposure_bound_bps=500,
        cognitive_steps=0,
        latency_bound_ms=50,
    )
    safer_typed_confirm = _cert(
        "safer_typed_confirm",
        mev_exposure_bound_bps=50,
        cognitive_steps=5,
        latency_bound_ms=500,
    )
    policy = ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id="safety_then_friction",
        safety_axes=("mev_exposure_bound_bps", "capital_at_risk_bps"),
        safety_budgets={"mev_exposure_bound_bps": 450},
        friction_weights={"cognitive_steps": 1_000, "latency_bound_ms": 1},
        max_safety_regret=0,
        max_friction_score=0,
    )

    certificate = build_zeno_ux_minimax_regret_certificate(
        [smooth_high_mev, safer_typed_confirm],
        chosen_certificate_id="smooth_high_mev",
        policy=policy,
        evidence_refs=("sha256:minimax_policy",),
    )

    assert certificate.schema == MINIMAX_REGRET_CERT_SCHEMA
    assert certificate.chosen_certificate_id == "smooth_high_mev"
    assert certificate.best_certificate_id == "safer_typed_confirm"
    assert certificate.chosen_safety_regret == 10_551
    assert certificate.best_safety_regret == 50
    assert certificate.safety_regret_delta == 10_501
    assert certificate.friction_score_delta == 0
    assert certificate.regret_ok is False
    assert certificate.top_regret_terms == (("mev_exposure_bound_bps", 450),)
    assert certificate.rejected_candidate_ids == ("smooth_high_mev",)


def test_minimax_regret_policy_and_certificate_payloads_are_stable() -> None:
    smooth_high_mev = _cert("smooth_high_mev", mev_exposure_bound_bps=500)
    safer_typed_confirm = _cert("safer_typed_confirm", mev_exposure_bound_bps=50)
    policy = ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id="safety_then_friction",
        safety_axes=("mev_exposure_bound_bps", "capital_at_risk_bps"),
        safety_budgets={"mev_exposure_bound_bps": 500},
        friction_weights={"cognitive_steps": 1_000, "latency_bound_ms": 1},
        max_safety_regret=500,
        max_friction_score=100,
    )

    parsed_policy = zeno_ux_minimax_regret_policy_from_payload(
        zeno_ux_minimax_regret_policy_to_payload(policy),
    )
    certificate = build_zeno_ux_minimax_regret_certificate(
        [smooth_high_mev, safer_typed_confirm],
        chosen_certificate_id="smooth_high_mev",
        policy=parsed_policy,
    )
    payload = zeno_ux_minimax_regret_certificate_to_payload(certificate)
    parsed_certificate = zeno_ux_minimax_regret_certificate_from_payload(payload)

    assert parsed_policy == policy
    assert parsed_certificate == certificate
    assert zeno_ux_minimax_regret_certificate_hash(parsed_certificate) == (
        zeno_ux_minimax_regret_certificate_hash(certificate)
    )


def test_minimax_regret_certificate_rejects_inconsistent_math() -> None:
    candidate_hash = zeno_ux_certificate_hash(_cert("candidate"))

    with pytest.raises(ValueError, match="safety_regret_delta"):
        ZenoUXMinimaxRegretCertificate(
            schema=MINIMAX_REGRET_CERT_SCHEMA,
            certificate_id="bad_minimax_regret_math",
            policy_id="safety_then_friction",
            surface="cow_trade",
            scenario_id="high_load_cow",
            chosen_certificate_id="smooth_high_mev",
            best_certificate_id="safer_typed_confirm",
            chosen_safety_regret=500,
            best_safety_regret=50,
            safety_regret_delta=449,
            safety_regret_threshold=0,
            chosen_friction_score=50,
            best_friction_score=5_500,
            friction_score_delta=0,
            friction_score_threshold=0,
            regret_ok=False,
            top_regret_terms=(("mev_exposure_bound_bps", 450),),
            rejected_candidate_ids=(),
            candidate_hashes=(candidate_hash,),
            evidence_refs=(),
        )
