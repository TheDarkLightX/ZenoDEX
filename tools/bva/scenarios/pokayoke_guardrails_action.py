from __future__ import annotations

from tools.bva.spec import IntDomain, Scenario

from src.core.pokayoke_swap_guardrails import SwapGuardrailContext, decide_swap_guardrails


def _status_from_code(code: int) -> str:
    m = {
        0: "ok",
        1: "mev_conflict",
        2: "inconclusive_mev",
        3: "no_revert_safe_option",
        4: "unknown_status",
    }
    return m.get(int(code), "unknown_status")


def _none_or_bps(code: int) -> int | None:
    # Use -1 as the sentinel for None (because IntDomain is integer-only).
    if int(code) < 0:
        return None
    return int(code)


def _run(
    *,
    price_impact_bps: int,
    slippage_advice_status_code: int,
    required_slippage_bps: int,
    recommended_revert_safe_code: int,
    recommended_mev_safe_code: int,
    user_slippage_bps: int,
):
    ctx = SwapGuardrailContext(
        price_impact_bps=int(price_impact_bps),
        slippage_advice_status=_status_from_code(int(slippage_advice_status_code)),
        required_slippage_bps=int(required_slippage_bps),
        recommended_slippage_bps_revert_safe=_none_or_bps(int(recommended_revert_safe_code)),
        recommended_slippage_bps_mev_safe=_none_or_bps(int(recommended_mev_safe_code)),
        recommended_slippage_bps=None,
    )
    return decide_swap_guardrails(ctx=ctx, user_slippage_bps=int(user_slippage_bps))


def _label(out) -> tuple[str, tuple[str, ...]]:
    # Keep the label compact but informative: action tier + reason codes.
    return (str(out.action), tuple(str(r) for r in out.reasons))


SCENARIO = Scenario(
    name="pokayoke_guardrails_action",
    fn=_run,
    domains={
        "price_impact_bps": IntDomain(
            min_value=0,
            max_value=10_000,
            specials=(0, 1, 99, 100, 101, 499, 500, 501, 10_000),
            include_bool=True,
        ),
        "slippage_advice_status_code": IntDomain(
            min_value=0,
            max_value=6,
            specials=(0, 1, 2, 3, 4, 5, 6),
            include_bool=True,
        ),
        "required_slippage_bps": IntDomain(
            min_value=0,
            max_value=10_000,
            specials=(0, 1, 10, 50, 100, 300, 500, 9999, 10_000),
            include_bool=True,
        ),
        # -1 sentinel means "None" when building the context.
        "recommended_revert_safe_code": IntDomain(
            min_value=-1,
            max_value=10_000,
            specials=(-1, 0, 1, 10, 50, 100, 300, 10_000),
            include_bool=True,
        ),
        "recommended_mev_safe_code": IntDomain(
            min_value=-1,
            max_value=10_000,
            specials=(-1, 0, 1, 10, 50, 100, 300, 10_000),
            include_bool=True,
        ),
        "user_slippage_bps": IntDomain(
            min_value=0,
            max_value=10_000,
            specials=(0, 1, 10, 49, 50, 51, 99, 100, 101, 300, 10_000),
            include_bool=True,
        ),
    },
    label_fn=_label,
    seed=0,
    max_contexts=12,
    samples_per_context=96,
    random_contexts=8,
    random_context_budget=256,
    global_samples=96,
)


def get_scenario() -> Scenario:
    return SCENARIO

