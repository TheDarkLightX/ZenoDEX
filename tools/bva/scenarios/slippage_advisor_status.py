from __future__ import annotations

from tools.bva.spec import IntDomain, Scenario

from src.core.slippage_advisor import slippage_advice_exact_in_cpmm


def _label(out) -> tuple[int, int, int | None, str]:
    # Compact label used to find "interesting" flips as confidence changes:
    # - amount_out_at_confidence is integer/quantized and often stepwise
    # - required_slippage_bps changes at output steps
    # - status flips (ok/mev_conflict/inconclusive_mev/no_revert_safe_option)
    return (
        int(out.amount_out_at_confidence),
        int(out.required_slippage_bps),
        int(out.recommended_slippage_bps_revert_safe)
        if out.recommended_slippage_bps_revert_safe is not None
        else None,
        str(out.status),
    )


SCENARIO = Scenario(
    name="slippage_advisor_status_by_confidence_bps",
    fn=slippage_advice_exact_in_cpmm,
    domains={
        # Fix all but confidence to keep boundary mining cheap and interpretable.
        "reserve_in": IntDomain(1000, 1000),
        "reserve_out": IntDomain(1000, 1000),
        "fee_bps": IntDomain(0, 0),
        "amount_in": IntDomain(50, 50),
        "pending_volume_same_direction": IntDomain(10, 10),
        "confidence_bps": IntDomain(0, 10_000, specials=(0, 1, 9500, 9999, 10_000)),
        "max_attacker_amount_in": IntDomain(2000, 2000),
    },
    fixed_kwargs={
        # Include duplicates and out-of-range values to exercise option normalization.
        "slippage_options_bps": [10, 50, 100, 300, 300, -1, 10_001],
    },
    label_fn=_label,
    seed=0,
    max_contexts=1,
    samples_per_context=256,
)


def get_scenario() -> Scenario:
    return SCENARIO

