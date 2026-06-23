from __future__ import annotations

from tools.bva.spec import IntDomain, Scenario

from src.core.price_impact_preview import price_impact_preview


def _label(out) -> tuple[int, int, int]:
    # Quantized outputs + recommended_min_out are the UX-critical integer lattice effects.
    return (
        int(out.amount_out_at_confidence),
        int(out.recommended_min_out),
    )


SCENARIO = Scenario(
    name="price_impact_preview_by_confidence_bps",
    fn=price_impact_preview,
    domains={
        "reserve_in": IntDomain(100_000, 100_000),
        "reserve_out": IntDomain(100_000, 100_000),
        "amount_in": IntDomain(5_000, 5_000),
        "fee_bps": IntDomain(30, 30),
        "pending_volume_same_direction": IntDomain(80_000, 80_000),
        "confidence_bps": IntDomain(0, 10_000, specials=(0, 1, 9500, 9999, 10_000)),
    },
    label_fn=_label,
    seed=0,
    max_contexts=1,
    samples_per_context=512,
)


def get_scenario() -> Scenario:
    return SCENARIO
