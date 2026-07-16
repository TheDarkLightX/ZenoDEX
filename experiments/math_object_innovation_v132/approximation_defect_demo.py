"""Named replay witnesses for the approximation-defect receipt checker."""

from __future__ import annotations

import copy

from approximation_defect_receipt import SCHEMA, seal_receipt


def _component(certificate_id: str, bound: str) -> dict[str, str]:
    return {
        "certificate_id": certificate_id,
        "certified_bound": bound,
        "allocated_bound": bound,
    }


def _region(region_id: str, lo: str, hi: str) -> dict[str, object]:
    return {
        "region_id": region_id,
        "interval": {"lo": lo, "hi": hi},
        "model": {
            "model_id": f"model-{region_id}",
            "certificate_id": f"model-cert-{region_id}",
            "certified_margin": "1/4",
        },
        "errors": {
            "defect": _component(f"defect-cert-{region_id}", "1/16"),
            "interaction": _component(f"interaction-cert-{region_id}", "1/32"),
            "reconstruction": _component(
                f"reconstruction-cert-{region_id}", "1/32"
            ),
        },
    }


def _valid_receipt() -> dict[str, object]:
    return seal_receipt(
        {
            "schema": SCHEMA,
            "claim_id": "jacobi-envelope-demo",
            "domain": {"lo": "0", "hi": "1"},
            "regions": [
                _region("left", "0", "1/2"),
                _region("right", "1/2", "1"),
            ],
            "overlaps": [
                {
                    "left_region_id": "left",
                    "right_region_id": "right",
                    "interval": {"lo": "1/2", "hi": "1/2"},
                    "left_contract_id": "join-at-half",
                    "right_contract_id": "join-at-half",
                }
            ],
        }
    )


def _reseal(receipt: dict[str, object]) -> dict[str, object]:
    body = copy.deepcopy(receipt)
    body.pop("coverage_root", None)
    return seal_receipt(body)


def builtin_demo() -> list[dict[str, object]]:
    """Return one valid receipt and four fail-closed adversarial witnesses."""

    valid = _valid_receipt()

    missing_region = copy.deepcopy(valid)
    missing_region["regions"][1]["interval"]["lo"] = "3/4"  # type: ignore[index]
    missing_region = _reseal(missing_region)

    underestimated = copy.deepcopy(valid)
    underestimated["regions"][0]["errors"]["defect"][  # type: ignore[index]
        "allocated_bound"
    ] = "1/32"
    underestimated = _reseal(underestimated)

    omitted_interaction = copy.deepcopy(valid)
    del omitted_interaction["regions"][0]["errors"]["interaction"]  # type: ignore[index]
    omitted_interaction = _reseal(omitted_interaction)

    overlap_mismatch = copy.deepcopy(valid)
    overlap_mismatch["overlaps"][0][  # type: ignore[index]
        "right_contract_id"
    ] = "different-join"
    overlap_mismatch = _reseal(overlap_mismatch)

    return [
        {"name": "alice_valid_cover", "receipt": valid},
        {"name": "mallory_missing_region", "receipt": missing_region},
        {
            "name": "mallory_underestimated_defect",
            "receipt": underestimated,
        },
        {"name": "mallory_omitted_interaction", "receipt": omitted_interaction},
        {"name": "mallory_overlap_mismatch", "receipt": overlap_mismatch},
    ]
