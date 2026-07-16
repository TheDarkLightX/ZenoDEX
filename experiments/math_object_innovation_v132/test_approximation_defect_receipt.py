from __future__ import annotations

import copy
import json
import subprocess
from pathlib import Path

from approximation_defect_receipt import (
    SCHEMA,
    check_receipt,
    seal_receipt,
)

ROOT = Path(__file__).resolve().parent


def component(certificate_id: str, bound: str) -> dict[str, str]:
    return {
        "certificate_id": certificate_id,
        "certified_bound": bound,
        "allocated_bound": bound,
    }


def region(
    region_id: str,
    lo: str,
    hi: str,
    margin: str = "1/4",
) -> dict[str, object]:
    return {
        "region_id": region_id,
        "interval": {"lo": lo, "hi": hi},
        "model": {
            "model_id": f"model-{region_id}",
            "certificate_id": f"model-cert-{region_id}",
            "certified_margin": margin,
        },
        "errors": {
            "defect": component(f"defect-cert-{region_id}", "1/16"),
            "interaction": component(f"interaction-cert-{region_id}", "1/32"),
            "reconstruction": component(f"reconstruction-cert-{region_id}", "1/32"),
        },
    }


def valid_receipt() -> dict[str, object]:
    raw: dict[str, object] = {
        "schema": SCHEMA,
        "claim_id": "jacobi-envelope-demo",
        "domain": {"lo": "0", "hi": "1"},
        "regions": [
            region("left", "0", "1/2"),
            region("right", "1/2", "1"),
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
    return seal_receipt(raw)


def reseal(receipt: dict[str, object]) -> dict[str, object]:
    raw = copy.deepcopy(receipt)
    raw.pop("coverage_root", None)
    return seal_receipt(raw)


def test_valid_receipt_accepts_with_exact_budget_details() -> None:
    result = check_receipt(valid_receipt())

    assert result.status == "ACCEPT"
    assert result.reason_code is None
    assert result.theorem == (
        "ApproximationDefectCertificates.finiteCover_target_nonneg"
    )
    assert result.detail["evidence_scope"] == "arithmetic_and_cover_binding_only"
    assert result.detail["regions"] == [
        {
            "region_id": "left",
            "model_margin": "1/4",
            "total_allocated_error": "1/8",
            "remaining_margin": "1/8",
        },
        {
            "region_id": "right",
            "model_margin": "1/4",
            "total_allocated_error": "1/8",
            "remaining_margin": "1/8",
        },
    ]


def test_missing_region_gap_is_unknown() -> None:
    receipt = valid_receipt()
    receipt["regions"][1]["interval"]["lo"] = "3/4"  # type: ignore[index]
    receipt["overlaps"][0]["interval"] = {"lo": "3/4", "hi": "1/2"}  # type: ignore[index]

    result = check_receipt(reseal(receipt))

    assert result.status == "UNKNOWN"
    assert result.reason_code == "COVERAGE_GAP"


def test_underestimated_defect_is_unknown() -> None:
    receipt = valid_receipt()
    defect = receipt["regions"][0]["errors"]["defect"]  # type: ignore[index]
    defect["allocated_bound"] = "1/32"

    result = check_receipt(reseal(receipt))

    assert result.status == "UNKNOWN"
    assert result.reason_code == "ALLOCATED_BOUND_UNDERESTATES_CERTIFIED_BOUND"


def test_omitted_interaction_budget_is_unknown() -> None:
    receipt = valid_receipt()
    del receipt["regions"][0]["errors"]["interaction"]  # type: ignore[index]

    result = check_receipt(reseal(receipt))

    assert result.status == "UNKNOWN"
    assert result.reason_code == "FIELD_SET_MISMATCH"


def test_overlap_contract_mismatch_is_unknown() -> None:
    receipt = valid_receipt()
    receipt["overlaps"][0]["right_contract_id"] = "different-join"  # type: ignore[index]

    result = check_receipt(reseal(receipt))

    assert result.status == "UNKNOWN"
    assert result.reason_code == "OVERLAP_CONTRACT_MISMATCH"


def test_model_margin_must_dominate_all_allocated_errors() -> None:
    receipt = valid_receipt()
    receipt["regions"][0]["model"]["certified_margin"] = "1/16"  # type: ignore[index]

    result = check_receipt(reseal(receipt))

    assert result.status == "UNKNOWN"
    assert result.reason_code == "MODEL_MARGIN_EXCEEDED"


def test_coverage_root_binds_the_receipt_body() -> None:
    receipt = valid_receipt()
    receipt["claim_id"] = "tampered-after-sealing"

    result = check_receipt(receipt)

    assert result.status == "UNKNOWN"
    assert result.reason_code == "COVERAGE_ROOT_MISMATCH"


def test_noncanonical_or_inexact_rationals_are_unknown() -> None:
    receipt = valid_receipt()
    receipt["domain"]["lo"] = 0.0  # type: ignore[index]
    assert check_receipt(reseal(receipt)).reason_code == "INVALID_RATIONAL"

    receipt = valid_receipt()
    receipt["domain"]["lo"] = "0/2"  # type: ignore[index]
    assert check_receipt(reseal(receipt)).reason_code == "INVALID_RATIONAL"


def test_rational_resource_budget_fails_closed() -> None:
    receipt = valid_receipt()
    receipt["domain"]["hi"] = "1" * 129  # type: ignore[index]

    result = check_receipt(reseal(receipt))

    assert result.status == "UNKNOWN"
    assert result.reason_code == "RESOURCE_LIMIT_EXCEEDED"


def test_region_order_and_unknown_fields_are_rejected() -> None:
    receipt = valid_receipt()
    receipt["regions"].reverse()  # type: ignore[union-attr]
    assert check_receipt(reseal(receipt)).reason_code == "REGION_ORDER_NONCANONICAL"

    receipt = valid_receipt()
    receipt["regions"][0]["unchecked_hint"] = "ignore me"  # type: ignore[index]
    assert check_receipt(reseal(receipt)).reason_code == "FIELD_SET_MISMATCH"


def test_cli_demo_contains_named_adversarial_witnesses() -> None:
    proc = subprocess.run(
        ["python3", "approximation_defect_receipt.py", "--demo"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    report = json.loads(proc.stdout)
    by_name = {row["name"]: row for row in report["results"]}

    assert report["schema"] == "zenodex-approximation-defect-check-report/v1"
    assert report["summary"] == {"accepted": 1, "unknown": 4, "total": 5}
    assert by_name["alice_valid_cover"]["status"] == "ACCEPT"
    assert by_name["mallory_missing_region"]["reason_code"] == "COVERAGE_GAP"
    assert by_name["mallory_underestimated_defect"]["reason_code"] == (
        "ALLOCATED_BOUND_UNDERESTATES_CERTIFIED_BOUND"
    )
    assert by_name["mallory_omitted_interaction"]["reason_code"] == (
        "FIELD_SET_MISMATCH"
    )
    assert by_name["mallory_overlap_mismatch"]["reason_code"] == (
        "OVERLAP_CONTRACT_MISMATCH"
    )
