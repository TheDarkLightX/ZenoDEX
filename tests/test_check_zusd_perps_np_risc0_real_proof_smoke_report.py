from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from tools.check_zusd_perps_np_risc0_real_proof_smoke_report import (
    PERPS_NP_SPEC,
    ZUSD_SPEC,
    main,
    validate_scoped_risc0_real_proof_smoke_report_v1,
)


def _hex(byte: str) -> str:
    return byte * 64


def _proof_file(tmp_path: Path, name: str) -> str:
    path = tmp_path / f"{name}.json"
    path.write_text('{"proof":"receipt"}\n', encoding="utf-8")
    return str(path)


def _positive_zusd_case(tmp_path: Path) -> dict[str, object]:
    return {
        "case": "mint",
        "kind": "positive",
        "ok": True,
        "proof_type": ZUSD_SPEC.proof_type,
        "minted_zusd_e8": "100000000000",
        "collateral_value_e8": "200000000000",
        "mcr_bps": 11000,
        "risc0_image_id": _hex("a"),
        "strict_verify": True,
        "tamper_rejections": sorted(ZUSD_SPEC.required_tamper_rejections),
        "proof_base64_len": 1024,
        "proof_path": _proof_file(tmp_path, "zusd-proof"),
    }


def _positive_perps_case(tmp_path: Path) -> dict[str, object]:
    return {
        "case": "four_wallet",
        "kind": "positive",
        "ok": True,
        "transition_kind": "match_epoch",
        "claims_paid_delta_e8": "0",
        "insurance_delta_e8": "0",
        "position_abs_reduction_base": "0",
        "proof_type": PERPS_NP_SPEC.proof_type,
        "current_surface_binding_check": True,
        "funding_residual_e8": "0",
        "intent_count": 4,
        "matched_base_volume": "5",
        "net_position_base": "0",
        "participant_count": 4,
        "risc0_image_id": _hex("b"),
        "strict_verify": True,
        "tamper_rejections": sorted(PERPS_NP_SPEC.required_tamper_rejections),
        "proof_base64_len": 1024,
        "proof_path": _proof_file(tmp_path, "perps-proof"),
    }


def _positive_perps_adl_case(tmp_path: Path) -> dict[str, object]:
    return {
        "case": "adl_wallet",
        "kind": "positive",
        "ok": True,
        "transition_kind": "adl_epoch",
        "claims_paid_delta_e8": "30",
        "insurance_delta_e8": "-30",
        "position_abs_reduction_base": "20",
        "proof_type": PERPS_NP_SPEC.proof_type,
        "current_surface_binding_check": True,
        "funding_residual_e8": "0",
        "intent_count": 0,
        "matched_base_volume": "0",
        "net_position_base": "0",
        "participant_count": 4,
        "risc0_image_id": _hex("c"),
        "strict_verify": True,
        "tamper_rejections": sorted(PERPS_NP_SPEC.required_tamper_rejections),
        "proof_base64_len": 1024,
        "proof_path": _proof_file(tmp_path, "perps-adl-proof"),
    }


def _negative_case(name: str) -> dict[str, object]:
    return {
        "case": name,
        "kind": "negative",
        "ok": True,
        "rejected_as_expected": True,
        "exit_code": 1,
        "reject_signal": "rejected",
    }


def _zusd_report(tmp_path: Path) -> dict[str, object]:
    cases = [_positive_zusd_case(tmp_path), _negative_case("neg_mcr")]
    return {
        "schema": ZUSD_SPEC.report_schema,
        "ok": True,
        "proof_type": ZUSD_SPEC.proof_type,
        "case_count": len(cases),
        "positive": 1,
        "negative": 1,
        "production_security_claim": False,
        "cases": cases,
    }


def _perps_report(tmp_path: Path) -> dict[str, object]:
    cases = [_positive_perps_case(tmp_path), _negative_case("neg_duplicate_nonce")]
    return {
        "schema": PERPS_NP_SPEC.report_schema,
        "ok": True,
        "proof_surface": PERPS_NP_SPEC.proof_type,
        "case_count": len(cases),
        "positive": 1,
        "negative": 1,
        "production_security_claim": False,
        "dynamic_membership_floor": 4,
        "cases": cases,
    }


def test_scoped_risc0_report_accepts_zusd(tmp_path: Path) -> None:
    check = validate_scoped_risc0_real_proof_smoke_report_v1(
        _zusd_report(tmp_path),
        require_proof_files=True,
        min_positive=1,
        min_negative=1,
    )

    assert check["ok"] is True
    assert check["surface"] == "zusd"
    assert check["proof_type"] == ZUSD_SPEC.proof_type


def test_scoped_risc0_report_accepts_perps_np(tmp_path: Path) -> None:
    check = validate_scoped_risc0_real_proof_smoke_report_v1(
        _perps_report(tmp_path),
        require_proof_files=True,
        min_positive=1,
        min_negative=1,
    )

    assert check["ok"] is True
    assert check["surface"] == "perps_np"
    assert check["proof_type"] == PERPS_NP_SPEC.proof_type


def test_scoped_risc0_report_accepts_perps_np_adl_epoch(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    report["cases"].append(_positive_perps_adl_case(tmp_path))  # type: ignore[index,union-attr]
    report["case_count"] = 3
    report["positive"] = 2

    check = validate_scoped_risc0_real_proof_smoke_report_v1(
        report,
        require_proof_files=True,
        min_positive=2,
        min_negative=1,
        required_cases={"four_wallet", "adl_wallet"},
    )

    assert check["ok"] is True


def test_scoped_risc0_report_accepts_legacy_adl_epoch_shape(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    adl = _positive_perps_adl_case(tmp_path)
    adl.pop("transition_kind")
    report["cases"].append(adl)  # type: ignore[index,union-attr]
    report["case_count"] = 3
    report["positive"] = 2

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is True


def test_scoped_risc0_report_accepts_legacy_match_epoch_shape(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case.pop("transition_kind")

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is True


@pytest.mark.parametrize("bad_value", [123, "", [], {}, True, None])
def test_scoped_risc0_report_rejects_malformed_explicit_transition_kind(
    tmp_path: Path,
    bad_value: object,
) -> None:
    report = _perps_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["transition_kind"] = bad_value

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[0].transition_kind must be match_epoch or adl_epoch" in check["errors"]


def test_scoped_risc0_report_rejects_match_epoch_without_fill(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["intent_count"] = 0
    case["matched_base_volume"] = "0"

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[0].intent_count must be positive for match_epoch" in check["errors"]
    assert "cases[0].matched_base_volume must be positive for match_epoch" in check["errors"]


def test_scoped_risc0_report_rejects_adl_epoch_with_fill(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    report["cases"][0] = _positive_perps_adl_case(tmp_path)  # type: ignore[index]
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["intent_count"] = 1
    case["matched_base_volume"] = "1"

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[0].intent_count must be zero for adl_epoch" in check["errors"]
    assert "cases[0].matched_base_volume must be zero for adl_epoch" in check["errors"]


def test_scoped_risc0_report_rejects_adl_epoch_without_adl_evidence(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    report["cases"][0] = _positive_perps_adl_case(tmp_path)  # type: ignore[index]
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["claims_paid_delta_e8"] = "0"
    case["position_abs_reduction_base"] = "0"

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[0].claims_paid_delta_e8 must be positive for adl_epoch" in check["errors"]
    assert "cases[0].position_abs_reduction_base must be positive for adl_epoch" in check["errors"]


def test_scoped_risc0_report_rejects_production_claim(tmp_path: Path) -> None:
    report = _zusd_report(tmp_path)
    report["production_security_claim"] = True

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "production_security_claim must be false" in check["errors"]


def test_scoped_risc0_report_rejects_missing_tamper_case(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["tamper_rejections"] = ["wrong_proof_type"]

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert any("tamper_rejections missing" in error for error in check["errors"])


def test_scoped_risc0_report_rejects_zero_image_id(tmp_path: Path) -> None:
    report = _zusd_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["risc0_image_id"] = "0" * 64

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[0].risc0_image_id must be nonzero" in check["errors"]


def test_scoped_risc0_report_rejects_perps_below_participant_floor(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["participant_count"] = 3

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[0].participant_count must be at least 4" in check["errors"]


def test_scoped_risc0_report_rejects_perps_top_level_floor_below_four(tmp_path: Path) -> None:
    report = _perps_report(tmp_path)
    report["dynamic_membership_floor"] = 3

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "dynamic_membership_floor must be at least 4" in check["errors"]


def test_scoped_risc0_report_rejects_missing_proof_file(tmp_path: Path) -> None:
    report = _zusd_report(tmp_path)
    case = report["cases"][0]  # type: ignore[index]
    assert isinstance(case, dict)
    case["proof_path"] = str(tmp_path / "missing.json")

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report, require_proof_files=True)

    assert check["ok"] is False
    assert "cases[0].proof_path does not exist" in check["errors"]


def test_scoped_risc0_report_rejects_negative_acceptance(tmp_path: Path) -> None:
    report = _zusd_report(tmp_path)
    case = report["cases"][1]  # type: ignore[index]
    assert isinstance(case, dict)
    case["rejected_as_expected"] = False

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "cases[1].rejected_as_expected must be true" in check["errors"]


def test_scoped_risc0_report_cli_outputs_check(tmp_path: Path, capsys) -> None:
    report_path = tmp_path / "report.json"
    report_path.write_text(json.dumps(_perps_report(tmp_path)), encoding="utf-8")

    rc = main([str(report_path), "--require-proof-files", "--min-negative", "1"])

    assert rc == 0
    out = json.loads(capsys.readouterr().out)
    assert out["schema"] == "zenodex.scoped_risc0_real_proof_smoke_report_check.v1"
    assert out["ok"] is True


def test_scoped_risc0_report_cli_can_require_extra_case(tmp_path: Path, capsys) -> None:
    report_path = tmp_path / "report.json"
    report_path.write_text(json.dumps(_perps_report(tmp_path)), encoding="utf-8")

    rc = main([str(report_path), "--required-case", "five_wallet"])

    assert rc == 1
    out = json.loads(capsys.readouterr().out)
    assert "missing required cases: five_wallet" in out["errors"]


def test_scoped_risc0_report_rejects_mutated_count(tmp_path: Path) -> None:
    report = copy.deepcopy(_perps_report(tmp_path))
    report["positive"] = 2

    check = validate_scoped_risc0_real_proof_smoke_report_v1(report)

    assert check["ok"] is False
    assert "positive count mismatch" in check["errors"]
