from __future__ import annotations

import copy
import json

from tools.check_zeno_ledger_proof_coverage_matrix import (
    DEFAULT_MATRIX,
    main,
    validate_proof_coverage_matrix_v0,
)


def _matrix() -> dict[str, object]:
    return json.loads(DEFAULT_MATRIX.read_text(encoding="utf-8"))


def test_proof_coverage_matrix_accepts_default_matrix() -> None:
    report = validate_proof_coverage_matrix_v0(_matrix())

    assert report["ok"] is True
    assert report["supported_surface_count"] == 9
    assert report["gap_surface_count"] == 11
    assert report["non_claim_count"] == 10
    assert report["value_moving_surface_count"] == 8
    assert report["value_moving_full_zk_ready_count"] == 0
    assert report["full_zk_execution_ready"] is False
    assert "spot_v1_complete_block_execution" in report["succinct_open_value_moving_surfaces"]
    assert "spot_complete_block_real_proof" in report["succinct_open_gap_ids"]
    supported_by_id = {item["id"]: item for item in report["supported_surfaces"]}
    assert supported_by_id["recursive_lifecycle_asset_delta_rows"]["claim_status"] == "supported"
    assert supported_by_id["recursive_lifecycle_admission_packet_checker"]["claim_status"] == "supported"
    assert {item["claim_status"] for item in report["supported_surfaces"]} <= {"proved", "supported"}


def test_proof_coverage_matrix_rejects_missing_required_gap() -> None:
    matrix = _matrix()
    gaps = list(matrix["gap_surfaces"])  # type: ignore[arg-type]
    matrix["gap_surfaces"] = [
        gap for gap in gaps if gap["id"] != "light_client_production_finality"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("missing required gap surfaces: light_client_production_finality" == err for err in report["errors"])


def test_proof_coverage_matrix_rejects_missing_recursive_oracle_gap() -> None:
    matrix = _matrix()
    gaps = list(matrix["gap_surfaces"])  # type: ignore[arg-type]
    matrix["gap_surfaces"] = [
        gap for gap in gaps if gap["id"] != "recursive_oracle_leaf_real_proof"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("missing required gap surfaces: recursive_oracle_leaf_real_proof" == err for err in report["errors"])


def test_proof_coverage_matrix_rejects_missing_zusd_lifecycle_gap() -> None:
    matrix = _matrix()
    gaps = list(matrix["gap_surfaces"])  # type: ignore[arg-type]
    matrix["gap_surfaces"] = [
        gap for gap in gaps if gap["id"] != "zusd_non_deposit_mint_lifecycle_rows"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("missing required gap surfaces: zusd_non_deposit_mint_lifecycle_rows" == err for err in report["errors"])


def test_proof_coverage_matrix_rejects_missing_recursive_production_admission_gap() -> None:
    matrix = _matrix()
    gaps = list(matrix["gap_surfaces"])  # type: ignore[arg-type]
    matrix["gap_surfaces"] = [
        gap for gap in gaps if gap["id"] != "recursive_production_admission"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("missing required gap surfaces: recursive_production_admission" == err for err in report["errors"])


def test_proof_coverage_matrix_rejects_missing_recursive_lifecycle_supported_surface() -> None:
    matrix = _matrix()
    supported = list(matrix["supported_surfaces"])  # type: ignore[arg-type]
    matrix["supported_surfaces"] = [
        item for item in supported if item["id"] != "recursive_lifecycle_asset_delta_rows"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any(
        "missing required supported surfaces: recursive_lifecycle_asset_delta_rows" == err
        for err in report["errors"]
    )


def test_proof_coverage_matrix_rejects_missing_recursive_lifecycle_checker_surface() -> None:
    matrix = _matrix()
    supported = list(matrix["supported_surfaces"])  # type: ignore[arg-type]
    matrix["supported_surfaces"] = [
        item for item in supported if item["id"] != "recursive_lifecycle_admission_packet_checker"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any(
        "missing required supported surfaces: recursive_lifecycle_admission_packet_checker" == err
        for err in report["errors"]
    )


def test_proof_coverage_matrix_rejects_missing_recursive_scaling_nonclaim() -> None:
    matrix = _matrix()
    non_claims = list(matrix["non_claims"])  # type: ignore[arg-type]
    matrix["non_claims"] = [
        item for item in non_claims if item != "does_not_claim_recursive_production_admission"
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any(
        "missing required non-claims: does_not_claim_recursive_production_admission" == err
        for err in report["errors"]
    )


def test_proof_coverage_matrix_rejects_missing_value_moving_surface() -> None:
    matrix = _matrix()
    surfaces = list(matrix["full_zk_value_moving_surfaces"])  # type: ignore[arg-type]
    matrix["full_zk_value_moving_surfaces"] = [
        item for item in surfaces if item["id"] != "proof_market_reward_execution"  # type: ignore[index]
    ]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("missing required value-moving surfaces: proof_market_reward_execution" == err for err in report["errors"])


def test_proof_coverage_matrix_rejects_hidden_value_moving_gap_ref() -> None:
    matrix = _matrix()
    surface = copy.deepcopy(matrix["full_zk_value_moving_surfaces"][0])  # type: ignore[index]
    surface["gap_surface_ids"] = []
    matrix["full_zk_value_moving_surfaces"][0] = surface  # type: ignore[index]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("value-moving coverage missing required gap refs: spot_complete_block_real_proof" == err for err in report["errors"])


def test_proof_coverage_matrix_rejects_full_zk_overclaim_with_gap_ref() -> None:
    matrix = _matrix()
    surface = copy.deepcopy(matrix["full_zk_value_moving_surfaces"][0])  # type: ignore[index]
    surface["coverage_status"] = "covered"
    matrix["full_zk_value_moving_surfaces"][0] = surface  # type: ignore[index]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("covered value-moving surface must not carry gap_surface_ids" in err for err in report["errors"])


def test_proof_coverage_matrix_rejects_gap_with_claim_id() -> None:
    matrix = _matrix()
    gap = copy.deepcopy(matrix["gap_surfaces"][0])  # type: ignore[index]
    gap["claim_id"] = "py:fake:overclaim"
    matrix["gap_surfaces"][0] = gap  # type: ignore[index]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("gap surface must not carry claim_id" in err for err in report["errors"])


def test_proof_coverage_matrix_rejects_missing_claim_from_registry() -> None:
    matrix = _matrix()
    supported = copy.deepcopy(matrix["supported_surfaces"][0])  # type: ignore[index]
    supported["claim_id"] = "py:missing:claim"
    matrix["supported_surfaces"][0] = supported  # type: ignore[index]

    report = validate_proof_coverage_matrix_v0(matrix)

    assert report["ok"] is False
    assert any("claim_id missing from claims registry" in err for err in report["errors"])


def test_proof_coverage_matrix_require_full_zk_mode_fails_until_open_surfaces_close(capsys) -> None:
    code = main(["--require-full-zk"])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 1
    assert report["ok"] is False
    assert report["full_zk_execution_ready"] is False
    assert "uniform_batch_upba_execution" in report["succinct_open_value_moving_surfaces"]
    assert any("full zk execution is not ready" in err for err in report["errors"])


def test_proof_coverage_matrix_require_full_zk_mode_can_pass_after_gaps_close() -> None:
    matrix = _matrix()
    matrix["gap_surfaces"] = []
    matrix["non_claims"] = []
    closed_surfaces = []
    for raw_surface in matrix["full_zk_value_moving_surfaces"]:  # type: ignore[index]
        surface = copy.deepcopy(raw_surface)
        surface["coverage_status"] = "covered"
        surface["proof_surface_ids"] = ["risc0_supported_transition_real_proof_smoke"]
        surface["gap_surface_ids"] = []
        surface["required_non_claims"] = []
        closed_surfaces.append(surface)
    matrix["full_zk_value_moving_surfaces"] = closed_surfaces

    report = validate_proof_coverage_matrix_v0(matrix, require_full_zk=True)

    assert report["ok"] is True
    assert report["full_zk_execution_ready"] is True
    assert report["value_moving_full_zk_ready_count"] == 8
    assert report["succinct_open_value_moving_surfaces"] == []
    assert report["succinct_open_gap_ids"] == []


def test_proof_coverage_matrix_cli_outputs_report(tmp_path, capsys) -> None:
    matrix_path = tmp_path / "proof_coverage_matrix.json"
    matrix_path.write_text(json.dumps(_matrix(), indent=2, sort_keys=True), encoding="utf-8")

    code = main(["--matrix", str(matrix_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zeno_ledger.proof_coverage_matrix_report.v0"
