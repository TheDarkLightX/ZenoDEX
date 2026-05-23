from __future__ import annotations


def test_derivatives_authorization_matrix_is_valid() -> None:
    from tools.check_derivatives_authorization_matrix import validate_matrix

    report = validate_matrix()

    assert report["area_count"] == 5
    assert report["open_requirements"] == 0


def test_disputed_derivative_claims_stay_explicit() -> None:
    from tools.check_derivatives_authorization_matrix import load_matrix

    matrix = load_matrix()
    areas = {area["area_id"]: area for area in matrix["areas"]}

    assert areas["funding_rate_market"]["disputed_claim_refs"] == [
        "smt:funding_rate_market_v1:inductive_z3_cvc5"
    ]
    assert areas["curve_selection"]["disputed_claim_refs"] == [
        "smt:curve_selection_market_v1:inductive_z3_cvc5"
    ]
    assert areas["curve_selection"]["authorization_complete"] is True
    assert areas["funding_rate_market"]["authorization_complete"] is True
    assert areas["il_futures"]["authorization_complete"] is True
    assert areas["general_cfmo_fire"]["authorization_complete"] is True
    assert areas["perps_clearinghouse"]["authorization_complete"] is True


def test_all_derivative_areas_close_bounded_authorization_requirements() -> None:
    from tools.check_derivatives_authorization_matrix import load_matrix

    matrix = load_matrix()

    for area in matrix["areas"]:
        assert area["production_ready"] is False
        assert any(req["covered_required"] for req in area["requirements"])
        assert area["authorization_complete"] is True
        assert all(req["covered_required"] for req in area["requirements"])
