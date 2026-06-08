from __future__ import annotations

from types import SimpleNamespace
from typing import Any

from src.integration.api_server_pokayoke_routes import maybe_handle_pokayoke_swap_route


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "reserve_in": 10_000,
        "reserve_out": 20_000,
        "amount_in": 100,
        "fee_bps": 30,
        "pending_volume_same_direction": 50,
        "confidence_bps": 9500,
    }
    request.update(overrides)
    return request


def _fast_suggestion(kind: str, target_bps: int, *, suggested: int | None = 42) -> SimpleNamespace:
    return SimpleNamespace(
        kind=kind,
        target_bps=target_bps,
        suggested_amount_in=suggested,
        status="ok" if suggested is not None else "not_found",
        eval_count=3,
        baseline_value_bps=900,
        suggested_value_bps=target_bps - 1 if suggested is not None else None,
    )


def _heavy_suggestion(target_action: str, *, suggested: int | None = 41) -> SimpleNamespace:
    return SimpleNamespace(
        target_action=target_action,
        suggested_amount_in=suggested,
        status="ok" if suggested is not None else "not_found",
        eval_count=5,
        baseline_action="block",
        suggested_action=target_action if suggested is not None else None,
        baseline_reasons=("large_impact",),
        suggested_reasons=("within_slippage",) if suggested is not None else None,
    )


def test_unknown_pokayoke_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_pokayoke_swap_route(
        path="/api/dex/not_pokayoke",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_fast_pokayoke_success_filters_options_and_passes_expected_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    impact_calls: list[dict[str, object]] = []
    required_calls: list[dict[str, object]] = []

    def suggest_amount_in_for_impact_lt_bps(**kwargs: object) -> SimpleNamespace:
        impact_calls.append(kwargs)
        return _fast_suggestion("impact_lt_bps", int(kwargs["target_impact_bps"]))

    def suggest_amount_in_for_required_slippage_le_bps(**kwargs: object) -> SimpleNamespace:
        required_calls.append(kwargs)
        return _fast_suggestion("required_slippage_le_bps", int(kwargs["target_required_slippage_bps"]))

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_for_impact_lt_bps",
        suggest_amount_in_for_impact_lt_bps,
    )
    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_for_required_slippage_le_bps",
        suggest_amount_in_for_required_slippage_le_bps,
    )

    handled = maybe_handle_pokayoke_swap_route(
        path="/api/dex/pokayoke_swap_suggest",
        obj=_request(
            user_slippage_bps="75",
            slippage_options_bps=[50, "100", -1, 10001, "bad"],
        ),
        write_json=write_json,
    )

    assert handled is True
    assert [call["target_impact_bps"] for call in impact_calls] == [500, 100]
    assert [call["target_required_slippage_bps"] for call in required_calls] == [75, 100]
    assert all(call["reserve_in"] == 10_000 for call in impact_calls + required_calls)
    assert all(call["reserve_out"] == 20_000 for call in impact_calls + required_calls)
    assert all(call["fee_bps"] == 30 for call in impact_calls + required_calls)
    assert all(call["amount_in"] == 100 for call in impact_calls + required_calls)
    assert all(call["window"] == 256 for call in impact_calls + required_calls)
    status, payload = writes[0]
    assert status == 200
    assert isinstance(payload, dict)
    assert payload["ok"] is True
    suggestions = payload["suggestions"]
    assert isinstance(suggestions, dict)
    assert suggestions["impact_lt_500_bps"]["target_bps"] == 500
    assert suggestions["impact_lt_100_bps"]["target_bps"] == 100
    assert suggestions["required_slippage_le_user_bps"]["target_bps"] == 75
    assert suggestions["required_slippage_le_max_option_bps"]["target_bps"] == 100


def test_fast_pokayoke_omitted_optional_targets_return_none(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_for_impact_lt_bps",
        lambda **kwargs: _fast_suggestion("impact_lt_bps", int(kwargs["target_impact_bps"]), suggested=None),
    )

    def required_should_not_run(**_kwargs: object) -> SimpleNamespace:
        raise AssertionError("required slippage suggestions should not run without targets")

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_for_required_slippage_le_bps",
        required_should_not_run,
    )

    handled = maybe_handle_pokayoke_swap_route(
        path="/api/dex/pokayoke_swap_suggest",
        obj=_request(slippage_options_bps="not-a-list"),
        write_json=write_json,
    )

    assert handled is True
    status, payload = writes[0]
    assert status == 200
    assert isinstance(payload, dict)
    assert payload["suggestions"]["required_slippage_le_user_bps"] is None
    assert payload["suggestions"]["required_slippage_le_max_option_bps"] is None
    assert payload["suggestions"]["impact_lt_500_bps"]["suggested_amount_in"] is None


def test_fast_pokayoke_invalid_numeric_input_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def suggestion_should_not_run(**_kwargs: object) -> SimpleNamespace:
        raise AssertionError("suggestion should not run after parse failure")

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_for_impact_lt_bps",
        suggestion_should_not_run,
    )

    handled = maybe_handle_pokayoke_swap_route(
        path="/api/dex/pokayoke_swap_suggest",
        obj=_request(reserve_in="not-an-int"),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"})]


def test_heavy_pokayoke_success_filters_options_targets_and_formats_rows(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def suggest_amount_in_exact_in_cpmm(**kwargs: object) -> list[SimpleNamespace]:
        captured.update(kwargs)
        return [_heavy_suggestion("allow"), _heavy_suggestion("confirm", suggested=None)]

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_exact_in_cpmm",
        suggest_amount_in_exact_in_cpmm,
    )

    handled = maybe_handle_pokayoke_swap_route(
        path="/api/dex/pokayoke_swap_suggest_heavy",
        obj=_request(
            user_slippage_bps="75",
            slippage_options_bps=[10, "20", -1, 10001, "bad"],
            max_attacker_amount_in="1234",
            max_evals="7",
            target_actions=["Allow", "confirm", "allow", "bad", ""],
        ),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "reserve_in": 10_000,
        "reserve_out": 20_000,
        "fee_bps": 30,
        "amount_in": 100,
        "pending_volume_same_direction": 50,
        "confidence_bps": 9500,
        "slippage_options_bps": [10, 20],
        "max_attacker_amount_in": 1234,
        "user_slippage_bps": 75,
        "max_evals": 7,
        "target_actions": ("allow", "confirm"),
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "suggestions": [
                    {
                        "target_action": "allow",
                        "suggested_amount_in": 41,
                        "status": "ok",
                        "eval_count": 5,
                        "baseline_action": "block",
                        "suggested_action": "allow",
                        "baseline_reasons": ["large_impact"],
                        "suggested_reasons": ["within_slippage"],
                    },
                    {
                        "target_action": "confirm",
                        "suggested_amount_in": None,
                        "status": "not_found",
                        "eval_count": 5,
                        "baseline_action": "block",
                        "suggested_action": None,
                        "baseline_reasons": ["large_impact"],
                        "suggested_reasons": None,
                    },
                ],
            },
        )
    ]


def test_heavy_pokayoke_defaults_options_and_targets(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def suggest_amount_in_exact_in_cpmm(**kwargs: object) -> list[SimpleNamespace]:
        captured.update(kwargs)
        return []

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_exact_in_cpmm",
        suggest_amount_in_exact_in_cpmm,
    )

    handled = maybe_handle_pokayoke_swap_route(
        path="/api/dex/pokayoke_swap_suggest_heavy",
        obj=_request(user_slippage_bps=75, slippage_options_bps="not-a-list", target_actions=["bad"]),
        write_json=write_json,
    )

    assert handled is True
    assert captured["slippage_options_bps"] is None
    assert captured["max_attacker_amount_in"] == 2000
    assert captured["max_evals"] == 16
    assert captured["target_actions"] == ("confirm", "allow")
    assert writes == [(200, {"ok": True, "suggestions": []})]


def test_heavy_pokayoke_invalid_inputs_map_to_generic_error(monkeypatch: Any) -> None:
    def suggestion_should_not_run(**_kwargs: object) -> list[SimpleNamespace]:
        raise AssertionError("suggestion should not run after parse failure")

    monkeypatch.setattr(
        "src.core.pokayoke_swap_suggest.suggest_amount_in_exact_in_cpmm",
        suggestion_should_not_run,
    )

    cases = [
        _request(),
        _request(user_slippage_bps=75, max_attacker_amount_in=-1),
        _request(user_slippage_bps=75, max_attacker_amount_in=50_001),
        _request(user_slippage_bps=75, max_evals=0),
        _request(user_slippage_bps=75, max_evals=65),
        _request(user_slippage_bps="bad"),
    ]
    for obj in cases:
        writes, write_json = _capture()

        handled = maybe_handle_pokayoke_swap_route(
            path="/api/dex/pokayoke_swap_suggest_heavy",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [
            (400, {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": "request failed"})
        ]
