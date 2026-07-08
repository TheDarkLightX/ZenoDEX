from __future__ import annotations

from src.integration.api_server_dex_dispatch import DexRequestContext
from src.integration.dex_dispatch_slippage_handlers import (
    _handle_pokayoke_swap_suggest,
    _handle_pokayoke_swap_suggest_heavy,
    _handle_slippage_advice,
    build_swap_execution_regret_tau_binding,
    project_swap_execution_regret_tau_facts,
    swap_execution_regret_tau_binding_to_payload,
    verify_swap_execution_regret_tau_binding,
)


def _ctx() -> DexRequestContext:
    return DexRequestContext(server=object(), cors_origin=None, raw_body=None)


def _base_slippage_request(*, inaction_regret_bps: int | None = None) -> dict[str, object]:
    request: dict[str, object] = {
        "reserve_in": 1_000_000,
        "reserve_out": 1_000_000,
        "amount_in": 10_000,
        "fee_bps": 30,
        "user_slippage_bps": 50,
        "slippage_options_bps": [10, 50, 100],
    }
    if inaction_regret_bps is not None:
        request["inaction_regret_bps"] = inaction_regret_bps
    return request


def _quote_snapshot(body: dict[str, object]) -> dict[str, object]:
    advice = body["advice"]
    assert isinstance(advice, dict)
    return {
        key: value
        for key, value in advice.items()
        if key != "pokayoke"
    }


def _all_true_tau_projection(body: dict[str, object]):
    advice = body["advice"]
    assert isinstance(advice, dict)
    pokayoke = advice["pokayoke"]
    assert isinstance(pokayoke, dict)
    return project_swap_execution_regret_tau_facts(
        pokayoke,
        impact_within_limit_ok=True,
        quote_age_within_limit_ok=True,
        hop_count_within_limit_ok=True,
        route_cert_ok=True,
        oracle_fresh_ok=True,
        not_expired_ok=True,
        require_route_cert=True,
        require_oracle_fresh=True,
        require_not_expired=True,
        proof_ok=True,
        binding_ok=True,
    )


def test_slippage_advice_handler_rejects_bool_amount() -> None:
    status, body = _handle_slippage_advice(
        {"reserve_in": 1_000, "reserve_out": 1_000, "amount_in": True},
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "slippage_advice_error", "details": "request failed"}


def test_slippage_advice_handler_rejects_numeric_string_amount() -> None:
    status, body = _handle_slippage_advice(
        {"reserve_in": 1_000, "reserve_out": 1_000, "amount_in": "100"},
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "slippage_advice_error", "details": "request failed"}


def test_slippage_advice_handler_emits_proofux_when_inaction_regret_is_supplied() -> None:
    status, body = _handle_slippage_advice(
        _base_slippage_request(inaction_regret_bps=800),
        _ctx(),
    )

    assert status == 200
    pokayoke = body["advice"]["pokayoke"]
    assert pokayoke["action"] == "typed_confirm"
    proofux = pokayoke["proofux"]
    assert proofux["legacy_action"] == "typed_confirm"
    assert proofux["selected_action"] == "wait_or_requote"
    assert proofux["regret_within_limit_ok"] is False
    assert proofux["inaction_regret_bps"] == 800
    assert proofux["minimax_certificate"]["chosen_certificate_id"] == "execute_typed_confirm"
    assert proofux["minimax_certificate"]["best_certificate_id"] == "wait_or_requote"


def test_slippage_advice_proofux_projects_to_rejecting_tau_facts() -> None:
    status, body = _handle_slippage_advice(
        _base_slippage_request(inaction_regret_bps=800),
        _ctx(),
    )

    assert status == 200
    projection = _all_true_tau_projection(body)

    assert projection.reason == "regret_outside_limit"
    assert projection.tau_step["i1"] == 0
    assert projection.tau_step["i11"] == 1
    assert projection.tau_step["i12"] == 1
    assert projection.certificate_hash is not None


def test_slippage_advice_proofux_projects_to_accepting_tau_facts() -> None:
    status, body = _handle_slippage_advice(
        _base_slippage_request(inaction_regret_bps=10_000),
        _ctx(),
    )

    assert status == 200
    projection = _all_true_tau_projection(body)

    assert projection.reason == "ok"
    assert projection.tau_step == {
        "i1": 1,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
        "i12": 1,
    }
    assert projection.certificate_hash is not None


def test_slippage_advice_missing_proofux_projects_to_all_zero_tau_facts() -> None:
    status, body = _handle_slippage_advice(
        _base_slippage_request(),
        _ctx(),
    )

    assert status == 200
    projection = _all_true_tau_projection(body)

    assert projection.reason == "missing_proofux_payload"
    assert set(projection.tau_step.values()) == {0}
    assert projection.certificate_hash is None


def test_slippage_advice_tau_binding_verifies_exact_transcript() -> None:
    request = _base_slippage_request(inaction_regret_bps=10_000)
    status, body = _handle_slippage_advice(request, _ctx())

    assert status == 200
    projection = _all_true_tau_projection(body)
    quote_snapshot = _quote_snapshot(body)
    binding = build_swap_execution_regret_tau_binding(
        request_snapshot=request,
        quote_snapshot=quote_snapshot,
        projection=projection,
    )
    payload = swap_execution_regret_tau_binding_to_payload(binding)

    assert payload["schema"] == "zenodex.proofux.swap_execution_regret_tau_binding.v1"
    assert payload["binding_hash"].startswith("sha256:")
    assert verify_swap_execution_regret_tau_binding(
        payload,
        request_snapshot=request,
        quote_snapshot=quote_snapshot,
        projection=projection,
    )


def test_slippage_advice_tau_binding_rejects_tampered_transcript_surfaces() -> None:
    request = _base_slippage_request(inaction_regret_bps=10_000)
    status, body = _handle_slippage_advice(request, _ctx())

    assert status == 200
    projection = _all_true_tau_projection(body)
    quote_snapshot = _quote_snapshot(body)
    payload = swap_execution_regret_tau_binding_to_payload(
        build_swap_execution_regret_tau_binding(
            request_snapshot=request,
            quote_snapshot=quote_snapshot,
            projection=projection,
        )
    )

    tampered_request = dict(request, amount_in=10_001)
    assert not verify_swap_execution_regret_tau_binding(
        payload,
        request_snapshot=tampered_request,
        quote_snapshot=quote_snapshot,
        projection=projection,
    )

    tampered_quote = dict(quote_snapshot, best_amount_out=999_999)
    assert not verify_swap_execution_regret_tau_binding(
        payload,
        request_snapshot=request,
        quote_snapshot=tampered_quote,
        projection=projection,
    )

    tampered_projection = project_swap_execution_regret_tau_facts(
        body["advice"]["pokayoke"],
        impact_within_limit_ok=True,
        quote_age_within_limit_ok=True,
        hop_count_within_limit_ok=True,
        route_cert_ok=True,
        oracle_fresh_ok=True,
        not_expired_ok=True,
        require_route_cert=True,
        require_oracle_fresh=True,
        require_not_expired=True,
        proof_ok=False,
        binding_ok=True,
    )
    assert not verify_swap_execution_regret_tau_binding(
        payload,
        request_snapshot=request,
        quote_snapshot=quote_snapshot,
        projection=tampered_projection,
    )

    tampered_payload = dict(payload, certificate_hash="sha256:" + "0" * 64)
    assert not verify_swap_execution_regret_tau_binding(
        tampered_payload,
        request_snapshot=request,
        quote_snapshot=quote_snapshot,
        projection=projection,
    )


def test_slippage_advice_handler_rejects_bool_inaction_regret() -> None:
    status, body = _handle_slippage_advice(
        {
            "reserve_in": 1_000_000,
            "reserve_out": 1_000_000,
            "amount_in": 10_000,
            "fee_bps": 30,
            "user_slippage_bps": 50,
            "inaction_regret_bps": True,
        },
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "slippage_advice_error", "details": "request failed"}


def test_pokayoke_suggest_handler_rejects_bool_amount() -> None:
    status, body = _handle_pokayoke_swap_suggest(
        {"reserve_in": 1_000, "reserve_out": 1_000, "amount_in": True},
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"}


def test_pokayoke_suggest_handler_rejects_numeric_string_amount() -> None:
    status, body = _handle_pokayoke_swap_suggest(
        {"reserve_in": 1_000, "reserve_out": 1_000, "amount_in": "100"},
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"}


def test_pokayoke_heavy_handler_rejects_bool_numeric_fields() -> None:
    status, body = _handle_pokayoke_swap_suggest_heavy(
        {
            "reserve_in": 1_000,
            "reserve_out": 1_000,
            "amount_in": 100,
            "user_slippage_bps": True,
        },
        _ctx(),
    )

    assert status == 400
    assert body == {
        "ok": False,
        "error": "pokayoke_swap_suggest_heavy_error",
        "details": "request failed",
    }


def test_pokayoke_heavy_handler_rejects_numeric_string_user_slippage() -> None:
    status, body = _handle_pokayoke_swap_suggest_heavy(
        {
            "reserve_in": 1_000,
            "reserve_out": 1_000,
            "amount_in": 100,
            "user_slippage_bps": "25",
        },
        _ctx(),
    )

    assert status == 400
    assert body == {
        "ok": False,
        "error": "pokayoke_swap_suggest_heavy_error",
        "details": "request failed",
    }
