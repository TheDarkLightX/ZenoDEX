from __future__ import annotations

from src.core.perp_tau_ingress_stream import (
    REJECT_LEGACY_DEX_CONFLICT,
    REJECT_NO_PERP_STREAM,
    REJECT_OK,
    evaluate_perp_tau_ingress_stream,
)


def test_perp_tau_ingress_stream_prefers_upstream_even_if_legacy_is_bad() -> None:
    outcome = evaluate_perp_tau_ingress_stream(
        upstream_stream_present=True,
        legacy_stream_present=True,
        legacy_dex_stream_present=True,
        legacy_candidate_dex_like=True,
        legacy_candidate_perp_like=False,
    )

    assert outcome.selected is True
    assert outcome.upstream_stream_selected is True
    assert outcome.legacy_fallback_used is False
    assert outcome.reject_code == REJECT_OK


def test_perp_tau_ingress_stream_accepts_clean_legacy_fallback() -> None:
    outcome = evaluate_perp_tau_ingress_stream(
        upstream_stream_present=False,
        legacy_stream_present=True,
        legacy_dex_stream_present=False,
        legacy_candidate_dex_like=False,
        legacy_candidate_perp_like=True,
    )

    assert outcome.selected is True
    assert outcome.upstream_stream_selected is False
    assert outcome.legacy_fallback_used is True
    assert outcome.reject_code == REJECT_OK


def test_perp_tau_ingress_stream_rejects_legacy_dex_conflict() -> None:
    outcome = evaluate_perp_tau_ingress_stream(
        upstream_stream_present=False,
        legacy_stream_present=True,
        legacy_dex_stream_present=True,
        legacy_candidate_dex_like=False,
        legacy_candidate_perp_like=True,
    )

    assert outcome.selected is False
    assert outcome.legacy_fallback_used is False
    assert outcome.reject_code == REJECT_LEGACY_DEX_CONFLICT


def test_perp_tau_ingress_stream_rejects_when_no_stream_is_available() -> None:
    outcome = evaluate_perp_tau_ingress_stream(
        upstream_stream_present=False,
        legacy_stream_present=False,
        legacy_dex_stream_present=False,
        legacy_candidate_dex_like=False,
        legacy_candidate_perp_like=False,
    )

    assert outcome.selected is False
    assert outcome.upstream_stream_selected is False
    assert outcome.legacy_fallback_used is False
    assert outcome.reject_code == REJECT_NO_PERP_STREAM
