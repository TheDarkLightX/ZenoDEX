from __future__ import annotations

from src.core.perp_market_version_prefix_guard import (
    REJECT_CH2P_PREFIX_MISMATCH,
    REJECT_CH3P_PREFIX_MISMATCH,
    REJECT_INVALID_VERSION,
    REJECT_OK,
    evaluate_perp_market_version_prefix_guard,
)


def test_perp_market_version_prefix_guard_accepts_ch3p_market() -> None:
    outcome = evaluate_perp_market_version_prefix_guard(
        version_is_v0_1=False,
        version_is_ch2p=False,
        version_is_ch3p=True,
        market_has_ch2p_prefix=False,
        market_has_ch3p_prefix=True,
    )

    assert outcome.version_ok is True
    assert outcome.clearinghouse_3p_version is True
    assert outcome.market_prefix_ok is True
    assert outcome.admission_ok is True
    assert outcome.reject_code == REJECT_OK


def test_perp_market_version_prefix_guard_rejects_missing_ch2p_prefix() -> None:
    outcome = evaluate_perp_market_version_prefix_guard(
        version_is_v0_1=False,
        version_is_ch2p=True,
        version_is_ch3p=False,
        market_has_ch2p_prefix=False,
        market_has_ch3p_prefix=False,
    )

    assert outcome.version_ok is True
    assert outcome.clearinghouse_2p_version is True
    assert outcome.market_prefix_ok is False
    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_CH2P_PREFIX_MISMATCH


def test_perp_market_version_prefix_guard_rejects_missing_ch3p_prefix() -> None:
    outcome = evaluate_perp_market_version_prefix_guard(
        version_is_v0_1=False,
        version_is_ch2p=False,
        version_is_ch3p=True,
        market_has_ch2p_prefix=False,
        market_has_ch3p_prefix=False,
    )

    assert outcome.version_ok is True
    assert outcome.clearinghouse_3p_version is True
    assert outcome.market_prefix_ok is False
    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_CH3P_PREFIX_MISMATCH


def test_perp_market_version_prefix_guard_rejects_unknown_version() -> None:
    outcome = evaluate_perp_market_version_prefix_guard(
        version_is_v0_1=False,
        version_is_ch2p=False,
        version_is_ch3p=False,
        market_has_ch2p_prefix=False,
        market_has_ch3p_prefix=False,
    )

    assert outcome.version_ok is False
    assert outcome.market_prefix_ok is False
    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_INVALID_VERSION
