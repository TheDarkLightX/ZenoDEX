from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
U16_MOD = 1 << 16


def _legacy_wrapping_delay_ok(proposal_ts: int, current_ts: int, min_delay: int) -> bool:
    return current_ts >= ((proposal_ts + min_delay) % U16_MOD)


def _subtraction_guard_delay_ok(proposal_ts: int, current_ts: int, min_delay: int) -> bool:
    return current_ts >= proposal_ts and (current_ts - proposal_ts) >= min_delay


def test_revision_policy_timelock_rejects_wrapping_delay_bypass() -> None:
    spec = (ROOT / "src/tau_specs/recommended/revision_policy_v1.tau").read_text(encoding="utf-8")

    assert "current_ts >= (proposal_ts + min_delay)" not in spec
    assert (
        "delay_ok(proposal_ts : bv[16], current_ts : bv[16], min_delay : bv[16]) := "
        "(current_ts >= proposal_ts) && ((current_ts - proposal_ts) >= min_delay)."
    ) in spec
    assert _legacy_wrapping_delay_ok(proposal_ts=65_530, current_ts=5, min_delay=10) is True
    assert _subtraction_guard_delay_ok(proposal_ts=65_530, current_ts=5, min_delay=10) is False


def _legacy_rate_valid(count: int, proposing: bool, max_ch: int, elapsed: bool) -> bool:
    params_ok = max_ch > 0
    current_ok = count < max_ch
    after_change_ok = (not proposing) or ((count + 1) <= max_ch)
    return params_ok and current_ok and (elapsed or after_change_ok)


def _reset_or_after_change_rate_valid(count: int, proposing: bool, max_ch: int, elapsed: bool) -> bool:
    params_ok = max_ch > 0
    current_ok = count < max_ch
    after_change_ok = (not proposing) or (current_ok and ((count + 1) <= max_ch))
    return params_ok and (elapsed or after_change_ok)


def test_governance_rate_limiter_reset_allows_fresh_window_at_saturated_count() -> None:
    spec = (ROOT / "src/tau_specs/recommended/governance_rate_limiter_v1.tau").read_text(
        encoding="utf-8"
    )

    assert "params_ok(max_ch) && current_ok(count, max_ch) && (window_allows" not in spec
    assert (
        "gov_rate_valid(count : bv[32], proposing : sbf, max_ch : bv[32], elapsed : sbf) := "
        "params_ok(max_ch) && (window_allows(elapsed) || after_change_ok(count, max_ch, proposing))."
    ) in spec
    assert _legacy_rate_valid(count=3, proposing=True, max_ch=3, elapsed=True) is False
    assert _reset_or_after_change_rate_valid(count=3, proposing=True, max_ch=3, elapsed=True) is True
