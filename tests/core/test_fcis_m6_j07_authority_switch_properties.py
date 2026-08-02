"""Deterministic property checks for J07 writer-profile closure."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_j07_authority_switch_check import build_f06_token, build_gate
from src.core.fcis_m6_j07_authority_switch import (
    J07RejectCodeV1,
    J07SwitchSuccessV1,
    J07WriterAcceptedV1,
    J07WriterRejectV1,
    _mint_writer_token_v1,
    authorize_writer_v1,
    switch_authority_v1,
)


def _switch() -> J07SwitchSuccessV1:
    reopened, genesis, migration_token, verifier = build_f06_token()
    gate = build_gate(migration_token)
    result = switch_authority_v1(
        gate,
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    assert type(result) is J07SwitchSuccessV1
    return result


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(profile=st.sampled_from(("legacy", "target")))  # type: ignore[untyped-decorator]
def test_only_target_profile_is_admitted_after_switch(profile: str) -> None:
    switched = _switch()
    profile_root = (
        switched.post_context.legacy_profile_root
        if profile == "legacy"
        else switched.post_context.target_profile_root
    )
    token = _mint_writer_token_v1(switched.post_context, profile_root)
    result = authorize_writer_v1(switched.post_context, token)
    if profile == "target":
        assert type(result) is J07WriterAcceptedV1
    else:
        assert type(result) is J07WriterRejectV1
        assert result.code is J07RejectCodeV1.WRITER_PROFILE_DISABLED
