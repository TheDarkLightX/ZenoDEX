"""Deterministic property checks for J07 writer-profile closure."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_j07_authority_switch_check import (
    build_f06_token,
    build_gate,
    build_writer_admission_context,
    build_writer_eligibility,
)
from src.core.fcis_m6_j07_authority_switch import (
    J07SwitchSuccessV1,
    switch_authority_v1,
)
from src.core.fcis_m6_j07_writer_admission_v2 import (
    J07WriterAdmissionRejectCodeV2,
    J07WriterAdmissionRejectV2,
)
from src.core.fcis_m6_j07_writer_token_v3 import (
    J07WriterAcceptedV3,
    J07WriterTokenV3,
    authorize_writer_v3,
    issue_writer_token_v3,
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


@settings(max_examples=24, deadline=None, derandomize=True)
@given(profile=st.sampled_from(("legacy", "target")))
def test_only_target_profile_is_admitted_after_switch(profile: str) -> None:
    switched = _switch()
    profile_root = (
        switched.post_context.legacy_profile_root
        if profile == "legacy"
        else switched.post_context.target_profile_root
    )
    admission = build_writer_admission_context(switched.post_context)
    eligibility = build_writer_eligibility(switched.post_context, profile_root)
    issued = issue_writer_token_v3(switched.post_context, admission, eligibility)
    if profile == "target":
        assert type(issued) is J07WriterTokenV3
        result = authorize_writer_v3(
            switched.post_context,
            admission,
            issued,
            eligibility,
        )
        assert type(result) is J07WriterAcceptedV3
    else:
        assert type(issued) is J07WriterAdmissionRejectV2
        assert issued.code is J07WriterAdmissionRejectCodeV2.WRITER_PROFILE_DISABLED
