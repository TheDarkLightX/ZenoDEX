"""Focused J08 rollback and complete-state lineage tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_j08_rollback_check import (
    _root,
    _state_values,
    build_states,
)
from src.core.fcis_m6_j08_rollback import (
    J08Error,
    J08RollbackCodeV1,
    J08RollbackReasonV1,
    J08RollbackRejectV1,
    J08RollbackSuccessV1,
    _state_from_values,
    rollback_j08_v1,
)


def _rollback() -> J08RollbackSuccessV1:
    switch, source, anchor = build_states()
    result = rollback_j08_v1(
        switch,
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        rollback_sequence=source.authority_epoch_index + 1,
    )
    assert type(result) is J08RollbackSuccessV1
    return result


def test_rollback_restores_every_complete_state_root_and_appends_history() -> None:
    result = _rollback()
    certificate = result.certificate
    anchor = certificate.anchor
    target = certificate.target
    assert target.current_state_root == anchor.current_state_root
    assert target.deployment_config_root == anchor.deployment_config_root
    assert target.residual_state_root == anchor.residual_state_root
    assert target.nullifier_root == anchor.nullifier_root
    assert target.outbox_root == anchor.outbox_root
    assert target.effect_identity_root == anchor.effect_identity_root
    assert target.history_root != anchor.history_root
    assert target.authority_epoch_index == certificate.source.authority_epoch_index + 1
    assert target.allowed_writer_roots == ()
    assert result.requires_fresh_authorization
    assert not result.can_accept_value_movement


@pytest.mark.parametrize(
    "field",
    (
        "current_state_root",
        "deployment_config_root",
        "residual_state_root",
        "nullifier_root",
        "outbox_root",
        "effect_identity_root",
    ),
)  # type: ignore[untyped-decorator]
def test_partial_rollback_target_is_rejected(field: str) -> None:
    result = _rollback()
    certificate = result.certificate
    values = _state_values(certificate.target)
    values[field] = _root(f"j08-forged-target:{field}")
    forged_target = _state_from_values(values)
    object.__setattr__(certificate, "target", forged_target)
    with pytest.raises(J08Error, match="canonically derived"):
        certificate.to_wire()


def test_history_erasure_is_rejected() -> None:
    result = _rollback()
    certificate = result.certificate
    values = _state_values(certificate.target)
    values["history_root"] = certificate.anchor.history_root
    forged_target = _state_from_values(values)
    object.__setattr__(certificate, "target", forged_target)
    with pytest.raises(J08Error, match="canonically derived"):
        certificate.to_wire()


def test_public_constructors_do_not_mint_state_or_rollback_authority() -> None:
    result = _rollback()
    with pytest.raises(J08Error, match="verifier-owned"):
        replace(result.certificate.source)
    with pytest.raises(J08Error, match="verifier-owned"):
        replace(result.certificate)
    with pytest.raises(J08Error, match="verifier-owned"):
        replace(result)


def test_wrong_inputs_and_path_boundaries_fail_closed() -> None:
    switch, source, anchor = build_states()
    wrong = rollback_j08_v1(
        object(),
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        rollback_sequence=source.authority_epoch_index + 1,
    )
    assert type(wrong) is J08RollbackRejectV1
    assert wrong.code is J08RollbackCodeV1.SWITCH_REJECTED
    with pytest.raises(J08Error):
        J08RollbackRejectV1(J08RollbackCodeV1.WRONG_EXACT_TYPE, ())
    with pytest.raises(J08Error):
        J08RollbackRejectV1(
            J08RollbackCodeV1.WRONG_EXACT_TYPE,
            tuple(f"p{index}" for index in range(9)),
        )
    with pytest.raises(J08Error):
        J08RollbackRejectV1(J08RollbackCodeV1.WRONG_EXACT_TYPE, ("x" * 65,))
