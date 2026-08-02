"""Independent deterministic checks for the J08 rollback relation."""

from __future__ import annotations

import argparse
from hashlib import sha256
from typing import Final, cast

from experiments.fcis_m6_j07_authority_switch_check import build_f06_token, build_gate
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_j07_authority_switch import J07SwitchSuccessV1, switch_authority_v1
from src.core.fcis_m6_j08_rollback import (
    J08CompleteStateV1,
    J08RollbackCodeV1,
    J08RollbackReasonV1,
    J08RollbackRejectV1,
    J08RollbackSuccessV1,
    _register_state_v1,
    _state_body,
    _state_from_values,
    rollback_j08_v1,
)

J08_VECTOR_PATH: Final = "docs/research/m6_tasks/TASK_J08_ROLLBACK_V1.json"


def _root(label: str) -> str:
    return sha256(label.encode("ascii")).hexdigest()


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


def _state_values(state: J08CompleteStateV1) -> dict[str, object]:
    body = _state_body(state)
    return {
        "phase": dra.MigrationPhaseV1(cast(str, body["phase"])),
        "authority_epoch_index": body["authority_epoch_index"],
        "allowed_writer_roots": tuple(cast(list[str], body["allowed_writer_roots"])),
        "active_profile_root": body["active_profile_root"],
        "authority_state_root": body["authority_state_root"],
        "context_snapshot_root": body["context_snapshot_root"],
        "current_state_root": body["current_state_root"],
        "deployment_config_root": body["deployment_config_root"],
        "history_root": body["history_root"],
        "residual_state_root": body["residual_state_root"],
        "nullifier_root": body["nullifier_root"],
        "outbox_root": body["outbox_root"],
        "effect_identity_root": body["effect_identity_root"],
    }


def build_states() -> tuple[J07SwitchSuccessV1, J08CompleteStateV1, J08CompleteStateV1]:
    switch = _switch()
    pre = switch.pre_context
    post = switch.post_context
    anchor = _state_from_values(
        {
            "phase": pre.phase,
            "authority_epoch_index": pre.epoch_index,
            "allowed_writer_roots": (),
            "active_profile_root": pre.active_profile_root,
            "authority_state_root": pre.authority_state_root,
            "context_snapshot_root": pre.current_snapshot_root,
            "current_state_root": pre.current_state_root,
            "deployment_config_root": pre.deployment_config_root,
            "history_root": _root("j08-anchor-history"),
            "residual_state_root": _root("j08-anchor-residual"),
            "nullifier_root": _root("j08-anchor-nullifiers"),
            "outbox_root": _root("j08-anchor-outbox"),
            "effect_identity_root": _root("j08-anchor-effects"),
        }
    )
    source = _state_from_values(
        {
            "phase": post.phase,
            "authority_epoch_index": post.epoch_index,
            "allowed_writer_roots": post.allowed_writer_roots,
            "active_profile_root": post.active_profile_root,
            "authority_state_root": post.authority_state_root,
            "context_snapshot_root": post.current_snapshot_root,
            "current_state_root": post.current_state_root,
            "deployment_config_root": post.deployment_config_root,
            "history_root": anchor.history_root,
            "residual_state_root": anchor.residual_state_root,
            "nullifier_root": anchor.nullifier_root,
            "outbox_root": anchor.outbox_root,
            "effect_identity_root": anchor.effect_identity_root,
        }
    )
    return switch, source, anchor


def build_payload() -> dict[str, object]:
    switch, source, anchor = build_states()
    result = rollback_j08_v1(
        switch,
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        rollback_sequence=source.authority_epoch_index + 1,
    )
    assert type(result) is J08RollbackSuccessV1
    payload = result.to_wire()
    payload["rollback_root"] = result.certificate.rollback_root
    payload["source_snapshot_root"] = result.certificate.source.snapshot_root
    payload["anchor_snapshot_root"] = result.certificate.anchor.snapshot_root
    payload["target_snapshot_root"] = result.certificate.target.snapshot_root
    payload["target_history_root"] = result.certificate.target.history_root
    payload["target_state_root"] = result.certificate.target.current_state_root
    payload["target_outbox_root"] = result.certificate.target.outbox_root
    payload["target_effect_identity_root"] = result.certificate.target.effect_identity_root
    return payload


def _assert_rejected(
    switch: object,
    source: object,
    anchor: object,
    *,
    reason: object,
    sequence: object,
    code: J08RollbackCodeV1,
) -> None:
    result = rollback_j08_v1(
        switch,
        source,
        anchor,
        reason=reason,
        rollback_sequence=sequence,
    )
    assert type(result) is J08RollbackRejectV1
    assert result.code is code


def run_checks(*, check_vector: bool = True) -> None:
    switch, source, anchor = build_states()
    accepted = rollback_j08_v1(
        switch,
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        rollback_sequence=source.authority_epoch_index + 1,
    )
    assert type(accepted) is J08RollbackSuccessV1
    certificate = accepted.certificate
    assert certificate.target.current_state_root == anchor.current_state_root
    assert certificate.target.deployment_config_root == anchor.deployment_config_root
    assert certificate.target.residual_state_root == anchor.residual_state_root
    assert certificate.target.nullifier_root == anchor.nullifier_root
    assert certificate.target.outbox_root == anchor.outbox_root
    assert certificate.target.effect_identity_root == anchor.effect_identity_root
    assert certificate.target.history_root != anchor.history_root
    assert certificate.target.authority_epoch_index == source.authority_epoch_index + 1
    assert certificate.target.allowed_writer_roots == ()
    assert accepted.requires_fresh_authorization
    assert not accepted.can_accept_value_movement

    source_values = _state_values(source)
    source_values["current_state_root"] = _root("j08-forged-source-state")
    forged_source = _register_state_v1(_state_from_values(source_values))
    _assert_rejected(
        switch,
        forged_source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        sequence=source.authority_epoch_index + 1,
        code=J08RollbackCodeV1.TARGET_MISMATCH,
    )

    anchor_values = _state_values(anchor)
    anchor_values["residual_state_root"] = _root("j08-forged-residual")
    forged_anchor = _register_state_v1(_state_from_values(anchor_values))
    _assert_rejected(
        switch,
        source,
        forged_anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        sequence=source.authority_epoch_index + 1,
        code=J08RollbackCodeV1.COMPLETE_STATE_MISMATCH,
    )

    _assert_rejected(
        switch,
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        sequence=source.authority_epoch_index,
        code=J08RollbackCodeV1.SEQUENCE_REJECTED,
    )
    _assert_rejected(
        switch,
        source,
        anchor,
        reason=object(),
        sequence=source.authority_epoch_index + 1,
        code=J08RollbackCodeV1.REASON_REJECTED,
    )
    _assert_rejected(
        object(),
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        sequence=source.authority_epoch_index + 1,
        code=J08RollbackCodeV1.SWITCH_REJECTED,
    )
    if check_vector:
        import json

        with open(J08_VECTOR_PATH, encoding="utf-8") as handle:
            expected = json.load(handle)
        assert expected == build_payload()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-vector", action="store_true")
    args = parser.parse_args()
    run_checks(check_vector=not args.no_vector)
    payload = build_payload()
    print(f"J08_ROLLBACK_MATCH {payload['rollback_root']}")
    if not args.no_vector:
        print("J08_ROLLBACK_VECTOR_MATCH")


if __name__ == "__main__":
    main()
