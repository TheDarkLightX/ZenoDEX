"""Independent J07 authority-switch checker and vector builder."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

from experiments.fcis_m6_f01_history_atom_check import build_atom
from experiments.fcis_m6_f06_reopen_authorization_check import (
    AcceptingVerifier,
    RejectingVerifier,
    build_evidence,
    build_genesis,
)
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_f02_history_encoder import (
    F02AckRowV1,
    F02AuthorityEpochV1,
    F02AuthorizedHistoryV1,
    F02DurableLayoutV1,
    encode_history,
)
from src.core.fcis_m6_f03_reopen import F03ReopenSuccessV1, reopen_layout
from src.core.fcis_m6_f06_reopen_authorization import (
    F06AuthorizationTokenV1,
    issue_f06_reopen_token,
)
from src.core.fcis_m6_j06_quiescence import (
    J06_QUIESCENCE_MARKERS_V1,
    J06_REQUIRED_WRITER_IDS_V1,
    J06QuiescenceGateV1,
    _mint_gate_v1,
    is_verified_quiescence_gate_v1,
    quiescence_root_from_body_v1,
)
from src.core.fcis_m6_j07_authority_switch import (
    J07RejectCodeV1,
    J07StateKindV1,
    J07SwitchRejectV1,
    J07SwitchSuccessV1,
    J07WriterAcceptedV1,
    J07WriterRejectV1,
    _mint_writer_token_v1,
    authorize_writer_v1,
    switch_authority_v1,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_J07_AUTHORITY_SWITCH_V1.json"
J04_MANIFEST_PATH = ROOT / "docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json"
J06_CONFIG_PATH = ROOT / "config/deploy/fcis_m6_j06_quiescence_v1.json"
J07_CONFIG_PATH = ROOT / "config/deploy/fcis_m6_j07_authority_switch_v1.json"


def _root(label: str) -> str:
    return cast(str, dra.tagged_digest(f"j07/{label}"))


def _read_object(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if type(payload) is not dict:
        raise AssertionError(f"{path} is not an object")
    return cast(dict[str, Any], payload)


def build_switch_layout() -> F02DurableLayoutV1:
    atom = build_atom()
    writer = atom.writer_profile_root
    phases = (
        dra.MigrationPhaseV1.LEGACY,
        dra.MigrationPhaseV1.SHADOW_REPLAY,
        dra.MigrationPhaseV1.DUAL_CHECK,
        dra.MigrationPhaseV1.QUIESCED,
    )
    authority_rows = tuple(
        F02AuthorityEpochV1(
            epoch_index=index,
            phase=phase,
            authority_state_root="0x" + _root(f"authority-{index}"),
            allowed_writer_roots=() if phase is dra.MigrationPhaseV1.QUIESCED else (writer,),
            transition_root="0x" + _root(f"transition-{index}"),
        )
        for index, phase in enumerate(phases)
    )
    switched_atom = replace(
        atom,
        authority_epoch_index=2,
        authority_state_root=authority_rows[2].authority_state_root,
    )
    record = switched_atom.outbox[0]
    ack = F02AckRowV1(
        effect_id=record.effect_id,
        commit_id=switched_atom.commit_id,
        destination=record.destination,
        payload_root=record.payload_root,
        destination_receipt_root="0x" + _root("destination-receipt"),
        adapter_profile_root=record.adapter_profile_root,
        idempotency_root=record.idempotency_root,
        response_root=switched_atom.response_root,
    )
    history = F02AuthorizedHistoryV1(
        genesis_state_root=switched_atom.expected_pre_state_root,
        deployment_config_root=switched_atom.deployment_config_root,
        verifier_profile_root=switched_atom.verifier_profile_root,
        authority_epochs=authority_rows,
        atoms=(switched_atom,),
        acks=(ack,),
    )
    return encode_history(history)


def build_f06_token() -> tuple[object, object, F06AuthorizationTokenV1, AcceptingVerifier]:
    layout = build_switch_layout()
    reopened = reopen_layout(layout)
    if type(reopened) is not F03ReopenSuccessV1:
        raise AssertionError("F06 fixture did not reopen")
    genesis = build_genesis(layout)
    external_root = "0x" + _root("external-authorization")
    evidence = build_evidence(reopened, external_authorization_root=external_root)
    verifier = AcceptingVerifier()
    issued = issue_f06_reopen_token(
        reopened,
        genesis=genesis,
        external_authorization_root=external_root,
        evidence=evidence,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    if type(issued) is not F06AuthorizationTokenV1:
        raise AssertionError("F06 did not issue the canonical migration token")
    return reopened, genesis, issued, verifier


def build_gate(token: F06AuthorizationTokenV1) -> J06QuiescenceGateV1:
    manifest = _read_object(J04_MANIFEST_PATH)
    config = _read_object(J06_CONFIG_PATH)
    head = token.head
    head_root = head.head_root[2:]
    snapshot_root = head.snapshot_root[2:]
    authority_root = head.authority_state_root[2:]
    body: dict[str, object] = {
        "manifest_root": cast(str, manifest["manifest_root"]),
        "entrypoint_inventory_root": cast(str, config["expected_k01_entrypoint_inventory_root"]),
        "phase": dra.MigrationPhaseV1.QUIESCED.value,
        "activation_sequence": cast(int, config["activation_sequence"]),
        "authority_epoch_index": head.authority_epoch,
        "authority_state_root": authority_root,
        "legacy_profile_root": cast(str, config["expected_legacy_profile_root"]),
        "target_profile_root": cast(str, config["expected_target_profile_root"]),
        "current_head_root": head_root,
        "replay_head_root": head_root,
        "current_snapshot_root": snapshot_root,
        "replay_snapshot_root": snapshot_root,
        "replay_evidence_root": cast(str, config["expected_replay_evidence_root"]),
        "covered_writer_ids": list(J06_REQUIRED_WRITER_IDS_V1),
        "evidence_markers": list(J06_QUIESCENCE_MARKERS_V1),
    }
    return _mint_gate_v1(
        manifest_root=cast(str, body["manifest_root"]),
        entrypoint_inventory_root=cast(str, body["entrypoint_inventory_root"]),
        phase=dra.MigrationPhaseV1.QUIESCED,
        activation_sequence=cast(int, body["activation_sequence"]),
        authority_epoch_index=cast(int, body["authority_epoch_index"]),
        authority_state_root=cast(str, body["authority_state_root"]),
        legacy_profile_root=cast(str, body["legacy_profile_root"]),
        target_profile_root=cast(str, body["target_profile_root"]),
        current_head_root=head_root,
        replay_head_root=head_root,
        current_snapshot_root=snapshot_root,
        replay_snapshot_root=snapshot_root,
        replay_evidence_root=cast(str, body["replay_evidence_root"]),
        covered_writer_ids=J06_REQUIRED_WRITER_IDS_V1,
        evidence_markers=J06_QUIESCENCE_MARKERS_V1,
        quiescence_root=quiescence_root_from_body_v1(body),
    )


def build_payload() -> dict[str, object]:
    reopened, genesis, migration_token, verifier = build_f06_token()
    gate = build_gate(migration_token)
    switched = switch_authority_v1(
        gate,
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    if type(switched) is not J07SwitchSuccessV1:
        raise AssertionError("J07 fixture did not switch")
    _check_config(switched)
    return {
        "schema": "zenodex/fcis/m6/j07/authority-switch-vector/v1",
        "profile_id": "research-unmounted-j07-authority-switch",
        "gate_root": switched.gate_root,
        "migration_token_root": switched.migration_token_root,
        "pre_context_root": switched.pre_context.context_root,
        "post_context_root": switched.post_context.context_root,
        "switch_root": switched.switch_root,
        "pre_phase": switched.pre_context.phase.value,
        "post_phase": switched.post_context.phase.value,
        "pre_epoch_index": switched.pre_context.epoch_index,
        "post_epoch_index": switched.post_context.epoch_index,
        "pre_authority_state_root": switched.pre_context.authority_state_root,
        "post_authority_state_root": switched.post_context.authority_state_root,
        "pre_head_root": switched.pre_context.current_head_root,
        "post_head_root": switched.post_context.current_head_root,
        "pre_snapshot_root": switched.pre_context.current_snapshot_root,
        "post_snapshot_root": switched.post_context.current_snapshot_root,
        "post_active_profile_root": switched.post_context.active_profile_root,
        "post_allowed_writer_roots": list(switched.post_context.allowed_writer_roots),
        "migration_verifier_calls": verifier.calls,
    }


def _assert_reject(value: object, code: J07RejectCodeV1, message: str) -> None:
    if type(value) is not J07SwitchRejectV1:
        raise AssertionError(message)
    reject = value
    if reject.code is not code:
        raise AssertionError(f"{message}: got {reject.code.value}")


def _check_config(switched: J07SwitchSuccessV1) -> None:
    config = _read_object(J07_CONFIG_PATH)
    if config["expected_pre_phase"] != switched.pre_context.phase.value:
        raise AssertionError("J07 config pre-phase does not match the switch")
    if config["expected_post_phase"] != switched.post_context.phase.value:
        raise AssertionError("J07 config post-phase does not match the switch")
    if config["expected_epoch_delta"] != (
        switched.post_context.epoch_index - switched.pre_context.epoch_index
    ):
        raise AssertionError("J07 config epoch delta does not match the switch")
    if config["expected_post_active_profile_root"] != switched.post_context.active_profile_root:
        raise AssertionError("J07 config active profile does not match the switch")
    if config["expected_post_allowed_writer_roots"] != list(
        switched.post_context.allowed_writer_roots
    ):
        raise AssertionError("J07 config writer set does not match the switch")
    if config["pinned_switch_root"] != switched.switch_root:
        raise AssertionError("J07 config switch root is stale")
    required = config["required_switch_fields"]
    if type(required) is not list or set(required) - set(switched.to_wire()):
        raise AssertionError("J07 config omits a switch field")


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    reopened, genesis, migration_token, verifier = build_f06_token()
    gate = build_gate(migration_token)
    if not is_verified_quiescence_gate_v1(gate):
        raise AssertionError("J07 fixture gate lacks J06 verifier provenance")
    switched = switch_authority_v1(
        gate,
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    if type(switched) is not J07SwitchSuccessV1:
        raise AssertionError("J07 rejected the canonical switch")
    _check_config(switched)
    pre = switched.pre_context
    post = switched.post_context
    if pre.kind is not J07StateKindV1.PRE_QUIESCED:
        raise AssertionError("J07 pre context has the wrong kind")
    if post.kind is not J07StateKindV1.POST_AUTHORITY_SWITCH:
        raise AssertionError("J07 post context has the wrong kind")
    if post.epoch_index != pre.epoch_index + 1:
        raise AssertionError("J07 did not advance the authority epoch exactly once")
    if post.active_profile_root != gate.target_profile_root:
        raise AssertionError("J07 did not activate the target profile")
    if post.allowed_writer_roots != (gate.target_profile_root,):
        raise AssertionError("J07 post switch writer set is not target-only")
    if pre.current_state_root != post.current_state_root:
        raise AssertionError("J07 changed the state root outside the switch atom")
    if pre.deployment_config_root != post.deployment_config_root:
        raise AssertionError("J07 changed deployment configuration unexpectedly")
    if len({pre.authority_state_root, post.authority_state_root}) != 2:
        raise AssertionError("J07 authority root did not change")
    if len({pre.current_head_root, post.current_head_root}) != 2:
        raise AssertionError("J07 head root did not change")
    if len({pre.current_snapshot_root, post.current_snapshot_root}) != 2:
        raise AssertionError("J07 snapshot root did not change")
    if verifier.calls != 2:
        raise AssertionError("J07 did not perform the F06 issue and use checks")

    legacy_token = _mint_writer_token_v1(pre, gate.legacy_profile_root)
    stale = authorize_writer_v1(post, legacy_token)
    if type(stale) is not J07WriterRejectV1:
        raise AssertionError("J07 stale-token result is not typed")
    if stale.code is not J07RejectCodeV1.STALE_TOKEN:
        raise AssertionError("old legacy token was not rejected after switch")
    target_token = _mint_writer_token_v1(post, gate.target_profile_root)
    accepted = authorize_writer_v1(post, target_token)
    if type(accepted) is not J07WriterAcceptedV1:
        raise AssertionError("fresh target token was not accepted after switch")
    if accepted.writer_profile_root != gate.target_profile_root:
        raise AssertionError("accepted writer is not the target profile")

    disabled_before = authorize_writer_v1(pre, legacy_token)
    if type(disabled_before) is not J07WriterRejectV1:
        raise AssertionError("quiesced writer result is not typed")
    if disabled_before.code is not J07RejectCodeV1.WRITER_PROFILE_DISABLED:
        raise AssertionError("quiesced pre-state admitted the legacy writer")

    forged_gate = object.__new__(J06QuiescenceGateV1)
    for name in (
        "manifest_root",
        "entrypoint_inventory_root",
        "phase",
        "activation_sequence",
        "authority_epoch_index",
        "authority_state_root",
        "legacy_profile_root",
        "target_profile_root",
        "current_head_root",
        "replay_head_root",
        "current_snapshot_root",
        "replay_snapshot_root",
        "replay_evidence_root",
        "covered_writer_ids",
        "evidence_markers",
        "quiescence_root",
    ):
        object.__setattr__(forged_gate, name, getattr(gate, name))
    _assert_reject(
        switch_authority_v1(
            forged_gate,
            reopened,
            genesis=genesis,
            migration_token=migration_token,
            verifier_adapter=verifier,
            current_epoch=3,
        ),
        J07RejectCodeV1.GATE_REJECTED,
        "J07 accepted an exact-class forged J06 gate",
    )

    forged_token = object.__new__(type(migration_token))
    object.__setattr__(forged_token, "head", migration_token.head)
    object.__setattr__(forged_token, "evidence", migration_token.evidence)
    object.__setattr__(forged_token, "token_root", "0x" + "f" * 64)
    _assert_reject(
        switch_authority_v1(
            gate,
            reopened,
            genesis=genesis,
            migration_token=forged_token,
            verifier_adapter=verifier,
            current_epoch=3,
        ),
        J07RejectCodeV1.AUTHORIZATION_REJECTED,
        "J07 accepted a forged F06 migration token",
    )

    mutated_target = target_token
    object.__setattr__(mutated_target, "writer_profile_root", gate.legacy_profile_root)
    mutated_result = authorize_writer_v1(post, mutated_target)
    if type(mutated_result) is not J07WriterRejectV1:
        raise AssertionError("mutated writer result is not typed")
    if mutated_result.code is not J07RejectCodeV1.TOKEN_REJECTED:
        raise AssertionError("J07 accepted a mutated registered writer token")

    rejecting_verifier = RejectingVerifier()
    _assert_reject(
        switch_authority_v1(
            gate,
            reopened,
            genesis=genesis,
            migration_token=migration_token,
            verifier_adapter=rejecting_verifier,
            current_epoch=3,
        ),
        J07RejectCodeV1.AUTHORIZATION_REJECTED,
        "J07 accepted a rejecting external authority",
    )

    if check_vector:
        expected = _read_object(VECTOR_PATH)
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: J07 authority-switch vector is stale")
    return build_payload()


if __name__ == "__main__":
    result = run_checks()
    print("J07_AUTHORITY_SWITCH_MATCH", result["switch_root"])
