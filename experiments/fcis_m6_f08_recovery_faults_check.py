"""Independent PRE/POST fault checker and vector builder for F08."""

from __future__ import annotations

import copy
import json
from dataclasses import replace
from pathlib import Path
from typing import cast

from experiments.fcis_m6_f02_history_encoder_check import build_history
from experiments.fcis_m6_f03_reopen_check import build_layout
from experiments.fcis_m6_f04_fixed_point_check import build_mutation_payloads
from src.core.fcis_durable_retraction import (
    derive_destination_idempotency_root,
    derive_effect_id,
    tagged_digest,
)
from src.core.fcis_m6_e01_request_identity import E01CommandFamilyV1
from src.core.fcis_m6_e02_nonce_nullifier import nullifier_root_from_body_v1
from src.core.fcis_m6_f01_history_atom import (
    F01HistoryAtomV1,
    F01HistoryNullifierV1,
    F01HistoryOutboxRecordV1,
)
from src.core.fcis_m6_f02_history_encoder import encode_history, encode_layout_v1
from src.core.fcis_m6_f04_fixed_point import F04FixedPointCodeV1
from src.core.fcis_m6_f08_recovery_faults import (
    FCIS_M6_F08_RECOVERY_SCHEMA_V1,
    F08RecoveryCodeV1,
    F08RecoveryObservationV1,
    F08RecoveryOutcomeV1,
    F08RecoverySetupRejectV1,
    observe_f08_recovery,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F08_RECOVERY_FAULTS_V1.json"


def _root(label: str) -> str:
    return f"0x{tagged_digest(f'f08/{label}')}"


def _build_second_atom(first: F01HistoryAtomV1) -> F01HistoryAtomV1:
    deployment = first.deployment_config_root
    writer = first.writer_profile_root
    commit_id = _root("commit-2")
    payload = _root("payload-2")
    effect_id = derive_effect_id(
        commit_id=commit_id[2:],
        ordinal=0,
        destination="destination/f08-2",
        payload_root=payload[2:],
        writer_profile_root=writer[2:],
    )
    nullifier_body = {
        "deployment_config_root": deployment[2:],
        "sender_id": "alice/f08",
        "command_family": E01CommandFamilyV1.STATE_CHANGE.value,
        "nonce": 2,
    }
    nullifier = F01HistoryNullifierV1(
        deployment_config_root=deployment,
        sender_id="alice/f08",
        command_family=E01CommandFamilyV1.STATE_CHANGE,
        nonce=2,
        request_identity_root=_root("request-identity-2"),
        nullifier_root=f"0x{nullifier_root_from_body_v1(nullifier_body)}",
    )
    record = F01HistoryOutboxRecordV1(
        ordinal=0,
        effect_id=f"0x{effect_id}",
        destination="destination/f08-2",
        payload_root=payload,
        adapter_profile_root=_root("adapter-2"),
        idempotency_root=f"0x{derive_destination_idempotency_root(effect_id)}",
    )
    return F01HistoryAtomV1(
        sequence=2,
        commit_id=commit_id,
        command_root=_root("command-2"),
        expected_pre_state_root=first.post_state_root,
        post_state_root=_root("post-state-2"),
        deployment_config_root=deployment,
        verifier_profile_root=first.verifier_profile_root,
        writer_profile_root=writer,
        authority_epoch_index=first.authority_epoch_index,
        authority_state_root=first.authority_state_root,
        anf_root=_root("anf-2"),
        proof_context_requirement=first.proof_context_requirement,
        proof_context_root=_root("proof-context-2"),
        nullifier=nullifier,
        response_root=_root("response-2"),
        receipt_root=_root("receipt-2"),
        decision_root=_root("decision-2"),
        bundle_root=_root("bundle-2"),
        replay_root=_root("replay-2"),
        outbox=(record,),
    )


def build_pre_payload() -> bytes:
    return cast(bytes, encode_layout_v1(build_layout()))


def build_post_payload() -> bytes:
    base = build_history()
    second = _build_second_atom(base.atoms[0])
    post_history = replace(base, atoms=(base.atoms[0], second), acks=())
    return cast(bytes, encode_layout_v1(encode_history(post_history)))


def build_third_payload() -> bytes:
    third_history = replace(build_history(), atoms=(), acks=())
    return cast(bytes, encode_layout_v1(encode_history(third_history)))


def _rehash_layout_root(wire: dict[str, object]) -> None:
    value = wire["value"]
    if type(value) is not dict:
        raise AssertionError("F08 layout value is not an object")
    projection = dict(value)
    projection.pop("layout_root", None)
    value["layout_root"] = sha256_hex(
        domain_sep_bytes("zenodex/fcis/m6/f02/layout-root", version=1)
        + canonical_json_bytes(projection)
    )


def build_fault_payloads() -> dict[str, bytes]:
    faults = dict(build_mutation_payloads())
    pre_wire = cast(dict[str, object], json.loads(build_pre_payload().decode("utf-8")))
    header_wire = copy.deepcopy(pre_wire)
    header_value = cast(dict[str, object], header_wire["value"])
    header = cast(dict[str, object], header_value["header"])
    header["current_state_root"] = _root("corrupt-header-state")
    _rehash_layout_root(header_wire)
    faults["header:current_state_root"] = canonical_json_bytes(header_wire)
    selected_root = copy.deepcopy(pre_wire)
    selected_value = cast(dict[str, object], selected_root["value"])
    selected_value["layout_root"] = _root("corrupt-selected-root")
    faults["layout:selected_root"] = canonical_json_bytes(selected_root)
    faults["bytes:truncated"] = build_pre_payload()[:-1]
    faults["bytes:invalid_utf8"] = b"\xff"
    return faults


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    pre = build_pre_payload()
    post = build_post_payload()
    third = build_third_payload()
    if pre == post:
        raise AssertionError("F08 PRE and POST fixtures are not distinct")

    pre_result = observe_f08_recovery(pre, post, pre)
    post_result = observe_f08_recovery(pre, post, post)
    if type(pre_result) is not F08RecoveryObservationV1:
        raise AssertionError("F08 did not expose exact PRE")
    if type(post_result) is not F08RecoveryObservationV1:
        raise AssertionError("F08 did not expose exact POST")
    if pre_result.outcome is not F08RecoveryOutcomeV1.PRE:
        raise AssertionError("F08 PRE classifier returned the wrong outcome")
    if post_result.outcome is not F08RecoveryOutcomeV1.POST:
        raise AssertionError("F08 POST classifier returned the wrong outcome")
    for result in (pre_result, post_result):
        if result.can_accept_value_movement or not result.requires_fresh_authorization:
            raise AssertionError("F08 exposed movement authority after reopen")

    third_result = observe_f08_recovery(pre, post, third)
    if type(third_result) is not F08RecoveryObservationV1:
        raise AssertionError("F08 did not lock a valid third layout")
    if third_result.outcome is not F08RecoveryOutcomeV1.REJECTED_LOCKED:
        raise AssertionError("F08 accepted a third valid layout")

    rejected: dict[str, str] = {}
    for name, payload in build_fault_payloads().items():
        fault_result = observe_f08_recovery(pre, post, payload)
        if type(fault_result) is not F08RecoveryObservationV1:
            raise AssertionError(f"F08 produced a setup failure for observed fault: {name}")
        if fault_result.outcome is not F08RecoveryOutcomeV1.REJECTED_LOCKED:
            raise AssertionError(f"F08 accepted a corrupted layout: {name}")
        if fault_result.rejection_code is None:
            raise AssertionError(f"F08 omitted a typed rejection code: {name}")
        rejected[name] = fault_result.rejection_code.value

    wrong_observed = observe_f08_recovery(pre, post, object())
    if type(wrong_observed) is not F08RecoveryObservationV1:
        raise AssertionError("F08 did not lock an untyped observed payload")
    if wrong_observed.rejection_code is not F04FixedPointCodeV1.WRONG_EXACT_TYPE:
        raise AssertionError("F08 used the wrong wrong-type rejection code")
    rejected["observed:wrong_type"] = wrong_observed.rejection_code.value

    wrong_pre = observe_f08_recovery(object(), post, pre)
    if type(wrong_pre) is not F08RecoverySetupRejectV1:
        raise AssertionError("F08 accepted an untyped PRE reference")
    if wrong_pre.code is not F08RecoveryCodeV1.WRONG_EXACT_TYPE:
        raise AssertionError("F08 used the wrong setup rejection code")

    vector_payload: dict[str, object] = {
        "schema": FCIS_M6_F08_RECOVERY_SCHEMA_V1,
        "pre_layout_root": pre_result.observed_layout_root,
        "post_layout_root": post_result.observed_layout_root,
        "pre_outcome": pre_result.outcome.value,
        "post_outcome": post_result.outcome.value,
        "third_layout_outcome": third_result.outcome.value,
        "fault_count": len(rejected),
        "fault_rejection_codes": rejected,
        "all_faults_locked": True,
        "fresh_authorization_required": True,
        "value_movement_allowed": False,
        "setup_rejections_typed": True,
    }
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(vector_payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F08 recovery-fault vector is stale")
    return vector_payload


def main() -> None:
    result = run_checks()
    print("F08_RECOVERY_FAULT_CHECKS_PASS", result["fault_count"])


if __name__ == "__main__":
    main()
