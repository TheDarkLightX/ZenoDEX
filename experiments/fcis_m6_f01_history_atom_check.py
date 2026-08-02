"""Independent checker and canonical vector builder for F01."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from src.core.fcis_durable_retraction import (
    derive_destination_idempotency_root,
    derive_effect_id,
    tagged_digest,
)
from src.core.fcis_m6_e01_request_identity import E01CommandFamilyV1
from src.core.fcis_m6_e02_nonce_nullifier import nullifier_root_from_body_v1
from src.core.fcis_m6_f01_history_atom import (
    FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1,
    F01HistoryAtomCodeV1,
    F01HistoryAtomRejectV1,
    F01HistoryAtomV1,
    F01HistoryNullifierV1,
    F01HistoryOutboxRecordV1,
    F01ProofContextRequirementV1,
    decode_history_atom_v1,
    encode_history_atom_v1,
    history_atom_root_v1,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F01_HISTORY_ATOM_V1.json"


def _root(label: str) -> str:
    return f"0x{tagged_digest(f'f01/{label}')}"


def build_atom() -> F01HistoryAtomV1:
    deployment = _root("deployment")
    commit_id = _root("commit")
    writer = _root("writer")
    payload = _root("payload")
    effect_id = derive_effect_id(
        commit_id=commit_id[2:],
        ordinal=0,
        destination="destination/f01",
        payload_root=payload[2:],
        writer_profile_root=writer[2:],
    )
    nullifier_body = {
        "deployment_config_root": deployment[2:],
        "sender_id": "alice/f01",
        "command_family": E01CommandFamilyV1.STATE_CHANGE.value,
        "nonce": 1,
    }
    nullifier = F01HistoryNullifierV1(
        deployment_config_root=deployment,
        sender_id="alice/f01",
        command_family=E01CommandFamilyV1.STATE_CHANGE,
        nonce=1,
        request_identity_root=_root("request-identity"),
        nullifier_root=f"0x{nullifier_root_from_body_v1(nullifier_body)}",
    )
    outbox = F01HistoryOutboxRecordV1(
        ordinal=0,
        effect_id=f"0x{effect_id}",
        destination="destination/f01",
        payload_root=payload,
        adapter_profile_root=_root("adapter"),
        idempotency_root=f"0x{derive_destination_idempotency_root(effect_id)}",
    )
    return F01HistoryAtomV1(
        sequence=1,
        commit_id=commit_id,
        command_root=_root("command"),
        expected_pre_state_root=_root("pre-state"),
        post_state_root=_root("post-state"),
        deployment_config_root=deployment,
        verifier_profile_root=_root("verifier"),
        writer_profile_root=writer,
        authority_epoch_index=3,
        authority_state_root=_root("authority"),
        anf_root=_root("anf"),
        proof_context_requirement=F01ProofContextRequirementV1.REQUIRED,
        proof_context_root=_root("proof-context"),
        nullifier=nullifier,
        response_root=_root("response"),
        receipt_root=_root("receipt"),
        decision_root=_root("decision"),
        bundle_root=_root("bundle"),
        replay_root=_root("replay"),
        outbox=(outbox,),
    )


def _mutated_wire(atom: F01HistoryAtomV1, field: str, value: object) -> bytes:
    wire = json.loads(encode_history_atom_v1(atom).decode("utf-8"))
    cast(dict[str, object], cast(dict[str, object], wire)["value"])[field] = value
    return cast(bytes, canonical_json_bytes(wire))


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    atom = build_atom()
    encoded = encode_history_atom_v1(atom)
    decoded = decode_history_atom_v1(encoded)
    if type(decoded) is not F01HistoryAtomV1 or decoded != atom:
        raise AssertionError("F01 canonical round-trip failed")
    if history_atom_root_v1(atom) != atom.atom_root:
        raise AssertionError("F01 atom root is not stable")

    missing_anf = json.loads(encoded.decode("utf-8"))
    del cast(dict[str, object], cast(dict[str, object], missing_anf)["value"])["anf_root"]
    if decode_history_atom_v1(canonical_json_bytes(missing_anf)).__class__ is F01HistoryAtomV1:
        raise AssertionError("F01 accepted a missing ANF root")

    unknown = json.loads(encoded.decode("utf-8"))
    cast(dict[str, object], cast(dict[str, object], unknown)["value"])["foreign"] = 1
    if decode_history_atom_v1(canonical_json_bytes(unknown)).__class__ is F01HistoryAtomV1:
        raise AssertionError("F01 accepted an unknown atom field")

    crossed_nullifier = _mutated_wire(atom, "nullifier", {"schema": "foreign"})
    crossed_result = decode_history_atom_v1(crossed_nullifier)
    if type(crossed_result) is F01HistoryAtomV1:
        raise AssertionError("F01 accepted a crossed nullifier")

    crossed_effect = json.loads(encoded.decode("utf-8"))
    value = cast(dict[str, object], cast(dict[str, object], crossed_effect)["value"])
    outbox = cast(list[dict[str, object]], value["outbox"])
    outbox[0]["effect_id"] = _root("foreign-effect")
    if type(decode_history_atom_v1(canonical_json_bytes(crossed_effect))) is F01HistoryAtomV1:
        raise AssertionError("F01 accepted an effect crossed with its atom")

    noncanonical = encoded.replace(b'"schema":', b' "schema":', 1)
    noncanonical_result = decode_history_atom_v1(noncanonical)
    if type(noncanonical_result) is not F01HistoryAtomRejectV1:
        raise AssertionError("F01 accepted noncanonical bytes")
    if noncanonical_result.code is not F01HistoryAtomCodeV1.NONCANONICAL_BYTES:
        raise AssertionError("F01 used the wrong noncanonical rejection code")

    rejected_codes = {
        "missing_anf": cast(object, decode_history_atom_v1(canonical_json_bytes(missing_anf))),
        "unknown_field": cast(object, decode_history_atom_v1(canonical_json_bytes(unknown))),
        "crossed_nullifier": crossed_result,
        "crossed_effect": decode_history_atom_v1(canonical_json_bytes(crossed_effect)),
        "noncanonical": noncanonical_result,
    }
    if any(type(result) is F01HistoryAtomV1 for result in rejected_codes.values()):
        raise AssertionError("F01 mutation set did not reject every witness")
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F01 history-atom vector is stale")
    return build_payload()


def build_payload() -> dict[str, object]:
    atom = build_atom()
    return {
        "schema": FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1,
        "atom_root": atom.atom_root,
        "canonical_bytes_utf8": encode_history_atom_v1(atom).decode("utf-8"),
        "outbox_count": len(atom.outbox),
        "proof_context_requirement": atom.proof_context_requirement.value,
        "nullifier_root": atom.nullifier.nullifier_root,
        "field_count": 20,
    }


def main() -> None:
    result = run_checks()
    print("F01_HISTORY_ATOM_CHECKS_PASS", result["atom_root"])


if __name__ == "__main__":
    main()
