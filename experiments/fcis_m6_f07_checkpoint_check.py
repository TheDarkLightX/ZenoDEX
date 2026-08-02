"""Independent checker and deterministic vector builder for F07."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import cast

from experiments.fcis_m6_f02_history_encoder_check import build_history
from experiments.fcis_m6_f03_reopen_check import build_layout
from experiments.fcis_m6_f05_authenticated_genesis_check import build_pin
from experiments.fcis_m6_f06_reopen_authorization_check import build_genesis
from src.core.fcis_m6_f02_history_encoder import (
    encode_history,
    encode_layout_v1,
)
from src.core.fcis_m6_f04_fixed_point import (
    F04FixedPointSuccessV1,
    check_whole_layout_fixed_point,
)
from src.core.fcis_m6_f05_authenticated_genesis import (
    F05GenesisAcceptanceV1,
    authenticate_f05_genesis_v1,
)
from src.core.fcis_m6_f07_checkpoint import (
    FCIS_M6_F07_CHECKPOINT_SCHEMA_V1,
    F07CheckpointAcceptanceV1,
    F07CheckpointRejectV1,
    F07CheckpointV1,
    F07PendingOutboxV1,
    F07ProofKindV1,
    build_f07_checkpoint_v1,
    validate_f07_checkpoint_v1,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F07_CHECKPOINT_TRUNCATION_V1.json"


def build_source() -> F04FixedPointSuccessV1:
    layout = build_layout()
    result = check_whole_layout_fixed_point(encode_layout_v1(layout))
    if type(result) is not F04FixedPointSuccessV1:
        raise AssertionError("F04 fixture did not produce a fixed point")
    return result


def build_pending_source() -> F04FixedPointSuccessV1:
    history = replace(build_history(), acks=())
    layout = encode_history(history)
    result = check_whole_layout_fixed_point(encode_layout_v1(layout))
    if type(result) is not F04FixedPointSuccessV1:
        raise AssertionError("pending-ack F04 fixture did not produce a fixed point")
    return result


def build_genesis_acceptance(source: F04FixedPointSuccessV1) -> F05GenesisAcceptanceV1:
    genesis = build_genesis(source.layout)
    accepted = authenticate_f05_genesis_v1(genesis, build_pin(genesis))
    if type(accepted) is not F05GenesisAcceptanceV1:
        raise AssertionError("F05 fixture did not authenticate")
    return accepted


def recompute_checkpoint_with(
    checkpoint: F07CheckpointV1,
    **updates: object,
) -> F07CheckpointV1:
    """Construct a structurally valid changed certificate for adversarial checks."""

    values: dict[str, object] = {
        "checkpoint_sequence": checkpoint.checkpoint_sequence,
        "prior_layout_root": checkpoint.prior_layout_root,
        "prior_history_root": checkpoint.prior_history_root,
        "checkpoint_state_root": checkpoint.checkpoint_state_root,
        "deployment_config_root": checkpoint.deployment_config_root,
        "verifier_profile_root": checkpoint.verifier_profile_root,
        "genesis_admission_root": checkpoint.genesis_admission_root,
        "nullifier_accumulator_root": checkpoint.nullifier_accumulator_root,
        "authority_epoch_summary_root": checkpoint.authority_epoch_summary_root,
        "outbox_accumulator_root": checkpoint.outbox_accumulator_root,
        "pending_outbox": checkpoint.pending_outbox,
        "proof_kind": checkpoint.proof_kind,
        "proof_root": checkpoint.proof_root,
    }
    values.update(updates)
    if type(values["pending_outbox"]) is not tuple:
        raise AssertionError("test pending_outbox update must be an exact tuple")
    payload: dict[str, object] = {
        "schema": FCIS_M6_F07_CHECKPOINT_SCHEMA_V1,
        **values,
        "proof_kind": cast(F07ProofKindV1, values["proof_kind"]).value,
        "pending_outbox": [
            row.to_wire() for row in cast(tuple[F07PendingOutboxV1, ...], values["pending_outbox"])
        ],
    }
    root = sha256_hex(
        domain_sep_bytes("zenodex/fcis/m6/f07/checkpoint-genesis", version=1)
        + canonical_json_bytes(payload)
    )
    return F07CheckpointV1(
        checkpoint_sequence=cast(int, values["checkpoint_sequence"]),
        prior_layout_root=cast(str, values["prior_layout_root"]),
        prior_history_root=cast(str, values["prior_history_root"]),
        checkpoint_state_root=cast(str, values["checkpoint_state_root"]),
        deployment_config_root=cast(str, values["deployment_config_root"]),
        verifier_profile_root=cast(str, values["verifier_profile_root"]),
        genesis_admission_root=cast(str, values["genesis_admission_root"]),
        nullifier_accumulator_root=cast(str, values["nullifier_accumulator_root"]),
        authority_epoch_summary_root=cast(str, values["authority_epoch_summary_root"]),
        outbox_accumulator_root=cast(str, values["outbox_accumulator_root"]),
        pending_outbox=cast(
            tuple[F07PendingOutboxV1, ...],
            values["pending_outbox"],
        ),
        proof_kind=cast(F07ProofKindV1, values["proof_kind"]),
        proof_root=cast(str, values["proof_root"]),
        checkpoint_genesis_root=root,
    )


def mutate_checkpoint_without_revalidation(
    checkpoint: F07CheckpointV1,
    **updates: object,
) -> F07CheckpointV1:
    """Create an exact-class malformed witness for fail-closed tests."""

    mutated = object.__new__(F07CheckpointV1)
    for field_name in checkpoint.__dataclass_fields__:
        object.__setattr__(mutated, field_name, object.__getattribute__(checkpoint, field_name))
    for field_name, value in updates.items():
        object.__setattr__(mutated, field_name, value)
    return mutated


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    source = build_source()
    genesis = build_genesis_acceptance(source)
    built = build_f07_checkpoint_v1(source, genesis=genesis)
    if type(built) is not F07CheckpointAcceptanceV1:
        raise AssertionError("F07 rejected the canonical full-tip checkpoint")
    checked = validate_f07_checkpoint_v1(
        source,
        genesis=genesis,
        checkpoint=built.checkpoint,
    )
    if type(checked) is not F07CheckpointAcceptanceV1:
        raise AssertionError("F07 failed its source-bound revalidation")

    pending_source = build_pending_source()
    pending_genesis = build_genesis_acceptance(pending_source)
    pending = build_f07_checkpoint_v1(pending_source, genesis=pending_genesis)
    if type(pending) is not F07CheckpointAcceptanceV1:
        raise AssertionError("F07 dropped an unacknowledged outbox identity")
    if len(pending.checkpoint.pending_outbox) != 1:
        raise AssertionError("F07 pending outbox summary is incomplete")

    rejected: dict[str, str] = {}
    root_fields = (
        "prior_layout_root",
        "prior_history_root",
        "checkpoint_state_root",
        "deployment_config_root",
        "verifier_profile_root",
        "genesis_admission_root",
        "nullifier_accumulator_root",
        "authority_epoch_summary_root",
        "outbox_accumulator_root",
        "proof_root",
    )
    for field in root_fields:
        forged = recompute_checkpoint_with(built.checkpoint, **{field: "0x" + "e" * 64})
        result = validate_f07_checkpoint_v1(source, genesis=genesis, checkpoint=forged)
        if type(result) is not F07CheckpointRejectV1:
            raise AssertionError(f"F07 accepted a crossed {field}")
        rejected[field] = result.code.value

    omitted = recompute_checkpoint_with(built.checkpoint, pending_outbox=())
    omitted_result = validate_f07_checkpoint_v1(
        pending_source,
        genesis=pending_genesis,
        checkpoint=omitted,
    )
    if type(omitted_result) is not F07CheckpointRejectV1:
        raise AssertionError("F07 accepted an omitted pending outbox identity")
    rejected["pending_outbox:omitted"] = omitted_result.code.value

    unsupported = recompute_checkpoint_with(
        built.checkpoint,
        proof_kind=F07ProofKindV1.APPROVED_SNAPSHOT,
    )
    unsupported_result = validate_f07_checkpoint_v1(
        source,
        genesis=genesis,
        checkpoint=unsupported,
    )
    if type(unsupported_result) is not F07CheckpointRejectV1:
        raise AssertionError("F07 accepted an unverified snapshot proof mode")
    rejected["approved_snapshot_without_external_certificate"] = unsupported_result.code.value

    if type(build_f07_checkpoint_v1(object(), genesis=genesis)) is not F07CheckpointRejectV1:
        raise AssertionError("F07 accepted an untyped source")
    if type(build_f07_checkpoint_v1(source, genesis=object())) is not F07CheckpointRejectV1:
        raise AssertionError("F07 accepted an untyped genesis relation")

    payload = build_payload(built, pending, rejected)
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F07 checkpoint vector is stale")
    return payload


def build_payload(
    built: F07CheckpointAcceptanceV1,
    pending: F07CheckpointAcceptanceV1,
    rejected: dict[str, str],
) -> dict[str, object]:
    return {
        "schema": FCIS_M6_F07_CHECKPOINT_SCHEMA_V1,
        "checkpoint_genesis_root": built.checkpoint.checkpoint_genesis_root,
        "prior_layout_root": built.checkpoint.prior_layout_root,
        "prior_history_root": built.checkpoint.prior_history_root,
        "checkpoint_state_root": built.checkpoint.checkpoint_state_root,
        "nullifier_accumulator_root": built.checkpoint.nullifier_accumulator_root,
        "authority_epoch_summary_root": built.checkpoint.authority_epoch_summary_root,
        "outbox_accumulator_root": built.checkpoint.outbox_accumulator_root,
        "proof_root": built.checkpoint.proof_root,
        "compacted_snapshot_root": built.compacted_snapshot.snapshot_root,
        "removed_history_count": built.removed_history_count,
        "removed_nullifier_count": built.removed_nullifier_count,
        "removed_outbox_count": built.removed_outbox_count,
        "pending_outbox_count": len(pending.checkpoint.pending_outbox),
        "pending_effect_id": pending.checkpoint.pending_outbox[0].record.effect_id,
        "proof_kind": built.checkpoint.proof_kind.value,
        "rejection_codes": rejected,
        "all_rejections_typed": True,
        "partial_prefix_truncation": "rejected_by_v1_full_tip_policy",
        "approved_snapshot_mode": "reserved_until_external_certificate_adapter_exists",
    }


def main() -> None:
    result = run_checks()
    print("F07_CHECKPOINT_CHECKS_PASS", result["checkpoint_genesis_root"])


if __name__ == "__main__":
    main()
