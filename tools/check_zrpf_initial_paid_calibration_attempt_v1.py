#!/usr/bin/env python3
"""Qualify one bounded H100 source-proof calibration attempt without a receipt."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Sequence

if __package__:
    from tools import zrpf_paid_run_prerequisites_v1 as shared
else:
    import zrpf_paid_run_prerequisites_v1 as shared  # type: ignore[no-redef]

SCHEMA = "zenodex/zrpf_initial_paid_calibration_attempt/v1"
QUALIFIED_STATUS = "qualified_to_attempt_one_bounded_h100_source_calibration"
UNKNOWN_STATUS = "UNKNOWN"
ATTEMPT_BUDGET_SCHEMA = "zenodex/zrpf_initial_paid_calibration_budget/v1"
ATTEMPT_BUDGET_STATUS = "fresh_integer_attempt_budget_without_completion_or_spend_authority"
SOURCE_STAGE_ID = "source_spot_proof"
SOURCE_STAGE_ORDINAL = 4
MAX_ATTEMPT_BUDGET_MICROUSD = 4_000_000
MAX_HARD_ATTEMPT_CAP_MILLISECONDS = 30 * 60 * 1_000
MIN_WORKER_ATTEMPT_MILLISECONDS = 1_000
MAX_INPUT_BYTES = 2 * 1024 * 1024
MAX_PRICE_VALIDITY_SECONDS = 3_600
MAX_U64 = (1 << 64) - 1
ZERO_SHA256 = "0" * 64
EXECUTION_PACKET_SCHEMA = "zenodex/zrpf_remote_reproof_execution_packet/v4"
EXECUTION_PACKET_STATUS = "exact_inputs_bound_without_execution_provenance"
EXECUTION_PACKET_ID_DOMAIN = b"zenodex/zrpf_remote_reproof_execution_packet_id/v4\0"

ATTEMPT_BUDGET_ID_DOMAIN = b"zenodex/zrpf-initial-paid-calibration-budget-id/v1\0"
QUALIFICATION_ID_DOMAIN = b"zenodex/zrpf-initial-paid-calibration-attempt-id/v1\0"

AUTHORITY_FIELDS = list(shared.AUTHORITY_FIELDS)
AUTHORITY_FALSE = dict(shared.AUTHORITY_FALSE)
PACKET_AUTHORITY_FIELDS = [
    "data_availability_authority",
    "ledger_authority",
    "production_authority",
    "release_authority",
    "settlement_authority",
]
PACKET_NON_CLAIMS = [
    "handoff_and_return_metadata_do_not_verify_any_proof",
    "task_capture_records_do_not_prove_historical_execution_provenance",
    "execution_packets_bind_inputs_but_do_not_prove_when_or_whether_a_command_ran",
    "execution_packets_do_not_authenticate_operator_authorization_or_freshness",
    "pre_packet_external_input_substitution_requires_initial_expected_digests_to_detect",
    "same_handoff_same_bytes_stale_replay_is_indistinguishable_without_an_external_anchor",
    "content_ids_do_not_protect_against_coherent_checker_catalog_or_policy_changes",
    "command_templates_do_not_implement_a_bounded_remote_worker_or_output_stager",
    "inherited_identity_planner_git_capture_is_post_hoc_bounded_and_not_lazy_fetch_hardened",
    "worker_reported_program_image_ids_require_separate_governed_recomputation",
    "prover_compute_profile_does_not_attest_accelerator_identity_or_performance",
    "prover_r0vm_expectation_does_not_establish_source_to_binary_provenance_or_gpu_use",
    "literal_ancestry_does_not_grant_release_authority",
    "no_data_availability_finality_ledger_settlement_release_or_production_authority",
]
NON_CLAIMS = [
    "the initial gate requires no prior proof receipt",
    "the initial gate makes no forecast or claim that the source proof completes",
    "the hard deadline is a cost ceiling and not a proof-latency estimate",
    "pre-gate pod setup and profile time are outside this checker and require an externally enforced pod TTL",
    "the trusted epoch and price require an authenticated external controller or provider record",
    "the external pod TTL owns process-launch stalls and total allocation billing",
    "Apple CPU proving remained unusably slow after 30-plus minutes and is disqualified for this lane",
    "the attempted proof must still verify under the exact governed program and journal",
    "the CUDA build attestation does not establish release authority",
    "the H100 preflight does not establish hardware attestation",
    "qualification grants no proof release settlement or production authority",
]

PACKET_FIELDS = {
    "schema",
    "status",
    "execution_packet_id",
    "handoff_id",
    "source_binding_id",
    "task_id",
    "stage_id",
    "ordinal",
    "worker_commit",
    "worker_tree",
    "proof_profile_id",
    "input_artifact_ids",
    "authority",
    "non_claims",
}
ATTEMPT_BUDGET_FIELDS = [
    "schema",
    "status",
    "attempt_budget_record_id",
    "execution_profile_sha256",
    "execution_profile_record_id",
    "cuda_build_attestation_id",
    "h100_preflight_id",
    "execution_packet_id",
    "handoff_id",
    "source_task_id",
    "stage_id",
    "proof_profile_id",
    "prover_compute_profile_id",
    "program",
    "r0vm",
    "gpu",
    "runtime_image_sha256",
    "execution_shape",
    "attempt_budget_microusd",
    "price_microusd_per_hour",
    "price_observed_at_epoch_seconds",
    "price_valid_until_epoch_seconds",
    "hard_attempt_cap_milliseconds",
    "authority",
]
INPUT_HASH_FIELDS = [
    "source_execution_profile",
    "cuda_r0vm_build_attestation",
    "h100_preflight",
    "source_spot_proof_execution_packet",
    "attempt_budget_and_price",
]
QUALIFICATION_FIELDS = [
    "schema",
    "status",
    "qualification_id",
    "qualified",
    "input_sha256",
    "handoff_id",
    "source_task_id",
    "execution_packet_id",
    "stage_id",
    "proof_profile_id",
    "prover_compute_profile_id",
    "program",
    "r0vm",
    "gpu",
    "execution_shape",
    "trusted_current_epoch_seconds",
    "attempt_budget_microusd",
    "price_microusd_per_hour",
    "paid_window_milliseconds",
    "hard_attempt_cap_milliseconds",
    "hard_attempt_deadline_milliseconds",
    "deadline_limiting_factor",
    "completion_forecast_status",
    "authority",
    "non_claims",
]
UNKNOWN_FIELDS = [
    "schema",
    "status",
    "qualified",
    "reason_code",
    "reason",
    "authority",
    "non_claims",
]


class AttemptQualificationError(ValueError):
    """Stable fail-closed initial-attempt rejection."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code


def check_qualification(
    execution_profile_path: Path,
    cuda_build_attestation_path: Path,
    h100_preflight_path: Path,
    source_execution_packet_path: Path,
    attempt_budget_and_price_path: Path,
    *,
    trusted_current_epoch_seconds: int,
) -> dict[str, object]:
    """Return one bounded attempt decision with no completion forecast."""

    current_epoch = _u64(trusted_current_epoch_seconds, "trusted current epoch seconds")
    try:
        prerequisites = shared.validate_prerequisites(
            execution_profile_path,
            cuda_build_attestation_path,
            h100_preflight_path,
            expected_stage=SOURCE_STAGE_ID,
            trusted_current_epoch_seconds=current_epoch,
        )
    except shared.PrerequisiteError as exc:
        raise AttemptQualificationError("prerequisite_invalid", str(exc)) from exc
    profile = prerequisites.profile
    build = prerequisites.build
    preflight = prerequisites.preflight
    packet = _load_execution_packet(source_execution_packet_path)
    budget = _load_record(attempt_budget_and_price_path, "attempt budget and price")

    _validate_packet(packet.document)
    shape = prerequisites.execution_shape
    _validate_budget(
        budget.document,
        profile,
        build.document,
        preflight.document,
        packet.document,
        shape,
        current_epoch,
    )
    _require_exact_bindings(
        profile.document,
        build.document,
        preflight.document,
        packet.document,
        budget.document,
        shape,
    )

    attempt_budget = _positive_u64(
        budget.document["attempt_budget_microusd"], "attempt budget microusd"
    )
    price = _positive_u64(budget.document["price_microusd_per_hour"], "price microusd per hour")
    paid_window = _checked_mul_u64(3_600_000, attempt_budget, "paid window numerator") // price
    hard_cap = _positive_u64(budget.document["hard_attempt_cap_milliseconds"], "hard attempt cap")
    deadline = min(paid_window, hard_cap)
    if deadline < MIN_WORKER_ATTEMPT_MILLISECONDS:
        raise AttemptQualificationError(
            "attempt_window_below_worker_minimum",
            "budget and price yield less than one governed worker second",
        )
    if paid_window < hard_cap:
        limiting_factor = "paid_window"
    elif hard_cap < paid_window:
        limiting_factor = "hard_cap"
    else:
        limiting_factor = "equal"

    input_hashes: dict[str, object] = {
        "source_execution_profile": profile.sha256,
        "cuda_r0vm_build_attestation": build.sha256,
        "h100_preflight": preflight.sha256,
        "source_spot_proof_execution_packet": packet.sha256,
        "attempt_budget_and_price": budget.sha256,
    }
    _ordered_fields(input_hashes, INPUT_HASH_FIELDS, "qualification input hashes")
    result: dict[str, object] = {
        "schema": SCHEMA,
        "status": QUALIFIED_STATUS,
        "qualification_id": ZERO_SHA256,
        "qualified": True,
        "input_sha256": input_hashes,
        "handoff_id": packet.document["handoff_id"],
        "source_task_id": packet.document["task_id"],
        "execution_packet_id": packet.document["execution_packet_id"],
        "stage_id": SOURCE_STAGE_ID,
        "proof_profile_id": profile.document["proof_profile_id"],
        "prover_compute_profile_id": profile.document["prover_compute_profile_id"],
        "program": copy.deepcopy(profile.document["program"]),
        "r0vm": copy.deepcopy(profile.document["r0vm"]),
        "gpu": copy.deepcopy(preflight.document["gpu"]),
        "execution_shape": copy.deepcopy(shape),
        "trusted_current_epoch_seconds": current_epoch,
        "attempt_budget_microusd": attempt_budget,
        "price_microusd_per_hour": price,
        "paid_window_milliseconds": paid_window,
        "hard_attempt_cap_milliseconds": hard_cap,
        "hard_attempt_deadline_milliseconds": deadline,
        "deadline_limiting_factor": limiting_factor,
        "completion_forecast_status": "not_available",
        "authority": dict(AUTHORITY_FALSE),
        "non_claims": list(NON_CLAIMS),
    }
    _ordered_fields(result, QUALIFICATION_FIELDS, "initial attempt qualification")
    result["qualification_id"] = _derive_id(result, "qualification_id", QUALIFICATION_ID_DOMAIN)
    return result


def evaluate_qualification(
    execution_profile_path: Path | None,
    cuda_build_attestation_path: Path | None,
    h100_preflight_path: Path | None,
    source_execution_packet_path: Path | None,
    attempt_budget_and_price_path: Path | None,
    *,
    trusted_current_epoch_seconds: int | None,
) -> dict[str, object]:
    """Return authority-false UNKNOWN for every bounded rejection."""

    try:
        paths = [
            _required_path(execution_profile_path, "source execution profile"),
            _required_path(cuda_build_attestation_path, "CUDA r0vm build attestation"),
            _required_path(h100_preflight_path, "H100 preflight"),
            _required_path(source_execution_packet_path, "source execution packet"),
            _required_path(attempt_budget_and_price_path, "attempt budget and price"),
        ]
        if trusted_current_epoch_seconds is None:
            raise AttemptQualificationError(
                "trusted_epoch_missing", "trusted current epoch seconds are required"
            )
        return check_qualification(
            paths[0],
            paths[1],
            paths[2],
            paths[3],
            paths[4],
            trusted_current_epoch_seconds=trusted_current_epoch_seconds,
        )
    except AttemptQualificationError as exc:
        return _unknown(exc.code, str(exc))


def canonical_bytes(value: object) -> bytes:
    return shared.canonical_bytes(value)


def derive_attempt_budget_record_id(document: dict[str, object]) -> str:
    return _derive_id(document, "attempt_budget_record_id", ATTEMPT_BUDGET_ID_DOMAIN)


def _validate_packet(document: dict[str, object]) -> None:
    if set(document) != PACKET_FIELDS:
        raise AttemptQualificationError(
            "execution_packet_invalid", "execution packet field inventory mismatch"
        )
    if (
        document["schema"] != EXECUTION_PACKET_SCHEMA
        or document["status"] != EXECUTION_PACKET_STATUS
        or document["stage_id"] != SOURCE_STAGE_ID
        or document["ordinal"] != SOURCE_STAGE_ORDINAL
        or document["proof_profile_id"] != shared.PROOF_PROFILE
    ):
        raise AttemptQualificationError(
            "execution_packet_invalid", "source execution packet policy mismatch"
        )
    for field in (
        "execution_packet_id",
        "handoff_id",
        "source_binding_id",
        "task_id",
    ):
        _sha256(document[field], f"execution packet {field}", nonzero=True)
    for field in ("worker_commit", "worker_tree"):
        _commit(document[field], f"execution packet {field}")
    inputs = document["input_artifact_ids"]
    if type(inputs) is not list or not 1 <= len(inputs) <= 64:
        raise AttemptQualificationError(
            "execution_packet_invalid", "execution packet input set is empty or oversized"
        )
    seen: set[str] = set()
    for ordinal, value in enumerate(inputs):
        artifact_id = _sha256(value, f"packet input artifact {ordinal}", nonzero=True)
        if artifact_id in seen:
            raise AttemptQualificationError(
                "execution_packet_invalid", "execution packet input IDs contain a duplicate"
            )
        seen.add(artifact_id)
    packet_authority = document["authority"]
    if (
        type(packet_authority) is not dict
        or set(packet_authority) != set(PACKET_AUTHORITY_FIELDS)
        or any(packet_authority[field] is not False for field in PACKET_AUTHORITY_FIELDS)
    ):
        raise AttemptQualificationError(
            "authority_promotion_rejected", "execution packet authority must remain false"
        )
    if document["non_claims"] != PACKET_NON_CLAIMS:
        raise AttemptQualificationError(
            "execution_packet_invalid", "execution packet non-claims mismatch"
        )
    if document["execution_packet_id"] != derive_execution_packet_id(document):
        raise AttemptQualificationError(
            "execution_packet_id_mismatch", "execution packet ID mismatch"
        )


def _validate_budget(
    document: dict[str, object],
    profile: shared.LoadedRecord,
    build: dict[str, object],
    preflight: dict[str, object],
    packet: dict[str, object],
    shape: dict[str, object],
    current_epoch: int,
) -> None:
    _ordered_fields(document, ATTEMPT_BUDGET_FIELDS, "attempt budget")
    if document["schema"] != ATTEMPT_BUDGET_SCHEMA or document["status"] != ATTEMPT_BUDGET_STATUS:
        raise AttemptQualificationError(
            "attempt_budget_invalid", "attempt budget schema or status mismatch"
        )
    expected = {
        "execution_profile_sha256": profile.sha256,
        "execution_profile_record_id": profile.document["profile_record_id"],
        "cuda_build_attestation_id": build["build_attestation_id"],
        "h100_preflight_id": preflight["h100_preflight_id"],
        "execution_packet_id": packet["execution_packet_id"],
        "handoff_id": packet["handoff_id"],
        "source_task_id": packet["task_id"],
        "stage_id": SOURCE_STAGE_ID,
        "proof_profile_id": profile.document["proof_profile_id"],
        "prover_compute_profile_id": profile.document["prover_compute_profile_id"],
        "program": profile.document["program"],
        "r0vm": profile.document["r0vm"],
        "gpu": preflight["gpu"],
        "runtime_image_sha256": preflight["runtime_image_sha256"],
        "execution_shape": shape,
    }
    for field, value in expected.items():
        if document[field] != value:
            raise AttemptQualificationError(
                "attempt_binding_mismatch", f"attempt budget {field} binding mismatch"
            )
    attempt_budget = _positive_u64(document["attempt_budget_microusd"], "attempt budget microusd")
    _checked_mul_u64(3_600_000, attempt_budget, "paid window numerator")
    if attempt_budget > MAX_ATTEMPT_BUDGET_MICROUSD:
        raise AttemptQualificationError(
            "attempt_budget_exceeds_cap", "attempt budget exceeds four-dollar cap"
        )
    _positive_u64(document["price_microusd_per_hour"], "price microusd per hour")
    observed = _u64(document["price_observed_at_epoch_seconds"], "price observed epoch")
    valid_until = _u64(document["price_valid_until_epoch_seconds"], "price valid-until epoch")
    if observed > current_epoch:
        raise AttemptQualificationError("price_from_future", "price observation is from the future")
    if current_epoch > valid_until:
        raise AttemptQualificationError("stale_price", "price record is stale")
    if valid_until < observed or valid_until - observed > MAX_PRICE_VALIDITY_SECONDS:
        raise AttemptQualificationError(
            "price_validity_invalid", "price validity interval exceeds bound"
        )
    hard_cap = _positive_u64(document["hard_attempt_cap_milliseconds"], "hard attempt cap")
    if hard_cap > MAX_HARD_ATTEMPT_CAP_MILLISECONDS:
        raise AttemptQualificationError(
            "hard_attempt_cap_exceeded", "hard attempt cap exceeds governed maximum"
        )
    _authority_false(document["authority"], "attempt budget authority")
    _sha256(document["attempt_budget_record_id"], "attempt budget record ID", nonzero=True)
    if document["attempt_budget_record_id"] != derive_attempt_budget_record_id(document):
        raise AttemptQualificationError(
            "attempt_budget_id_mismatch", "attempt budget record ID mismatch"
        )


def _require_exact_bindings(
    profile: dict[str, object],
    build: dict[str, object],
    preflight: dict[str, object],
    packet: dict[str, object],
    budget: dict[str, object],
    shape: dict[str, object],
) -> None:
    del packet, shape
    if build["output_r0vm"] != profile["r0vm"] or preflight["r0vm"] != profile["r0vm"]:
        raise AttemptQualificationError("r0vm_binding_mismatch", "r0vm identity substitution")
    if (
        profile["stage_id"] != SOURCE_STAGE_ID
        or profile["proof_profile_id"] != shared.PROOF_PROFILE
        or profile["prover_compute_profile_id"] != shared.CUDA_COMPUTE_PROFILE
        or budget["program"] != profile["program"]
        or budget["r0vm"] != profile["r0vm"]
    ):
        raise AttemptQualificationError(
            "attempt_binding_mismatch", "source program or proving profile substitution"
        )


def _load_record(path: Path, label: str) -> shared.LoadedRecord:
    try:
        return shared.load_canonical_record(path, label)
    except shared.PrerequisiteError as exc:
        raise AttemptQualificationError(exc.code, str(exc)) from exc


def _load_execution_packet(path: Path) -> shared.LoadedRecord:
    try:
        raw = shared.stable_read(path, "source execution packet", MAX_INPUT_BYTES)
        value = shared.strict_json(raw, "source execution packet")
    except shared.PrerequisiteError as exc:
        raise AttemptQualificationError(
            "execution_packet_invalid", f"source execution packet rejected: {exc}"
        ) from exc
    if _execution_packet_canonical_bytes(value) != raw:
        raise AttemptQualificationError(
            "execution_packet_invalid", "source execution packet JSON is not canonical"
        )
    return shared.LoadedRecord(raw=raw, sha256=hashlib.sha256(raw).hexdigest(), document=value)


def _derive_id(document: dict[str, object], field: str, domain: bytes) -> str:
    candidate = copy.deepcopy(document)
    if field not in candidate:
        raise AttemptQualificationError("record_id_field_missing", f"{field} is missing")
    candidate[field] = ZERO_SHA256
    payload = canonical_bytes(candidate)
    return hashlib.sha256(domain + len(payload).to_bytes(8, "big") + payload).hexdigest()


def _authority_false(value: object, label: str) -> None:
    if type(value) is not dict or list(value) != AUTHORITY_FIELDS:
        raise AttemptQualificationError(
            "authority_promotion_rejected", f"{label} field inventory mismatch"
        )
    if value != AUTHORITY_FALSE or any(
        type(value[field]) is not bool for field in AUTHORITY_FIELDS
    ):
        raise AttemptQualificationError(
            "authority_promotion_rejected", f"{label} must remain false"
        )


def _unknown(code: str, reason: str) -> dict[str, object]:
    result: dict[str, object] = {
        "schema": SCHEMA,
        "status": UNKNOWN_STATUS,
        "qualified": False,
        "reason_code": code,
        "reason": reason,
        "authority": dict(AUTHORITY_FALSE),
        "non_claims": list(NON_CLAIMS),
    }
    _ordered_fields(result, UNKNOWN_FIELDS, "UNKNOWN result")
    return result


def _required_path(value: Path | None, label: str) -> Path:
    if value is None:
        raise AttemptQualificationError("required_input_missing", f"{label} input is required")
    return value


def _ordered_fields(row: dict[str, object], fields: list[str], label: str) -> None:
    if list(row) != fields:
        raise AttemptQualificationError(
            "field_inventory_mismatch", f"{label} field order or inventory mismatch"
        )


def _sha256(value: object, label: str, *, nonzero: bool) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise AttemptQualificationError("digest_invalid", f"{label} is not lowercase SHA-256")
    if nonzero and value == ZERO_SHA256:
        raise AttemptQualificationError("digest_invalid", f"{label} is zero")
    return value


def _commit(value: object, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise AttemptQualificationError("commit_invalid", f"{label} is not lowercase Git SHA-1")
    return value


def _u64(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64:
        raise AttemptQualificationError("integer_out_of_range", f"{label} is outside u64")
    return value


def _positive_u64(value: object, label: str) -> int:
    result = _u64(value, label)
    if result == 0:
        code = "zero_price" if label == "price microusd per hour" else "integer_out_of_range"
        raise AttemptQualificationError(code, f"{label} must be positive")
    return result


def _checked_mul_u64(left: int, right: int, label: str) -> int:
    if left != 0 and right > MAX_U64 // left:
        raise AttemptQualificationError("arithmetic_overflow", f"{label} overflows u64")
    return left * right


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-execution-profile", type=Path)
    parser.add_argument("--cuda-r0vm-build-attestation", type=Path)
    parser.add_argument("--h100-preflight", type=Path)
    parser.add_argument("--source-execution-packet", type=Path)
    parser.add_argument("--attempt-budget-and-price", type=Path)
    parser.add_argument("--trusted-current-epoch-seconds", type=int)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    result = evaluate_qualification(
        args.source_execution_profile,
        args.cuda_r0vm_build_attestation,
        args.h100_preflight,
        args.source_execution_packet,
        args.attempt_budget_and_price,
        trusted_current_epoch_seconds=args.trusted_current_epoch_seconds,
    )
    sys.stdout.write(json.dumps(result, ensure_ascii=False, separators=(",", ":")) + "\n")
    return 0 if result["qualified"] is True else 1


def derive_execution_packet_id(document: dict[str, object]) -> str:
    candidate = copy.deepcopy(document)
    candidate["execution_packet_id"] = ZERO_SHA256
    return hashlib.sha256(
        EXECUTION_PACKET_ID_DOMAIN + _execution_packet_canonical_bytes(candidate)
    ).hexdigest()


def _execution_packet_canonical_bytes(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")


if __name__ == "__main__":
    raise SystemExit(main())
