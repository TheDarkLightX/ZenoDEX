"""Deterministic validator scheduling and fork choice for ZenoLedger v0."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_v0 import canonical_header_hash_v0, hash_v0, validate_header_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

SCHEDULED_VALIDATOR_SET_SCHEMA_V1 = "zenodex/zeno_ledger/scheduled_validator_set/v1"
SCHEDULED_VALIDATOR_SET_HASH_DOMAIN_V1 = "scheduled_validator_set_v1"
SCHEDULED_VALIDATOR_ENTRY_HASH_DOMAIN_V1 = "scheduled_validator_set_entry_v1"
PROPOSER_DUTY_SCHEMA_V0 = "zenodex/zeno_ledger/proposer_duty/v0"
SCHEDULED_HEADER_ADMISSION_SCHEMA_V0 = "zenodex/zeno_ledger/scheduled_header_admission/v0"
FORK_CHOICE_REPORT_SCHEMA_V0 = "zenodex/zeno_ledger/fork_choice_report/v0"
SCHEDULE_MODE_V0 = "weighted_round_robin_v0"
FORK_CHOICE_POLICY_V0 = "extend_only_same_validator_set_v0"
MAX_VALIDATOR_POWER_V0 = 1024
MAX_ACTIVE_SLOT_COUNT_V0 = 4096
MAX_SCHEDULED_VALIDATORS_V1 = 256


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_sequence(value: object, *, name: str) -> Sequence[object]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_positive_int(value: object, *, name: str, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    out = int(value)
    if maximum is not None and out > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return out


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_bls_public_key(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _validator_body(
    *,
    validator_id: str,
    key_id: str,
    public_key: str,
    voting_power: int,
    status: str,
) -> dict[str, Any]:
    checked_status = _require_str(status, name="status")
    if checked_status not in {"active", "revoked"}:
        raise ValueError("validator status must be active or revoked")
    body = {
        "validator_id": _require_str(validator_id, name="validator_id"),
        "key_id": _require_str(key_id, name="key_id"),
        "public_key": _require_bls_public_key(public_key, name="public_key"),
        "voting_power": _require_positive_int(
            voting_power,
            name="voting_power",
            maximum=MAX_VALIDATOR_POWER_V0,
        ),
        "status": checked_status,
    }
    return {**body, "validator_hash": hash_v0(SCHEDULED_VALIDATOR_ENTRY_HASH_DOMAIN_V1, body)}


def _require_new_validator_identity_v1(
    entry: Mapping[str, Any],
    *,
    seen: tuple[set[str], set[str], set[str]],
) -> None:
    validator_ids, key_ids, public_keys = seen
    validator_id = str(entry["validator_id"])
    key_id = str(entry["key_id"])
    public_key = str(entry["public_key"])
    if validator_id in validator_ids:
        raise ValueError("duplicate validator_id")
    if key_id in key_ids:
        raise ValueError("duplicate validator key_id")
    if public_key in public_keys:
        raise ValueError("duplicate validator public_key")
    validator_ids.add(validator_id)
    key_ids.add(key_id)
    public_keys.add(public_key)


def _scheduled_validator_set_hash_v1(validator_set: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(validator_set).items() if key != "validator_set_hash"}
    return hash_v0(SCHEDULED_VALIDATOR_SET_HASH_DOMAIN_V1, body)


def build_validator_set_v0(
    *,
    chain_id: str,
    epoch: int,
    start_height: int,
    validators: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Build a canonical weighted round-robin validator set."""

    items = _require_sequence(validators, name="validators")
    if not items:
        raise ValueError("validator set requires at least one validator")
    if len(items) > MAX_SCHEDULED_VALIDATORS_V1:
        raise ValueError("scheduled validator set exceeds maximum validator count")

    entries: list[dict[str, Any]] = []
    seen_identities: tuple[set[str], set[str], set[str]] = (set(), set(), set())
    active_slot_count = 0
    for index, raw in enumerate(items):
        obj = _require_mapping(raw, name=f"validators[{index}]")
        entry = _validator_body(
            validator_id=_require_str(obj.get("validator_id"), name=f"validators[{index}].validator_id"),
            key_id=_require_str(obj.get("key_id"), name=f"validators[{index}].key_id"),
            public_key=_require_bls_public_key(obj.get("public_key"), name=f"validators[{index}].public_key"),
            voting_power=_require_positive_int(
                obj.get("voting_power", 1),
                name=f"validators[{index}].voting_power",
                maximum=MAX_VALIDATOR_POWER_V0,
            ),
            status=_require_str(obj.get("status", "active"), name=f"validators[{index}].status"),
        )
        _require_new_validator_identity_v1(entry, seen=seen_identities)
        if entry["status"] == "active":
            active_slot_count += int(entry["voting_power"])
        entries.append(entry)

    if active_slot_count <= 0:
        raise ValueError("validator set requires at least one active validator")
    if active_slot_count > MAX_ACTIVE_SLOT_COUNT_V0:
        raise ValueError("active validator schedule exceeds maximum slot count")

    entries.sort(key=lambda item: (str(item["validator_id"]), str(item["key_id"])))
    body = {
        "schema": SCHEDULED_VALIDATOR_SET_SCHEMA_V1,
        "chain_id": _require_str(chain_id, name="chain_id"),
        "epoch": _require_nonnegative_int(epoch, name="epoch"),
        "start_height": _require_nonnegative_int(start_height, name="start_height"),
        "schedule_mode": SCHEDULE_MODE_V0,
        "active_slot_count": active_slot_count,
        "validators": entries,
    }
    return {**body, "validator_set_hash": _scheduled_validator_set_hash_v1(body)}


def validate_validator_set_v0(validator_set: Mapping[str, Any]) -> None:
    obj = _require_mapping(validator_set, name="validator_set")
    if obj.get("schema") != SCHEDULED_VALIDATOR_SET_SCHEMA_V1:
        raise ValueError("validator set schema mismatch")
    if obj.get("schedule_mode") != SCHEDULE_MODE_V0:
        raise ValueError("validator set schedule_mode mismatch")
    validators = _require_sequence(obj.get("validators"), name="validator_set.validators")
    if len(validators) > MAX_SCHEDULED_VALIDATORS_V1:
        raise ValueError("scheduled validator set exceeds maximum validator count")
    expected = build_validator_set_v0(
        chain_id=_require_str(obj.get("chain_id"), name="validator_set.chain_id"),
        epoch=_require_nonnegative_int(obj.get("epoch"), name="validator_set.epoch"),
        start_height=_require_nonnegative_int(obj.get("start_height"), name="validator_set.start_height"),
        validators=[
            _require_mapping(item, name=f"validator_set.validators[{index}]")
            for index, item in enumerate(validators)
        ],
    )
    if dict(obj) != expected:
        raise ValueError("validator set binding mismatch")


def _active_schedule_slots_v0(validator_set: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    validate_validator_set_v0(validator_set)
    slots: list[Mapping[str, Any]] = []
    for entry in validator_set["validators"]:
        validator = _require_mapping(entry, name="validator_set.validator")
        if validator["status"] != "active":
            continue
        slots.extend([validator] * int(validator["voting_power"]))
    if not slots:
        raise ValueError("validator set has no active slots")
    return slots


def build_proposer_duty_v0(*, validator_set: Mapping[str, Any], height: int) -> dict[str, Any]:
    """Return the scheduled proposer for a height."""

    validate_validator_set_v0(validator_set)
    checked_height = _require_nonnegative_int(height, name="height")
    start_height = int(validator_set["start_height"])
    if checked_height < start_height:
        raise ValueError("height precedes validator set start_height")
    slots = _active_schedule_slots_v0(validator_set)
    offset = checked_height - start_height
    slot_index = offset % len(slots)
    cycle = offset // len(slots)
    proposer = slots[slot_index]
    body = {
        "schema": PROPOSER_DUTY_SCHEMA_V0,
        "chain_id": validator_set["chain_id"],
        "epoch": validator_set["epoch"],
        "height": checked_height,
        "validator_set_hash": validator_set["validator_set_hash"],
        "schedule_mode": SCHEDULE_MODE_V0,
        "slot_index": slot_index,
        "cycle": cycle,
        "proposer": {
            "validator_id": proposer["validator_id"],
            "key_id": proposer["key_id"],
            "public_key": proposer["public_key"],
            "validator_hash": proposer["validator_hash"],
        },
    }
    return {**body, "duty_hash": hash_v0("proposer_duty_v0", body)}


def validate_proposer_duty_v0(*, duty: Mapping[str, Any], validator_set: Mapping[str, Any]) -> None:
    obj = _require_mapping(duty, name="duty")
    if obj.get("schema") != PROPOSER_DUTY_SCHEMA_V0:
        raise ValueError("proposer duty schema mismatch")
    expected = build_proposer_duty_v0(
        validator_set=validator_set,
        height=_require_nonnegative_int(obj.get("height"), name="duty.height"),
    )
    if dict(obj) != expected:
        raise ValueError("proposer duty binding mismatch")


def build_scheduled_header_admission_v0(
    *,
    header: Mapping[str, Any],
    validator_set: Mapping[str, Any],
    proposer_id: str,
    key_id: str,
) -> dict[str, Any]:
    """Admit a header only when its sequencer set and proposer duty match."""

    header_obj = dict(_require_mapping(header, name="header"))
    validate_header_v0(header_obj)
    validate_validator_set_v0(validator_set)
    if header_obj["chain_id"] != validator_set["chain_id"]:
        raise ValueError("header chain_id does not match validator set")
    if header_obj["sequencer_set_hash"] != validator_set["validator_set_hash"]:
        raise ValueError("header sequencer_set_hash does not match validator set")
    duty = build_proposer_duty_v0(validator_set=validator_set, height=int(header_obj["height"]))
    proposer = _require_mapping(duty["proposer"], name="duty.proposer")
    if proposer["validator_id"] != proposer_id or proposer["key_id"] != key_id:
        raise ValueError("header proposer does not match scheduled duty")
    body = {
        "schema": SCHEDULED_HEADER_ADMISSION_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "chain_id": header_obj["chain_id"],
        "height": header_obj["height"],
        "header_hash": canonical_header_hash_v0(header_obj),
        "validator_set_hash": validator_set["validator_set_hash"],
        "duty_hash": duty["duty_hash"],
        "proposer_id": proposer_id,
        "key_id": key_id,
    }
    return {**body, "admission_hash": hash_v0("scheduled_header_admission_v0", body)}


def validate_scheduled_header_admission_v0(
    *,
    admission: Mapping[str, Any],
    header: Mapping[str, Any],
    validator_set: Mapping[str, Any],
) -> None:
    obj = _require_mapping(admission, name="admission")
    if obj.get("schema") != SCHEDULED_HEADER_ADMISSION_SCHEMA_V0:
        raise ValueError("scheduled header admission schema mismatch")
    expected = build_scheduled_header_admission_v0(
        header=header,
        validator_set=validator_set,
        proposer_id=_require_str(obj.get("proposer_id"), name="admission.proposer_id"),
        key_id=_require_str(obj.get("key_id"), name="admission.key_id"),
    )
    if dict(obj) != expected:
        raise ValueError("scheduled header admission binding mismatch")


def _tip_fields(tip: Mapping[str, Any], *, name: str) -> dict[str, Any]:
    obj = _require_mapping(tip, name=name)
    return {
        "chain_id": _require_str(obj.get("chain_id"), name=f"{name}.chain_id"),
        "height": _require_nonnegative_int(obj.get("height"), name=f"{name}.height"),
        "header_hash": _require_root(obj.get("header_hash"), name=f"{name}.header_hash"),
        "validator_set_hash": _require_root(obj.get("validator_set_hash"), name=f"{name}.validator_set_hash"),
    }


def build_fork_choice_report_v0(
    *,
    local_tip: Mapping[str, Any],
    candidate_tip: Mapping[str, Any],
    common_height: int,
    local_common_header_hash: str,
    candidate_common_header_hash: str,
) -> dict[str, Any]:
    """Apply extend-only fork choice over two already-verified tips."""

    local = _tip_fields(local_tip, name="local_tip")
    candidate = _tip_fields(candidate_tip, name="candidate_tip")
    checked_common_height = _require_nonnegative_int(common_height, name="common_height")
    local_common = _require_root(local_common_header_hash, name="local_common_header_hash")
    candidate_common = _require_root(candidate_common_header_hash, name="candidate_common_header_hash")
    decision = "reject_candidate"
    reason = "common_prefix_mismatch"
    candidate_accepted = False

    if local["chain_id"] != candidate["chain_id"]:
        reason = "chain_id_mismatch"
    elif local["validator_set_hash"] != candidate["validator_set_hash"]:
        reason = "validator_set_mismatch"
    elif checked_common_height > min(int(local["height"]), int(candidate["height"])):
        reason = "common_height_exceeds_tip"
    elif local_common != candidate_common:
        reason = "common_prefix_mismatch"
    elif int(candidate["height"]) > int(local["height"]):
        if checked_common_height == int(local["height"]) and local_common == local["header_hash"]:
            decision = "follow_candidate"
            reason = "candidate_extends_local_tip"
            candidate_accepted = True
        else:
            reason = "candidate_does_not_extend_local_tip"
    elif int(candidate["height"]) == int(local["height"]):
        if candidate["header_hash"] == local["header_hash"]:
            decision = "same_tip"
            reason = "same_height_same_header"
            candidate_accepted = True
        else:
            reason = "same_height_conflict"
    elif checked_common_height == int(candidate["height"]) and candidate_common == candidate["header_hash"]:
        decision = "keep_local"
        reason = "candidate_is_local_prefix"
    else:
        reason = "candidate_not_on_local_prefix"

    body = {
        "schema": FORK_CHOICE_REPORT_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "policy": FORK_CHOICE_POLICY_V0,
        "decision": decision,
        "reason": reason,
        "candidate_accepted": candidate_accepted,
        "local_tip": local,
        "candidate_tip": candidate,
        "common_height": checked_common_height,
        "local_common_header_hash": local_common,
        "candidate_common_header_hash": candidate_common,
    }
    return {**body, "fork_choice_hash": hash_v0("fork_choice_report_v0", body)}


def validate_fork_choice_report_v0(report: Mapping[str, Any]) -> None:
    obj = _require_mapping(report, name="report")
    if obj.get("schema") != FORK_CHOICE_REPORT_SCHEMA_V0:
        raise ValueError("fork choice report schema mismatch")
    expected = build_fork_choice_report_v0(
        local_tip=_require_mapping(obj.get("local_tip"), name="report.local_tip"),
        candidate_tip=_require_mapping(obj.get("candidate_tip"), name="report.candidate_tip"),
        common_height=_require_nonnegative_int(obj.get("common_height"), name="report.common_height"),
        local_common_header_hash=_require_root(
            obj.get("local_common_header_hash"),
            name="report.local_common_header_hash",
        ),
        candidate_common_header_hash=_require_root(
            obj.get("candidate_common_header_hash"),
            name="report.candidate_common_header_hash",
        ),
    )
    if dict(obj) != expected:
        raise ValueError("fork choice report binding mismatch")
