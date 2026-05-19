from __future__ import annotations

import pytest

from src.integration.zeno_ledger_v0 import build_header_v0, hash_v0
from src.integration.zeno_ledger_validator_schedule_v0 import (
    FORK_CHOICE_POLICY_V0,
    build_fork_choice_report_v0,
    build_proposer_duty_v0,
    build_scheduled_header_admission_v0,
    build_validator_set_v0,
    validate_fork_choice_report_v0,
    validate_proposer_duty_v0,
    validate_scheduled_header_admission_v0,
    validate_validator_set_v0,
)


ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _pubkey(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 48


def _validators() -> list[dict[str, object]]:
    return [
        {
            "validator_id": "validator-b",
            "key_id": "key-b",
            "public_key": _pubkey(2),
            "voting_power": 1,
            "status": "active",
        },
        {
            "validator_id": "validator-a",
            "key_id": "key-a",
            "public_key": _pubkey(1),
            "voting_power": 2,
            "status": "active",
        },
        {
            "validator_id": "validator-c",
            "key_id": "key-c",
            "public_key": _pubkey(3),
            "voting_power": 99,
            "status": "revoked",
        },
    ]


def _validator_set() -> dict[str, object]:
    return build_validator_set_v0(
        chain_id="zeno-ledger-schedule-testnet-0",
        epoch=0,
        start_height=1,
        validators=_validators(),
    )


def _header(*, height: int, sequencer_set_hash: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-schedule-testnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=_root(f"ingress-{height}"),
        tx_root=_root(f"tx-{height}"),
        pre_state_root=_root(f"pre-{height}"),
        post_state_root=_root(f"post-{height}"),
        app_hash=_root(f"app-{height}"),
        evidence_root=_root(f"evidence-{height}"),
        body_root=_root(f"body-{height}"),
        data_availability_root=_root(f"da-{height}"),
        proof_journal_hash=_root(f"proof-{height}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _tip(*, height: int, header_hash: str, validator_set_hash: str) -> dict[str, object]:
    return {
        "chain_id": "zeno-ledger-schedule-testnet-0",
        "height": height,
        "header_hash": header_hash,
        "validator_set_hash": validator_set_hash,
    }


def test_validator_set_is_canonical_and_hash_bound() -> None:
    validator_set = _validator_set()

    assert validator_set["active_slot_count"] == 3
    assert [entry["validator_id"] for entry in validator_set["validators"]] == [
        "validator-a",
        "validator-b",
        "validator-c",
    ]
    validate_validator_set_v0(validator_set)

    tampered = dict(validator_set)
    tampered["start_height"] = 2
    with pytest.raises(ValueError, match="binding mismatch"):
        validate_validator_set_v0(tampered)


def test_validator_set_rejects_duplicate_identity() -> None:
    validators = _validators()
    validators.append(dict(validators[0]))

    with pytest.raises(ValueError, match="duplicate validator_id/key_id"):
        build_validator_set_v0(
            chain_id="zeno-ledger-schedule-testnet-0",
            epoch=0,
            start_height=1,
            validators=validators,
        )


def test_weighted_round_robin_proposer_duties_are_deterministic() -> None:
    validator_set = _validator_set()

    duties = [build_proposer_duty_v0(validator_set=validator_set, height=height) for height in range(1, 7)]
    assert [(duty["proposer"]["validator_id"], duty["slot_index"], duty["cycle"]) for duty in duties] == [
        ("validator-a", 0, 0),
        ("validator-a", 1, 0),
        ("validator-b", 2, 0),
        ("validator-a", 0, 1),
        ("validator-a", 1, 1),
        ("validator-b", 2, 1),
    ]
    validate_proposer_duty_v0(duty=duties[0], validator_set=validator_set)

    tampered = dict(duties[0])
    tampered["slot_index"] = 2
    with pytest.raises(ValueError, match="proposer duty binding mismatch"):
        validate_proposer_duty_v0(duty=tampered, validator_set=validator_set)


def test_scheduled_header_admission_binds_proposer_and_validator_set_hash() -> None:
    validator_set = _validator_set()
    header = _header(height=3, sequencer_set_hash=str(validator_set["validator_set_hash"]))

    admission = build_scheduled_header_admission_v0(
        header=header,
        validator_set=validator_set,
        proposer_id="validator-b",
        key_id="key-b",
    )

    assert admission["ok"] is True
    assert admission["height"] == 3
    validate_scheduled_header_admission_v0(
        admission=admission,
        header=header,
        validator_set=validator_set,
    )


def test_scheduled_header_admission_rejects_wrong_proposer() -> None:
    validator_set = _validator_set()
    header = _header(height=3, sequencer_set_hash=str(validator_set["validator_set_hash"]))

    with pytest.raises(ValueError, match="scheduled duty"):
        build_scheduled_header_admission_v0(
            header=header,
            validator_set=validator_set,
            proposer_id="validator-a",
            key_id="key-a",
        )


def test_scheduled_header_admission_rejects_wrong_validator_set_hash() -> None:
    validator_set = _validator_set()
    header = _header(height=1, sequencer_set_hash=_root("other-validator-set"))

    with pytest.raises(ValueError, match="sequencer_set_hash"):
        build_scheduled_header_admission_v0(
            header=header,
            validator_set=validator_set,
            proposer_id="validator-a",
            key_id="key-a",
        )


def test_fork_choice_follows_candidate_that_extends_local_tip() -> None:
    validator_set_hash = str(_validator_set()["validator_set_hash"])
    local_header = _root("local-height-5")
    candidate_header = _root("candidate-height-8")

    report = build_fork_choice_report_v0(
        local_tip=_tip(height=5, header_hash=local_header, validator_set_hash=validator_set_hash),
        candidate_tip=_tip(height=8, header_hash=candidate_header, validator_set_hash=validator_set_hash),
        common_height=5,
        local_common_header_hash=local_header,
        candidate_common_header_hash=local_header,
    )

    assert report["policy"] == FORK_CHOICE_POLICY_V0
    assert report["decision"] == "follow_candidate"
    assert report["candidate_accepted"] is True
    validate_fork_choice_report_v0(report)


def test_fork_choice_keeps_local_when_candidate_is_known_prefix() -> None:
    validator_set_hash = str(_validator_set()["validator_set_hash"])
    candidate_header = _root("height-4")
    local_header = _root("height-6")

    report = build_fork_choice_report_v0(
        local_tip=_tip(height=6, header_hash=local_header, validator_set_hash=validator_set_hash),
        candidate_tip=_tip(height=4, header_hash=candidate_header, validator_set_hash=validator_set_hash),
        common_height=4,
        local_common_header_hash=candidate_header,
        candidate_common_header_hash=candidate_header,
    )

    assert report["decision"] == "keep_local"
    assert report["candidate_accepted"] is False
    validate_fork_choice_report_v0(report)


def test_fork_choice_rejects_candidate_that_requires_reorg() -> None:
    validator_set_hash = str(_validator_set()["validator_set_hash"])

    report = build_fork_choice_report_v0(
        local_tip=_tip(height=6, header_hash=_root("local-height-6"), validator_set_hash=validator_set_hash),
        candidate_tip=_tip(height=8, header_hash=_root("candidate-height-8"), validator_set_hash=validator_set_hash),
        common_height=4,
        local_common_header_hash=_root("height-4"),
        candidate_common_header_hash=_root("height-4"),
    )

    assert report["decision"] == "reject_candidate"
    assert report["reason"] == "candidate_does_not_extend_local_tip"
    assert report["candidate_accepted"] is False


def test_fork_choice_rejects_same_height_conflict() -> None:
    validator_set_hash = str(_validator_set()["validator_set_hash"])
    common_header = _root("height-6")

    report = build_fork_choice_report_v0(
        local_tip=_tip(height=7, header_hash=_root("local-height-7"), validator_set_hash=validator_set_hash),
        candidate_tip=_tip(height=7, header_hash=_root("candidate-height-7"), validator_set_hash=validator_set_hash),
        common_height=6,
        local_common_header_hash=common_header,
        candidate_common_header_hash=common_header,
    )

    assert report["decision"] == "reject_candidate"
    assert report["reason"] == "same_height_conflict"
    assert report["candidate_accepted"] is False


def test_fork_choice_rejects_common_prefix_mismatch() -> None:
    validator_set_hash = str(_validator_set()["validator_set_hash"])

    report = build_fork_choice_report_v0(
        local_tip=_tip(height=7, header_hash=_root("local-height-7"), validator_set_hash=validator_set_hash),
        candidate_tip=_tip(height=8, header_hash=_root("candidate-height-8"), validator_set_hash=validator_set_hash),
        common_height=7,
        local_common_header_hash=_root("local-height-7"),
        candidate_common_header_hash=_root("candidate-height-7"),
    )

    assert report["decision"] == "reject_candidate"
    assert report["reason"] == "common_prefix_mismatch"
    assert report["candidate_accepted"] is False


def test_fork_choice_rejects_validator_set_mismatch() -> None:
    report = build_fork_choice_report_v0(
        local_tip=_tip(height=5, header_hash=_root("same"), validator_set_hash=_root("set-a")),
        candidate_tip=_tip(height=6, header_hash=_root("new"), validator_set_hash=_root("set-b")),
        common_height=5,
        local_common_header_hash=_root("same"),
        candidate_common_header_hash=_root("same"),
    )

    assert report["decision"] == "reject_candidate"
    assert report["reason"] == "validator_set_mismatch"
