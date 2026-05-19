from __future__ import annotations

import copy

import pytest

from src.integration.production_key_management_v0 import (
    DEFAULT_ACTION_POLICIES_V0,
    build_admission_receipt_v0,
    build_key_descriptor_v0,
    build_privileged_action_packet_v0,
    build_signature_envelope_v0,
    validate_admission_receipt_v0,
    validate_privileged_action_packet_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0


def _hash(tag: str) -> str:
    return hash_v0("production_key_management_test_hash_v0", {"tag": tag})


def _verifier(packet: dict, descriptor: dict, envelope: dict) -> bool:
    expected = f"fixture:{descriptor['key_id']}:{packet['packet_hash']}"
    return envelope["signature"] == expected


def _packet(action: str, *, epoch: int = 10, not_before_epoch: int = 5) -> dict:
    policy = DEFAULT_ACTION_POLICIES_V0[action]
    return build_privileged_action_packet_v0(
        environment="production",
        action=action,
        target_kind="test-target",
        target_hash=_hash(f"{action}:target"),
        policy_hash=str(policy["policy_hash"]),
        nonce=1,
        epoch=epoch,
        not_before_epoch=not_before_epoch,
        expires_at_epoch=20,
        payload_hash=_hash(f"{action}:payload"),
    )


def _keys_for(action: str, *, storage_class: str = "hardware", same_custodian: bool = False) -> list[dict]:
    policy = DEFAULT_ACTION_POLICIES_V0[action]
    keys = []
    for index in range(int(policy["threshold"])):
        keys.append(
            build_key_descriptor_v0(
                key_id=f"{action}-key-{index}",
                public_key=f"pub-{action}-{index}",
                role=str(policy["role"]),
                environment="production",
                status="active",
                storage_class=storage_class,
                custodian_id="same-custodian" if same_custodian else f"custodian-{index}",
                valid_from_epoch=0,
                valid_until_epoch=100,
                break_glass=(policy["role"] == "emergency"),
            )
        )
    return keys


def _signatures(packet: dict, keys: list[dict]) -> list[dict]:
    return [
        build_signature_envelope_v0(
            key_id=str(key["key_id"]),
            public_key=str(key["public_key"]),
            packet_hash=str(packet["packet_hash"]),
            signature_scheme="external-verifier-v0",
            signature=f"fixture:{key['key_id']}:{packet['packet_hash']}",
        )
        for key in keys
    ]


def _receipt(action: str, keys: list[dict] | None = None, packet: dict | None = None) -> dict:
    packet = packet or _packet(action)
    keys = keys or _keys_for(action)
    return build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        _signatures(packet, keys),
        transparency_log_hash=_hash(f"{action}:transparency"),
        signature_verifier=_verifier,
    )


@pytest.mark.parametrize("action", sorted(DEFAULT_ACTION_POLICIES_V0))
def test_every_default_action_policy_can_build_receipt(action: str) -> None:
    receipt = _receipt(action)

    assert receipt["ok"] is True
    assert receipt["status"] == "accepted"
    assert receipt["accepted_signature_count"] == DEFAULT_ACTION_POLICIES_V0[action]["threshold"]
    validate_admission_receipt_v0(receipt)


def test_admission_rejects_without_signature_verifier() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        _signatures(packet, keys),
        transparency_log_hash=_hash("transparency"),
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "missing_signature_verifier"


def test_rejects_policy_action_mismatch() -> None:
    packet = _packet("protocol_treasury_spend")
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0["dao_treasury_grant"],
        _keys_for("dao_treasury_grant"),
        _signatures(packet, _keys_for("dao_treasury_grant")),
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "policy_action_mismatch"


def test_rejects_policy_hash_mismatch() -> None:
    action = "protocol_treasury_spend"
    packet = copy.deepcopy(_packet(action))
    packet["policy_hash"] = _hash("wrong-policy")
    packet["packet_hash"] = hash_v0("production_privileged_action_packet_v0", {k: v for k, v in packet.items() if k != "packet_hash"})
    keys = _keys_for(action)
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        _signatures(packet, keys),
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "policy_hash_mismatch"


def test_rejects_packet_hash_tamper() -> None:
    packet = _packet("protocol_treasury_spend")
    packet["packet_hash"] = _hash("tampered")

    with pytest.raises(ValueError, match="hash mismatch"):
        validate_privileged_action_packet_v0(packet)


def test_rejects_duplicate_key_id() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    keys[1] = {**keys[1], "key_id": keys[0]["key_id"]}
    keys[1]["key_descriptor_hash"] = hash_v0(
        "production_key_descriptor_v0",
        {k: v for k, v in keys[1].items() if k != "key_descriptor_hash"},
    )
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        _signatures(packet, keys),
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "duplicate_key_id"


def test_rejects_duplicate_public_key() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    keys[1] = {**keys[1], "public_key": keys[0]["public_key"]}
    keys[1]["key_descriptor_hash"] = hash_v0(
        "production_key_descriptor_v0",
        {k: v for k, v in keys[1].items() if k != "key_descriptor_hash"},
    )
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        _signatures(packet, keys),
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "duplicate_public_key"


def test_rejects_duplicate_signature_envelope() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    signatures = _signatures(packet, keys)
    signatures[1] = signatures[0]
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        signatures,
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "duplicate_signature_envelope"


def test_rejects_signature_packet_hash_mismatch() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    signatures = _signatures(packet, keys)
    signatures[0] = {**signatures[0], "packet_hash": _hash("other-packet")}
    signatures[0]["signature_envelope_hash"] = hash_v0(
        "production_signature_envelope_v0",
        {k: v for k, v in signatures[0].items() if k != "signature_envelope_hash"},
    )
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        signatures,
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "signature_packet_hash_mismatch"


def test_rejects_wrong_role() -> None:
    action = "protocol_treasury_spend"
    keys = _keys_for(action)
    keys[0] = build_key_descriptor_v0(
        key_id="wrong-role",
        public_key="pub-wrong-role",
        role="oracle",
        environment="production",
        status="active",
        storage_class="hardware",
        custodian_id="custodian-x",
        valid_from_epoch=0,
        valid_until_epoch=100,
    )
    receipt = _receipt(action, keys=keys)

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "wrong_role"


def test_rejects_revoked_and_expired_keys() -> None:
    action = "protocol_treasury_spend"
    for status in ("revoked", "expired"):
        keys = _keys_for(action)
        keys[0] = {**keys[0], "status": status}
        keys[0]["key_descriptor_hash"] = hash_v0(
            "production_key_descriptor_v0",
            {k: v for k, v in keys[0].items() if k != "key_descriptor_hash"},
        )
        receipt = _receipt(action, keys=keys)
        assert receipt["ok"] is False
        assert receipt["reject_reason"] == "revoked_or_expired_key"


def test_rejects_testnet_key_for_production() -> None:
    action = "protocol_treasury_spend"
    keys = _keys_for(action)
    keys[0] = {**keys[0], "environment": "testnet"}
    keys[0]["key_descriptor_hash"] = hash_v0(
        "production_key_descriptor_v0",
        {k: v for k, v in keys[0].items() if k != "key_descriptor_hash"},
    )
    receipt = _receipt(action, keys=keys)

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "testnet_key_for_production"


def test_rejects_insufficient_threshold_and_same_custodian() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    too_few = keys[:1]
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        too_few,
        _signatures(packet, too_few),
        transparency_log_hash=_hash("transparency"),
        signature_verifier=_verifier,
    )
    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "threshold_not_met"

    same_custodian = _keys_for(action, same_custodian=True)
    receipt = _receipt(action, keys=same_custodian)
    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "distinct_custodian_threshold_not_met"


def test_rejects_software_when_non_software_custody_required_and_accepts_mpc() -> None:
    action = "protocol_treasury_spend"
    assert _receipt(action, keys=_keys_for(action, storage_class="software"))["reject_reason"] == (
        "non_software_custody_required"
    )
    assert _receipt(action, keys=_keys_for(action, storage_class="mpc"))["ok"] is True


def test_rejects_missing_timelock() -> None:
    action = "protocol_treasury_spend"
    receipt = _receipt(action, packet=_packet(action, epoch=3, not_before_epoch=5))

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "timelock_not_satisfied"


def test_rejects_break_glass_outside_emergency_pause() -> None:
    action = "protocol_treasury_spend"
    keys = [
        build_key_descriptor_v0(
            key_id=f"emergency-{index}",
            public_key=f"pub-emergency-{index}",
            role="emergency",
            environment="production",
            status="active",
            storage_class="hardware",
            custodian_id=f"custodian-{index}",
            valid_from_epoch=0,
            valid_until_epoch=100,
            break_glass=True,
        )
        for index in range(3)
    ]
    receipt = _receipt(action, keys=keys)

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "break_glass_scope_violation"


def test_rejects_missing_transparency_log_hash() -> None:
    action = "protocol_treasury_spend"
    packet = _packet(action)
    keys = _keys_for(action)
    receipt = build_admission_receipt_v0(
        packet,
        DEFAULT_ACTION_POLICIES_V0[action],
        keys,
        _signatures(packet, keys),
        transparency_log_hash=None,
        signature_verifier=_verifier,
    )

    assert receipt["ok"] is False
    assert receipt["reject_reason"] == "missing_transparency_log_hash"


def test_receipt_tampering_fails_closed() -> None:
    receipt = _receipt("protocol_treasury_spend")
    receipt["accepted_signature_count"] = 1

    with pytest.raises(ValueError, match="accepted_signature_count mismatch"):
        validate_admission_receipt_v0(receipt)

    receipt = _receipt("protocol_treasury_spend")
    receipt["receipt_hash"] = _hash("tampered-receipt")
    with pytest.raises(ValueError, match="receipt hash mismatch"):
        validate_admission_receipt_v0(receipt)
