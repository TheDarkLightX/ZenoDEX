from tools.zeno_log_redaction import redact_for_log


def test_redact_for_log_masks_key_material_without_hiding_authority_fields() -> None:
    report = {
        "oracle_authority_profile": {"authority_id": "oracle-authority-v1"},
        "fixture_key_bundle": "/tmp/secret/keys.json",
        "operator_privkey": "0xdeadbeef",
        "submit_peer_auth_token": "token",
        "token_distribution": {"distribution_hash": "0xabc"},
    }

    redacted = redact_for_log(report)

    assert redacted["fixture_key_bundle"] == "[redacted]"
    assert redacted["operator_privkey"] == "[redacted]"
    assert redacted["submit_peer_auth_token"] == "[redacted]"
    assert redacted["oracle_authority_profile"] == {"authority_id": "oracle-authority-v1"}
    assert redacted["token_distribution"] == {"distribution_hash": "0xabc"}
