from __future__ import annotations

import json
from pathlib import Path

from src.integration.production_key_management_v0 import (
    DEFAULT_ACTION_POLICIES_V0,
    build_key_descriptor_v0,
    build_action_policy_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from tools.check_production_key_management_config import (
    CONFIG_SCHEMA_V0,
    config_content_hash_v0,
    main,
    validate_config,
)


ROOT = Path(__file__).resolve().parents[1]
POLICY_MODEL = json.loads((ROOT / "formal/property/production_key_management_v0.json").read_text(encoding="utf-8"))


def _hash(tag: str) -> str:
    return hash_v0("production_key_management_config_test_v0", {"tag": tag})


def _role_key(role: str, index: int, *, storage_class: str = "hardware", status: str = "active") -> dict:
    recovery_policy_hash = _hash(f"{role}:recovery") if storage_class == "mpc" else None
    return build_key_descriptor_v0(
        key_id=f"{role}-{index}",
        public_key=f"pub-{role}-{index}",
        role=role,
        environment="production",
        status=status,
        storage_class=storage_class,
        custodian_id=f"custodian-{role}-{index}",
        valid_from_epoch=0,
        valid_until_epoch=100,
        break_glass=(role == "emergency"),
        custody_model="mpc_tss" if storage_class == "mpc" else "hardware_wallet",
        recovery_policy_hash=recovery_policy_hash,
    )


def _config() -> dict:
    keys: list[dict] = []
    max_threshold_by_role: dict[str, int] = {}
    for policy in DEFAULT_ACTION_POLICIES_V0.values():
        role = str(policy["role"])
        max_threshold_by_role[role] = max(max_threshold_by_role.get(role, 0), int(policy["threshold"]))
    for role, threshold in sorted(max_threshold_by_role.items()):
        storage_class = "mpc" if role == "treasury" else "hardware"
        for index in range(threshold):
            keys.append(_role_key(role, index, storage_class=storage_class))
    config = {
        "schema": CONFIG_SCHEMA_V0,
        "environment": "production",
        "config_hash": "0x" + "00" * 32,
        "policies": {action: dict(policy) for action, policy in DEFAULT_ACTION_POLICIES_V0.items()},
        "keys": keys,
        "revoked_key_ids": [],
        "signer_rotations": [],
        "recovery_policies": {
            _hash("treasury:recovery"): {
                "schema": "zenodex.production_key_management.recovery_policy.v0",
                "custody_model": "mpc_tss",
                "threshold": 2,
                "participants_hash": _hash("participants"),
            }
        },
    }
    config["config_hash"] = config_content_hash_v0(config)
    return config


def _refresh_config_hash(config: dict) -> dict:
    config["config_hash"] = config_content_hash_v0(config)
    return config


def test_valid_config_passes() -> None:
    result = validate_config(_config(), policy_model=POLICY_MODEL)

    assert result["ok"] is True
    assert result["errors"] == []
    assert "protocol_treasury_spend" in result["actions"]


def test_cli_accepts_valid_config(tmp_path: Path, capsys) -> None:
    config_path = tmp_path / "pkm_config.json"
    config_path.write_text(json.dumps(_config(), indent=2, sort_keys=True), encoding="utf-8")

    assert main(["--config", str(config_path), "--policy-model", str(ROOT / "formal/property/production_key_management_v0.json")]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["ok"] is True


def test_rejects_threshold_weakening() -> None:
    config = _config()
    policy = dict(config["policies"]["protocol_treasury_spend"])
    config["policies"]["protocol_treasury_spend"] = build_action_policy_v0(
        action="protocol_treasury_spend",
        role=str(policy["role"]),
        critical=bool(policy["critical"]),
        threshold=2,
        min_distinct_custodians=2,
        hardware_required=bool(policy["hardware_required"]),
        timelock_required=bool(policy["timelock_required"]),
        break_glass_allowed=bool(policy["break_glass_allowed"]),
        transparency_required=bool(policy["transparency_required"]),
    )
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("weakens threshold" in error for error in result["errors"])


def test_rejects_duplicate_custodian_quorum() -> None:
    config = _config()
    for key in config["keys"]:
        if key["role"] == "treasury":
            key["custodian_id"] = "same-custodian"
            key["key_descriptor_hash"] = hash_v0(
                "production_key_descriptor_v0",
                {k: v for k, v in key.items() if k != "key_descriptor_hash"},
            )
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("insufficient active production custodians" in error for error in result["errors"])


def test_rejects_revoked_active_key() -> None:
    config = _config()
    config["revoked_key_ids"] = ["treasury-0"]
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("revoked key cannot be active" in error for error in result["errors"])


def test_rejects_testnet_production_quorum_gap() -> None:
    config = _config()
    for key in config["keys"]:
        if key["role"] == "treasury":
            key["environment"] = "testnet"
            key["key_descriptor_hash"] = hash_v0(
                "production_key_descriptor_v0",
                {k: v for k, v in key.items() if k != "key_descriptor_hash"},
            )
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("insufficient active production keys" in error for error in result["errors"])


def test_rejects_break_glass_spend_policy_expansion() -> None:
    config = _config()
    policy = dict(config["policies"]["protocol_treasury_spend"])
    policy["break_glass_allowed"] = True
    policy["policy_hash"] = hash_v0(
        "production_action_policy_v0",
        {k: v for k, v in policy.items() if k != "policy_hash"},
    )
    config["policies"]["protocol_treasury_spend"] = policy
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("break_glass" in error for error in result["errors"])


def test_rejects_mpc_without_recovery_policy_hash() -> None:
    config = _config()
    key = config["keys"][0]
    key["storage_class"] = "mpc"
    key["recovery_policy_hash"] = None
    key["key_descriptor_hash"] = hash_v0(
        "production_key_descriptor_v0",
        {k: v for k, v in key.items() if k != "key_descriptor_hash"},
    )
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("mpc key requires" in error for error in result["errors"])


def test_rejects_shamir_recovery_only_as_active_signer() -> None:
    config = _config()
    key = config["keys"][0]
    key["custody_model"] = "sss_recovery_only"
    key["key_descriptor_hash"] = hash_v0(
        "production_key_descriptor_v0",
        {k: v for k, v in key.items() if k != "key_descriptor_hash"},
    )
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("Shamir recovery-only key cannot be active signer" in error for error in result["errors"])


def test_rejects_rotation_that_breaks_future_quorum() -> None:
    config = _config()
    config["signer_rotations"] = [{"revoke_key_ids": ["treasury-0", "treasury-1"], "add_keys": []}]
    result = validate_config(_refresh_config_hash(config), policy_model=POLICY_MODEL)

    assert result["ok"] is False
    assert any("would break future quorum" in error for error in result["errors"])
