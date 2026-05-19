#!/usr/bin/env python3
"""Bounded property checks for the production key-management specification."""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MODEL = ROOT / "formal/property/production_key_management_v0.json"
RESULT_SCHEMA = "zenodex.production_key_management.property_check.v1"


@dataclass(frozen=True)
class Key:
    key_id: str
    role: str
    environment: str
    status: str
    storage_class: str
    custodian_id: str
    break_glass: bool = False


def _load_model(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError("property model must be a JSON object")
    if obj.get("schema") != "zenodex.production_key_management.property_model.v0":
        raise ValueError("property model schema mismatch")
    return obj


def _active_key(role: str, index: int, *, storage_class: str = "hardware", environment: str = "production") -> Key:
    return Key(
        key_id=f"{role}-{index}",
        role=role,
        environment=environment,
        status="active",
        storage_class=storage_class,
        custodian_id=f"custodian-{index}",
        break_glass=(role == "emergency"),
    )


def _admit(
    *,
    action: str,
    policy: Mapping[str, Any],
    signers: Iterable[Key],
    environment: str,
    timelock_satisfied: bool,
    transparency_receipt_bound: bool,
) -> bool:
    signer_list = list(signers)
    if environment == "production" and any(key.environment != "production" for key in signer_list):
        return False
    if any(key.status != "active" for key in signer_list):
        return False
    role = str(policy["role"])
    role_signers = [key for key in signer_list if key.role == role]
    if len(role_signers) < int(policy["threshold"]):
        return False
    if len({key.custodian_id for key in role_signers}) < int(policy["min_distinct_custodians"]):
        return False
    if policy["hardware_required"] is True and any(key.storage_class not in {"hardware", "hsm", "mpc"} for key in role_signers):
        return False
    if policy["timelock_required"] is True and not timelock_satisfied:
        return False
    if policy["transparency_required"] is True and not transparency_receipt_bound:
        return False
    if any(key.break_glass for key in signer_list) and action != "emergency_pause":
        return False
    return True


def _case(name: str, ok: bool, detail: str = "") -> dict[str, Any]:
    return {"name": name, "ok": ok, "detail": detail}


def _valid_quorum(policy: Mapping[str, Any]) -> list[Key]:
    return [_active_key(str(policy["role"]), index) for index in range(int(policy["threshold"]))]


def run_check(model_path: Path = DEFAULT_MODEL) -> dict[str, Any]:
    model = _load_model(model_path)
    policies = model.get("action_policies")
    if not isinstance(policies, dict):
        raise ValueError("action_policies must be an object")
    cases: list[dict[str, Any]] = []
    for action, raw_policy in sorted(policies.items()):
        if not isinstance(raw_policy, dict):
            raise ValueError(f"{action} policy must be an object")
        policy = raw_policy
        valid = _valid_quorum(policy)
        accepted = _admit(
            action=action,
            policy=policy,
            signers=valid,
            environment="production",
            timelock_satisfied=True,
            transparency_receipt_bound=True,
        )
        cases.append(_case(f"{action}:valid_quorum_accepts", accepted))

        if policy["critical"] is True:
            single = [_active_key(str(policy["role"]), 0)]
            rejected_single = not _admit(
                action=action,
                policy=policy,
                signers=single,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            )
            cases.append(_case(f"{action}:single_key_rejected", rejected_single))

            duplicated_custodian = [
                Key(
                    key_id=f"{policy['role']}-dup-{index}",
                    role=str(policy["role"]),
                    environment="production",
                    status="active",
                    storage_class="hardware",
                    custodian_id="same-custodian",
                    break_glass=(policy["role"] == "emergency"),
                )
                for index in range(int(policy["threshold"]))
            ]
            rejected_same_custodian = not _admit(
                action=action,
                policy=policy,
                signers=duplicated_custodian,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            )
            cases.append(_case(f"{action}:same_custodian_quorum_rejected", rejected_same_custodian))

        revoked = [*valid]
        revoked[0] = Key(**{**revoked[0].__dict__, "status": "revoked"})
        cases.append(
            _case(
                f"{action}:revoked_key_rejected",
                not _admit(
                    action=action,
                    policy=policy,
                    signers=revoked,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
            )
        )

        expired = [*valid]
        expired[0] = Key(**{**expired[0].__dict__, "status": "expired"})
        cases.append(
            _case(
                f"{action}:expired_key_rejected",
                not _admit(
                    action=action,
                    policy=policy,
                    signers=expired,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
            )
        )

        testnet = [Key(**{**key.__dict__, "environment": "testnet"}) for key in valid]
        cases.append(
            _case(
                f"{action}:testnet_keys_rejected_for_production",
                not _admit(
                    action=action,
                    policy=policy,
                    signers=testnet,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
            )
        )

        wrong_role = [_active_key("oracle" if policy["role"] != "oracle" else "config", index) for index in range(int(policy["threshold"]))]
        cases.append(
            _case(
                f"{action}:wrong_role_rejected",
                not _admit(
                    action=action,
                    policy=policy,
                    signers=wrong_role,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
            )
        )

        if policy["hardware_required"] is True:
            mpc = [Key(**{**key.__dict__, "storage_class": "mpc"}) for key in valid]
            cases.append(
                _case(
                    f"{action}:mpc_keys_accept_as_non_software_custody",
                    _admit(
                        action=action,
                        policy=policy,
                        signers=mpc,
                        environment="production",
                        timelock_satisfied=True,
                        transparency_receipt_bound=True,
                    ),
                )
            )

            software = [Key(**{**key.__dict__, "storage_class": "software"}) for key in valid]
            cases.append(
                _case(
                    f"{action}:software_keys_rejected",
                    not _admit(
                        action=action,
                        policy=policy,
                        signers=software,
                        environment="production",
                        timelock_satisfied=True,
                        transparency_receipt_bound=True,
                    ),
                )
            )

        if policy["timelock_required"] is True:
            cases.append(
                _case(
                    f"{action}:missing_timelock_rejected",
                    not _admit(
                        action=action,
                        policy=policy,
                        signers=valid,
                        environment="production",
                        timelock_satisfied=False,
                        transparency_receipt_bound=True,
                    ),
                )
            )

        if policy["transparency_required"] is True:
            cases.append(
                _case(
                    f"{action}:missing_transparency_receipt_rejected",
                    not _admit(
                        action=action,
                        policy=policy,
                        signers=valid,
                        environment="production",
                        timelock_satisfied=True,
                        transparency_receipt_bound=False,
                    ),
                )
            )

        break_glass = [_active_key("emergency", index) for index in range(max(2, int(policy["threshold"])))]
        break_glass_ok = _admit(
            action=action,
            policy=policy,
            signers=break_glass,
            environment="production",
            timelock_satisfied=True,
            transparency_receipt_bound=True,
        )
        expected_break_glass = action == "emergency_pause"
        cases.append(_case(f"{action}:break_glass_scope", break_glass_ok is expected_break_glass))

    ok = all(case["ok"] is True for case in cases)
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "model_path": str(model_path),
        "case_count": len(cases),
        "cases": cases,
    }


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    model_path = Path(args[0]) if args else DEFAULT_MODEL
    result = run_check(model_path)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
