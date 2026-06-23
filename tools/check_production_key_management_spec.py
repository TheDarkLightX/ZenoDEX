#!/usr/bin/env python3
"""Bounded property checks for the production key-management specification."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MODEL = ROOT / "formal/property/production_key_management_v0.json"
RESULT_SCHEMA = "zenodex.production_key_management.property_check.v1"

PRIMARY_AXES = {
    "packet",
    "signature_binding",
    "role",
    "environment",
    "status",
    "quorum",
    "storage",
    "timelock",
    "break_glass",
    "transparency",
}

INVARIANT_AXIS = {
    "PKM-G-001": "environment",
    "PKM-G-002": "status",
    "PKM-G-003": "quorum",
    "PKM-G-004": "storage",
    "PKM-G-005": "timelock",
    "PKM-G-006": "break_glass",
    "PKM-G-007": "transparency",
}


@dataclass(frozen=True)
class Key:
    key_id: str
    role: str
    environment: str
    status: str
    storage_class: str
    custodian_id: str
    break_glass: bool = False


@dataclass(frozen=True)
class AdmissionDecision:
    accepted: bool
    reject_reason: str


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


def _admission_decision(
    *,
    action: str,
    policy: Mapping[str, Any],
    signers: Iterable[Key],
    environment: str,
    packet_ok: bool = True,
    signatures_bind: bool = True,
    timelock_satisfied: bool,
    transparency_receipt_bound: bool,
) -> AdmissionDecision:
    signer_list = list(signers)
    role = str(policy["role"])
    if not packet_ok:
        return AdmissionDecision(False, "packet_invalid")
    if not signatures_bind:
        return AdmissionDecision(False, "signature_binding_invalid")
    if environment == "production" and any(key.environment != "production" for key in signer_list):
        return AdmissionDecision(False, "testnet_key_for_production")
    if any(key.status != "active" for key in signer_list):
        return AdmissionDecision(False, "revoked_or_expired_key")
    role_signers = [key for key in signer_list if key.role == role]
    if len(role_signers) < int(policy["threshold"]):
        return AdmissionDecision(False, "threshold_not_met")
    if len({key.custodian_id for key in role_signers}) < int(policy["min_distinct_custodians"]):
        return AdmissionDecision(False, "distinct_custodian_quorum_not_met")
    if policy["hardware_required"] is True and any(
        key.storage_class not in {"hardware", "hsm", "mpc"} for key in role_signers
    ):
        return AdmissionDecision(False, "software_key_for_hardware_required_action")
    if policy["timelock_required"] is True and not timelock_satisfied:
        return AdmissionDecision(False, "timelock_required")
    if policy["transparency_required"] is True and not transparency_receipt_bound:
        return AdmissionDecision(False, "transparency_receipt_required")
    if any(key.break_glass for key in signer_list) and action != "emergency_pause":
        return AdmissionDecision(False, "break_glass_scope_violation")
    return AdmissionDecision(True, "")


def _valid_quorum(policy: Mapping[str, Any]) -> list[Key]:
    return [_active_key(str(policy["role"]), index) for index in range(int(policy["threshold"]))]


def _key_summary(keys: Iterable[Key]) -> list[dict[str, object]]:
    return [
        {
            "key_id": key.key_id,
            "role": key.role,
            "environment": key.environment,
            "status": key.status,
            "storage_class": key.storage_class,
            "custodian_id": key.custodian_id,
            "break_glass": key.break_glass,
        }
        for key in keys
    ]


def _policy_summary(policy: Mapping[str, Any]) -> dict[str, object]:
    return {
        "role": policy["role"],
        "critical": policy["critical"],
        "threshold": policy["threshold"],
        "min_distinct_custodians": policy["min_distinct_custodians"],
        "hardware_required": policy["hardware_required"],
        "timelock_required": policy["timelock_required"],
        "break_glass_allowed": policy["break_glass_allowed"],
        "transparency_required": policy["transparency_required"],
    }


def _case(
    *,
    name: str,
    action: str,
    policy: Mapping[str, Any],
    signers: Iterable[Key],
    decision: AdmissionDecision,
    expected_accept: bool,
    invariant_id: str,
    primary_axis: str,
    polarity: str,
    reject_reason: str = "",
) -> dict[str, Any]:
    if invariant_id not in INVARIANT_AXIS:
        raise ValueError(f"unknown invariant_id:{invariant_id}")
    if primary_axis not in PRIMARY_AXES:
        raise ValueError(f"unknown primary_axis:{primary_axis}")
    if polarity not in {"positive", "negative"}:
        raise ValueError(f"unknown polarity:{polarity}")
    if polarity == "negative" and not reject_reason:
        raise ValueError(f"{name}: negative cases require reject_reason")
    ok = decision.accepted is expected_accept
    return {
        "name": name,
        "ok": ok,
        "action": action,
        "expected_accept": expected_accept,
        "observed_accept": decision.accepted,
        "reject_reason": reject_reason if polarity == "negative" else "",
        "observed_reject_reason": decision.reject_reason,
        "invariant_ids": [invariant_id],
        "primary_axis": primary_axis,
        "polarity": polarity,
        "detail": "" if ok else f"expected_accept={expected_accept}, observed_accept={decision.accepted}",
        "counterexample": None
        if ok
        else {
            "action": action,
            "policy": _policy_summary(policy),
            "signers": _key_summary(signers),
            "failed_invariant_id": invariant_id,
            "primary_axis": primary_axis,
            "expected_reject_reason": reject_reason,
            "observed_reject_reason": decision.reject_reason,
        },
    }


def _accepted_case(action: str, policy: Mapping[str, Any], invariant_id: str) -> dict[str, Any]:
    signers = _valid_quorum(policy)
    decision = _admission_decision(
        action=action,
        policy=policy,
        signers=signers,
        environment="production",
        timelock_satisfied=True,
        transparency_receipt_bound=True,
    )
    return _case(
        name=f"{action}:{invariant_id}:valid_quorum_accepts",
        action=action,
        policy=policy,
        signers=signers,
        decision=decision,
        expected_accept=True,
        invariant_id=invariant_id,
        primary_axis=INVARIANT_AXIS[invariant_id],
        polarity="positive",
    )


def _negative_cases_for_action(action: str, policy: Mapping[str, Any]) -> list[dict[str, Any]]:
    valid = _valid_quorum(policy)
    cases: list[dict[str, Any]] = []

    testnet = [Key(**{**key.__dict__, "environment": "testnet"}) for key in valid]
    cases.append(
        _case(
            name=f"{action}:PKM-G-001:testnet_keys_rejected_for_production",
            action=action,
            policy=policy,
            signers=testnet,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=testnet,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=False,
            invariant_id="PKM-G-001",
            primary_axis="environment",
            polarity="negative",
            reject_reason="testnet_key_for_production",
        )
    )

    revoked = [*valid]
    revoked[0] = Key(**{**revoked[0].__dict__, "status": "revoked"})
    cases.append(
        _case(
            name=f"{action}:PKM-G-002:revoked_key_rejected",
            action=action,
            policy=policy,
            signers=revoked,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=revoked,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=False,
            invariant_id="PKM-G-002",
            primary_axis="status",
            polarity="negative",
            reject_reason="revoked_or_expired_key",
        )
    )
    expired = [*valid]
    expired[0] = Key(**{**expired[0].__dict__, "status": "expired"})
    cases.append(
        _case(
            name=f"{action}:PKM-G-002:expired_key_rejected",
            action=action,
            policy=policy,
            signers=expired,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=expired,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=False,
            invariant_id="PKM-G-002",
            primary_axis="status",
            polarity="negative",
            reject_reason="revoked_or_expired_key",
        )
    )

    if policy["critical"] is True:
        single = [_active_key(str(policy["role"]), 0)]
        cases.append(
            _case(
                name=f"{action}:PKM-G-003:single_key_rejected",
                action=action,
                policy=policy,
                signers=single,
                decision=_admission_decision(
                    action=action,
                    policy=policy,
                    signers=single,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
                expected_accept=False,
                invariant_id="PKM-G-003",
                primary_axis="quorum",
                polarity="negative",
                reject_reason="threshold_not_met",
            )
        )
        same_custodian = [
            Key(**{**valid[0].__dict__, "custodian_id": "custodian-shared"}),
            Key(**{**valid[1].__dict__, "custodian_id": "custodian-shared"}),
        ]
        cases.append(
            _case(
                name=f"{action}:PKM-G-003:same_custodian_quorum_rejected",
                action=action,
                policy=policy,
                signers=same_custodian,
                decision=_admission_decision(
                    action=action,
                    policy=policy,
                    signers=same_custodian,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
                expected_accept=False,
                invariant_id="PKM-G-003",
                primary_axis="quorum",
                polarity="negative",
                reject_reason="distinct_custodian_quorum_not_met",
            )
        )

    if policy["hardware_required"] is True:
        software = [Key(**{**key.__dict__, "storage_class": "software"}) for key in valid]
        cases.append(
            _case(
                name=f"{action}:PKM-G-004:software_keys_rejected",
                action=action,
                policy=policy,
                signers=software,
                decision=_admission_decision(
                    action=action,
                    policy=policy,
                    signers=software,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=True,
                ),
                expected_accept=False,
                invariant_id="PKM-G-004",
                primary_axis="storage",
                polarity="negative",
                reject_reason="software_key_for_hardware_required_action",
            )
        )

    if policy["timelock_required"] is True:
        cases.append(
            _case(
                name=f"{action}:PKM-G-005:missing_timelock_rejected",
                action=action,
                policy=policy,
                signers=valid,
                decision=_admission_decision(
                    action=action,
                    policy=policy,
                    signers=valid,
                    environment="production",
                    timelock_satisfied=False,
                    transparency_receipt_bound=True,
                ),
                expected_accept=False,
                invariant_id="PKM-G-005",
                primary_axis="timelock",
                polarity="negative",
                reject_reason="timelock_required",
            )
        )

    break_glass = [
        Key(**{**key.__dict__, "break_glass": True})
        for key in valid
    ]
    cases.append(
        _case(
            name=f"{action}:PKM-G-006:break_glass_scope",
            action=action,
            policy=policy,
            signers=break_glass,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=break_glass,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=(action == "emergency_pause"),
            invariant_id="PKM-G-006",
            primary_axis="break_glass",
            polarity="positive" if action == "emergency_pause" else "negative",
            reject_reason="" if action == "emergency_pause" else "break_glass_scope_violation",
        )
    )

    if policy["transparency_required"] is True:
        cases.append(
            _case(
                name=f"{action}:PKM-G-007:missing_transparency_receipt_rejected",
                action=action,
                policy=policy,
                signers=valid,
                decision=_admission_decision(
                    action=action,
                    policy=policy,
                    signers=valid,
                    environment="production",
                    timelock_satisfied=True,
                    transparency_receipt_bound=False,
                ),
                expected_accept=False,
                invariant_id="PKM-G-007",
                primary_axis="transparency",
                polarity="negative",
                reject_reason="transparency_receipt_required",
            )
        )

    return cases


def _axis_coverage_cases(action: str, policy: Mapping[str, Any]) -> list[dict[str, Any]]:
    valid = _valid_quorum(policy)
    wrong_role = [_active_key("oracle" if policy["role"] != "oracle" else "config", index) for index in range(int(policy["threshold"]))]
    return [
        _case(
            name=f"{action}:packet_invalid_rejected",
            action=action,
            policy=policy,
            signers=valid,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=valid,
                environment="production",
                packet_ok=False,
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=False,
            invariant_id="PKM-G-001",
            primary_axis="packet",
            polarity="negative",
            reject_reason="packet_invalid",
        ),
        _case(
            name=f"{action}:signature_binding_rejected",
            action=action,
            policy=policy,
            signers=valid,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=valid,
                environment="production",
                signatures_bind=False,
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=False,
            invariant_id="PKM-G-002",
            primary_axis="signature_binding",
            polarity="negative",
            reject_reason="signature_binding_invalid",
        ),
        _case(
            name=f"{action}:wrong_role_rejected",
            action=action,
            policy=policy,
            signers=wrong_role,
            decision=_admission_decision(
                action=action,
                policy=policy,
                signers=wrong_role,
                environment="production",
                timelock_satisfied=True,
                transparency_receipt_bound=True,
            ),
            expected_accept=False,
            invariant_id="PKM-G-003",
            primary_axis="role",
            polarity="negative",
            reject_reason="threshold_not_met",
        ),
    ]


def run_check(model_path: Path = DEFAULT_MODEL) -> dict[str, Any]:
    model = _load_model(model_path)
    policies = model.get("action_policies")
    if not isinstance(policies, dict):
        raise ValueError("action_policies must be an object")

    cases: list[dict[str, Any]] = []
    first_action: str | None = None
    first_policy: Mapping[str, Any] | None = None
    for action, raw_policy in sorted(policies.items()):
        if not isinstance(raw_policy, dict):
            raise ValueError(f"{action} policy must be an object")
        if first_action is None:
            first_action = action
            first_policy = raw_policy
        for invariant_id in sorted(INVARIANT_AXIS):
            cases.append(_accepted_case(action, raw_policy, invariant_id))
        cases.extend(_negative_cases_for_action(action, raw_policy))

    if first_action is not None and first_policy is not None:
        cases.extend(_axis_coverage_cases(first_action, first_policy))

    counterexamples = [
        case["counterexample"]
        for case in cases
        if case.get("counterexample") is not None
    ]
    ok = all(case["ok"] is True for case in cases)
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "model_path": str(model_path),
        "case_count": len(cases),
        "invariant_ids": sorted(INVARIANT_AXIS),
        "primary_axes": sorted(PRIMARY_AXES),
        "counterexamples": counterexamples,
        "cases": cases,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("model_path", nargs="?", default=str(DEFAULT_MODEL))
    parser.add_argument("--json-out", type=Path, help="Optional path to write the result JSON")
    args = parser.parse_args(argv)

    result = run_check(Path(args.model_path))
    output = json.dumps(result, indent=2, sort_keys=True)
    print(output)
    if args.json_out is not None:
        args.json_out.write_text(output + "\n", encoding="utf-8")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
