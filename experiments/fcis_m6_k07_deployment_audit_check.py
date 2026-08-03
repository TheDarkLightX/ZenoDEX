"""Independent K07 deployment-boundary audit checker."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import cast

from src.core.fcis_m6_k07_deployment_audit import (
    K07AuditBlockedV1,
    K07AuditCleanV1,
    K07AuditStatusV1,
    K07DeploymentAuditV1,
    K07Error,
    K07FindingKindV1,
    is_verified_deployment_audit_v1,
    require_clean_deployment_audit_v1,
)
from src.state.canonical import canonical_json_bytes
from tools.build_fcis_m6_k07_deployment_audit import (
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    build_audit,
    build_payload,
)

ROOT = Path(__file__).resolve().parents[1]


def _read_vector() -> dict[str, object]:
    value = json.loads((ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("K07 vector must be an object")
    return cast(dict[str, object], value)


def _copy_with(audit: K07DeploymentAuditV1, field_name: str, value: object) -> object:
    result = copy.copy(audit)
    object.__setattr__(result, field_name, value)
    return result


def run_checks() -> dict[str, object]:
    payload = build_payload()
    vector = _read_vector()
    if canonical_json_bytes(payload) != canonical_json_bytes(vector):
        raise AssertionError("K07 vector is not the independently regenerated payload")
    audit = build_audit(ROOT / DEFAULT_CONFIG_PATH)
    if not is_verified_deployment_audit_v1(audit):
        raise AssertionError("canonical K07 audit failed fresh provenance verification")
    if audit.status is not K07AuditStatusV1.GAP:
        raise AssertionError("K07 silently promoted a nonempty audit to PASS")
    if len(audit.findings) != 5:
        raise AssertionError(f"unexpected K07 finding count: {len(audit.findings)}")
    kinds = {finding.kind for finding in audit.findings}
    if kinds != {
        K07FindingKindV1.CREDENTIAL_POLICY_GAP,
        K07FindingKindV1.DIRECT_PROTECTED_WRITER,
    }:
        raise AssertionError(f"unexpected K07 finding classes: {kinds!r}")
    if any(finding.kind is K07FindingKindV1.UNTRACKED_WORKER for finding in audit.findings):
        raise AssertionError("K07 reported an unexpected untracked worker")

    decision = require_clean_deployment_audit_v1(audit)
    if type(decision) is not K07AuditBlockedV1 or decision.finding_count != 5:
        raise AssertionError("K07 GAP did not produce a typed blocking decision")

    forged = _copy_with(audit, "status", K07AuditStatusV1.PASS)
    if is_verified_deployment_audit_v1(forged):
        raise AssertionError("mutated K07 status remained verifier-owned")
    try:
        require_clean_deployment_audit_v1(forged)
    except K07Error:
        pass
    else:
        raise AssertionError("mutated K07 audit reached the clean gate")

    crossed = _copy_with(audit, "k04_topology_root", "0" * 64)
    if is_verified_deployment_audit_v1(crossed):
        raise AssertionError("crossed K04 root remained verifier-owned")

    forged_object = object.__new__(type(audit))
    for name in (
        "k04_topology_root",
        "k06_seal_root",
        "k01_entrypoint_inventory_root",
        "audited_paths",
        "deployment_paths",
        "launch_bindings",
        "findings",
        "status",
        "audit_root",
    ):
        object.__setattr__(forged_object, name, getattr(audit, name))
    if is_verified_deployment_audit_v1(forged_object):
        raise AssertionError("object.__new__ K07 audit bypassed provenance")

    try:
        K07DeploymentAuditV1(
            k04_topology_root=audit.k04_topology_root,
            k06_seal_root=audit.k06_seal_root,
            k01_entrypoint_inventory_root=audit.k01_entrypoint_inventory_root,
            audited_paths=audit.audited_paths,
            deployment_paths=audit.deployment_paths,
            launch_bindings=audit.launch_bindings,
            findings=audit.findings,
            status=audit.status,
            audit_root=audit.audit_root,
        )
    except K07Error:
        pass
    else:
        raise AssertionError("caller constructed K07 audit without builder token")

    try:
        K07AuditCleanV1(audit.audit_root)
    except K07Error:
        pass
    else:
        raise AssertionError("caller constructed a clean deployment decision")

    return {
        "audit_root": audit.audit_root,
        "status": audit.status.value,
        "finding_count": len(audit.findings),
        "direct_writer_findings": sum(
            finding.kind is K07FindingKindV1.DIRECT_PROTECTED_WRITER for finding in audit.findings
        ),
        "credential_findings": sum(
            finding.kind is K07FindingKindV1.CREDENTIAL_POLICY_GAP for finding in audit.findings
        ),
        "untracked_worker_findings": 0,
        "clean_gate": "BLOCKED",
        "mutants_killed": 4,
    }


if __name__ == "__main__":
    result = run_checks()
    print("K07_DEPLOYMENT_AUDIT_CHECKS_PASS", result["audit_root"])
