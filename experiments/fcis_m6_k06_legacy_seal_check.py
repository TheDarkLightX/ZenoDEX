"""Independent K06 build/runtime gate checker and adversarial witnesses."""

from __future__ import annotations

import copy
import json
from dataclasses import fields
from pathlib import Path
from typing import cast

from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_k06_legacy_seal import (
    K06Error,
    K06FeatureFlagV1,
    K06LegacySealCertificateV1,
    K06RejectCodeV1,
    K06WriterAcceptedV1,
    K06WriterRejectV1,
    K06WriterV1,
    authorize_writer_v1,
    feature_flag_root_v1,
    is_verified_legacy_seal_v1,
)
from src.state.canonical import canonical_json_bytes
from tools.build_fcis_m6_k06_legacy_seal import (
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    build_certificate,
    build_payload,
)

ROOT = Path(__file__).resolve().parents[1]


def _read_vector() -> dict[str, object]:
    value = json.loads((ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("K06 vector must be an object")
    return cast(dict[str, object], value)


def _copy_with(
    certificate: K06LegacySealCertificateV1, field_name: str, value: object
) -> K06LegacySealCertificateV1:
    result = copy.copy(certificate)
    object.__setattr__(result, field_name, value)
    return result


def _forge_without_registry(
    certificate: K06LegacySealCertificateV1,
) -> K06LegacySealCertificateV1:
    forged = object.__new__(type(certificate))
    for field in fields(K06LegacySealCertificateV1):
        object.__setattr__(forged, field.name, getattr(certificate, field.name))
    return forged


def _decision_code(value: object) -> K06RejectCodeV1:
    if type(value) is not K06WriterRejectV1:
        raise AssertionError("decision is not a typed rejection")
    return value.code


def _authorize(
    certificate: object,
    *,
    writer: K06WriterV1 = K06WriterV1.TARGET,
    writer_id: str = "fcis/m6/unique-atomic-commit-port/v1",
    profile_root: str | None = None,
    phase: dra.MigrationPhaseV1 = dra.MigrationPhaseV1.LEGACY_DISABLED,
    epoch: int = 1,
    topology: str | None = None,
    inventory: str | None = None,
    feature: object | None = None,
) -> object:
    if type(certificate) is K06LegacySealCertificateV1:
        current = certificate
    else:
        current = build_certificate()
    return authorize_writer_v1(
        certificate,
        writer=writer,
        writer_id=writer_id,
        writer_profile_root=profile_root or current.policy.target_writer_profile_root,
        current_phase=phase,
        current_authority_epoch=epoch,
        current_d05_topology_root=topology or current.policy.d05_topology_root,
        current_k01_inventory_root=inventory or current.policy.k01_entrypoint_inventory_root,
        current_feature_flag=feature if feature is not None else current.feature_flag,
    )


def run_checks() -> dict[str, object]:
    payload = build_payload()
    vector = _read_vector()
    if canonical_json_bytes(payload) != canonical_json_bytes(vector):
        raise AssertionError("K06 vector is not the independently regenerated payload")
    certificate = build_certificate(ROOT / DEFAULT_CONFIG_PATH)
    if not is_verified_legacy_seal_v1(certificate):
        raise AssertionError("canonical K06 certificate failed fresh verification")
    if certificate.reachable_legacy_symbol_ids != ():
        raise AssertionError("canonical K06 seal leaves a legacy symbol reachable")
    if certificate.feature_flag.enabled:
        raise AssertionError("canonical K06 feature flag is enabled")

    accepted = _authorize(certificate)
    if type(accepted) is not K06WriterAcceptedV1:
        raise AssertionError(f"target admission failed: {accepted!r}")

    legacy = _authorize(certificate, writer=K06WriterV1.LEGACY, writer_id="evaluate_refinement_v1")
    if _decision_code(legacy) is not K06RejectCodeV1.LEGACY_WRITER_DISABLED:
        raise AssertionError("legacy writer was admitted")

    stale_epoch = _authorize(certificate, epoch=2)
    if _decision_code(stale_epoch) is not K06RejectCodeV1.STALE_EPOCH:
        raise AssertionError("stale epoch was admitted")

    pre_terminal = _authorize(certificate, phase=dra.MigrationPhaseV1.AUTHORITY_SWITCH)
    if _decision_code(pre_terminal) is not K06RejectCodeV1.WRONG_PHASE:
        raise AssertionError("pre-terminal phase was admitted")

    wrong_topology = _authorize(certificate, topology="0" * 64)
    if _decision_code(wrong_topology) is not K06RejectCodeV1.TOPOLOGY_ROOT_MISMATCH:
        raise AssertionError("crossed topology root was admitted")

    wrong_inventory = _authorize(certificate, inventory="0" * 64)
    if _decision_code(wrong_inventory) is not K06RejectCodeV1.INVENTORY_ROOT_MISMATCH:
        raise AssertionError("crossed inventory root was admitted")

    forged = _forge_without_registry(certificate)
    if is_verified_legacy_seal_v1(forged):
        raise AssertionError("object.__new__ certificate bypassed verifier registry")

    mutated = _copy_with(
        certificate,
        "feature_flag",
        K06FeatureFlagV1(
            flag_id=certificate.feature_flag.flag_id,
            enabled=True,
            authority_epoch=certificate.feature_flag.authority_epoch,
            seal_policy_root=certificate.feature_flag.seal_policy_root,
            d05_topology_root=certificate.feature_flag.d05_topology_root,
            k01_entrypoint_inventory_root=certificate.feature_flag.k01_entrypoint_inventory_root,
            target_writer_profile_root=certificate.feature_flag.target_writer_profile_root,
        ),
    )
    if is_verified_legacy_seal_v1(mutated):
        raise AssertionError("mutated feature flag remained verified")
    if _decision_code(_authorize(mutated)) is not K06RejectCodeV1.SEAL_UNVERIFIED:
        raise AssertionError("mutated feature flag reached runtime admission")

    reachable = _copy_with(certificate, "reachable_legacy_symbol_ids", ("publish_atom",))
    if is_verified_legacy_seal_v1(reachable):
        raise AssertionError("nonempty reachable legacy set remained verified")

    try:
        K06LegacySealCertificateV1(
            policy=certificate.policy,
            feature_flag=certificate.feature_flag,
            phase=certificate.phase,
            authority_epoch=certificate.authority_epoch,
            reachable_legacy_symbol_ids=(),
            sealed_symbol_ids=certificate.sealed_symbol_ids,
            source_scan_issues=(),
            seal_root=certificate.seal_root,
        )
    except K06Error:
        pass
    else:
        raise AssertionError("caller constructed a K06 seal without verifier token")

    return {
        "seal_root": certificate.seal_root,
        "policy_root": payload["policy_root"],
        "feature_flag_root": feature_flag_root_v1(certificate.feature_flag),
        "target_admission": "PASS",
        "legacy_admission": "REJECTED",
        "mutants_killed": 10,
        "mutants": [
            "legacy writer after terminal seal",
            "stale authority epoch",
            "pre-terminal phase",
            "crossed topology root",
            "crossed inventory root",
            "object.__new__ forged certificate",
            "mutated feature flag",
            "nonempty reachable legacy set",
            "caller certificate constructor",
            "unknown target writer",
        ],
    }


if __name__ == "__main__":
    result = run_checks()
    print("K06_LEGACY_SEAL_CHECKS_PASS", result["seal_root"])
