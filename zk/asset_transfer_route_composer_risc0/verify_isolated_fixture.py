"""Replay five retained genuine receipts through the exact measured profile set."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from build_isolated_fixture import (
    Evidence,
    EvidenceManifest,
    EvidenceStatus,
    IsolatedVerifierArtifactV1,
    VerifierRegistry,
    VerifierRelease,
    abi,
    bind_isolated_economic_verifier_set_v1,
    canonical,
    decode_profile,
    record,
)


def bind(directory):
    value = json.loads((directory / "route.input.json").read_bytes())
    selected = decode_profile(value)
    raw = json.loads((directory / "verifier-manifest.json").read_bytes())
    raw["evidence_artifacts"] = tuple(
        record(Evidence, row, enums={"status": EvidenceStatus}) for row in raw["evidence_artifacts"]
    )
    manifest = record(EvidenceManifest, raw)
    raw = json.loads((directory / "verifier-registry.json").read_bytes())
    releases = tuple(
        record(
            VerifierRelease,
            row,
            enums={"status": abi.ReleaseStatusV1, "evidence_statuses": EvidenceStatus},
        )
        for row in raw["releases"]
    )
    registry = VerifierRegistry(releases)
    meta = json.loads((directory / "metadata.json").read_bytes())
    artifacts = tuple(
        IsolatedVerifierArtifactV1(**row)
        for row in sorted(meta["artifacts"], key=lambda row: row["image_id"])
    )
    bound = bind_isolated_economic_verifier_set_v1(
        profile=selected,
        verifier_registry=registry,
        evidence_manifest=manifest,
        artifacts=artifacts,
        deployment_root=value["pre_state"]["deployment_root"],
        timeout_ms=30000,
    )
    return selected, bound


def verify_leaves(profile, bound, evidence):
    module = profile.lane_registry.release_for(abi.LaneIdV1.ASSET_TRANSFER)
    coordinator = profile.lane_coordinator_registry.release_for(abi.LaneIdV1.ASSET_TRANSFER)
    route = profile.route_registry.routes[0]
    calls = [
        (
            "module",
            bound.verify_profile_lane_receipt,
            dict(
                profile=profile,
                lane_id=module.lane_id,
                expected_module_release_id=module.release_id,
                expected_image_id=module.guest_image_id,
            ),
        ),
        (
            "coordinator",
            bound.verify_profile_lane_coordinator_receipt,
            dict(
                profile=profile,
                lane_id=coordinator.lane_id,
                expected_coordinator_release_id=coordinator.coordinator_release_id,
                expected_image_id=coordinator.guest_image_id,
            ),
        ),
        (
            "route",
            bound.verify_profile_route_receipt,
            dict(
                profile=profile,
                expected_route_release_id=route.route_release_id,
                expected_image_id=route.guest_image_id,
            ),
        ),
    ]
    results = []
    for name, method, keywords in calls:
        receipt = (evidence / "transfer" / f"{name}.receipt.json").read_bytes()
        journal = (evidence / "transfer" / f"{name}.journal").read_bytes()
        method(receipt, expected_journal_bytes=journal, **keywords)
        results.append(name)
    return results


def verify_roots(directory, evidence, profile, bound):
    results = []
    initial = json.loads((directory / "initial.input.json").read_bytes())
    epoch = json.loads((directory / "epoch.input.json").read_bytes())["DirectEpoch"]
    for name, expected in [
        ("genesis", canonical(initial["statement"])),
        ("epoch", bytes(epoch["certificate_journal_bytes"])),
    ]:
        journal = (evidence / name / "root.journal").read_bytes()
        if journal != expected:
            raise ValueError(f"{name} journal differs from exact supplied statement")
        bound.verify_succinct_receipt(
            (evidence / name / "root.receipt").read_bytes(),
            expected_image_id=profile.root_image_id,
            expected_journal_bytes=expected,
        )
        results.append(name)
    return results


def verify(directory, evidence):
    profile, bound = bind(directory)
    results = verify_leaves(profile, bound, evidence)
    results.extend(verify_roots(directory, evidence, profile, bound))
    result = {
        "verified_receipts": results,
        "profile_id": profile.profile_id,
        "all_five_measured_verifier_calls_passed": True,
        "signer_authority_verified": False,
        "genesis_allocation_authority_verified": False,
        "publication_qualified": False,
        "whole_epoch_economic_commitments_proved": False,
        "production_authority": False,
    }
    (evidence / "measured-set-verification.json").write_bytes(canonical(result))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    verify(Path(sys.argv[1]), Path(sys.argv[2]))
