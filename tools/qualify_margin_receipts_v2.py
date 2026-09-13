"""Prepare or replay the fixed AS02 isolated margin receipt workload.

Uses public test genesis and a public deterministic signing scalar. Requires
the development test helpers. No production policy, genesis, custody route,
finality or deployment qualification follows. Remote provers receive only the
three framed inputs; returned configuration is never consumed by publication.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import replace
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.core.economic_receipt_verifier_evidence_v1 import (
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.perps_margin_guest_role_v2 import PerpsMarginGuestRoleBindingV2
from src.core.perps_margin_receipt_v2 import (
    encode_perps_margin_frame_v2,
    replay_perps_margin_frame_v2,
)
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration.economic_command_authentication_v2 import (
    verify_isolated_economic_command_occurrence_v2,
)
from src.integration.global_receipt_verifier_v1 import MAX_RECEIPT_BYTES_V1
from src.integration.isolated_custody_publisher_v2 import (
    CustodyPublicationConfigurationV2,
    CustodyPublicationOutcomeV2,
    CustodyPublicationStatusV2,
    IsolatedCustodyPublisherV2,
    JointMarginPublicationConfigurationV2,
)
from tests.core.test_perps_margin_global_v2 import CLOSE, DEPOSIT, WITHDRAW, _command
from tests.integration.test_isolated_economic_command_authentication_v2 import _NATIVE_SHA256
from tests.integration.test_isolated_joint_margin_publisher_v2 import _signed_command
from tests.integration.test_profiled_asset_lane_custody_receipt_v2 import _binding
from tests.integration.test_profiled_perps_margin_receipt_v2 import (
    PerpsMarginSignedCase,
    perps_margin_signed_case,
)
from tools.isolated_bls_evidence_v1 import read_regular

_EVIDENCE = Path(__file__).resolve().parents[1] / "tests/evidence/perps_margin_guest_execution_v2_20260913.json"
_STEPS = ((DEPOSIT, 40), (WITHDRAW, 40), (CLOSE, 0))


def read_bounded(path: Path, ceiling: int) -> bytes:
    data = read_regular(path, maximum=ceiling)
    if not data:
        raise ValueError("qualification artifact is empty")
    return data


def build_workload(
    signature_path: Path, receipt_path: Path,
) -> tuple[JointMarginPublicationConfigurationV2, tuple[PerpsMarginSignedCase, ...]]:
    """Rebuild every dependent root from locally selected measured endpoints."""
    evidence = json.loads(read_bounded(_EVIDENCE, 64 * 1024))
    measurement = evidence["artifacts"]
    expected = measurement["artifacts"]["verify_margin_receipt_v2"]
    signature_bytes = read_bounded(signature_path, 1024 * 1024)
    receipt_bytes = read_bounded(receipt_path, expected["bytes"])
    if hashlib.sha256(signature_bytes).hexdigest() != _NATIVE_SHA256:
        raise ValueError("qualification signature executable hash drift")
    if hashlib.sha256(receipt_bytes).hexdigest() != expected["sha256"]:
        raise ValueError("qualification receipt executable hash drift")
    base = perps_margin_signed_case(signature_artifact=signature_bytes)
    manifest = replace(
        base.receipt_manifest,
        root_image_id=measurement["image_id"],
        implementation_root=economic_receipt_verifier_implementation_root_v1(receipt_bytes),
        source_root="0x" + evidence["source_manifest"]["sha256"],
        toolchain_root="0x" + hashlib.sha256(json.dumps(
            (measurement["host_toolchain"], measurement["guest_toolchain"]),
            separators=(",", ":"),
        ).encode()).hexdigest(),
    )
    role = PerpsMarginGuestRoleBindingV2(base.profile.profile_id, base.profile.authority_epoch, manifest)
    base = replace(base, receipt_manifest=manifest, guest_role_binding=role)
    # The custody role remains an unqualified fixture. This workload invokes
    # only the independently selected margin role and makes no transfer claim.
    configuration = JointMarginPublicationConfigurationV2(
        CustodyPublicationConfigurationV2(
            base.profile, _binding(base, receipt_bytes), base.signature_manifest,
            str(receipt_path), signature_path, receipt_timeout_ms=30_000,
        ), role, str(receipt_path),
    )
    assets, margin, state = base.assets, base.margin, base.global_pre
    cases = []
    for nonce, (kind, amount) in enumerate(_STEPS, 1):
        command = _command(kind, amount, nonce)
        candidate, occurrence = _signed_command(base, state, command, nonce)
        request = PerpsMarginRequestV2(command, occurrence)
        case = replace(base, assets=assets, margin=margin, global_pre=state, candidate=candidate, request=request)
        result = replay_perps_margin_frame_v2(frame(case)).result
        cases.append(case)
        assets, margin, state = result.post_assets, result.post_margin, result.post_state
    return configuration, tuple(cases)


def frame(case: PerpsMarginSignedCase) -> bytes:
    return encode_perps_margin_frame_v2(case.assets, case.margin, case.global_pre, case.request)


def authenticate(case: PerpsMarginSignedCase, configuration: JointMarginPublicationConfigurationV2) -> None:
    verify_isolated_economic_command_occurrence_v2(
        case.candidate, case.request.occurrence,
        signature_artifact_path=configuration.custody.signature_artifact_path,
        signature_evidence_manifest=case.signature_manifest,
        signature_timeout_ms=configuration.custody.signature_timeout_ms,
    )


def prepare(signature_path: Path, receipt_path: Path, output: Path) -> dict[str, object]:
    configuration, cases = build_workload(signature_path, receipt_path)
    for case in cases:
        authenticate(case, configuration)
    output.mkdir(parents=True, exist_ok=False)
    entries = []
    for index, case in enumerate(cases, 1):
        inner = frame(case)
        framed = len(inner).to_bytes(4, "little") + inner
        journal = replay_perps_margin_frame_v2(inner).statement
        name = f"{index:02}"
        (output / f"{name}.input.bin").write_bytes(framed)
        (output / f"{name}.journal.json").write_bytes(journal)
        entries.append({
            "name": name, "command": case.request.command.command_kind,
            "input_sha256": hashlib.sha256(framed).hexdigest(),
            "journal_sha256": hashlib.sha256(journal).hexdigest(),
        })
    report = {
        "schema": "zenodex/isolated-margin-proving-workload/v2",
        "profile_root": cases[0].profile.profile_id,
        "image_id": configuration.margin_role.evidence_manifest.root_image_id,
        "guest_role_binding_root": configuration.margin_role.binding_root,
        "steps": entries, "actual_signature_checks": len(cases),
        "public_test_genesis_and_key": True, "genuine_receipts_produced": False,
        "economic_release_and_evidence_status_labels": "isolated fixture assumptions",
        "production_authority": False,
    }
    (output / "workload.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def publish(signature_path: Path, receipt_path: Path, receipts: Path, database: Path) -> dict[str, object]:
    """Use only receipt bytes from the prover; derive all authority locally."""
    configuration, cases = build_workload(signature_path, receipt_path)
    raw = tuple(read_bounded(receipts / f"{index:02}.receipt.json", MAX_RECEIPT_BYTES_V1)
                for index in range(1, len(cases) + 1))
    base = cases[0]
    with IsolatedCustodyPublisherV2.create(
        database, base.global_pre, base.assets, configuration, margin_state=base.margin,
    ) as publisher:
        for case, receipt in zip(cases, raw, strict=True):
            result = publisher.publish(case.candidate, case.request, receipt_bytes=receipt)
            if type(result) is not CustodyPublicationOutcomeV2 or result.status is not CustodyPublicationStatusV2.COMMITTED:
                raise ValueError("qualification command did not commit")
        final = publisher.snapshot()
        expected = replay_perps_margin_frame_v2(frame(cases[-1])).result
        if (final.sequence, final.global_state, final.custody_state, final.margin_state) != (
            len(cases), expected.post_state, expected.post_assets, expected.post_margin,
        ):
            raise ValueError("qualified publication differs from complete expected successor")
    with IsolatedCustodyPublisherV2.open(
        database, base.global_pre, base.assets, configuration, margin_state=base.margin,
    ) as reopened:
        if reopened.snapshot() != final:
            raise ValueError("qualification restart changed committed state")
        for case, receipt in zip(cases, raw, strict=True):
            result = reopened.publish(case.candidate, case.request, receipt_bytes=receipt)
            if type(result) is not CustodyPublicationOutcomeV2 or result.status is not CustodyPublicationStatusV2.ALREADY_COMMITTED:
                raise ValueError("qualification exact retry did not identify its original commit")
        if reopened.snapshot() != final:
            raise ValueError("qualification retry changed committed state")
    audited = IsolatedCustodyPublisherV2.audit(
        database, base.global_pre, base.assets, configuration, margin_state=base.margin,
        authentication_candidates=tuple(case.candidate for case in cases),
        expected_publication_id=final.publication_id,
        expected_authority_root=final.authority.authority_root,
    )
    if audited != final:
        raise ValueError("qualification read-only history audit changed the expected result")
    return {"schema": "zenodex/isolated-margin-receipt-publication/v2",
            "profile_root": base.profile.profile_id, "committed": final.sequence,
            "publication_id": final.publication_id, "authority_root": final.authority.authority_root,
            "retained_evidence_reverified": True,
            "post_state_root": final.global_state.state_root, "production_authority": False}


def audit(
    signature_path: Path, receipt_path: Path, database: Path, *,
    expected_publication_id: str, expected_authority_root: str,
) -> dict[str, object]:
    """Reverify the closed fixed workload against caller-retained checkpoints.

    Rebuild policy witnesses from the locally pinned workload. Never derive
    either expected checkpoint from the database being checked. Checkpoint
    authenticity, freshness and finality require an independently qualified source.
    """
    configuration, cases = build_workload(signature_path, receipt_path)
    base = cases[0]
    head = IsolatedCustodyPublisherV2.audit(
        database, base.global_pre, base.assets, configuration, margin_state=base.margin,
        authentication_candidates=tuple(case.candidate for case in cases),
        expected_publication_id=expected_publication_id,
        expected_authority_root=expected_authority_root,
    )
    return {"schema": "zenodex/isolated-margin-history-audit/v2",
            "profile_root": base.profile.profile_id, "verified_publications": head.sequence,
            "publication_id": head.publication_id, "authority_root": head.authority.authority_root,
            "post_state_root": head.global_state.state_root,
            "retained_evidence_reverified": True, "production_authority": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    operations = parser.add_subparsers(dest="operation", required=True)
    for name in ("prepare", "publish", "audit"):
        command = operations.add_parser(name)
        command.add_argument("--signature-verifier", required=True, type=Path)
        command.add_argument("--receipt-verifier", required=True, type=Path)
        if name == "audit":
            command.add_argument("--database", required=True, type=Path)
            command.add_argument("--expected-publication-id", required=True)
            command.add_argument("--expected-authority-root", required=True)
        else:
            command.add_argument("--output", required=True, type=Path,
                                 help="new packet directory or fresh isolated database")
        if name == "publish":
            command.add_argument("--receipts", required=True, type=Path)
    args = parser.parse_args()
    signature, receipt = args.signature_verifier.resolve(), args.receipt_verifier.resolve()
    if args.operation == "prepare":
        result = prepare(signature, receipt, args.output)
    elif args.operation == "publish":
        result = publish(signature, receipt, args.receipts, args.output)
    else:
        result = audit(signature, receipt, args.database,
                       expected_publication_id=args.expected_publication_id,
                       expected_authority_root=args.expected_authority_root)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
