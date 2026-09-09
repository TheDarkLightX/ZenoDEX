"""Same-call signature, typed command and custody-statement binding.

The receipt exchange is a protocol fixture throughout, including the separately
configured native BLS test. No test here claims a genuine RISC0 receipt.
"""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass, fields, replace
from pathlib import Path

import pytest
from py_ecc.bls import G2Basic

from src.core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    EconomicCommandIntentV2,
)
from src.core.economic_command_authentication_v2 import (
    prepare_isolated_economic_command_authentication_v2,
)
from src.core.economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationRegistryV1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, ReplayStateV2
from src.core.global_settlement_primitives_v2 import (
    canonical_economic_command_body_bytes_v2,
    canonical_global_bytes_v2,
    hash_economic_command_body_bytes_v2,
)
from src.core.global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorRegistryV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
)
from src.core.global_settlement_types_v2 import LaneIdV2
from src.integration import authenticated_asset_lane_custody_receipt_v2 as pipeline
from src.integration import global_receipt_verifier_v1 as receipt_transport
from src.integration import sealed_bls_command_verifier_deployment_v1 as bls_deployment
from tests.core.test_asset_lane_custody_statement_parity_v2 import CASES, typed_inputs
from tests.core.test_economic_command_authentication_v1 import _rebuild_profile
from tests.core.test_lane_module_release_route_binding_v1 import _active_evidence
from tests.integration.test_global_receipt_verifier_v1 import IMAGE, OTHER_IMAGE, backend
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    _ARTIFACT,
    _NATIVE_SHA256,
    _SECRET,
    _signed_case,
)
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    protocol_case as protocol_case,
)
from tools.render_asset_lane_custody_v2_golden import _oracle

_RECEIPT = b"isolated-custody-protocol-fixture-not-a-proof"


@dataclass(frozen=True)
class _Case:
    candidate: EconomicCommandAuthenticationCandidateV2
    inputs: tuple[
        AssetLaneContextV2,
        AssetLaneCustodyStateV2,
        AssetLaneCommandV2,
        GlobalEconomicStateV2,
        GlobalEconomicStateV2,
    ]
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1
    expected: bytes | AssetLaneRejectedV2


def _sign(candidate, scalar=_SECRET):
    _, _, message = prepare_isolated_economic_command_authentication_v2(candidate)
    return replace(
        candidate,
        envelope=replace(candidate.envelope, signature_bytes=G2Basic.Sign(scalar, message)),
    )


def _case(index=0, artifact=_ARTIFACT, *, amount=None, profile=None):
    base, _, manifest, _ = _signed_case(artifact)
    if profile is not None:
        base = replace(base, profile=profile)
    context, lane, command, before, after = typed_inputs(CASES[index])
    if amount is not None:
        command = replace(command, amount_atoms=amount)
    occurrence = context.occurrence
    assert occurrence is not None
    route = base.profile.route_registry.route_for_command(command.command_kind)
    authorization = replace(
        base.authorization_registry.authorizations[0],
        command_kind=command.command_kind,
        route_release_id=route.route_release_id,
        subject_id=occurrence.subject_id,
        grant_root=occurrence.grant_root,
        min_nonce=occurrence.nonce,
        max_nonce=occurrence.nonce,
        valid_from_height=occurrence.height,
        valid_through_height=occurrence.height,
    )
    authorizations = EconomicCommandAuthorizationRegistryV1((authorization,))
    policies = EconomicPolicyRegistryV1(
        tuple(
            replace(
                binding,
                command_kind=command.command_kind,
                policy_root=(
                    authorizations.registry_root
                    if binding.policy_kind == ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1
                    else base.signature_verifier_registry.registry_root
                ),
            )
            for binding in base.policy_registry.bindings
        )
    )
    profile = _rebuild_profile(base.profile, policies.registry_root)
    release = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    lane = AssetLaneCustodyStateV2(
        replace(lane.transfer_state, module_release_id=release.release_id),
        replace(lane.origin_registry, module_release_id=release.release_id),
        lane.managed_policies,
        lane.custody,
    )
    releases = {row.lane_id.value: row for row in profile.lane_registry.releases}
    before = replace(
        before,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        lane_roots=tuple(
            replace(
                row,
                module_release_id=releases[row.lane_id.value].release_id,
                enabled=releases[row.lane_id.value].status is ReleaseStatusV1.ACTIVE_NEW,
                state_root=lane.state_root
                if row.lane_id is LaneIdV2.ASSET_TRANSFER
                else row.state_root,
            )
            for row in before.lane_roots
        ),
    )
    occurrence = replace(
        occurrence,
        profile_root=profile.profile_id,
        route_release_id=route.route_release_id,
        command_body_hash=command.command_body_hash,
        pre_state_root=before.state_root,
    )
    context = AssetLaneContextV2(
        profile.authority_epoch, release.release_id, before.state_root, occurrence
    )
    intent = EconomicCommandIntentV2(
        occurrence.chain_id,
        occurrence.deployment_root,
        profile.profile_id,
        command.command_kind,
        command.command_body_hash,
        route.route_release_id,
        occurrence.subject_id,
        occurrence.grant_root,
        occurrence.nonce,
        occurrence.consumed_object_ids,
        occurrence.height,
        occurrence.height,
    )
    candidate = _sign(
        replace(
            base,
            profile=profile,
            policy_registry=policies,
            authorization_registry=authorizations,
            intent=intent,
            envelope=replace(
                base.envelope,
                command_body_bytes=canonical_economic_command_body_bytes_v2(
                    command.command_kind, command
                ),
            ),
        )
    )
    return _recompute_economics(
        _Case(candidate, (context, lane, command, before, after), manifest, b"")
    )


def _recompute_economics(case):
    context, lane, command, before, after = case.inputs
    occurrence = context.occurrence
    assert occurrence is not None
    occurrence = replace(occurrence, pre_state_root=before.state_root)
    context = AssetLaneContextV2(
        context.writer_epoch, context.module_release_id, before.state_root, occurrence
    )
    # Rebind the retained economics to the supplied test metadata. Expected
    # bytes use the leaf coordinator plus independent integer row arithmetic;
    # neither the statement producer nor the new consumer constructs the oracle.
    result = transition_asset_lane_custody_v2(context, lane, command)
    expected: bytes | AssetLaneRejectedV2
    if type(result) is AssetLaneCustodyAcceptedV2:
        _oracle(lane, command, result)
        after = replace(
            before,
            height=occurrence.height,
            balances=result.post_state.transfer_state.balances,
            supplies=tuple(
                row for row in result.post_state.transfer_state.supplies if row.amount_atoms
            ),
            lane_roots=tuple(
                replace(row, state_root=result.post_state.state_root)
                if row.lane_id is LaneIdV2.ASSET_TRANSFER
                else row
                for row in before.lane_roots
            ),
            replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
        )
        expected = canonical_global_bytes_v2(
            {
                "schema": "zenodex/asset-lane-custody-global-statement/v2",
                "module_journal": result.module_journal,
                "global_pre_state_root": before.state_root,
                "global_post_state_root": after.state_root,
            }
        )
    else:
        assert type(result) is AssetLaneRejectedV2
        expected = result
    return replace(case, inputs=(context, lane, command, before, after), expected=expected)


def _profile_with_spot(profile, route_lanes):
    # Synthetic evidence labels test structural compatibility only. They do not
    # qualify Spot or either guest. Rebuild every changed content-derived ID.
    old_spot = profile.lane_registry.release_for(LaneIdV1.SPOT_LIQUIDITY)
    spot = LaneModuleReleaseV1.build(
        **(
            {
                field.name: getattr(old_spot, field.name)
                for field in fields(old_spot)
                if field.name != "release_id"
            }
            | {
                "command_variants": ("asset_transfer",),
                "status": ReleaseStatusV1.ACTIVE_NEW,
                "accepts_new_objects": True,
                "evidence_statuses": _active_evidence(),
            }
        )
    )
    lanes = LaneRegistryV1(
        tuple(
            spot if row.lane_id is LaneIdV1.SPOT_LIQUIDITY else row
            for row in profile.lane_registry.releases
        )
    )
    coordinators = LaneCoordinatorRegistryV1(
        tuple(
            replace(
                row,
                status=ReleaseStatusV1.ACTIVE_NEW,
                accepts_new_objects=True,
                evidence_statuses=_active_evidence(),
            )
            if row.lane_id is LaneIdV1.SPOT_LIQUIDITY
            else row
            for row in profile.lane_coordinator_registry.releases
        )
    )
    route = profile.route_registry.route_for_command("asset_transfer")
    selected = RouteReleaseV1.build(
        **(
            {
                field.name: getattr(route, field.name)
                for field in fields(route)
                if field.name != "route_release_id"
            }
            | {
                "ordered_lanes": route_lanes,
                "module_release_ids": tuple(
                    lanes.release_for(lane).release_id for lane in route_lanes
                ),
                "dependency_roles": tuple(lane.value for lane in route_lanes),
                "port_schema_roots": tuple(OTHER_IMAGE for _ in route_lanes),
            }
        )
    )
    routes = RouteRegistryV1(
        tuple(
            selected if row.command_kind == "asset_transfer" else row
            for row in profile.route_registry.routes
        )
    )
    return EconomicProfileSnapshotV1.build(
        **(
            {
                field.name: getattr(profile, field.name)
                for field in fields(profile)
                if field.name != "profile_id"
            }
            | {
                "lane_registry": lanes,
                "lane_coordinator_registry": coordinators,
                "route_registry": routes,
            }
        )
    )


def _run(case, path, verifier, receipt_bytes=_RECEIPT):
    return pipeline.verify_isolated_authenticated_asset_lane_custody_receipt_v2(
        case.candidate,
        *case.inputs,
        signature_artifact_path=path,
        signature_evidence_manifest=case.manifest,
        signature_timeout_ms=5_000,
        receipt_bytes=receipt_bytes,
        receipt_verifier=verifier,
    )


def _receipt_exchange(monkeypatch, expected):
    requests = []

    def exchange(descriptor, request, timeout_ms):
        assert os.fstat(descriptor).st_size > 0
        assert timeout_ms == 5_000
        assert request[:8] == b"ZDXRV1RQ"
        assert request[8:40] == bytes.fromhex(IMAGE[2:])
        assert type(expected) is bytes
        assert int.from_bytes(request[40:44], "little") == len(expected)
        assert int.from_bytes(request[44:48], "little") == len(_RECEIPT)
        assert request[48:] == expected + _RECEIPT
        requests.append(request)
        return b"ZDXRV1OK" + hashlib.sha256(request).digest() + request[8:40], b"", 0

    # BLS has already imported its own transport function. Patching only this
    # receipt exchange leaves the optional real sealed BLS execution intact.
    monkeypatch.setattr(receipt_transport, "_invoke_v1", exchange)
    return requests


@pytest.mark.parametrize("index", range(5), ids=[case["name"] for case in CASES])
def test_signed_custody_lifecycles_reach_the_exact_receipt_statement(
    protocol_case, monkeypatch, index
):
    _, path, signatures = protocol_case
    case = _case(index)
    requests = _receipt_exchange(monkeypatch, case.expected)
    original = canonical_global_bytes_v2(case.inputs)
    assert _run(case, path, backend()) == case.expected
    assert len(signatures) == len(requests) == 1
    assert canonical_global_bytes_v2(case.inputs) == original


@pytest.mark.parametrize(
    "kind", ("writer_epoch", "custody_module", "other_lane_release", "other_lane_enabled")
)
def test_coherent_foreign_profile_metadata_rejects_before_verifier_io(
    protocol_case, monkeypatch, kind
):
    _, path, signatures = protocol_case
    case = _case()
    context, lane, command, before, after = case.inputs
    if kind == "writer_epoch":
        before = replace(before, writer_epoch=before.writer_epoch + 1)
        context = AssetLaneContextV2(
            before.writer_epoch, context.module_release_id, before.state_root, context.occurrence
        )
    else:
        target = LaneIdV2.ASSET_TRANSFER if kind == "custody_module" else LaneIdV2.SPOT_LIQUIDITY
        if kind == "custody_module":
            lane = AssetLaneCustodyStateV2(
                replace(lane.transfer_state, module_release_id=OTHER_IMAGE),
                replace(lane.origin_registry, module_release_id=OTHER_IMAGE),
                lane.managed_policies,
                lane.custody,
            )
            context = AssetLaneContextV2(
                context.writer_epoch, OTHER_IMAGE, before.state_root, context.occurrence
            )
        before = replace(
            before,
            lane_roots=tuple(
                replace(
                    row,
                    module_release_id=row.module_release_id
                    if kind == "other_lane_enabled"
                    else OTHER_IMAGE,
                    enabled=not row.enabled if kind == "other_lane_enabled" else row.enabled,
                    state_root=lane.state_root if kind == "custody_module" else row.state_root,
                )
                if row.lane_id is target
                else row
                for row in before.lane_roots
            ),
        )
    case = _recompute_economics(replace(case, inputs=(context, lane, command, before, after)))
    assert type(case.expected) is bytes
    requests = _receipt_exchange(monkeypatch, case.expected)
    error = {
        "writer_epoch": "custody profile writer epoch mismatch",
        "custody_module": "custody profile module release mismatch",
        "other_lane_release": "custody profile predecessor lane release mismatch",
        "other_lane_enabled": "custody profile predecessor enabled mismatch",
    }[kind]
    original = canonical_global_bytes_v2(case.inputs)
    with pytest.raises(ValueError, match=error):
        _run(case, path, backend())
    assert signatures == requests == []
    assert canonical_global_bytes_v2(case.inputs) == original


@pytest.mark.parametrize("kind", ("enabled_other_lane", "nonzero_disabled_root"))
def test_unchanged_other_lane_state_remains_compatible(protocol_case, monkeypatch, kind):
    _, path, signatures = protocol_case
    case = _case()
    if kind == "enabled_other_lane":
        profile = _profile_with_spot(case.candidate.profile, (LaneIdV1.ASSET_TRANSFER,))
        case = _case(profile=profile)
    else:
        context, lane, command, before, after = case.inputs
        before = replace(
            before,
            lane_roots=tuple(
                replace(row, state_root=OTHER_IMAGE)
                if row.lane_id is LaneIdV2.SPOT_LIQUIDITY
                else row
                for row in before.lane_roots
            ),
        )
        case = _recompute_economics(replace(case, inputs=(context, lane, command, before, after)))
    assert type(case.expected) is bytes
    requests = _receipt_exchange(monkeypatch, case.expected)
    assert _run(case, path, backend()) == case.expected
    assert len(signatures) == len(requests) == 1


def test_two_lane_route_cannot_be_satisfied_by_a_flat_custody_statement(protocol_case, monkeypatch):
    _, path, signatures = protocol_case
    case = _case()
    profile = _profile_with_spot(
        case.candidate.profile, (LaneIdV1.ASSET_TRANSFER, LaneIdV1.SPOT_LIQUIDITY)
    )
    case = _case(profile=profile)
    assert type(case.expected) is bytes
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(ValueError, match="custody profile route lane name mismatch"):
        _run(case, path, backend())
    assert signatures == requests == []


@pytest.mark.parametrize("kind", ("writer_epoch", "profile_root", "lane_release", "lane_enabled"))
def test_accepted_economics_cannot_change_profile_metadata_in_the_successor(
    protocol_case, monkeypatch, kind
):
    _, path, signatures = protocol_case
    case = _case()
    context, lane, command, before, after = case.inputs
    if kind in ("writer_epoch", "profile_root"):
        after = replace(
            after, **{kind: after.writer_epoch + 1 if kind == "writer_epoch" else OTHER_IMAGE}
        )
        error = "global refinement fixed context changed"
    else:
        after = replace(
            after,
            lane_roots=tuple(
                replace(
                    row,
                    **(
                        {"module_release_id": OTHER_IMAGE}
                        if kind == "lane_release"
                        else {"enabled": not row.enabled}
                    ),
                )
                if row.lane_id is LaneIdV2.SPOT_LIQUIDITY
                else row
                for row in after.lane_roots
            ),
        )
        error = "global refinement lane ownership changed outside migration"
    case = replace(case, inputs=(context, lane, command, before, after))
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(ValueError, match=error):
        _run(case, path, backend())
    assert len(signatures) == 1 and requests == []


@pytest.mark.parametrize("change", ("amount", "origin", "noncanonical_signed_body"))
def test_signed_body_must_equal_the_actual_typed_command_before_io(
    protocol_case, monkeypatch, change
):
    _, path, signatures = protocol_case
    case = _case()
    context, lane, command, before, after = case.inputs
    if change == "noncanonical_signed_body":
        raw = case.candidate.envelope.command_body_bytes + b" "
        candidate = _sign(
            replace(
                case.candidate,
                intent=replace(
                    case.candidate.intent,
                    command_body_hash=hash_economic_command_body_bytes_v2(raw),
                ),
                envelope=replace(case.candidate.envelope, command_body_bytes=raw),
            )
        )
        case = replace(case, candidate=candidate)
    else:
        command = replace(
            command,
            **(
                {"amount_atoms": command.amount_atoms + 1}
                if change == "amount"
                else {"asset_origin_root": OTHER_IMAGE}
            ),
        )
        case = replace(case, inputs=(context, lane, command, before, after))
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(ValueError, match="authenticated command body does not match"):
        _run(case, path, backend())
    assert signatures == requests == []


@pytest.mark.parametrize("amount", (10, 1000), ids=("valid_economics", "rejected_economics"))
def test_foreign_signature_blocks_valid_and_rejected_economics(protocol_case, monkeypatch, amount):
    _, path, signatures = protocol_case
    case = _case(amount=amount)
    assert type(case.expected) is (bytes if amount == 10 else AssetLaneRejectedV2)
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(ValueError, match="command authentication signature rejected"):
        _run(replace(case, candidate=_sign(case.candidate, _SECRET + 1)), path, backend())
    assert len(signatures) == 1
    assert requests == []


def test_authenticated_economic_rejection_is_exact_and_launches_no_receipt(
    protocol_case, monkeypatch
):
    _, path, signatures = protocol_case
    case = _case(amount=1000)
    requests = _receipt_exchange(monkeypatch, case.expected)
    result = _run(case, path, backend())
    assert type(result) is AssetLaneRejectedV2
    assert result.code.value == "INSUFFICIENT_BALANCE"
    assert result == case.expected
    assert result.pre_state_root == result.post_state_root == case.inputs[1].state_root
    assert result.effects.is_empty
    assert len(signatures) == 1 and requests == []


def test_leaf_rejection_precedes_semantic_successor_checks(protocol_case, monkeypatch):
    _, path, signatures = protocol_case
    case = _case(amount=1000)
    context, lane, command, before, after = case.inputs
    after = replace(after, writer_epoch=after.writer_epoch + 1)
    case = replace(case, inputs=(context, lane, command, before, after))
    requests = _receipt_exchange(monkeypatch, case.expected)
    result = _run(case, path, backend())
    assert type(result) is AssetLaneRejectedV2
    assert result == case.expected
    assert result.pre_state_root == result.post_state_root == lane.state_root
    assert result.effects.is_empty
    assert len(signatures) == 1 and requests == []


def test_revoked_profile_rejects_before_verifier_io(protocol_case, monkeypatch):
    _, path, signatures = protocol_case
    case = _case()
    candidate = replace(
        case.candidate, profile=replace(case.candidate.profile, status=ProfileStatusV1.REVOKED)
    )
    case = replace(case, candidate=candidate)
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(ValueError, match="custody profile requires an ACTIVE profile"):
        _run(case, path, backend())
    assert signatures == requests == []


def test_valid_signature_cannot_move_an_existing_claimant(protocol_case, monkeypatch):
    _, path, signatures = protocol_case
    case = _case()
    context, lane, command, before, after = case.inputs
    after = replace(after, liabilities=(replace(after.liabilities[0], owner="mallory"),))
    case = replace(case, inputs=(context, lane, command, before, after))
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(ValueError, match="claimant or custody frame changed"):
        _run(case, path, backend())
    assert len(signatures) == 1 and requests == []


def test_bls_artifact_acquisition_cannot_change_the_owned_custody_inputs(
    protocol_case, monkeypatch
):
    _, path, signatures = protocol_case
    case = _case()
    verifier = backend()
    requests = _receipt_exchange(monkeypatch, case.expected)
    original_read = bls_deployment._read_regular_artifact_bytes_v1

    def mutate_originals_then_read(path):
        context, lane, command, before, after = case.inputs
        object.__setattr__(command, "amount_atoms", command.amount_atoms + 1)
        object.__setattr__(context, "writer_epoch", context.writer_epoch + 1)
        object.__setattr__(lane, "_custody", ())
        object.__setattr__(before, "profile_root", OTHER_IMAGE)
        object.__setattr__(after, "_liabilities", ())
        object.__setattr__(case.candidate.envelope, "signature_bytes", b"\0" * 96)
        object.__setattr__(case.candidate.profile, "status", ProfileStatusV1.REVOKED)
        object.__setattr__(case.candidate.profile, "authority_epoch", context.writer_epoch)
        object.__setattr__(
            case.candidate.profile.lane_registry.releases[0], "release_id", OTHER_IMAGE
        )
        object.__setattr__(verifier, "expected_image_id", OTHER_IMAGE)
        object.__setattr__(verifier, "timeout_ms", 1)
        return original_read(path)

    monkeypatch.setattr(
        bls_deployment, "_read_regular_artifact_bytes_v1", mutate_originals_then_read
    )
    assert _run(case, path, verifier) == case.expected
    assert len(signatures) == len(requests) == 1


@pytest.mark.parametrize(
    "kind",
    (
        "mutable_receipt",
        "verifier_type",
        "verifier_config",
        "missing_occurrence",
        "malformed_global",
    ),
)
def test_structural_input_failures_precede_bls_io(protocol_case, monkeypatch, kind):
    _, path, signatures = protocol_case
    case = _case(amount=1000)
    verifier: object = backend()
    raw: object = _RECEIPT
    if kind == "mutable_receipt":
        raw = bytearray(_RECEIPT)
    elif kind == "verifier_type":
        verifier = object()
    elif kind == "verifier_config":
        object.__setattr__(verifier, "timeout_ms", 0)
    elif kind == "missing_occurrence":
        context, *rest = case.inputs
        context = AssetLaneContextV2(
            context.writer_epoch, context.module_release_id, context.global_pre_state_root, None
        )
        case = replace(case, inputs=(context, *rest))
    else:
        case = replace(case, inputs=(*case.inputs[:3], object(), case.inputs[4]))
    requests = _receipt_exchange(monkeypatch, case.expected)
    error, message = {
        "mutable_receipt": (TypeError, "authenticated custody receipt must be exact bytes"),
        "verifier_type": (TypeError, "authenticated custody receipt requires an exact V1 verifier"),
        "verifier_config": (ValueError, "receipt verifier timeout must be between 1 and 60000 ms"),
        "missing_occurrence": (ValueError, "authenticated custody receipt requires an occurrence"),
        "malformed_global": (
            TypeError,
            "global economic state snapshot requires the exact V2 type",
        ),
    }[kind]
    with pytest.raises(error, match=message):
        _run(case, path, verifier, raw)
    assert signatures == requests == []


def test_receipt_transport_failure_cannot_return_an_authenticated_statement(
    protocol_case, monkeypatch
):
    _, path, signatures = protocol_case
    case = _case()
    requests = _receipt_exchange(monkeypatch, case.expected)
    invoke = receipt_transport._invoke_v1

    def rejected(descriptor, request, timeout):
        invoke(descriptor, request, timeout)
        return b"", b"", 2

    monkeypatch.setattr(receipt_transport, "_invoke_v1", rejected)
    with pytest.raises(receipt_transport.GlobalReceiptVerifierErrorV1) as caught:
        _run(case, path, backend())
    assert caught.value.reason.value == "VERIFICATION_REJECTED"
    assert len(signatures) == len(requests) == 1


def test_native_bls_checks_all_five_custody_vectors_before_protocol_receipts(monkeypatch):
    configured = os.environ.get("ZENODEX_BLS_VERIFIER_TEST_BINARY")
    if not configured:
        pytest.skip("explicit measured native BLS artifact required")
    path = Path(configured)
    artifact = path.read_bytes()
    assert hashlib.sha256(artifact).hexdigest() == _NATIVE_SHA256
    for index in range(5):
        case = _case(index, artifact)
        requests = _receipt_exchange(monkeypatch, case.expected)
        assert _run(case, path, backend()) == case.expected
        with pytest.raises(ValueError, match="command authentication signature rejected"):
            _run(replace(case, candidate=_sign(case.candidate, _SECRET + 1)), path, backend())
        assert len(requests) == 1
