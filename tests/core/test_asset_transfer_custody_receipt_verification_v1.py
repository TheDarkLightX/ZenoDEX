"""Custody successor receipt verification: root guards and retained receipt controls.

The receipt doubles record host-port inputs only. The imported command-signature
helper also uses a synthetic accepting backend. These fixtures establish no real
signature, cryptographic receipt, release evidence, or publication authority.
"""

from __future__ import annotations

import inspect
from dataclasses import fields, replace

import pytest

from src.core import lane_module_receipt_verification_v1 as receipt_verification
from src.core.asset_transfer_lane_module_custody_v1 import (
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
)
from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    canonical_global_bytes_v1,
)
from src.core.lane_module_receipt_verification_v1 import (
    MAX_LANE_MODULE_RECEIPT_BYTES_V1,
    AssetTransferLaneModuleReceiptCandidateV1,
    LaneModuleReceiptEnvelopeV1,
    prepare_asset_transfer_lane_module_custody_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    AssetTransferReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    bind_asset_transfer_lane_output_to_custody_release_route_v1,
    bind_asset_transfer_lane_output_to_release_route_v1,
)
from src.integration.lane_module_receipt_verification_v1 import (
    verify_asset_transfer_lane_module_custody_receipt_v1 as verify_custody_receipt_integration_v1,
)
from tests.core import test_asset_transfer_custody_semantics_v1 as semantic_fixtures
from tests.core.lane_module_receipt_fixtures_v1 import (
    verify_asset_transfer_lane_module_custody_receipt_v1,
    verify_asset_transfer_lane_module_receipt_v1,
)
from tests.core.test_asset_transfer_custody_release_route_binding_v1 import (
    _honest_candidate,
)
from tests.core.test_asset_transfer_custody_semantics_v1 import (
    _CustodyGovernanceV1,
    _governance,
    _ReleaseMetadataV1,
    _root,
    _SemanticRootsV1,
)
from tests.core.test_lane_module_release_route_binding_v1 import (
    _authenticate_occurrence_for_test,
    _authentication_policy_registry_v1,
    _authorization_registry_v1,
    _signature_verifier_registry_v1,
)


class _RecordingReceiptVerifierV1:
    """A controlled port double that checks the image and journal it observes."""

    def __init__(
        self,
        *,
        expected_image_id: str | None = None,
        expected_journal_bytes: bytes | None = None,
    ) -> None:
        self.expected_image_id = expected_image_id
        self.expected_journal_bytes = expected_journal_bytes
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if (
            self.expected_image_id is not None
            and expected_image_id != self.expected_image_id
        ):
            raise ValueError("test receipt image mismatch")
        if (
            self.expected_journal_bytes is not None
            and expected_journal_bytes != self.expected_journal_bytes
        ):
            raise ValueError("test receipt journal mismatch")


class _RecomputationCallsV1:
    def __init__(self) -> None:
        self.custody = 0
        self.legacy = 0


def _observe_recomputations(
    monkeypatch: pytest.MonkeyPatch,
) -> _RecomputationCallsV1:
    calls = _RecomputationCallsV1()
    real_custody = receipt_verification.recompute_asset_transfer_lane_module_custody_v1
    real_legacy = receipt_verification._recompute_asset_transfer_lane_module_accepted_v1

    def counted_custody(
        module_input: AssetTransferLaneModuleInputV1,
        accepted: AssetTransferLaneModuleAcceptedV1,
    ) -> AssetTransferLaneModuleAcceptedV1:
        calls.custody += 1
        return real_custody(module_input, accepted)

    def counted_legacy(
        module_input: AssetTransferLaneModuleInputV1,
        accepted: AssetTransferLaneModuleAcceptedV1,
    ) -> tuple[AssetTransferLaneModuleInputV1, AssetTransferLaneModuleAcceptedV1]:
        calls.legacy += 1
        return real_legacy(module_input, accepted)

    monkeypatch.setattr(
        receipt_verification,
        "recompute_asset_transfer_lane_module_custody_v1",
        counted_custody,
    )
    monkeypatch.setattr(
        receipt_verification,
        "_recompute_asset_transfer_lane_module_accepted_v1",
        counted_legacy,
    )
    return calls


def _profile_with_policy_registry(
    governance: _CustodyGovernanceV1,
    *,
    status: ProfileStatusV1 | None = None,
    authority_epoch: int | None = None,
) -> _CustodyGovernanceV1:
    authorization_registry = _authorization_registry_v1(governance.profile.route_registry)
    signature_verifier_registry = _signature_verifier_registry_v1()
    policy_registry = _authentication_policy_registry_v1(
        authorization_registry,
        signature_verifier_registry,
        transfer_policy_registry=governance.asset_policy_registry,
    )
    previous = governance.profile
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=previous.authority_epoch if authority_epoch is None else authority_epoch,
        lane_registry=previous.lane_registry,
        lane_coordinator_registry=previous.lane_coordinator_registry,
        route_registry=previous.route_registry,
        proof_shape_root=previous.proof_shape_root,
        root_image_id=previous.root_image_id,
        verifier_registry_root=previous.verifier_registry_root,
        migration_registry_root=previous.migration_registry_root,
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=previous.terminal_registry_root,
        status=previous.status if status is None else status,
    )
    return replace(governance, profile=profile, policy_registry=policy_registry)


def _receipt_fixture(
    roots: _SemanticRootsV1 | None = None,
    *,
    custody_atoms: int = 7,
) -> tuple[
    _CustodyGovernanceV1,
    AssetTransferLaneModuleReceiptCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
]:
    governance = _profile_with_policy_registry(
        _governance(_SemanticRootsV1() if roots is None else roots)
    )
    occurrence, module_input, accepted, binding_candidate = _honest_candidate(
        governance,
        custody_atoms=custody_atoms,
    )
    bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(binding_candidate)
    authenticated = _authenticate_occurrence_for_test(
        governance.profile,
        occurrence,
        module_input.command,
        policy_registry=governance.policy_registry,
    )
    return (
        governance,
        AssetTransferLaneModuleReceiptCandidateV1(
            governance.profile,
            governance.policy_registry,
            governance.asset_policy_registry,
            authenticated,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"custody-receipt-v1"),
        ),
        bound,
    )


def _coherently_rebuilt_root_mismatch_candidate(
    role: str,
) -> AssetTransferLaneModuleReceiptCandidateV1:
    roots = replace(_SemanticRootsV1(), **{role: _root(8_000 + len(role))})
    governance = _profile_with_policy_registry(_governance(roots))
    occurrence, module_input, accepted, binding_candidate = _honest_candidate(
        governance,
        custody_atoms=0,
    )
    bound = bind_asset_transfer_lane_output_to_release_route_v1(binding_candidate)
    authenticated = _authenticate_occurrence_for_test(
        governance.profile,
        occurrence,
        module_input.command,
        policy_registry=governance.policy_registry,
    )
    return AssetTransferLaneModuleReceiptCandidateV1(
        governance.profile,
        governance.policy_registry,
        governance.asset_policy_registry,
        authenticated,
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"root-mismatch"),
    )


def test_custody_receipt_recomputes_once_and_selects_successor_image_and_journal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Matching roots and nonzero custody dispatch only the recomputed successor journal."""

    governance, candidate, bound = _receipt_fixture(custody_atoms=7)
    release = governance.profile.lane_registry.release_for(bound.lane_id)
    expected_journal = canonical_global_bytes_v1(candidate.accepted.module_journal)
    verifier = _RecordingReceiptVerifierV1(
        expected_image_id=release.guest_image_id,
        expected_journal_bytes=expected_journal,
    )
    calls = _observe_recomputations(monkeypatch)

    verified = verify_asset_transfer_lane_module_custody_receipt_v1(candidate, verifier)

    assert calls.custody == 1
    assert calls.legacy == 0
    assert verifier.calls == [
        (candidate.receipt.receipt_bytes, release.guest_image_id, expected_journal)
    ]
    assert verified.expected_image_id == release.guest_image_id
    assert verified.module_journal_root == candidate.accepted.module_journal.journal_root


@pytest.mark.parametrize("role", ("module", "coordinator", "route"))
def test_custody_semantic_root_mismatches_reject_before_recomputation_or_receipt_port(
    role: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Each coherently rebuilt foreign root kills the selector before host receipt I/O."""

    candidate = _coherently_rebuilt_root_mismatch_candidate(role)
    verifier = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)

    with pytest.raises(ValueError, match=f"custody semantics {role} specification root mismatch"):
        verify_asset_transfer_lane_module_custody_receipt_v1(candidate, verifier)

    assert calls.custody == 0
    assert calls.legacy == 0
    assert verifier.calls == []


def test_custody_receipt_rejects_wrong_supplied_structural_binding_before_recomputation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    governance, candidate, _ = _receipt_fixture()
    foreign_command = replace(candidate.module_input.command, amount_atoms=29)
    foreign_occurrence = replace(
        candidate.authenticated_command.occurrence,
        command_body_hash=foreign_command.command_body_hash,
    )
    foreign_input = replace(
        candidate.module_input,
        context=replace(
            candidate.module_input.context,
            command_occurrence_id=foreign_occurrence.occurrence_id,
        ),
        command=foreign_command,
    )
    foreign_accepted = transition_asset_transfer_lane_module_custody_v1(foreign_input)
    assert type(foreign_accepted) is type(candidate.accepted)
    foreign_bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(
        AssetTransferReleaseRouteBindingCandidateV1(
            governance.profile,
            governance.policy_registry,
            governance.asset_policy_registry,
            foreign_occurrence,
            foreign_input,
            foreign_accepted,
        )
    )
    verifier = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)

    with pytest.raises(ValueError, match="structural binding mismatch"):
        verify_asset_transfer_lane_module_custody_receipt_v1(
            replace(candidate, release_route_binding=foreign_bound),
            verifier,
        )

    assert calls.custody == 0
    assert calls.legacy == 0
    assert verifier.calls == []


@pytest.mark.parametrize("failure", ("image", "journal"))
def test_custody_receipt_port_rejects_wrong_successor_image_or_exact_journal(
    failure: str,
) -> None:
    governance, candidate, bound = _receipt_fixture()
    release = governance.profile.lane_registry.release_for(bound.lane_id)
    journal = canonical_global_bytes_v1(candidate.accepted.module_journal)
    verifier = _RecordingReceiptVerifierV1(
        expected_image_id=_root(9_001) if failure == "image" else release.guest_image_id,
        expected_journal_bytes=(journal + b"wrong") if failure == "journal" else journal,
    )

    with pytest.raises(ValueError, match=f"test receipt {failure} mismatch"):
        verify_asset_transfer_lane_module_custody_receipt_v1(candidate, verifier)

    assert verifier.calls == [(candidate.receipt.receipt_bytes, release.guest_image_id, journal)]


@pytest.mark.parametrize(
    ("receipt_kind", "receipt_bytes", "message"),
    (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ),
)
def test_custody_receipt_envelope_controls_reject_without_receipt_port_call(
    receipt_kind: ReceiptKindV1,
    receipt_bytes: bytes,
    message: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, candidate, _ = _receipt_fixture()
    verifier = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)

    with pytest.raises(ValueError, match=message):
        verify_asset_transfer_lane_module_custody_receipt_v1(
            replace(
                candidate,
                receipt=LaneModuleReceiptEnvelopeV1(receipt_kind, receipt_bytes),
            ),
            verifier,
        )

    assert calls.custody == 1
    assert calls.legacy == 0
    assert verifier.calls == []


def test_zero_custody_dispatches_successor_image_to_the_recording_port() -> None:
    governance, candidate, bound = _receipt_fixture(custody_atoms=0)
    release = governance.profile.lane_registry.release_for(bound.lane_id)
    verifier = _RecordingReceiptVerifierV1(
        expected_image_id=_root(9_002),
        expected_journal_bytes=canonical_global_bytes_v1(candidate.accepted.module_journal),
    )

    with pytest.raises(ValueError, match="test receipt image mismatch"):
        verify_asset_transfer_lane_module_custody_receipt_v1(
            replace(
                candidate,
                receipt=LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"synthetic-image-control"),
            ),
            verifier,
        )

    assert verifier.calls[0][1] == release.guest_image_id
    assert verifier.calls[0][1] != _root(9_002)


@pytest.mark.parametrize("foreign_binding", ("occurrence", "profile", "context"))
def test_foreign_authenticated_binding_rejects_before_recomputation_or_receipt_port(
    foreign_binding: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    governance, candidate, _ = _receipt_fixture()
    occurrence = candidate.authenticated_command.occurrence
    if foreign_binding == "occurrence":
        foreign_occurrence = replace(occurrence, nonce=occurrence.nonce + 1)
        authenticated = _authenticate_occurrence_for_test(
            governance.profile, foreign_occurrence, candidate.module_input.command,
            policy_registry=governance.policy_registry,
        )
        candidate = replace(candidate, authenticated_command=authenticated)
        reason = "lane module release-route command occurrence mismatch"
    elif foreign_binding == "profile":
        foreign_governance = _profile_with_policy_registry(
            governance, authority_epoch=governance.profile.authority_epoch + 1,
        )
        foreign_occurrence = replace(
            occurrence, profile_root=foreign_governance.profile.profile_id,
        )
        authenticated = _authenticate_occurrence_for_test(
            foreign_governance.profile, foreign_occurrence, candidate.module_input.command,
            policy_registry=foreign_governance.policy_registry,
        )
        candidate = replace(candidate, authenticated_command=authenticated)
        reason = "lane module occurrence profile root mismatch"
    else:
        foreign_input = replace(
            candidate.module_input,
            context=replace(candidate.module_input.context, chain_id="foreign-chain"),
        )
        foreign_accepted = transition_asset_transfer_lane_module_custody_v1(foreign_input)
        assert isinstance(foreign_accepted, AssetTransferLaneModuleAcceptedV1)
        candidate = replace(candidate, module_input=foreign_input, accepted=foreign_accepted)
        reason = "lane module release-route chain id mismatch"

    # Each changed value is constructible and the signature helper has completed.
    # The new receipt entry owns this mismatch check before economic recomputation.
    verifier = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)
    with pytest.raises(ValueError, match=f"^{reason}$"):
        verify_asset_transfer_lane_module_custody_receipt_v1(candidate, verifier)
    assert (calls.custody, calls.legacy) == (0, 0)
    assert verifier.calls == []


def _receipt_fixture_with_journal_ceiling(
    monkeypatch: pytest.MonkeyPatch,
    ceiling: int,
) -> AssetTransferLaneModuleReceiptCandidateV1:
    build_release = semantic_fixtures._lane_release

    def bounded_release(
        lane_id: LaneIdV1,
        ordinal: int,
        *,
        active: bool,
        specification_root: str,
        metadata: _ReleaseMetadataV1,
    ) -> LaneModuleReleaseV1:
        release = build_release(
            lane_id, ordinal, active=active,
            specification_root=specification_root, metadata=metadata,
        )
        if lane_id is not LaneIdV1.ASSET_TRANSFER:
            return release
        values = {
            field.name: getattr(release, field.name)
            for field in fields(release) if field.name != "release_id"
        }
        values["max_journal_bytes"] = ceiling
        return LaneModuleReleaseV1.build(**values)

    # Parameterize only the test graph builder. It derives the new module ID,
    # route ID, registries, profile, authenticated occurrence and bound output.
    with monkeypatch.context() as fixture_patch:
        fixture_patch.setattr(semantic_fixtures, "_lane_release", bounded_release)
        _, candidate, _ = _receipt_fixture()
    return candidate


def test_exact_journal_release_ceiling_accepts_and_one_more_byte_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, baseline, _ = _receipt_fixture()
    journal_size = len(canonical_global_bytes_v1(baseline.accepted.module_journal))
    exact = _receipt_fixture_with_journal_ceiling(monkeypatch, journal_size)
    over = _receipt_fixture_with_journal_ceiling(monkeypatch, journal_size - 1)
    assert len(canonical_global_bytes_v1(exact.accepted.module_journal)) == journal_size
    assert len(canonical_global_bytes_v1(over.accepted.module_journal)) == journal_size
    assert exact.profile.profile_id != over.profile.profile_id

    accepted_port = _RecordingReceiptVerifierV1()
    refused_port = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)
    verify_asset_transfer_lane_module_custody_receipt_v1(exact, accepted_port)
    with pytest.raises(
        ValueError, match="^lane module canonical journal exceeds its release byte ceiling$",
    ):
        verify_asset_transfer_lane_module_custody_receipt_v1(over, refused_port)
    assert (calls.custody, calls.legacy) == (2, 0)
    assert len(accepted_port.calls) == 1
    assert refused_port.calls == []


def test_nonactive_profile_rejects_before_custody_recomputation_or_receipt_port(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    governance, candidate, _ = _receipt_fixture()
    stale_governance = _profile_with_policy_registry(
        governance,
        status=ProfileStatusV1.SHADOW,
    )
    verifier = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)

    with pytest.raises(ValueError, match="economic profile is not ACTIVE"):
        verify_asset_transfer_lane_module_custody_receipt_v1(
            replace(
                candidate,
                profile=stale_governance.profile,
                policy_registry=stale_governance.policy_registry,
            ),
            verifier,
        )

    assert calls.custody == 0
    assert calls.legacy == 0
    assert verifier.calls == []


def test_custody_receipt_byte_ceiling_precedes_receipt_port_dispatch() -> None:
    _, candidate, _ = _receipt_fixture()
    at_limit = b"c" * MAX_LANE_MODULE_RECEIPT_BYTES_V1
    at_limit_verifier = _RecordingReceiptVerifierV1()

    verify_asset_transfer_lane_module_custody_receipt_v1(
        replace(
            candidate,
            receipt=LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, at_limit),
        ),
        at_limit_verifier,
    )
    assert len(at_limit_verifier.calls) == 1
    del at_limit_verifier, at_limit

    over_limit = b"c" * (MAX_LANE_MODULE_RECEIPT_BYTES_V1 + 1)
    over_limit_verifier = _RecordingReceiptVerifierV1()
    with pytest.raises(ValueError, match="exceed.*byte ceiling"):
        verify_asset_transfer_lane_module_custody_receipt_v1(
            replace(
                candidate,
                receipt=LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, over_limit),
            ),
            over_limit_verifier,
        )

    assert over_limit_verifier.calls == []


def test_legacy_receipt_verifier_remains_available_for_zero_custody_vector(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    governance, candidate, bound = _receipt_fixture(custody_atoms=0)
    verifier = _RecordingReceiptVerifierV1()
    calls = _observe_recomputations(monkeypatch)

    verified = verify_asset_transfer_lane_module_receipt_v1(candidate, verifier)

    assert calls.custody == 0
    assert calls.legacy == 1
    assert len(verifier.calls) == 1
    assert verified.expected_image_id == governance.profile.lane_registry.release_for(
        bound.lane_id
    ).guest_image_id


def test_core_prepares_and_shell_preserves_the_legacy_custody_receipt_api() -> None:
    assert list(
        inspect.signature(prepare_asset_transfer_lane_module_custody_receipt_v1).parameters
    ) == ["candidate"]
    assert (
        "prepare_asset_transfer_lane_module_custody_receipt_v1"
        in receipt_verification.__all__
    )
    assert "verify_asset_transfer_lane_module_custody_receipt_v1" not in receipt_verification.__all__
    assert list(inspect.signature(verify_custody_receipt_integration_v1).parameters) == [
        "candidate",
        "receipt_verifier",
    ]
