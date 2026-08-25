"""Receipt substitution obligations for the SHADOW perps-margin lane."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import LaneIdV1, canonical_global_bytes_v1
from src.core.lane_composition_receipt_verification_v1 import (
    LaneCompositionReceiptCandidateV1,
    LaneCompositionReceiptEnvelopeV1,
    verify_perps_margin_lane_composition_receipt_v1,
)
from src.core.lane_module_receipt_verification_v1 import (
    LaneModuleReceiptEnvelopeV1,
    PerpsMarginLaneModuleReceiptCandidateV1,
    verify_perps_margin_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    bind_perps_margin_lane_output_to_release_route_v1,
)
from src.core.perps_margin_lane_coordinator_v1 import (
    PerpsMarginLaneCompositionAcceptedV1,
    PerpsMarginLaneCompositionCandidateV1,
    compose_perps_margin_lane_single_v1,
)
from src.core.receipt_backed_perps_margin_lane_composition_v1 import (
    ReceiptBackedPerpsMarginLaneCompositionCandidateV1,
    compose_receipt_backed_perps_margin_lane_single_v1,
)
from tests.core.test_perps_margin_lane_coordinator_v1 import _projection_pair
from tests.core.test_perps_margin_release_receipt_binding_v1 import (
    _binding_candidate,
)


class _RecordingVerifier:
    def __init__(self, *, reject: bool = False) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []
        self.reject = reject

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("test verifier rejected perps lane receipt")


def _structural_fixture():
    fixture, pre, post, context = _projection_pair()
    binding = bind_perps_margin_lane_output_to_release_route_v1(
        _binding_candidate(fixture, fixture.verified_price)
    )
    verified_module = verify_perps_margin_lane_module_receipt_v1(
        PerpsMarginLaneModuleReceiptCandidateV1(
            fixture.profile,
            fixture.policy_registry,
            fixture.market_policy,
            fixture.authenticated_command,
            fixture.module_input,
            fixture.accepted,
            binding,
            fixture.verified_price,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"perps-module-receipt-v1",
            ),
        ),
        _RecordingVerifier(),
    )
    lane_result = compose_perps_margin_lane_single_v1(
        PerpsMarginLaneCompositionCandidateV1(
            context,
            fixture.accepted.module_journal,
            fixture.accepted.private_port,
            pre,
            post,
            fixture.accepted.effects,
        )
    )
    assert isinstance(lane_result, PerpsMarginLaneCompositionAcceptedV1)
    candidate = ReceiptBackedPerpsMarginLaneCompositionCandidateV1(
        fixture.profile,
        fixture.occurrence,
        context,
        fixture.accepted.module_journal,
        fixture.accepted.private_port,
        pre,
        post,
        fixture.accepted.effects,
        verified_module,
    )
    structural = compose_receipt_backed_perps_margin_lane_single_v1(candidate)
    return fixture, candidate, structural, lane_result.lane_journal


def test_given_verified_module_when_perps_lane_receipt_verifies_then_exact_image_and_journal_bind() -> None:
    # Arrange.
    fixture, _, structural, lane_journal = _structural_fixture()
    verifier = _RecordingVerifier()

    # Act.
    verified = verify_perps_margin_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            fixture.profile,
            fixture.occurrence,
            structural,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"perps-coordinator-receipt-v1",
            ),
        ),
        verifier,
    )

    # Assert.
    release = fixture.profile.lane_coordinator_registry.release_for(
        LaneIdV1.PERPS_MARKET
    )
    assert verified.lane_id is LaneIdV1.PERPS_MARKET
    assert verified.expected_image_id == release.guest_image_id
    assert verified.lane_journal_root == lane_journal.journal_root
    assert verifier.calls == [
        (
            b"perps-coordinator-receipt-v1",
            release.guest_image_id,
            canonical_global_bytes_v1(lane_journal),
        )
    ]


@pytest.mark.parametrize(
    ("mutate", "error"),
    (
        (
            lambda candidate: replace(
                candidate,
                coordinator_context=replace(
                    candidate.coordinator_context,
                    profile_root="0x" + "99" * 32,
                ),
            ),
            "coordinator profile mismatch",
        ),
        (
            lambda candidate: replace(
                candidate,
                module_journal=replace(
                    candidate.module_journal,
                    post_lane_root="0x" + "98" * 32,
                ),
            ),
            "verified module journal root mismatch",
        ),
        (
            lambda candidate: replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    balances=(
                        replace(
                            candidate.post_state.balances[0],
                            amount_atoms=(
                                candidate.post_state.balances[0].amount_atoms - 1
                            ),
                        ),
                    ),
                    accounting_locations=tuple(
                        sorted(
                            (
                                *candidate.post_state.accounting_locations,
                                replace(
                                    candidate.post_state.accounting_locations[0],
                                    owner="hidden-location",
                                    custody_domain="treasury",
                                    amount_atoms=1,
                                ),
                            ),
                            key=lambda row: row.key,
                        )
                    ),
                ),
            ),
            "perps lane composition rejected",
        ),
    ),
)
def test_structural_substitutions_reject_before_coordinator_proof(
    mutate,
    error: str,
) -> None:
    _, candidate, _, _ = _structural_fixture()

    with pytest.raises(ValueError, match=error):
        compose_receipt_backed_perps_margin_lane_single_v1(mutate(candidate))


@pytest.mark.parametrize(
    ("receipt_kind", "receipt_bytes", "error"),
    (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"receipt", "succinct"),
    ),
)
def test_coordinator_receipt_shape_rejects_before_verifier(
    receipt_kind: ReceiptKindV1,
    receipt_bytes: bytes,
    error: str,
) -> None:
    fixture, _, structural, lane_journal = _structural_fixture()
    verifier = _RecordingVerifier()

    with pytest.raises(ValueError, match=error):
        verify_perps_margin_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                fixture.profile,
                fixture.occurrence,
                structural,
                lane_journal,
                LaneCompositionReceiptEnvelopeV1(receipt_kind, receipt_bytes),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_lane_journal_substitution_and_verifier_reject_create_no_witness() -> None:
    fixture, _, structural, lane_journal = _structural_fixture()
    pre_verifier = _RecordingVerifier()
    substituted = replace(lane_journal, post_lane_root="0x" + "97" * 32)

    with pytest.raises(ValueError, match="journal post-lane root mismatch"):
        verify_perps_margin_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                fixture.profile,
                fixture.occurrence,
                structural,
                substituted,
                LaneCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"perps-coordinator-receipt-v1",
                ),
            ),
            pre_verifier,
        )
    assert pre_verifier.calls == []

    rejecting = _RecordingVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_perps_margin_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                fixture.profile,
                fixture.occurrence,
                structural,
                lane_journal,
                LaneCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid-receipt",
                ),
            ),
            rejecting,
        )
    assert len(rejecting.calls) == 1
