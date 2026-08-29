"""Authority and receipt obligations for the SHADOW perps-margin leaf.

These tests use a synthetic ACTIVE profile solely to exercise fail-closed
selection. They grant no release, mount, settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from src.core.economic_command_authentication_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
    EconomicCommandIntentV1,
    authenticate_economic_command_intent_v1,
    bind_authenticated_intent_to_occurrence_v1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    bind_economic_command_signature_verifier_deployment_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_oracle_occurrence_authority_v1 import (
    GlobalOracleOccurrenceAuthorityCandidateV1,
    GlobalOracleOccurrencePolicyV1,
    verify_global_oracle_occurrence_authority_v1,
)
from src.core.global_oracle_price_occurrence_v1 import (
    GlobalOraclePriceOccurrenceV1,
    VerifiedGlobalOraclePriceV1,
    verify_global_oracle_price_occurrence_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    ZERO_ROOT_V1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    GlobalEconomicStateV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneStateRootV1,
    OracleOccurrenceStateV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_economic_command_body_bytes_v1,
    canonical_global_bytes_v1,
)
from src.core.lane_module_receipt_verification_v1 import (
    LaneModuleReceiptEnvelopeV1,
    PerpsMarginLaneModuleReceiptCandidateV1,
    verify_perps_margin_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    PerpsMarginReleaseRouteBindingCandidateV1,
    bind_perps_margin_lane_output_to_release_route_v1,
)
from src.core.perps_margin_lane_module_v1 import PerpsMarginLaneModuleInputV1
from src.core.perps_margin_module_v1 import transition_perps_margin_v1
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
    PerpsMarginAcceptedV1,
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginCommandV1,
    PerpsMarginContextV1,
    PerpsMarginMarketStatusV1,
    PerpsMarginStateV1,
)
from src.core.perps_market_policy_v1 import (
    PERPS_MARKET_POLICY_KIND_V1,
    PerpsMarketPolicyV1,
)
from tests.core import test_lane_module_release_route_binding_v1 as support

ORACLE_ID = "zenodex.oracle.perps-index-price.v1"
MARKET_ID = "BTC-ZUSD-PERP"
BASE_ASSET = "BTC"
QUOTE_ASSET = "zUSD"
PRICE_E8 = 6_500_000_000_000
MARKET_POLICY = PerpsMarketPolicyV1(
    MARKET_ID,
    BASE_ASSET,
    QUOTE_ASSET,
    ORACLE_ID,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _active_evidence() -> tuple[EvidenceStatusV1, ...]:
    return support._active_evidence()


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    selected = lane_id is LaneIdV1.PERPS_MARKET
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-perps-binding-test",
        state_schema_root=_root(100 + offset),
        command_variants=(
            (
                PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
                PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
                PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
            )
            if selected
            else ()
        ),
        terminal_command_variants=(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,)
        if selected
        else (),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if selected else ReleaseStatusV1.SHADOW,
        accepts_new_objects=selected,
        evidence_statuses=(
            _active_evidence()
            if selected
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
) -> LaneCoordinatorReleaseV1:
    selected = lane_id is LaneIdV1.PERPS_MARKET
    offset = ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-perps-binding-test",
        coordinator_schema_root=_root(300 + offset),
        guest_image_id=_root(301 + offset),
        specification_root=_root(302 + offset),
        source_root=_root(303 + offset),
        toolchain_root=_root(304 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if selected else ReleaseStatusV1.SHADOW,
        accepts_new_objects=selected,
        evidence_statuses=(
            _active_evidence()
            if selected
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _authorization_registry(
    routes: RouteRegistryV1,
) -> EconomicCommandAuthorizationRegistryV1:
    return EconomicCommandAuthorizationRegistryV1(
        tuple(
            sorted(
                (
                    EconomicCommandAuthorizationV1(
                        command_kind=route.command_kind,
                        subject_id="alice",
                        grant_root=_root(7),
                        route_release_id=route.route_release_id,
                        signer_key_id="alice-key-1",
                        signer_public_key="bls12-381-g2:alice-public-key",
                        signature_algorithm="BLS12_381_G2_BASIC_V1",
                        valid_from_height=0,
                        valid_through_height=(1 << 64) - 1,
                        min_nonce=0,
                        max_nonce=(1 << 64) - 1,
                        enabled=True,
                    )
                    for route in routes.routes
                ),
                key=lambda item: item.key,
            )
        )
    )


def _policy_registry(
    authorizations: EconomicCommandAuthorizationRegistryV1,
):
    signature_verifiers = support._signature_verifier_registry_v1()
    bindings = tuple(
        sorted(
            (
                EconomicPolicyBindingV1(policy_kind, command_kind, policy_root)
                for command_kind in sorted(
                    authorization.command_kind
                    for authorization in authorizations.authorizations
                )
                for policy_kind, policy_root in (
                    (
                        ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
                        authorizations.registry_root,
                    ),
                    (
                        ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                        signature_verifiers.registry_root,
                    ),
                    (PERPS_MARKET_POLICY_KIND_V1, MARKET_POLICY.policy_root),
                )
            ),
            key=lambda binding: (binding.policy_kind, binding.command_kind),
        )
    )
    return EconomicPolicyRegistryV1(bindings), signature_verifiers


def _profile() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandAuthorizationRegistryV1,
    object,
    GlobalOracleOccurrencePolicyV1,
]:
    lanes = LaneRegistryV1(
        tuple(
            _lane_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    coordinators = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    release = lanes.release_for(LaneIdV1.PERPS_MARKET)
    oracle_policy = GlobalOracleOccurrencePolicyV1(ORACLE_ID, 1)
    routes = RouteRegistryV1(
        tuple(
            RouteReleaseV1.build(
                semantic_version="1.0.0-perps-binding-test",
                command_kind=command_kind,
                ordered_lanes=(LaneIdV1.PERPS_MARKET,),
                module_release_ids=(release.release_id,),
                dependency_roles=("PERPS_MARGIN",),
                port_schema_roots=(_root(500 + index),),
                guest_image_id=_root(520 + index),
                specification_root=_root(530 + index),
                source_root=_root(540 + index),
                toolchain_root=_root(550 + index),
                oracle_policy_root=oracle_policy.policy_root,
                issue_burn_policy_root=_root(511),
                max_cycles=2_000_000,
                max_journal_bytes=131_072,
                status=ReleaseStatusV1.ACTIVE_NEW,
                accepts_new_objects=True,
                evidence_statuses=_active_evidence(),
            )
            for index, command_kind in enumerate(
                (
                    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
                    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
                    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
                )
            )
        )
    )
    authorizations = _authorization_registry(routes)
    policies, signature_verifiers = _policy_registry(authorizations)
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=7,
        lane_registry=lanes,
        lane_coordinator_registry=coordinators,
        route_registry=routes,
        proof_shape_root=_root(601),
        root_image_id=_root(602),
        verifier_registry_root=_root(603),
        migration_registry_root=_root(604),
        policy_registry_root=policies.registry_root,
        terminal_registry_root=_root(605),
        status=ProfileStatusV1.ACTIVE,
    )
    return profile, authorizations, signature_verifiers, oracle_policy


def _perps_state(*, with_position: bool, price_e8: int) -> PerpsMarginStateV1:
    accounts = ()
    if with_position:
        accounts = (
            PerpsMarginAccountV1(
                "alice-margin",
                "alice",
                1,
                price_e8,
                1_000_000_000_000,
                0,
                PerpsMarginAccountStatusV1.OPEN,
            ),
            PerpsMarginAccountV1(
                "bob-margin",
                "bob",
                -1,
                price_e8,
                1_000_000_000_000,
                0,
                PerpsMarginAccountStatusV1.OPEN,
            ),
        )
    release = _profile()[0].lane_registry.release_for(LaneIdV1.PERPS_MARKET)
    return PerpsMarginStateV1(
        module_release_id=release.release_id,
        market_id=MARKET_ID,
        collateral_asset=QUOTE_ASSET,
        index_price_e8=price_e8,
        maintenance_margin_bps=500,
        depeg_buffer_bps=100,
        max_position_abs=10,
        market_status=PerpsMarginMarketStatusV1.ACTIVE,
        accounts=accounts,
    )


@dataclass(frozen=True, slots=True)
class _Fixture:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    market_policy: PerpsMarketPolicyV1
    occurrence: EconomicCommandOccurrenceV1
    authenticated_command: object
    module_input: PerpsMarginLaneModuleInputV1
    accepted: PerpsMarginAcceptedV1
    verified_price: VerifiedGlobalOraclePriceV1 | None


def _binding_candidate(
    fixture: _Fixture,
    verified_price: VerifiedGlobalOraclePriceV1 | None,
) -> PerpsMarginReleaseRouteBindingCandidateV1:
    return PerpsMarginReleaseRouteBindingCandidateV1(
        fixture.profile,
        fixture.policy_registry,
        fixture.market_policy,
        fixture.occurrence,
        fixture.module_input,
        fixture.accepted,
        verified_price,
    )


def _fixture(
    *,
    with_position: bool,
    price_e8: int = PRICE_E8,
    base_asset: str = BASE_ASSET,
) -> _Fixture:
    profile, authorizations, signature_verifiers, oracle_policy = _profile()
    command_kind = (
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1
        if with_position
        else PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1
    )
    command = PerpsMarginCommandV1(
        command_kind,
        "alice-margin",
        MARKET_ID,
        "alice",
        QUOTE_ASSET,
        10_000,
        1,
    )
    route = profile.route_registry.route_for_command(command_kind)
    payload = GlobalOraclePriceOccurrenceV1(
        ORACLE_ID,
        MARKET_ID,
        base_asset,
        QUOTE_ASSET,
        price_e8,
        40,
    )
    perps_state = _perps_state(with_position=with_position, price_e8=price_e8)
    global_state = GlobalEconomicStateV1(
        chain_id="zeno-perps-binding-test",
        deployment_root=_root(701),
        writer_epoch=profile.authority_epoch,
        height=41,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            LaneStateRootV1(
                lane_id,
                profile.lane_registry.release_for(lane_id).release_id,
                lane_id is LaneIdV1.PERPS_MARKET,
                perps_state.state_root if lane_id is LaneIdV1.PERPS_MARKET else ZERO_ROOT_V1,
            )
            for lane_id in ALL_LANE_IDS_V1
        ),
        oracle_occurrences=(
            OracleOccurrenceStateV1(ORACLE_ID, payload.occurrence_root, 40, True),
        ),
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=global_state.chain_id,
        deployment_root=global_state.deployment_root,
        height=42,
        tx_index=0,
        op_index=0,
        command_kind=command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=route.route_release_id,
        subject_id="alice",
        grant_root=_root(7),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=global_state.state_root,
        consumed_object_ids=(ORACLE_ID,) if with_position else (),
    )
    authorization = authorizations.authorization_for(
        occurrence,
        signer_key_id="alice-key-1",
    )
    policies, _ = _policy_registry(authorizations)
    authenticated_intent = authenticate_economic_command_intent_v1(
        EconomicCommandAuthenticationCandidateV1(
            profile=profile,
            policy_registry=policies,
            authorization_registry=authorizations,
            signature_verifier_registry=signature_verifiers,
            intent=EconomicCommandIntentV1(
                chain_id=occurrence.chain_id,
                deployment_root=occurrence.deployment_root,
                profile_root=occurrence.profile_root,
                command_kind=occurrence.command_kind,
                command_body_hash=occurrence.command_body_hash,
                route_release_id=occurrence.route_release_id,
                subject_id=occurrence.subject_id,
                grant_root=occurrence.grant_root,
                nonce=occurrence.nonce,
                consumed_object_ids=occurrence.consumed_object_ids,
                valid_from_height=0,
                valid_through_height=(1 << 64) - 1,
            ),
            envelope=EconomicCommandAuthenticationEnvelopeV1(
                command_body_bytes=canonical_economic_command_body_bytes_v1(
                    occurrence.command_kind,
                    command,
                ),
                signer_key_id=authorization.signer_key_id,
                signer_public_key=authorization.signer_public_key,
                signature_algorithm=authorization.signature_algorithm,
                signature_bytes=b"test-command-signature-v1",
            ),
        ),
        bind_economic_command_signature_verifier_deployment_v1(
            release=signature_verifiers.releases[0],
            evidence_manifest=support._signature_verifier_manifest_v1(),
            measured_artifact_bytes=support._COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            backend=support._AcceptingCommandSignatureVerifierV1(),
        ),
    )
    authenticated_command = bind_authenticated_intent_to_occurrence_v1(
        authenticated_intent,
        occurrence,
    )
    verified_price = None
    if with_position:
        oracle_authority = verify_global_oracle_occurrence_authority_v1(
            GlobalOracleOccurrenceAuthorityCandidateV1(
                global_state,
                route,
                occurrence,
                oracle_policy,
            )
        )
        verified_price = verify_global_oracle_price_occurrence_v1(
            oracle_authority,
            payload,
        )
    context = PerpsMarginContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        module_release_id=perps_state.module_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        subject_id=occurrence.subject_id,
        grant_root=occurrence.grant_root,
        oracle_authority_root=(
            verified_price.oracle_authority_root if verified_price else ZERO_ROOT_V1
        ),
        oracle_occurrence_root=(
            verified_price.occurrence_root if verified_price else ZERO_ROOT_V1
        ),
        oracle_price_e8=verified_price.price_e8 if verified_price else 0,
    )
    module_input = PerpsMarginLaneModuleInputV1(context, perps_state, command)
    accepted = transition_perps_margin_v1(context, perps_state, command)
    assert isinstance(accepted, PerpsMarginAcceptedV1)
    return _Fixture(
        profile,
        policies,
        MARKET_POLICY,
        occurrence,
        authenticated_command,
        module_input,
        accepted,
        verified_price,
    )


class _RecordingVerifier:
    def __init__(self) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt, expected_image_id, expected_journal_bytes))


def test_position_withdraw_binds_authenticated_command_exact_price_and_receipt() -> None:
    # Arrange.
    fixture = _fixture(with_position=True)
    verifier = _RecordingVerifier()
    binding = bind_perps_margin_lane_output_to_release_route_v1(
        _binding_candidate(fixture, fixture.verified_price)
    )

    # Act.
    verified = verify_perps_margin_lane_module_receipt_v1(
        PerpsMarginLaneModuleReceiptCandidateV1(
            fixture.profile,
            fixture.policy_registry,
            fixture.market_policy,
            fixture.authenticated_command,
            fixture.module_input,
            fixture.accepted,
            binding,
            fixture.verified_price,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"perps-receipt"),
        ),
        verifier,
    )

    # Assert.
    release = fixture.profile.lane_registry.release_for(LaneIdV1.PERPS_MARKET)
    assert verified.expected_image_id == release.guest_image_id
    assert verified.authenticated_command_binding_root == (
        fixture.authenticated_command.binding_root
    )
    assert fixture.module_input.statement_root == (
        "0xc5a148733e1e90151e0b4a2211d88f9da8936b7ba162bc7613664f8535994672"
    )
    assert fixture.accepted.module_journal.journal_root == (
        "0x847cd95b5de91325f8094c210b3ab5d3f6d46f759ccbffb3685c62be8e90dcf6"
    )
    assert verifier.calls == [
        (
            b"perps-receipt",
            release.guest_image_id,
            canonical_global_bytes_v1(fixture.accepted.module_journal),
        )
    ]


def test_caller_selected_price_and_missing_price_authority_reject_before_verifier() -> None:
    fixture = _fixture(with_position=True)
    wrong_price = _fixture(with_position=True, price_e8=PRICE_E8 + 1)
    wrong_context = replace(
        fixture.module_input.context,
        oracle_price_e8=fixture.module_input.context.oracle_price_e8 + 1,
    )
    wrong_input = replace(fixture.module_input, context=wrong_context)
    wrong_accepted = transition_perps_margin_v1(
        wrong_context,
        wrong_input.pre_state,
        wrong_input.command,
    )
    assert not isinstance(wrong_accepted, PerpsMarginAcceptedV1)

    with pytest.raises(ValueError, match="Oracle .* mismatch"):
        bind_perps_margin_lane_output_to_release_route_v1(
            _binding_candidate(fixture, wrong_price.verified_price)
        )
    with pytest.raises(ValueError, match="Oracle price authority"):
        bind_perps_margin_lane_output_to_release_route_v1(
            _binding_candidate(fixture, None)
        )


def test_flat_deposit_rejects_unexpected_oracle_price_authority() -> None:
    flat = _fixture(with_position=False)
    positioned = _fixture(with_position=True)

    binding = bind_perps_margin_lane_output_to_release_route_v1(
        _binding_candidate(flat, None)
    )
    assert binding.lane_id is LaneIdV1.PERPS_MARKET
    with pytest.raises(ValueError, match="unexpected Oracle price authority"):
        bind_perps_margin_lane_output_to_release_route_v1(
            _binding_candidate(flat, positioned.verified_price)
        )


def test_account_close_cannot_alias_unresolved_terminal_closeout_capability() -> None:
    # Arrange
    fixture = _fixture(with_position=False)
    ambiguous_input = replace(
        fixture.module_input,
        command=replace(
            fixture.module_input.command,
            command_kind=PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
            amount_atoms=0,
        ),
    )
    candidate = replace(
        _binding_candidate(fixture, None),
        module_input=ambiguous_input,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="lacks an exact capability binding"):
        bind_perps_margin_lane_output_to_release_route_v1(candidate)


def test_mutated_perps_output_and_wrong_receipt_kind_never_reach_verifier() -> None:
    fixture = _fixture(with_position=True)
    verifier = _RecordingVerifier()
    binding = bind_perps_margin_lane_output_to_release_route_v1(
        _binding_candidate(fixture, fixture.verified_price)
    )
    original_statement_root = fixture.accepted.statement_root
    object.__setattr__(fixture.accepted, "statement_root", _root(999))
    try:
        with pytest.raises(ValueError, match="receipt root|recomputed"):
            bind_perps_margin_lane_output_to_release_route_v1(
                _binding_candidate(fixture, fixture.verified_price)
            )
    finally:
        object.__setattr__(
            fixture.accepted,
            "statement_root",
            original_statement_root,
        )
    with pytest.raises(ValueError, match="succinct"):
        verify_perps_margin_lane_module_receipt_v1(
            PerpsMarginLaneModuleReceiptCandidateV1(
                fixture.profile,
                fixture.policy_registry,
                fixture.market_policy,
                fixture.authenticated_command,
                fixture.module_input,
                fixture.accepted,
                binding,
                fixture.verified_price,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.COMPOSITE, b"receipt"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_release_binding_candidate_rejects_untyped_parallel_inputs() -> None:
    fixture = _fixture(with_position=True)
    with pytest.raises(TypeError, match="route candidate must have the exact type"):
        bind_perps_margin_lane_output_to_release_route_v1(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="requires exact typed inputs"):
        PerpsMarginReleaseRouteBindingCandidateV1(
            fixture.profile,
            fixture.policy_registry,
            fixture.market_policy,
            fixture.occurrence,
            fixture.module_input,
            object(),  # type: ignore[arg-type]
            fixture.verified_price,
        )
