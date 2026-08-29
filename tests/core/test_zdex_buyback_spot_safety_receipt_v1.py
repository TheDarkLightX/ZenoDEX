"""Adversarial evidence for the shadow ZDEX buyback Spot receipt boundary."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

import pytest

from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    ReceiptKindV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    ZERO_ROOT_V1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
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
    canonical_global_bytes_v1,
)
from src.core.zdex_buyback_spot_safety_receipt_v1 import (
    VerifiedZDEXBuybackSpotSafetyPurchaseV1,
    ZDEXBuybackSpotReceiptCandidateV1,
    ZDEXBuybackSpotReceiptEnvelopeV1,
    ZDEXBuybackSpotReceiptRejectCodeV1,
    ZDEXBuybackSpotReceiptRejectedV1,
    ZDEXBuybackSpotSafetyPurchaseJournalV1,
    verify_zdex_buyback_spot_safety_receipt_shadow_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    offset = ordinal * 32
    commands: tuple[str, ...] = ()
    if lane_id in {LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS}:
        commands = (PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,)
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-buyback-spot-test",
        state_schema_root=_root(1_000 + offset),
        command_variants=commands,
        terminal_command_variants=(),
        guest_image_id=_root(1_001 + offset),
        specification_root=_root(1_002 + offset),
        source_root=_root(1_003 + offset),
        toolchain_root=_root(1_004 + offset),
        terminal_coverage_root=_root(1_005 + offset),
        migration_compatibility_root=_root(1_006 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
) -> LaneCoordinatorReleaseV1:
    offset = ordinal * 32
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-buyback-spot-test",
        coordinator_schema_root=_root(2_000 + offset),
        guest_image_id=_root(2_001 + offset),
        specification_root=_root(2_002 + offset),
        source_root=_root(2_003 + offset),
        toolchain_root=_root(2_004 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


@dataclass(frozen=True, slots=True)
class _Fixture:
    candidate: ZDEXBuybackSpotReceiptCandidateV1
    route: RouteReleaseV1
    spot_release: LaneModuleReleaseV1


def _fixture() -> _Fixture:
    policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=_root(10),
        pool_definition_root=_root(11),
        quote_asset_id=_root(12),
        zdex_asset_id=_root(13),
    )
    releases = tuple(
        _lane_release(lane_id, ordinal)
        for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )
    release_by_lane = {release.lane_id: release for release in releases}
    spot_release = release_by_lane[LaneIdV1.SPOT_LIQUIDITY]
    tokenomics_release = release_by_lane[LaneIdV1.ZDEX_TOKENOMICS]
    route = RouteReleaseV1.build(
        semantic_version="1.0.0-shadow-buyback-spot-test",
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS),
        module_release_ids=(spot_release.release_id, tokenomics_release.release_id),
        dependency_roles=(AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1),
        port_schema_roots=(
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        ),
        guest_image_id=_root(20),
        specification_root=_root(21),
        source_root=_root(22),
        toolchain_root=_root(23),
        oracle_policy_root=_root(24),
        issue_burn_policy_root=_root(25),
        max_cycles=2_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )
    policy_registry = EconomicPolicyRegistryV1(
        (
            EconomicPolicyBindingV1(
                ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
                PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                policy.policy_root,
            ),
        )
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=11,
        lane_registry=LaneRegistryV1(releases),
        lane_coordinator_registry=LaneCoordinatorRegistryV1(
            tuple(
                _coordinator_release(lane_id, ordinal)
                for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
            )
        ),
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(30),
        root_image_id=_root(31),
        verifier_registry_root=_root(32),
        migration_registry_root=_root(33),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(34),
        status=ProfileStatusV1.SHADOW,
    )
    oracle_id = "zdex-buyback-oracle"
    oracle_occurrence_root = _root(52)
    global_pre_state = GlobalEconomicStateV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(40),
        writer_epoch=profile.authority_epoch,
        height=76,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            LaneStateRootV1(
                release.lane_id,
                release.release_id,
                False,
                _root(50) if release.lane_id is LaneIdV1.SPOT_LIQUIDITY else _root(5_000 + ordinal),
            )
            for ordinal, release in enumerate(releases, start=1)
        ),
        oracle_occurrences=(
            OracleOccurrenceStateV1(oracle_id, oracle_occurrence_root, 76, True),
        ),
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(40),
        height=77,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        command_body_hash=_root(41),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(42),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=global_pre_state.state_root,
        consumed_object_ids=(),
    )
    expected_spot_pre_root = _root(50)
    journal = ZDEXBuybackSpotSafetyPurchaseJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        global_pre_state_root=occurrence.pre_state_root,
        spot_module_release_id=spot_release.release_id,
        spot_guest_image_id=spot_release.guest_image_id,
        pre_spot_lane_root=expected_spot_pre_root,
        post_spot_lane_root=_root(51),
        pool_id=policy.pool_id,
        pool_definition_root=policy.pool_definition_root,
        quote_asset_id=policy.quote_asset_id,
        zdex_asset_id=policy.zdex_asset_id,
        oracle_policy_root=route.oracle_policy_root,
        oracle_id=oracle_id,
        oracle_occurrence_root=oracle_occurrence_root,
        consensus_height=occurrence.height,
        route_safe_quote_limit_atoms=200,
        quote_amount_in_atoms=125,
        minimum_output_atoms=30,
        purchased_zdex_atoms=40,
    )
    candidate = ZDEXBuybackSpotReceiptCandidateV1(
        profile=profile,
        policy_registry=policy_registry,
        buyback_policy=policy,
        occurrence=occurrence,
        global_pre_state=global_pre_state,
        journal=journal,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"succinct-buyback-spot-receipt",
        ),
    )
    return _Fixture(candidate, route, spot_release)


class _RecordingVerifier:
    def __init__(self) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))


def _assert_reject(
    candidate: ZDEXBuybackSpotReceiptCandidateV1,
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    verifier = _RecordingVerifier()
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        verify_zdex_buyback_spot_safety_receipt_shadow_v1(candidate, verifier)
    assert exc_info.value.code is expected_code
    assert verifier.calls == []


def test_authenticated_journal_uses_exact_release_image_and_canonical_bytes() -> None:
    # Arrange
    fixture = _fixture()
    verifier = _RecordingVerifier()

    # Act
    verified = verify_zdex_buyback_spot_safety_receipt_shadow_v1(
        fixture.candidate,
        verifier,
    )

    # Assert
    assert len(verifier.calls) == 1
    receipt_bytes, image_id, journal_bytes = verifier.calls[0]
    assert receipt_bytes == fixture.candidate.receipt.receipt_bytes
    assert image_id == fixture.spot_release.guest_image_id
    assert journal_bytes == canonical_global_bytes_v1(fixture.candidate.journal)
    assert verified.expected_image_id == fixture.spot_release.guest_image_id
    assert verified.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified.journal == fixture.candidate.journal
    assert verified.journal is not fixture.candidate.journal
    assert verified.journal.terminal_obligations_root == ZERO_ROOT_V1
    assert verified.journal.quote_amount_in_atoms == 125
    assert verified.journal.purchased_zdex_atoms == 40


def test_verified_witness_is_opaque_immutable_and_binding_stable() -> None:
    fixture = _fixture()
    verified = verify_zdex_buyback_spot_safety_receipt_shadow_v1(
        fixture.candidate,
        _RecordingVerifier(),
    )
    binding_root = verified.binding_root
    journal_copy = verified.journal

    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXBuybackSpotSafetyPurchaseV1(object(), object())  # type: ignore[arg-type]
    with pytest.raises(AttributeError, match="immutable"):
        verified._fields = object()  # type: ignore[misc]
    object.__setattr__(journal_copy, "safety_binding_root", _root(90_001))

    assert verified.binding_root == binding_root
    assert verified.journal.safety_binding_root == fixture.candidate.journal.safety_binding_root


def test_canonical_journal_digest_is_fixed() -> None:
    journal_bytes = canonical_global_bytes_v1(_fixture().candidate.journal)

    assert hashlib.sha256(journal_bytes).hexdigest() == (
        "b6ec9db02d47909e2c524733f38ee69fb6b1c9b3aab5662e703eb23db4101f9e"
    )


@pytest.mark.parametrize(
    "receipt_kind",
    (
        ReceiptKindV1.COMPOSITE,
        ReceiptKindV1.CONDITIONAL,
        ReceiptKindV1.FAKE,
        ReceiptKindV1.DEVELOPMENT,
    ),
)
def test_fake_conditional_and_non_succinct_receipts_reject_before_callback(
    receipt_kind: ReceiptKindV1,
) -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(receipt_kind, b"inadmissible"),
    )

    _assert_reject(
        candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.UNSUPPORTED_RECEIPT_KIND,
    )


def test_empty_succinct_receipt_rejects_before_callback() -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""),
    )

    _assert_reject(candidate, ZDEXBuybackSpotReceiptRejectCodeV1.EMPTY_RECEIPT)


def test_callback_failure_creates_no_witness() -> None:
    fixture = _fixture()

    class _FailingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            raise RuntimeError("backend details must not escape")

    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        verify_zdex_buyback_spot_safety_receipt_shadow_v1(
            fixture.candidate,
            _FailingVerifier(),
        )

    assert exc_info.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED
    assert "backend details" not in str(exc_info.value)


def test_callback_non_none_success_shape_rejects() -> None:
    fixture = _fixture()

    class _HostileVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> bool:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            return True

    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        verify_zdex_buyback_spot_safety_receipt_shadow_v1(
            fixture.candidate,
            _HostileVerifier(),  # type: ignore[arg-type]
        )

    assert exc_info.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED


def test_quote_spend_above_authenticated_route_limit_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(fixture.candidate.journal, "quote_amount_in_atoms", 201)

    _assert_reject(
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_purchased_output_below_positive_minimum_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(fixture.candidate.journal, "purchased_zdex_atoms", 29)

    _assert_reject(
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


@pytest.mark.parametrize(
    ("field_name", "hostile_value", "expected_code"),
    (
        ("profile_root", _root(70_001), ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("writer_epoch", 12, ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("route_release_id", _root(70_002), ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("command_occurrence_id", _root(70_003), ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("spot_module_release_id", _root(70_004), ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("spot_guest_image_id", _root(70_005), ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("consensus_height", 78, ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        ("global_pre_state_root", _root(70_006), ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH),
        ("pre_spot_lane_root", _root(70_007), ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH),
        ("pool_id", _root(70_008), ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH),
        ("pool_definition_root", _root(70_009), ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH),
        ("quote_asset_id", _root(70_010), ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH),
        ("zdex_asset_id", _root(70_011), ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH),
        ("oracle_policy_root", _root(70_012), ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH),
        ("oracle_id", "substituted-oracle", ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH),
        ("oracle_occurrence_root", _root(70_013), ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH),
    ),
)
def test_hostile_coordinate_substitution_rejects_before_callback(
    field_name: str,
    hostile_value: object,
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    fixture = _fixture()
    journal = replace(fixture.candidate.journal, **{field_name: hostile_value})
    candidate = replace(fixture.candidate, journal=journal)

    _assert_reject(candidate, expected_code)


@pytest.mark.parametrize(
    ("field_name", "hostile_value"),
    (
        ("global_pre_state_root", _root(80_001)),
        ("pre_spot_lane_root", _root(80_002)),
    ),
)
def test_stale_global_or_spot_pre_root_rejects(
    field_name: str,
    hostile_value: str,
) -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        journal=replace(fixture.candidate.journal, **{field_name: hostile_value}),
    )

    _assert_reject(
        candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
    )


@pytest.mark.parametrize(
    ("oracle_occurrences", "expected_code"),
    (
        ((), ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH),
        (
            (OracleOccurrenceStateV1("zdex-buyback-oracle", _root(52), 76, False),),
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
        ),
        (
            (OracleOccurrenceStateV1("zdex-buyback-oracle", _root(52), 78, True),),
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
        ),
    ),
)
def test_missing_unfinalized_or_future_oracle_rejects_before_callback(
    oracle_occurrences: tuple[OracleOccurrenceStateV1, ...],
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    fixture = _fixture()
    state = replace(
        fixture.candidate.global_pre_state,
        oracle_occurrences=oracle_occurrences,
    )
    occurrence = replace(fixture.candidate.occurrence, pre_state_root=state.state_root)
    journal = replace(
        fixture.candidate.journal,
        global_pre_state_root=state.state_root,
        command_occurrence_id=occurrence.occurrence_id,
    )
    candidate = replace(
        fixture.candidate,
        occurrence=occurrence,
        global_pre_state=state,
        journal=journal,
    )

    _assert_reject(candidate, expected_code)


def test_enabled_spot_lane_rejects_from_shadow_receipt_boundary() -> None:
    fixture = _fixture()
    state = fixture.candidate.global_pre_state
    lanes = tuple(
        replace(row, enabled=True) if row.lane_id is LaneIdV1.SPOT_LIQUIDITY else row
        for row in state.lane_roots
    )
    substituted = replace(state, lane_roots=lanes)
    occurrence = replace(
        fixture.candidate.occurrence,
        pre_state_root=substituted.state_root,
    )
    journal = replace(
        fixture.candidate.journal,
        global_pre_state_root=substituted.state_root,
        command_occurrence_id=occurrence.occurrence_id,
    )

    _assert_reject(
        replace(
            fixture.candidate,
            global_pre_state=substituted,
            occurrence=occurrence,
            journal=journal,
        ),
        ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
    )


def test_stale_post_root_equal_to_pre_root_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(
        fixture.candidate.journal,
        "post_spot_lane_root",
        fixture.candidate.journal.pre_spot_lane_root,
    )

    _assert_reject(
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_safety_binding_root_mutation_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(fixture.candidate.journal, "safety_binding_root", _root(81_001))

    _assert_reject(
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_nonzero_terminal_obligation_mutation_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(
        fixture.candidate.journal,
        "terminal_obligations_root",
        _root(81_002),
    )

    _assert_reject(
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_hostile_scalar_subclass_rejects_without_behavior_or_callback() -> None:
    fixture = _fixture()

    class _ExplodingRoot(str):
        def __eq__(self, other: object) -> bool:
            raise AssertionError("hostile equality executed")

        def __hash__(self) -> int:
            raise AssertionError("hostile hash executed")

    object.__setattr__(
        fixture.candidate.journal,
        "profile_root",
        _ExplodingRoot(fixture.candidate.journal.profile_root),
    )

    _assert_reject(
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_callback_alias_mutation_cannot_rebind_returned_witness() -> None:
    fixture = _fixture()
    candidate = fixture.candidate
    expected_journal = candidate.journal
    expected_image_id = fixture.spot_release.guest_image_id
    expected_receipt_digest = "0x" + hashlib.sha256(candidate.receipt.receipt_bytes).hexdigest()

    class _MutatingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            assert receipt_bytes == b"succinct-buyback-spot-receipt"
            assert expected_image_id == fixture.spot_release.guest_image_id
            assert expected_journal_bytes == canonical_global_bytes_v1(expected_journal)
            object.__setattr__(candidate.journal, "quote_amount_in_atoms", 1)
            object.__setattr__(candidate.profile, "profile_id", _root(99_001))
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated")

    verified = verify_zdex_buyback_spot_safety_receipt_shadow_v1(
        candidate,
        _MutatingVerifier(),
    )

    assert verified.journal.quote_amount_in_atoms == 125
    assert verified.journal.profile_root == expected_journal.profile_root
    assert verified.expected_image_id == expected_image_id
    assert verified.receipt_digest == expected_receipt_digest
