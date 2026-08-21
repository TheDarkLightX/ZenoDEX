from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    REQUIRED_ACTIVE_EVIDENCE_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    EvidenceStatusV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneWriteV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXPurchaseReceiptCandidateV1,
    verify_zdex_amm_purchase_receipt_v1,
    verify_zdex_burn_receipt_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)
from src.core.zdex_purchase_burn_route_v1 import (
    ZDEXPurchaseBurnRouteCandidateV1,
    ZDEXPurchaseBurnRouteRejectedV1,
    compose_zdex_purchase_burn_route_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-test",
        state_schema_root=_root(100 + offset),
        command_variants=(PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,),
        terminal_command_variants=(),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _route_release(
    spot_release: LaneModuleReleaseV1,
    burn_release: LaneModuleReleaseV1,
    *,
    dependency_roles: tuple[str, str] = ("AMM_PURCHASE_OUTPUT", "ZDEX_BURN_INPUT"),
) -> RouteReleaseV1:
    return RouteReleaseV1.build(
        semantic_version="1.0.0-shadow-test",
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS),
        module_release_ids=(spot_release.release_id, burn_release.release_id),
        dependency_roles=dependency_roles,
        port_schema_roots=(
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        ),
        guest_image_id=_root(500),
        specification_root=_root(501),
        source_root=_root(502),
        toolchain_root=_root(503),
        oracle_policy_root=_root(504),
        issue_burn_policy_root=_root(505),
        max_cycles=2_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _occurrence(route: RouteReleaseV1) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(1),
        height=7,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(2),
        nonce=9,
        profile_root=_root(3),
        pre_state_root=_root(4),
        consumed_object_ids=(),
    )


def _purchase_journal(
    *,
    route: RouteReleaseV1,
    spot_release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    quote_atoms: int = 125,
    purchased_atoms: int = 40,
    quote_owned_atoms: int = 10_000,
    quote_supply_atoms: int = 10_000,
    zdex_owned_atoms: int = 1_000,
    zdex_supply_atoms: int = 1_000,
    effect_plan_root: str = _root(900),
) -> ZDEXAMMPurchaseJournalV1:
    return ZDEXAMMPurchaseJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=11,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        spot_module_release_id=spot_release.release_id,
        issue_burn_policy_root=route.issue_burn_policy_root,
        buyback_budget_occurrence_root=_root(590),
        quote_asset_id=_root(600),
        zdex_asset_id=_root(601),
        quote_source_bucket_id="protocol-fee-buyback-reserve",
        quote_pool_bucket_id="pool:quote",
        zdex_pool_bucket_id="pool:zdex",
        burn_bucket_id="protocol:zdex-burn-transient",
        quote_amount_in_atoms=quote_atoms,
        purchased_zdex_atoms=purchased_atoms,
        quote_source_pre_atoms=1_000,
        quote_source_post_atoms=1_000 - quote_atoms,
        quote_pool_pre_atoms=2_000,
        quote_pool_post_atoms=2_000 + quote_atoms,
        zdex_pool_pre_atoms=500,
        zdex_pool_post_atoms=500 - purchased_atoms,
        burn_bucket_pre_atoms=0,
        burn_bucket_post_atoms=purchased_atoms,
        quote_owned_atoms=quote_owned_atoms,
        quote_supply_atoms=quote_supply_atoms,
        zdex_owned_atoms=zdex_owned_atoms,
        zdex_supply_atoms=zdex_supply_atoms,
        pre_spot_lane_root=_root(610),
        post_spot_lane_root=_root(611),
        effect_plan_root=effect_plan_root,
    )


def _purchase_effects(
    journal: ZDEXAMMPurchaseJournalV1,
) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.quote_source_bucket_id,
                    journal.quote_asset_id,
                    "zenoledger:protocol-buyback",
                    -journal.quote_amount_in_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.quote_pool_bucket_id,
                    journal.quote_asset_id,
                    "zenoledger:amm-pool",
                    journal.quote_amount_in_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.zdex_pool_bucket_id,
                    journal.zdex_asset_id,
                    "zenoledger:amm-pool",
                    -journal.purchased_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.burn_bucket_id,
                    journal.zdex_asset_id,
                    "zenoledger:protocol-burn",
                    journal.purchased_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    conservation = tuple(
        sorted(
            (
                AssetConservationRowV1(
                    journal.quote_asset_id,
                    journal.quote_owned_atoms,
                    journal.quote_owned_atoms,
                    journal.quote_supply_atoms,
                    journal.quote_supply_atoms,
                    0,
                    0,
                ),
                AssetConservationRowV1(
                    journal.zdex_asset_id,
                    journal.zdex_owned_atoms,
                    journal.zdex_owned_atoms,
                    journal.zdex_supply_atoms,
                    journal.zdex_supply_atoms,
                    0,
                    0,
                ),
            ),
            key=lambda row: row.asset,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=conservation,
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                journal.pre_spot_lane_root,
                journal.post_spot_lane_root,
            ),
        ),
        occurrence_consumptions=(journal.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _burn_journal(
    *,
    route: RouteReleaseV1,
    burn_release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    purchase: ZDEXAMMPurchaseJournalV1,
    burned_atoms: int | None = None,
    burn_bucket_id: str | None = None,
    purchase_occurrence_root: str | None = None,
    owned_pre_atoms: int | None = None,
    supply_pre_atoms: int | None = None,
    effect_plan_root: str = _root(901),
) -> ZDEXBurnJournalV1:
    burned = purchase.purchased_zdex_atoms if burned_atoms is None else burned_atoms
    owned_pre = purchase.zdex_owned_atoms if owned_pre_atoms is None else owned_pre_atoms
    supply_pre = purchase.zdex_supply_atoms if supply_pre_atoms is None else supply_pre_atoms
    return ZDEXBurnJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=purchase.writer_epoch,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        tokenomics_module_release_id=burn_release.release_id,
        issue_burn_policy_root=route.issue_burn_policy_root,
        buyback_budget_occurrence_root=purchase.buyback_budget_occurrence_root,
        authorized_quote_input_atoms=purchase.quote_amount_in_atoms,
        purchase_occurrence_root=(
            purchase.journal_root
            if purchase_occurrence_root is None
            else purchase_occurrence_root
        ),
        zdex_asset_id=purchase.zdex_asset_id,
        burn_bucket_id=(
            purchase.burn_bucket_id if burn_bucket_id is None else burn_bucket_id
        ),
        burned_zdex_atoms=burned,
        burn_bucket_pre_atoms=burned,
        burn_bucket_post_atoms=0,
        zdex_owned_pre_atoms=owned_pre,
        zdex_owned_post_atoms=owned_pre - burned,
        zdex_supply_pre_atoms=supply_pre,
        zdex_supply_post_atoms=supply_pre - burned,
        pre_tokenomics_lane_root=_root(620),
        post_tokenomics_lane_root=_root(621),
        effect_plan_root=effect_plan_root,
    )


def _burn_effects(journal: ZDEXBurnJournalV1) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.BURN,
                    "protocol:zdex-supply",
                    journal.zdex_asset_id,
                    "zenoledger:protocol-supply",
                    -journal.burned_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.burn_bucket_id,
                    journal.zdex_asset_id,
                    "zenoledger:protocol-burn",
                    -journal.burned_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=(
            AssetConservationRowV1(
                journal.zdex_asset_id,
                journal.zdex_owned_pre_atoms,
                journal.zdex_owned_post_atoms,
                journal.zdex_supply_pre_atoms,
                journal.zdex_supply_post_atoms,
                0,
                journal.burned_zdex_atoms,
            ),
        ),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                journal.pre_tokenomics_lane_root,
                journal.post_tokenomics_lane_root,
            ),
        ),
        occurrence_consumptions=(journal.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


class _Verifier:
    def __init__(self, *, reject: bool = False) -> None:
        self.reject = reject
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("test verifier rejection")


def _verified_fixture(
    *,
    purchase_overrides: dict[str, object] | None = None,
    burn_overrides: dict[str, object] | None = None,
) -> ZDEXPurchaseBurnRouteCandidateV1:
    spot_release = _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1)
    burn_release = _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2)
    route = _route_release(spot_release, burn_release)
    occurrence = _occurrence(route)
    purchase = _purchase_journal(
        route=route,
        spot_release=spot_release,
        occurrence=occurrence,
    )
    if purchase_overrides:
        normalized_purchase_overrides = dict(purchase_overrides)
        if "quote_amount_in_atoms" in normalized_purchase_overrides:
            quote_atoms = int(normalized_purchase_overrides["quote_amount_in_atoms"])
            normalized_purchase_overrides.setdefault("quote_source_pre_atoms", quote_atoms + 100)
            normalized_purchase_overrides.setdefault("quote_source_post_atoms", 100)
            normalized_purchase_overrides.setdefault("quote_pool_pre_atoms", 2_000)
            normalized_purchase_overrides.setdefault("quote_pool_post_atoms", 2_000 + quote_atoms)
            normalized_purchase_overrides.setdefault("quote_owned_atoms", quote_atoms + 2_100)
            normalized_purchase_overrides.setdefault("quote_supply_atoms", quote_atoms + 2_100)
        if "purchased_zdex_atoms" in normalized_purchase_overrides:
            purchased_atoms = int(normalized_purchase_overrides["purchased_zdex_atoms"])
            normalized_purchase_overrides.setdefault("zdex_pool_pre_atoms", purchased_atoms + 60)
            normalized_purchase_overrides.setdefault("zdex_pool_post_atoms", 60)
            normalized_purchase_overrides.setdefault("burn_bucket_pre_atoms", 0)
            normalized_purchase_overrides.setdefault("burn_bucket_post_atoms", purchased_atoms)
            normalized_purchase_overrides.setdefault("zdex_owned_atoms", purchased_atoms + 100)
            normalized_purchase_overrides.setdefault("zdex_supply_atoms", purchased_atoms + 100)
        purchase = replace(purchase, **normalized_purchase_overrides)
    purchase_effects = _purchase_effects(purchase)
    purchase = replace(purchase, effect_plan_root=purchase_effects.effect_plan_root)
    purchase_effects = _purchase_effects(purchase)
    burn = _burn_journal(
        route=route,
        burn_release=burn_release,
        occurrence=occurrence,
        purchase=purchase,
    )
    if burn_overrides:
        normalized_burn_overrides = dict(burn_overrides)
        if "burned_zdex_atoms" in normalized_burn_overrides:
            burned_atoms = int(normalized_burn_overrides["burned_zdex_atoms"])
            normalized_burn_overrides.setdefault("burn_bucket_pre_atoms", burned_atoms)
            normalized_burn_overrides.setdefault("burn_bucket_post_atoms", 0)
        burn = replace(burn, **normalized_burn_overrides)
    burn_effects = _burn_effects(burn)
    burn = replace(burn, effect_plan_root=burn_effects.effect_plan_root)
    burn_effects = _burn_effects(burn)
    verifier = _Verifier()
    verified_purchase = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            route,
            spot_release,
            occurrence,
            purchase,
            purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"purchase-receipt"),
        ),
        verifier,
    )
    verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1(
            route,
            burn_release,
            occurrence,
            burn,
            burn_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"burn-receipt"),
        ),
        verifier,
    )
    return ZDEXPurchaseBurnRouteCandidateV1(
        route,
        occurrence,
        purchase,
        purchase_effects,
        verified_purchase,
        burn,
        burn_effects,
        verified_burn,
    )


def _assert_no_effect_reject(
    result: ZDEXPurchaseBurnRouteRejectedV1,
    code: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    assert isinstance(result, ZDEXPurchaseBurnRouteRejectedV1)
    assert result.code is code
    assert result.effects.is_empty


def test_verified_purchase_and_burn_compose_one_atomic_effect_plan() -> None:
    candidate = _verified_fixture()

    result = compose_zdex_purchase_burn_route_v1(candidate)

    assert result.effects.occurrence_consumptions == (candidate.occurrence.occurrence_id,)
    assert tuple(row.lane_id for row in result.effects.lane_writes) == (
        LaneIdV1.SPOT_LIQUIDITY,
        LaneIdV1.ZDEX_TOKENOMICS,
    )
    assert sum(
        -row.delta_atoms
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.BURN
    ) == candidate.purchase_journal.purchased_zdex_atoms
    assert all(
        row.principal != candidate.purchase_journal.burn_bucket_id
        for row in result.effects.rows
    )
    assert result.effects.external_outbox_enqueue == ()
    assert result.terminal_obligations_root == ZERO_ROOT_V1


def test_receipt_verifier_sees_exact_release_image_and_canonical_journal() -> None:
    candidate = _verified_fixture()
    verifier = _Verifier()

    verified = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            candidate.route_release,
            _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
            candidate.occurrence,
            candidate.purchase_journal,
            candidate.purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"exact"),
        ),
        verifier,
    )

    assert len(verifier.calls) == 1
    assert verifier.calls[0][1] == _lane_release(
        LaneIdV1.SPOT_LIQUIDITY, 1
    ).guest_image_id
    assert verified.journal_root == candidate.purchase_journal.journal_root
    assert verifier.calls[0][2] == canonical_global_bytes_v1(
        candidate.purchase_journal
    )


def test_verifier_rejection_produces_no_authenticated_purchase_witness() -> None:
    candidate = _verified_fixture()
    verifier = _Verifier(reject=True)

    with pytest.raises(ValueError, match="test verifier rejection"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                candidate.route_release,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"rejected"),
            ),
            verifier,
        )


@pytest.mark.parametrize(
    ("receipt_kind", "receipt_bytes"),
    (
        (ReceiptKindV1.COMPOSITE, b"receipt"),
        (ReceiptKindV1.CONDITIONAL, b"receipt"),
        (ReceiptKindV1.FAKE, b"receipt"),
        (ReceiptKindV1.DEVELOPMENT, b"receipt"),
        (ReceiptKindV1.SUCCINCT, b""),
    ),
)
def test_non_authoritative_receipt_shapes_reject_before_verifier(
    receipt_kind: ReceiptKindV1,
    receipt_bytes: bytes,
) -> None:
    candidate = _verified_fixture()
    verifier = _Verifier()

    with pytest.raises(ValueError, match="succinct receipt|must be nonempty"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                candidate.route_release,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(receipt_kind, receipt_bytes),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_active_release_cannot_cross_the_shadow_only_admission_boundary() -> None:
    candidate = _verified_fixture()
    active_route = replace(
        candidate.route_release,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_objects=True,
        evidence_statuses=tuple(
            sorted(REQUIRED_ACTIVE_EVIDENCE_V1, key=lambda item: item.value)
        ),
    )
    assert all(isinstance(item, EvidenceStatusV1) for item in active_route.evidence_statuses)
    verifier = _Verifier()

    with pytest.raises(ValueError, match="must remain SHADOW"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                active_route,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"active"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_quote_debit_mutant_rejects_before_receipt_verification() -> None:
    candidate = _verified_fixture()
    rows = list(candidate.purchase_effects.rows)
    source_index = next(
        index
        for index, row in enumerate(rows)
        if row.principal == candidate.purchase_journal.quote_source_bucket_id
    )
    rows[source_index] = replace(rows[source_index], delta_atoms=rows[source_index].delta_atoms + 1)
    mutated = replace(candidate.purchase_effects, rows=tuple(rows))
    mutated_journal = replace(
        candidate.purchase_journal,
        effect_plan_root=mutated.effect_plan_root,
    )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="purchase effect rows"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                candidate.route_release,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                mutated_journal,
                mutated,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"mutated"),
            ),
            verifier,
        )
    assert verifier.calls == []


@pytest.mark.parametrize(
    ("burn_overrides", "expected"),
    (
        ({"burned_zdex_atoms": 39, "zdex_owned_post_atoms": 961, "zdex_supply_post_atoms": 961}, ZDEXPurchaseBurnRouteRejectCodeV1.AMOUNT_MISMATCH),
        ({"burn_bucket_id": "protocol:other-burn"}, ZDEXPurchaseBurnRouteRejectCodeV1.BURN_BUCKET_MISMATCH),
        ({"purchase_occurrence_root": _root(999)}, ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_OCCURRENCE_MISMATCH),
        ({"authorized_quote_input_atoms": 124}, ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH),
        ({"buyback_budget_occurrence_root": _root(998)}, ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH),
        ({"zdex_owned_pre_atoms": 999, "zdex_owned_post_atoms": 959}, ZDEXPurchaseBurnRouteRejectCodeV1.CONSERVATION_HISTORY_DISCONNECTED),
        ({"zdex_asset_id": _root(997)}, ZDEXPurchaseBurnRouteRejectCodeV1.ASSET_MISMATCH),
    ),
)
def test_port_substitution_rejects_without_effects(
    burn_overrides: dict[str, object],
    expected: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    candidate = _verified_fixture(burn_overrides=burn_overrides)

    result = compose_zdex_purchase_burn_route_v1(candidate)

    _assert_no_effect_reject(result, expected)


def test_wrong_dependency_role_shape_cannot_authenticate_purchase() -> None:
    candidate = _verified_fixture()
    route = _route_release(
        _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
        _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
        dependency_roles=("WRONG", "ZDEX_BURN_INPUT"),
    )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="dependency roles"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                route,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"wrong-route"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_verified_leaf_for_another_journal_cannot_be_substituted() -> None:
    candidate = _verified_fixture()
    foreign = _verified_fixture(
        burn_overrides={"authorized_quote_input_atoms": 124}
    )
    substituted = replace(candidate, verified_burn=foreign.verified_burn)

    result = compose_zdex_purchase_burn_route_v1(substituted)

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH,
    )


@pytest.mark.parametrize(
    ("burn_overrides", "expected"),
    (
        (
            {"profile_root": _root(996)},
            ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH,
        ),
        (
            {"writer_epoch": 12},
            ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH,
        ),
        (
            {"command_occurrence_id": _root(995)},
            ZDEXPurchaseBurnRouteRejectCodeV1.OCCURRENCE_MISMATCH,
        ),
    ),
)
def test_cross_layer_binding_mutants_reject_with_no_effects(
    burn_overrides: dict[str, object],
    expected: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    candidate = _verified_fixture()
    mutated = replace(
        candidate,
        burn_journal=replace(candidate.burn_journal, **burn_overrides),
    )

    result = compose_zdex_purchase_burn_route_v1(mutated)

    _assert_no_effect_reject(result, expected)


@pytest.mark.parametrize(("quote_atoms", "purchased_atoms"), ((1, 1), (125, 40), (2**63, 2**32)))
def test_bva_positive_amounts_preserve_route_conservation(
    quote_atoms: int,
    purchased_atoms: int,
) -> None:
    candidate = _verified_fixture(
        purchase_overrides={
            "quote_amount_in_atoms": quote_atoms,
            "purchased_zdex_atoms": purchased_atoms,
            "zdex_owned_atoms": purchased_atoms + 100,
            "zdex_supply_atoms": purchased_atoms + 100,
        }
    )

    result = compose_zdex_purchase_burn_route_v1(candidate)

    assert result.effects.asset_conservation[-1].authorized_burn_atoms == purchased_atoms
    assert result.effects.asset_conservation[-1].supply_post_atoms == 100


def test_python_rust_golden_composition_root_is_stable() -> None:
    result = compose_zdex_purchase_burn_route_v1(_verified_fixture())

    assert result.composition_root == (
        "0x9b78d0e13245ed8fe956680fb1141d1542522c6f73bef459b796a62fc15d00d4"
    )


@pytest.mark.parametrize("amount", (2**127, 2**128 - 1))
def test_effect_width_overflow_is_unrepresentable(amount: int) -> None:
    candidate = _verified_fixture()

    with pytest.raises(ValueError, match="signed effect atoms"):
        replace(candidate.purchase_journal, quote_amount_in_atoms=amount)


@pytest.mark.parametrize(
    ("field", "value"),
    (("burn_bucket_pre_atoms", 1), ("burn_bucket_post_atoms", 39)),
)
def test_purchase_cannot_mix_preexisting_inventory_into_burn(
    field: str,
    value: int,
) -> None:
    purchase = _verified_fixture().purchase_journal

    with pytest.raises(ValueError, match="transient burn bucket projection"):
        replace(purchase, **{field: value})


@pytest.mark.parametrize(
    ("field", "value"),
    (("burn_bucket_pre_atoms", 39), ("burn_bucket_post_atoms", 1)),
)
def test_burn_must_drain_the_purchased_output_exactly_once(
    field: str,
    value: int,
) -> None:
    burn = _verified_fixture().burn_journal

    with pytest.raises(ValueError, match="transient bucket projection"):
        replace(burn, **{field: value})


def test_quote_source_cannot_spend_more_than_its_committed_balance() -> None:
    purchase = _verified_fixture().purchase_journal

    with pytest.raises(ValueError, match="quote source projection"):
        replace(purchase, quote_source_pre_atoms=124, quote_source_post_atoms=0)
