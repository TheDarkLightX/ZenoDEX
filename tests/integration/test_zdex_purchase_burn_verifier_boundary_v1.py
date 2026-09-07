"""Boundary evidence for the legacy purchase V1/V2 and burn V1 receipt extraction.

Core prepares one exact detached subject per leaf (the 15 marker fields plus
the exact receipt, module image and canonical journal bytes) and calls no
verifier; the integration shell executes exactly that subject on the
caller-supplied verifier and mints the existing non-authoritative markers from
the executed subject only.  The governed paths own the exact typed authority
head before its checked use and before I/O and never read a caller-held head,
profile or policy alias after the callback.  Every verifier here is a
deterministic recorder, never cryptographic evidence, and nothing below grants
publication or production authority.  The ownership repair is evidence against
callback-retained aliases inside one honest process, not against a compromised
Python process or OS.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
from collections.abc import Callable
from dataclasses import dataclass, replace
from dataclasses import fields as dataclass_fields
from pathlib import Path
from typing import Any, cast

import pytest

import src.core.economic_receipt_verifier_deployment_v1 as deployment
import src.core.zdex_purchase_burn_receipt_preparation_v1 as prep
import src.core.zdex_purchase_burn_receipt_verification_v1 as core
import src.integration.zdex_fee_allocation_receipt_verification_v1 as fee_shell
import src.integration.zdex_purchase_burn_receipt_verification_v1 as shell
import src.integration.zdex_tokenomics_lane_receipt_verification_v1 as tokenomics_shell
from src.core.global_economic_authority_head_v1 import GlobalEconomicAuthorityStatusV1
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    REQUIRED_ACTIVE_EVIDENCE_V1,
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
)
from src.core.zdex_atomic_buyback_v1 import (
    ZDEXAtomicBuybackCandidateV1,
    ZDEXAtomicBuybackPendingV1,
    prepare_zdex_atomic_buyback_v1,
)
from src.core.zdex_buyback_price_authority_v1 import ZDEXBuybackPriceAuthorityRejectedV1
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from src.core.zdex_fee_allocation_v1 import candidate_zdex_fee_allocation_policy_v1
from src.core.zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
    purchase_effects_v2,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEXAMMPurchaseJournalV2,
    ZDEXBuybackExecutionPolicyV1,
)
from tests.core.test_zdex_atomic_buyback_v1 import _candidate
from tests.core.test_zdex_atomic_buyback_v1 import _purchase_journal as _legacy_purchase_journal
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import _Fixture, _price_occurrence
from tests.core.test_zdex_purchase_burn_route_v1 import (
    _allocation_route_release,
    _burn_journal,
    _governed_shadow_profile,
    _HostileRoot,
    _lane_release,
    _occurrence,
    _purchase_journal,
    _root,
    _route_release,
    _verified_fixture,
)
from tests.core.test_zdex_purchase_burn_route_v2 import _global_pre_state

REPO_ROOT = Path(__file__).resolve().parents[2]
_PREPARATION_MODULE = "src/core/zdex_purchase_burn_receipt_preparation_v1.py"
_LEGACY_CORE_MODULE = "src/core/zdex_purchase_burn_receipt_verification_v1.py"
_SHELL_MODULE = "src/integration/zdex_purchase_burn_receipt_verification_v1.py"
_CONSUMER_SHELL_MODULES = (
    "src/integration/zdex_fee_allocation_receipt_verification_v1.py",
    "src/integration/zdex_tokenomics_lane_receipt_verification_v1.py",
)
_EFFECT_IMPORT_ROOTS = frozenset(
    {"threading", "weakref", "os", "sys", "time", "datetime", "random", "pathlib", "importlib"}
)
_MOVED_NAMES = (
    "verify_zdex_amm_purchase_receipt_v1",
    "verify_zdex_amm_purchase_receipt_v2",
    "verify_zdex_burn_receipt_v1",
    "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
    "verify_governed_zdex_amm_purchase_receipt_shadow_v2",
    "verify_governed_zdex_burn_receipt_shadow_v1",
    "ZDEXLaneSuccinctReceiptVerifierV1",
    "_ProfileLaneReceiptVerifierV1",
)
_RETAINED_CORE_NAMES = (
    "ZDEXLaneReceiptEnvelopeV1",
    "ZDEXPurchaseReceiptCandidateV1",
    "ZDEXPurchaseReceiptCandidateV2",
    "ZDEXBurnReceiptCandidateV1",
    "VerifiedZDEXAMMPurchaseV1",
    "VerifiedZDEXAMMPurchaseV2",
    "GovernedVerifiedZDEXAMMPurchaseV2",
    "VerifiedZDEXBurnV1",
    "_VerifiedZDEXLaneFieldsV1",
    "_GovernedVerifiedZDEXAMMPurchaseFieldsV2",
    "_require_current_shadow_authority_v1",
)
_MARKER_FIELD_NAMES = (
    "route_release_id",
    "module_release_id",
    "command_occurrence_id",
    "profile_root",
    "writer_epoch",
    "journal_root",
    "journal_digest",
    "effect_plan_root",
    "expected_image_id",
    "receipt_digest",
    "receipt_kind",
    "authority_head_root",
    "verifier_binding_root",
    "price_authority_root",
    "price_safety_policy_root",
)
# Fixed vectors captured on the pre-extraction tree (base 590028906) with the
# retained fixtures and recorders.  The extraction must reproduce them exactly.
_PURCHASE_V1_BINDING_ROOT_PIN = (
    "0xf3a17607641eb20e5c0aed8a6e4600629ac0786ae56628b18052316e09549647"
)
_BURN_V1_BINDING_ROOT_PIN = "0xf7085b8b832b80f63deae8d9f0b0bda67542be1c7b0b30801838e38ca8b63957"
_PURCHASE_V2_LEAF_BINDING_ROOT_PIN = (
    "0x4c28917c9a832f1402e19a18575ad6c2d1b689adcb99f598978d2138b10e0466"
)
_PURCHASE_V2_PRICE_AUTHORITY_ROOT_PIN = (
    "0x15ecdaa5390b408ee4439e5f96491fbddf6f1f339249c8135af787b933b7b421"
)
_GOVERNED_PURCHASE_V1_BINDING_ROOT_PIN = (
    "0x5434a9e25aa22ab07a8e576ae61ca3607cd0eb09caf9f4ceeb9df89da71a4643"
)
_GOVERNED_PURCHASE_V2_BINDING_ROOT_PIN = (
    "0x5df326676f022fea974af89269a4bbaa36d51bc16c621f779ef9c611625c2464"
)
_GOVERNED_BURN_V1_BINDING_ROOT_PIN = (
    "0xda674c5506e087ad5c94befd11cd7fdcb31f5a73cedb82550263d74d852475e6"
)
_GOVERNED_HEAD_ROOT_PIN = "0xa013d69a3b516cbfd7bdf6b0b8aa985590b42e332468f154cc4056883aaa5635"
_GOVERNED_VERIFIER_BINDING_ROOT_PIN = (
    "0x7cbc86eadc10c8154ac4ef54f93d7e58716400471e4afd7182e7d1b4bdaffcdd"
)
_GOVERNED_POLICY_REGISTRY_ROOT_PIN = (
    "0x8922a39e04250c7b3bffc5830655fbfc05bc31fcad6dc0107c57bab0429cb06f"
)
_PURCHASE_V1_JOURNAL_LEN_PIN = 1878
_BURN_V1_JOURNAL_LEN_PIN = 1621
_PURCHASE_V2_JOURNAL_LEN_PIN = 2330


def _digest(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


def _envelope(receipt_bytes: bytes) -> core.ZDEXLaneReceiptEnvelopeV1:
    return core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes)


class _RecordingVerifier:
    """Reference recorder: returns a caller-chosen value, optionally raises.

    The return annotation is deliberately ``Any``: the generic port's return
    value is ignored by contract, and this recorder replies with off-contract
    values (``False``, ``0``, objects) to observe exactly that.
    """

    def __init__(self, *, result: object = None, reject: bool = False) -> None:
        self.result = result
        self.reject = reject
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> Any:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("boundary verifier rejection")
        return self.result


# --- fixtures ----------------------------------------------------------------


def _purchase_v1_candidate(receipt_bytes: bytes = b"purchase-receipt") -> Any:
    route = _verified_fixture()
    return core.ZDEXPurchaseReceiptCandidateV1(
        route.route_release,
        _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
        route.occurrence,
        route.purchase_journal,
        route.purchase_effects,
        _envelope(receipt_bytes),
    )


def _burn_v1_candidate(receipt_bytes: bytes = b"burn-receipt") -> Any:
    route = _verified_fixture()
    return core.ZDEXBurnReceiptCandidateV1(
        route.route_release,
        _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
        route.occurrence,
        route.burn_journal,
        route.burn_effects,
        _envelope(receipt_bytes),
    )


def _governed_purchase_v2_candidate(
    fixture: _Fixture,
    candidate: ZDEXAtomicBuybackCandidateV1,
    receipt_bytes: bytes = b"purchase-v2-receipt",
) -> core.ZDEXPurchaseReceiptCandidateV2:
    return core.ZDEXPurchaseReceiptCandidateV2(
        route_release=fixture.route,
        module_release=fixture.spot_release,
        occurrence=fixture.candidate.occurrence,
        pre_state=fixture.candidate.global_pre_state,
        execution_policy=fixture.candidate.buyback_policy,
        price_policy=fixture.candidate.price_policy,
        price_occurrence=_price_occurrence(fixture),
        journal=candidate.purchase_journal,
        effects=candidate.purchase_effects,
        receipt=_envelope(receipt_bytes),
    )


def _purchase_v2_candidate(receipt_bytes: bytes = b"purchase-v2-receipt") -> Any:
    fixture, candidate = _candidate()
    return _governed_purchase_v2_candidate(fixture, candidate, receipt_bytes)


def _governed_purchase_v1_candidate(
    fixture: _Fixture,
    candidate: ZDEXAtomicBuybackCandidateV1,
    receipt_bytes: bytes = b"legacy",
    *,
    writer_epoch: int | None = None,
) -> core.ZDEXPurchaseReceiptCandidateV1:
    journal = _legacy_purchase_journal(fixture, candidate.verified_spend)
    if writer_epoch is not None:
        journal = replace(journal, writer_epoch=writer_epoch)
        journal = replace(journal, effect_plan_root=purchase_effects_v1(journal).effect_plan_root)
    return core.ZDEXPurchaseReceiptCandidateV1(
        fixture.route,
        fixture.spot_release,
        fixture.candidate.occurrence,
        journal,
        purchase_effects_v1(journal),
        _envelope(receipt_bytes),
    )


def _governed_burn_candidate(
    fixture: _Fixture,
    candidate: ZDEXAtomicBuybackCandidateV1,
    receipt_bytes: bytes = b"burn-receipt",
    *,
    writer_epoch: int | None = None,
) -> core.ZDEXBurnReceiptCandidateV1:
    pending = prepare_zdex_atomic_buyback_v1(candidate)
    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)
    journal = pending.burn.journal
    if writer_epoch is not None:
        journal = replace(journal, writer_epoch=writer_epoch)
        journal = replace(journal, effect_plan_root=burn_effects_v1(journal).effect_plan_root)
    return core.ZDEXBurnReceiptCandidateV1(
        fixture.route,
        fixture.candidate.profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        fixture.candidate.occurrence,
        journal,
        burn_effects_v1(journal),
        _envelope(receipt_bytes),
    )


def _governed_kwargs(fixture: _Fixture) -> dict[str, Any]:
    return {
        "profile": fixture.candidate.profile,
        "authority_head": fixture.authority_head,
        "receipt_verifier": fixture.receipt_verifier,
    }


_GOVERNED_SHAPES = ("purchase_v1", "purchase_v2", "burn_v1")


def _governed_run(
    fixture: _Fixture,
    candidate: ZDEXAtomicBuybackCandidateV1,
    shape: str,
    receipt_bytes: bytes = b"governed",
) -> tuple[Any, Callable[..., Any], dict[str, Any]]:
    """Return (candidate, governed entry point, keyword arguments) for one shape."""

    kwargs = _governed_kwargs(fixture)
    if shape == "purchase_v1":
        return (
            _governed_purchase_v1_candidate(fixture, candidate, receipt_bytes),
            shell.verify_governed_zdex_amm_purchase_receipt_shadow_v1,
            kwargs,
        )
    if shape == "purchase_v2":
        kwargs["policy_registry"] = fixture.candidate.policy_registry
        return (
            _governed_purchase_v2_candidate(fixture, candidate, receipt_bytes),
            shell.verify_governed_zdex_amm_purchase_receipt_shadow_v2,
            kwargs,
        )
    return (
        _governed_burn_candidate(fixture, candidate, receipt_bytes),
        shell.verify_governed_zdex_burn_receipt_shadow_v1,
        kwargs,
    )


def _expected_fields(
    candidate: Any,
    *,
    price_authority_root: str = ZERO_ROOT_V1,
    price_safety_policy_root: str = ZERO_ROOT_V1,
) -> core._VerifiedZDEXLaneFieldsV1:
    """Independent derivation of the 15 marker fields from candidate facts."""

    return core._VerifiedZDEXLaneFieldsV1(
        candidate.route_release.route_release_id,
        candidate.module_release.release_id,
        candidate.occurrence.occurrence_id,
        candidate.occurrence.profile_root,
        candidate.journal.writer_epoch,
        candidate.journal.journal_root,
        _digest(canonical_global_bytes_v1(candidate.journal)),
        candidate.effects.effect_plan_root,
        candidate.module_release.guest_image_id,
        _digest(candidate.receipt.receipt_bytes),
        candidate.receipt.receipt_kind,
        ZERO_ROOT_V1,
        ZERO_ROOT_V1,
        price_authority_root,
        price_safety_policy_root,
    )


def _expected_request(candidate: Any) -> tuple[bytes, str, bytes]:
    return (
        candidate.receipt.receipt_bytes,
        candidate.module_release.guest_image_id,
        canonical_global_bytes_v1(candidate.journal),
    )


def _marker_fields(marker: object) -> tuple[object, ...]:
    return tuple(getattr(marker, name) for name in _MARKER_FIELD_NAMES)


def _record_fields(fields: core._VerifiedZDEXLaneFieldsV1) -> tuple[object, ...]:
    return tuple(getattr(fields, name) for name in _MARKER_FIELD_NAMES)


def _prepared_facts(prepared: Any) -> tuple[object, ...]:
    return (
        _record_fields(prepared.verified_fields),
        prepared.receipt_bytes,
        prepared.expected_image_id,
        prepared.expected_journal_bytes,
    )


@dataclass(frozen=True)
class _Family:
    label: str
    candidate: Callable[[], Any]
    prepare: Callable[[Any], Any]
    snapshot: Callable[[Any], Any]
    build: Callable[[Any], Any]
    execute: Callable[[Any, Any], Any]
    verify: Callable[[Any, Any], Any]
    prepared_type: type[Any]
    marker_type: type[Any]
    binding_root_pin: str
    journal_len_pin: int
    name: str

    def expected_fields(self, candidate: Any) -> core._VerifiedZDEXLaneFieldsV1:
        if self.label != "purchase_v2":
            return _expected_fields(candidate)
        return _expected_fields(
            candidate,
            price_authority_root=_PURCHASE_V2_PRICE_AUTHORITY_ROOT_PIN,
            price_safety_policy_root=candidate.price_policy.policy_root,
        )


_FAMILIES = {
    "purchase_v1": _Family(
        "purchase_v1",
        _purchase_v1_candidate,
        prep.prepare_zdex_amm_purchase_receipt_v1,
        prep.snapshot_prepared_zdex_amm_purchase_receipt_v1,
        prep._build_verified_zdex_amm_purchase_v1,
        shell._execute_prepared_zdex_amm_purchase_receipt_v1,
        shell.verify_zdex_amm_purchase_receipt_v1,
        prep.PreparedZDEXAMMPurchaseReceiptV1,
        core.VerifiedZDEXAMMPurchaseV1,
        _PURCHASE_V1_BINDING_ROOT_PIN,
        _PURCHASE_V1_JOURNAL_LEN_PIN,
        "prepared ZDEX purchase",
    ),
    "purchase_v2": _Family(
        "purchase_v2",
        _purchase_v2_candidate,
        prep.prepare_zdex_amm_purchase_receipt_v2,
        prep.snapshot_prepared_zdex_amm_purchase_receipt_v2,
        prep._build_verified_zdex_amm_purchase_v2,
        shell._execute_prepared_zdex_amm_purchase_receipt_v2,
        shell.verify_zdex_amm_purchase_receipt_v2,
        prep.PreparedZDEXAMMPurchaseReceiptV2,
        core.VerifiedZDEXAMMPurchaseV2,
        _PURCHASE_V2_LEAF_BINDING_ROOT_PIN,
        _PURCHASE_V2_JOURNAL_LEN_PIN,
        "prepared ZDEX purchase V2",
    ),
    "burn_v1": _Family(
        "burn_v1",
        _burn_v1_candidate,
        prep.prepare_zdex_burn_receipt_v1,
        prep.snapshot_prepared_zdex_burn_receipt_v1,
        prep._build_verified_zdex_burn_v1,
        shell._execute_prepared_zdex_burn_receipt_v1,
        shell.verify_zdex_burn_receipt_v1,
        prep.PreparedZDEXBurnReceiptV1,
        core.VerifiedZDEXBurnV1,
        _BURN_V1_BINDING_ROOT_PIN,
        _BURN_V1_JOURNAL_LEN_PIN,
        "prepared ZDEX burn",
    ),
}
_FAMILY_LABELS = tuple(_FAMILIES)


def _tight_lane_release(
    lane_id: LaneIdV1, ordinal: int, max_journal_bytes: int
) -> LaneModuleReleaseV1:
    base = _lane_release(lane_id, ordinal)
    values = {
        field.name: getattr(base, field.name)
        for field in dataclass_fields(base)
        if field.name != "release_id"
    }
    values["max_journal_bytes"] = max_journal_bytes
    release = LaneModuleReleaseV1.build(**values)
    assert type(release) is LaneModuleReleaseV1
    return release


def _v1_leaves_with_ceilings(
    *,
    spot_max_journal_bytes: int,
    burn_max_journal_bytes: int,
    purchase_receipt: bytes = b"purchase-receipt",
    burn_receipt: bytes = b"burn-receipt",
) -> tuple[core.ZDEXPurchaseReceiptCandidateV1, core.ZDEXBurnReceiptCandidateV1]:
    """Rebuild both V1 leaves under releases with only their ceilings changed."""

    spot = _tight_lane_release(LaneIdV1.SPOT_LIQUIDITY, 1, spot_max_journal_bytes)
    burn = _tight_lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2, burn_max_journal_bytes)
    route = _route_release(spot, burn)
    policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=_root(602),
        pool_definition_root=_root(603),
        quote_asset_id=_root(600),
        zdex_asset_id=_root(601),
    )
    profile, _ = _governed_shadow_profile(
        spot_release=spot,
        tokenomics_release=burn,
        buyback_route=route,
        allocation_route=_allocation_route_release(burn),
        policy_root=candidate_zdex_fee_allocation_policy_v1().policy_root,
        buyback_execution_policy_root=policy.policy_root,
    )
    occurrence = _occurrence(route, profile)
    purchase = _purchase_journal(
        route=route, spot_release=spot, occurrence=occurrence, buyback_pool_id=policy.pool_id
    )
    purchase = replace(purchase, effect_plan_root=purchase_effects_v1(purchase).effect_plan_root)
    burn_journal = _burn_journal(
        route=route, burn_release=burn, occurrence=occurrence, purchase=purchase
    )
    burn_journal = replace(
        burn_journal, effect_plan_root=burn_effects_v1(burn_journal).effect_plan_root
    )
    return (
        core.ZDEXPurchaseReceiptCandidateV1(
            route, spot, occurrence, purchase, purchase_effects_v1(purchase), _envelope(purchase_receipt)
        ),
        core.ZDEXBurnReceiptCandidateV1(
            route, burn, occurrence, burn_journal, burn_effects_v1(burn_journal), _envelope(burn_receipt)
        ),
    )


def _v2_release_set(
    spot_max_journal_bytes: int,
) -> tuple[Any, Any, Any, ZDEXBuybackExecutionPolicyV1, ZDEXBuybackPriceSafetyPolicyV1, Any]:
    spot = _tight_lane_release(LaneIdV1.SPOT_LIQUIDITY, 1, spot_max_journal_bytes)
    burn = _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2)
    execution_policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=_root(602),
        pool_definition_root=_root(603),
        quote_asset_id=_root(600),
        zdex_asset_id=_root(601),
    )
    price_policy = ZDEXBuybackPriceSafetyPolicyV1(
        oracle_id="zdex-buyback-oracle",
        maximum_oracle_age_blocks=3,
        minimum_quote_reserve_atoms=500,
        minimum_zdex_reserve_atoms=500,
        maximum_pool_oracle_deviation_bps=500,
        maximum_execution_impact_bps=1_300,
        maximum_oracle_execution_deviation_bps=1_500,
        maximum_quote_reserve_spend_bps=2_000,
    )
    route = _route_release(spot, burn, oracle_policy_root=price_policy.policy_root)
    profile, _ = _governed_shadow_profile(
        spot_release=spot,
        tokenomics_release=burn,
        buyback_route=route,
        allocation_route=_allocation_route_release(burn),
        policy_root=candidate_zdex_fee_allocation_policy_v1().policy_root,
        buyback_execution_policy_root=execution_policy.policy_root,
        price_safety_policy_root=price_policy.policy_root,
    )
    return spot, burn, route, execution_policy, price_policy, profile


def _v2_ceiling_occurrence(
    pre_state: GlobalEconomicStateV1,
    route: RouteReleaseV1,
    profile: EconomicProfileSnapshotV1,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=77,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        command_body_hash=_root(3),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(2),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=pre_state.state_root,
        consumed_object_ids=(),
    )


def _v2_leaf_with_spot_ceiling(
    spot_max_journal_bytes: int,
    receipt_bytes: bytes = b"purchase-v2-receipt",
) -> core.ZDEXPurchaseReceiptCandidateV2:
    """Rebuild one generic V2 purchase leaf under a Spot release with one ceiling."""

    spot, _, route, execution_policy, price_policy, profile = _v2_release_set(
        spot_max_journal_bytes
    )
    price_occurrence = ZDEXBuybackOraclePriceOccurrenceV1(
        price_policy.oracle_id,
        execution_policy.quote_asset_id,
        execution_policy.zdex_asset_id,
        1,
        1,
        76,
    )
    pre_state = _global_pre_state(
        profile=profile, execution_policy=execution_policy, price_occurrence=price_occurrence
    )
    occurrence = _v2_ceiling_occurrence(pre_state, route, profile)
    legacy = _purchase_journal(
        route=route,
        spot_release=spot,
        occurrence=occurrence,
        buyback_pool_id=execution_policy.pool_id,
        quote_atoms=125,
        purchased_atoms=111,
        quote_pool_pre_atoms=1_000,
        zdex_pool_pre_atoms=1_000,
    )
    purchase = ZDEXAMMPurchaseJournalV2(
        **{name: getattr(legacy, name) for name in legacy.__dataclass_fields__},
        buyback_execution_policy_root=execution_policy.policy_root,
        price_safety_policy_root=price_policy.policy_root,
        oracle_occurrence_root=price_occurrence.occurrence_root,
        oracle_observed_height=price_occurrence.observed_height,
        oracle_quote_numerator_atoms=price_occurrence.quote_numerator_atoms,
        oracle_zdex_denominator_atoms=price_occurrence.zdex_denominator_atoms,
        route_safe_quote_limit_atoms=200,
        minimum_output_atoms=109,
    )
    purchase = replace(purchase, effect_plan_root=purchase_effects_v2(purchase).effect_plan_root)
    return core.ZDEXPurchaseReceiptCandidateV2(
        route,
        spot,
        occurrence,
        pre_state,
        execution_policy,
        price_policy,
        price_occurrence,
        purchase,
        purchase_effects_v2(purchase),
        _envelope(receipt_bytes),
    )


def _parse(relative: str) -> ast.Module:
    return ast.parse((REPO_ROOT / relative).read_text(encoding="utf-8"), filename=relative)


def _call_names(tree: ast.AST) -> list[str]:
    names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                names.append(node.func.attr)
            elif isinstance(node.func, ast.Name):
                names.append(node.func.id)
    return names


def _import_targets(tree: ast.AST) -> list[str]:
    targets: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            targets.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            targets.append("." * node.level + (node.module or ""))
    return targets


def _parameter_names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            args = node.args
            names.update(
                parameter.arg
                for parameter in (*args.posonlyargs, *args.args, *args.kwonlyargs)
            )
    return names


def _mutant(
    module: object,
    original: Callable[..., object],
    target: str,
    body: str,
    extra: dict[str, object] | None = None,
) -> Any:
    source = inspect.getsource(original)
    assert source.count(target) == 1, "mutant target is no longer unique"
    namespace = dict(vars(module))
    namespace.update(extra or {})
    exec(  # noqa: S102 - deliberate structure-preserving mutant of the boundary
        compile(source.replace(target, body, 1), f"<mutant:{original.__name__}>", "exec"),
        namespace,
    )
    return namespace[original.__name__]


# --- construction conformance ------------------------------------------------


def test_preparation_core_module_has_no_callback_parameter_call_or_shell_import() -> None:
    tree = _parse(_PREPARATION_MODULE)
    text = (REPO_ROOT / _PREPARATION_MODULE).read_text(encoding="utf-8")
    imports = _import_targets(tree)
    assert not any(name.split(".")[0] in _EFFECT_IMPORT_ROOTS for name in imports)
    assert not any("integration" in name.split(".") or name.startswith("..") for name in imports)
    assert "verify_succinct_receipt" not in _call_names(tree)
    assert "verify_profile_lane_receipt" not in _call_names(tree)
    assert "receipt_verifier" not in _parameter_names(tree)
    assert "ZDEXLaneSuccinctReceiptVerifierV1" not in text
    assert "BoundEconomicReceiptVerifierV1" not in text
    assert not any(name.startswith("verify_") for name in prep.__all__)
    assert not any(hasattr(prep, name) for name in _MOVED_NAMES)
    for name in (
        "prepare_zdex_amm_purchase_receipt_v1",
        "prepare_zdex_amm_purchase_receipt_v2",
        "prepare_zdex_burn_receipt_v1",
    ):
        assert tuple(inspect.signature(getattr(prep, name)).parameters) == ("candidate",), name
    assert tuple(
        inspect.signature(prep.prepare_governed_zdex_amm_purchase_receipt_shadow_v1).parameters
    ) == ("candidate", "profile", "authority_head", "verifier_binding_root")
    assert tuple(
        inspect.signature(prep.prepare_governed_zdex_amm_purchase_receipt_shadow_v2).parameters
    ) == ("candidate", "profile", "policy_registry", "authority_head", "verifier_binding_root")
    assert tuple(
        inspect.signature(prep.prepare_governed_zdex_burn_receipt_shadow_v1).parameters
    ) == ("candidate", "profile", "authority_head", "verifier_binding_root")
    assert len(dataclass_fields(core._VerifiedZDEXLaneFieldsV1)) == 15
    assert tuple(
        field.name for field in dataclass_fields(core._VerifiedZDEXLaneFieldsV1)
    ) == _MARKER_FIELD_NAMES


def test_legacy_core_module_keeps_identities_and_only_the_open_authority_debt() -> None:
    tree = _parse(_LEGACY_CORE_MODULE)
    text = (REPO_ROOT / _LEGACY_CORE_MODULE).read_text(encoding="utf-8")
    assert not any(hasattr(core, name) for name in _MOVED_NAMES)
    assert not any(name in text for name in _MOVED_NAMES)
    assert all(hasattr(core, name) for name in _RETAINED_CORE_NAMES)
    assert not any(name.startswith("verify_") for name in core.__all__)
    assert "verify_succinct_receipt" not in _call_names(tree)
    assert "verify_profile_lane_receipt" not in _call_names(tree)
    assert not any("integration" in name.split(".") or name.startswith("..") for name in _import_targets(tree))
    # The retained helper is the explicit open debt: it still takes the Bound
    # verifier and reads its registry-backed identity.  No purity claim here.
    assert "receipt_verifier.require_binding(" in text
    assert "receipt_verifier" in _parameter_names(tree)
    # The preparation module reuses the retained marker identities, never copies.
    assert prep._build_verified_zdex_amm_purchase_v1.__module__ == prep.__name__
    for family in _FAMILIES.values():
        assert family.marker_type.__module__ == core.__name__
    with pytest.raises(TypeError, match="verifier-constructed"):
        core.VerifiedZDEXAMMPurchaseV1(object(), cast(Any, object()))
    with pytest.raises(TypeError, match="verifier-constructed"):
        core.GovernedVerifiedZDEXAMMPurchaseV2(object(), cast(Any, object()))


def test_shell_owns_the_single_callback_the_adapter_and_the_relocated_protocol() -> None:
    tree = _parse(_SHELL_MODULE)
    calls = _call_names(tree)
    assert calls.count("verify_succinct_receipt") == 1
    assert calls.count("verify_profile_lane_receipt") == 1
    assert all(
        not name.startswith("..") or name.startswith("..core") for name in _import_targets(tree)
    )
    protocol = [
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name == "ZDEXLaneSuccinctReceiptVerifierV1"
    ]
    assert len(protocol) == 1
    assert [ast.unparse(base) for base in protocol[0].bases] == ["Protocol"]
    assert any(
        isinstance(node, ast.ClassDef) and node.name == "_ProfileLaneReceiptVerifierV1"
        for node in tree.body
    )
    assert shell.__all__ == [
        "ZDEXLaneSuccinctReceiptVerifierV1",
        "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
        "verify_governed_zdex_amm_purchase_receipt_shadow_v2",
        "verify_governed_zdex_burn_receipt_shadow_v1",
        "verify_zdex_amm_purchase_receipt_v1",
        "verify_zdex_amm_purchase_receipt_v2",
        "verify_zdex_burn_receipt_v1",
    ]
    for name in (
        "verify_zdex_amm_purchase_receipt_v1",
        "verify_zdex_amm_purchase_receipt_v2",
        "verify_zdex_burn_receipt_v1",
    ):
        assert tuple(inspect.signature(getattr(shell, name)).parameters) == (
            "candidate",
            "receipt_verifier",
        ), name
    for name in (
        "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
        "verify_governed_zdex_burn_receipt_shadow_v1",
    ):
        assert tuple(inspect.signature(getattr(shell, name)).parameters) == (
            "candidate",
            "profile",
            "authority_head",
            "receipt_verifier",
        ), name
    assert tuple(
        inspect.signature(shell.verify_governed_zdex_amm_purchase_receipt_shadow_v2).parameters
    ) == ("candidate", "profile", "policy_registry", "authority_head", "receipt_verifier")
    # No caller-held head, profile or policy alias is read after the callback.
    for name in (
        "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
        "verify_governed_zdex_amm_purchase_receipt_shadow_v2",
        "verify_governed_zdex_burn_receipt_shadow_v1",
    ):
        source = inspect.getsource(getattr(shell, name))
        tail = source[source.index("    return _execute_prepared") :]
        assert "authority_head" not in tail and "policy_registry" not in tail, name
        assert "profile," not in tail.replace("owned_profile,", ""), name


def test_fee_and_tokenomics_shells_consume_the_relocated_protocol() -> None:
    assert fee_shell.ZDEXLaneSuccinctReceiptVerifierV1 is shell.ZDEXLaneSuccinctReceiptVerifierV1
    assert (
        tokenomics_shell.ZDEXLaneSuccinctReceiptVerifierV1
        is shell.ZDEXLaneSuccinctReceiptVerifierV1
    )
    for relative in _CONSUMER_SHELL_MODULES:
        tree = _parse(relative)
        protocol_imports = [
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
            and any(alias.name == "ZDEXLaneSuccinctReceiptVerifierV1" for alias in node.names)
        ]
        assert [(node.level, node.module) for node in protocol_imports] == [
            (1, "zdex_purchase_burn_receipt_verification_v1")
        ], relative


# --- pure preparation -------------------------------------------------------


@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_prepare_is_deterministic_complete_and_reproduces_the_pinned_marker(label: str) -> None:
    # Arrange
    family = _FAMILIES[label]
    candidate = family.candidate()
    expected_fields = family.expected_fields(candidate)

    # Act: prepare twice with no verifier anywhere.
    first = family.prepare(candidate)
    second = family.prepare(candidate)

    # Assert: exact typed data, identical decision, complete request and field set.
    assert type(first) is family.prepared_type
    assert first == second
    assert first.verified_fields == expected_fields
    assert (first.receipt_bytes, first.expected_image_id, first.expected_journal_bytes) == (
        _expected_request(candidate)
    )
    assert first.verified_fields.receipt_digest == _digest(first.receipt_bytes)
    assert first.verified_fields.journal_digest == _digest(first.expected_journal_bytes)
    assert len(first.expected_journal_bytes) == family.journal_len_pin
    assert len(first.expected_journal_bytes) <= candidate.module_release.max_journal_bytes
    # Expected image is the module release image, distinct from the route image.
    assert first.expected_image_id == candidate.module_release.guest_image_id
    assert first.expected_image_id != candidate.route_release.guest_image_id
    # Generic leaves carry zero authority roots exactly as before.
    assert first.verified_fields.authority_head_root == ZERO_ROOT_V1
    assert first.verified_fields.verifier_binding_root == ZERO_ROOT_V1
    # The private factory mints the identical binding root the old path produced.
    marker = family.build(first)
    assert type(marker) is family.marker_type
    assert _marker_fields(marker) == _record_fields(expected_fields)
    assert marker.binding_root == family.binding_root_pin
    assert marker.leaf_binding_root == family.binding_root_pin


@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_prepared_subject_is_detached_from_the_candidate_graph(label: str) -> None:
    # Arrange
    family = _FAMILIES[label]
    candidate = family.candidate()
    prepared = family.prepare(candidate)
    facts = _prepared_facts(prepared)

    # Act: mutate every nested caller-held source after preparation.
    object.__setattr__(candidate.journal, "writer_epoch", 90_001)
    object.__setattr__(candidate, "effects", GlobalEconomicEffectPlanV1.empty())
    object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-after-prepare")
    object.__setattr__(candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)
    object.__setattr__(candidate.module_release, "guest_image_id", _root(90_004))
    object.__setattr__(candidate.module_release, "release_id", _root(90_005))
    object.__setattr__(candidate.route_release, "route_release_id", _root(90_006))
    object.__setattr__(candidate.occurrence, "profile_root", _root(90_007))
    snapshot = family.snapshot(prepared)

    # Assert
    assert _prepared_facts(prepared) == facts
    assert snapshot == prepared
    assert snapshot is not prepared
    assert snapshot.verified_fields is not prepared.verified_fields


@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_prepared_record_requires_exact_types_and_field_to_request_binding(label: str) -> None:
    family = _FAMILIES[label]
    prepared = family.prepare(family.candidate())

    class _Forged(family.prepared_type):  # type: ignore[name-defined]
        pass

    forged = _Forged(prepared.verified_fields, prepared.receipt_bytes, prepared.expected_journal_bytes)
    wrong_receipt_digest = replace(
        prepared, verified_fields=replace(prepared.verified_fields, receipt_digest=_root(1))
    )
    wrong_journal_digest = replace(
        prepared, verified_fields=replace(prepared.verified_fields, journal_digest=_root(2))
    )
    hostile_scalar = replace(
        prepared,
        verified_fields=replace(
            prepared.verified_fields,
            module_release_id=_HostileRoot(prepared.verified_fields.module_release_id),
        ),
    )
    open_kind = replace(
        prepared, verified_fields=replace(prepared.verified_fields, receipt_kind=cast(Any, "SUCCINCT"))
    )
    verifier = _RecordingVerifier()

    for subject, error, message in (
        (forged, TypeError, "exact typed data"),
        (object(), TypeError, "exact typed data"),
        (hostile_scalar, TypeError, "exact primitive"),
        (open_kind, TypeError, "exact primitive|not closed"),
        (wrong_receipt_digest, ValueError, "receipt digest mismatch"),
        (wrong_journal_digest, ValueError, "journal digest mismatch"),
    ):
        # These values intentionally cross the typed boundary malformed.
        untyped_subject: Any = subject
        with pytest.raises(error, match=message):
            family.snapshot(untyped_subject)
        with pytest.raises(error, match=message):
            family.build(untyped_subject)
        with pytest.raises(error, match=message):
            family.execute(untyped_subject, verifier)
    assert verifier.calls == []


def test_prepared_subject_cannot_cross_marker_families() -> None:
    purchase = _FAMILIES["purchase_v1"].prepare(_purchase_v1_candidate())
    burn = _FAMILIES["burn_v1"].prepare(_burn_v1_candidate())
    verifier = _RecordingVerifier()
    crossings: tuple[tuple[_Family, Any, str], ...] = (
        (_FAMILIES["burn_v1"], purchase, "prepared ZDEX burn receipt must be exact typed data"),
        (_FAMILIES["purchase_v2"], purchase, "prepared ZDEX purchase V2 receipt must be exact typed data"),
        (_FAMILIES["purchase_v1"], burn, "prepared ZDEX purchase receipt must be exact typed data"),
    )
    for family, subject, message in crossings:
        with pytest.raises(TypeError, match=message):
            family.snapshot(subject)
        with pytest.raises(TypeError, match=message):
            family.build(subject)
        with pytest.raises(TypeError, match=message):
            family.execute(subject, verifier)
    with pytest.raises(TypeError, match="governed ZDEX purchase V2 leaf must be exact typed data"):
        prep.PreparedGovernedZDEXAMMPurchaseReceiptV2(
            cast(Any, purchase), _root(1), _root(2), _root(3)
        )
    assert verifier.calls == []


def test_prepared_constructor_refuses_non_exact_field_and_byte_types() -> None:
    prepared = prep.prepare_zdex_amm_purchase_receipt_v1(_purchase_v1_candidate())
    for prepared_type in (
        prep.PreparedZDEXAMMPurchaseReceiptV1,
        prep.PreparedZDEXAMMPurchaseReceiptV2,
        prep.PreparedZDEXBurnReceiptV1,
    ):
        with pytest.raises(TypeError, match="receipt bytes must be exact bytes"):
            prepared_type(
                prepared.verified_fields,
                cast(Any, bytearray(prepared.receipt_bytes)),
                prepared.expected_journal_bytes,
            )
        with pytest.raises(TypeError, match="journal bytes must be exact bytes"):
            prepared_type(
                prepared.verified_fields,
                prepared.receipt_bytes,
                cast(Any, prepared.expected_journal_bytes.decode("ascii")),
            )
        with pytest.raises(TypeError, match="fields must be exact typed data"):
            prepared_type(cast(Any, object()), prepared.receipt_bytes, prepared.expected_journal_bytes)


def test_governed_prepared_record_requires_exact_roots_and_leaf() -> None:
    fixture, candidate = _candidate()
    leaf = prep.prepare_zdex_amm_purchase_receipt_v2(
        _governed_purchase_v2_candidate(fixture, candidate)
    )
    roots = (_root(11), _root(12), _root(13))
    governed = prep.PreparedGovernedZDEXAMMPurchaseReceiptV2(leaf, *roots)
    assert governed.expected_image_id == leaf.expected_image_id

    class _Forged(prep.PreparedGovernedZDEXAMMPurchaseReceiptV2):
        pass

    for index, name in enumerate(("authority head", "verifier binding", "policy registry")):
        hostile = list(roots)
        hostile[index] = _HostileRoot(roots[index])
        with pytest.raises(TypeError, match=f"{name} root must be exact str"):
            prep.PreparedGovernedZDEXAMMPurchaseReceiptV2(leaf, *hostile)
        short = list(roots)
        short[index] = "0x12"
        with pytest.raises(ValueError, match=f"{name} root"):
            prep.PreparedGovernedZDEXAMMPurchaseReceiptV2(leaf, *short)
    verifier = _RecordingVerifier()
    for subject in (_Forged(leaf, *roots), object(), leaf):
        untyped_subject: Any = subject
        with pytest.raises(TypeError, match="governed ZDEX purchase V2 receipt must be exact typed data"):
            prep.snapshot_prepared_governed_zdex_amm_purchase_receipt_v2(untyped_subject)
        with pytest.raises(TypeError, match="governed ZDEX purchase V2 receipt must be exact typed data"):
            shell._execute_prepared_governed_zdex_amm_purchase_receipt_v2(untyped_subject, verifier)
    inconsistent = replace(
        governed, leaf=replace(leaf, verified_fields=replace(leaf.verified_fields, receipt_digest=_root(9)))
    )
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        shell._execute_prepared_governed_zdex_amm_purchase_receipt_v2(inconsistent, verifier)
    assert verifier.calls == []


# --- rejection before any callback ------------------------------------------


def _v1_subject(candidate: Any, label: str) -> Any:
    """Build one- and two-defect V1 subjects; earlier phases must reject first."""

    subject: Any = candidate
    if label == "not_a_candidate":
        return object()
    if "active_route" in label:
        active_route = replace(
            candidate.route_release,
            status=ReleaseStatusV1.ACTIVE_NEW,
            accepts_new_objects=True,
            evidence_statuses=tuple(sorted(REQUIRED_ACTIVE_EVIDENCE_V1, key=lambda item: item.value)),
        )
        subject = replace(subject, route_release=active_route)
    if "wrong_lane" in label:
        other_lane = (
            LaneIdV1.ZDEX_TOKENOMICS
            if candidate.module_release.lane_id is LaneIdV1.SPOT_LIQUIDITY
            else LaneIdV1.SPOT_LIQUIDITY
        )
        subject = replace(subject, module_release=_lane_release(other_lane, 3))
    if "occurrence_route" in label:
        subject = replace(
            subject, occurrence=replace(candidate.occurrence, route_release_id=_root(777))
        )
    if "chain_binding" in label:
        subject = replace(subject, journal=replace(subject.journal, chain_id="other-chain"))
    if "effect_rows" in label:
        rows = list(subject.effects.rows)
        index = next(i for i, row in enumerate(rows) if row.kind is EconomicEffectKindV1.CUSTODY)
        rows[index] = replace(rows[index], delta_atoms=rows[index].delta_atoms + 1)
        mutated = replace(subject.effects, rows=tuple(rows))
        subject = replace(
            subject,
            effects=mutated,
            journal=replace(subject.journal, effect_plan_root=mutated.effect_plan_root),
        )
    if "conditional_kind" in label:
        subject = replace(
            subject,
            receipt=core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional"),
        )
    if "empty_bytes" in label:
        subject = replace(subject, receipt=core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""))
    if "fake_kind" in label:
        subject = replace(subject, receipt=core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.FAKE, b""))
    return subject


_V1_REJECTIONS = (
    ("not_a_candidate", TypeError, "candidate must be exact typed data"),
    ("active_route", ValueError, "must remain SHADOW"),
    ("wrong_lane", ValueError, "module release lane mismatch"),
    ("occurrence_route", ValueError, "occurrence route mismatch"),
    ("chain_binding", ValueError, "chain mismatch"),
    ("effect_rows", ValueError, "effect rows or conservation mismatch"),
    ("conditional_kind", ValueError, "requires a succinct receipt"),
    ("empty_bytes", ValueError, "receipt bytes must be nonempty"),
    # Paired defects: the earlier phase's rejection must be the first error.
    ("active_route_then_empty_bytes", ValueError, "must remain SHADOW"),
    ("wrong_lane_then_chain_binding", ValueError, "module release lane mismatch"),
    ("occurrence_route_then_effect_rows", ValueError, "occurrence route mismatch"),
    ("chain_binding_then_conditional_kind", ValueError, "chain mismatch"),
    ("effect_rows_then_empty_bytes", ValueError, "effect rows or conservation mismatch"),
    ("fake_kind", ValueError, "requires a succinct receipt"),
)


@pytest.mark.parametrize("family_label", ("purchase_v1", "burn_v1"))
@pytest.mark.parametrize(("label", "error", "message"), _V1_REJECTIONS)
def test_invalid_v1_leaf_rejects_before_callback_in_the_reference_order(
    family_label: str, label: str, error: type[Exception], message: str
) -> None:
    family = _FAMILIES[family_label]
    subject = _v1_subject(family.candidate(), label)
    verifier = _RecordingVerifier()

    # Act / Assert: core rejects with no callback available; shell rejects with no call.
    with pytest.raises(error, match=message):
        family.prepare(subject)
    with pytest.raises(error, match=message):
        family.verify(subject, verifier)
    assert verifier.calls == []


def _v2_subject(candidate: core.ZDEXPurchaseReceiptCandidateV2, label: str) -> Any:
    subject: Any = candidate
    if label == "not_a_candidate":
        return object()
    if "journal_binding" in label:
        journal = replace(candidate.journal, quote_source_bucket_id="protocol:other-source")
        journal = replace(journal, effect_plan_root=purchase_effects_v2(journal).effect_plan_root)
        subject = replace(subject, journal=journal, effects=purchase_effects_v2(journal))
    if "price_authority" in label:
        # The occurrence pre-state root no longer matches: a real pre-receipt check.
        subject = replace(subject, pre_state=replace(candidate.pre_state, height=candidate.pre_state.height + 1))
    if "conditional_kind" in label:
        subject = replace(
            subject,
            receipt=core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional"),
        )
    if "empty_bytes" in label:
        subject = replace(subject, receipt=core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""))
    return subject


@pytest.mark.parametrize(
    ("label", "error", "message"),
    (
        ("not_a_candidate", TypeError, "V2 receipt candidate must be exact typed data"),
        ("journal_binding", ValueError, "V2 journal or effects mismatch"),
        ("price_authority", ZDEXBuybackPriceAuthorityRejectedV1, "CONTEXT_MISMATCH"),
        ("conditional_kind", ValueError, "requires a succinct receipt"),
        ("empty_bytes", ValueError, "receipt bytes must be nonempty"),
        # Price authority stays after the journal phase and before the receipt phase.
        ("journal_binding_then_price_authority", ValueError, "V2 journal or effects mismatch"),
        ("price_authority_then_conditional_kind", ZDEXBuybackPriceAuthorityRejectedV1, "CONTEXT_MISMATCH"),
        ("price_authority_then_empty_bytes", ZDEXBuybackPriceAuthorityRejectedV1, "CONTEXT_MISMATCH"),
    ),
)
def test_invalid_v2_purchase_rejects_before_callback_with_price_authority_in_phase(
    label: str, error: type[Exception], message: str
) -> None:
    subject = _v2_subject(_purchase_v2_candidate(), label)
    verifier = _RecordingVerifier()

    with pytest.raises(error, match=message):
        prep.prepare_zdex_amm_purchase_receipt_v2(subject)
    with pytest.raises(error, match=message):
        shell.verify_zdex_amm_purchase_receipt_v2(subject, verifier)
    assert verifier.calls == []


@pytest.mark.parametrize("tight", ("purchase_v1", "burn_v1"))
def test_journal_ceiling_accepts_at_bound_and_rejects_one_below_for_v1_leaves(tight: str) -> None:
    # Arrange: the tight leaf's release ceiling equals its canonical journal length.
    loose = 65_536
    family = _FAMILIES[tight]
    index = 0 if tight == "purchase_v1" else 1
    long_receipt = b"r" * (family.journal_len_pin + 1)

    def leaves(limit: int, receipt: bytes) -> tuple[Any, Any]:
        return _v1_leaves_with_ceilings(
            spot_max_journal_bytes=limit if index == 0 else loose,
            burn_max_journal_bytes=limit if index == 1 else loose,
            purchase_receipt=receipt,
            burn_receipt=receipt,
        )

    at_bound = leaves(family.journal_len_pin, long_receipt)[index]
    one_below = leaves(family.journal_len_pin - 1, b"receipt")[index]
    assert at_bound.module_release.max_journal_bytes == family.journal_len_pin
    assert len(canonical_global_bytes_v1(at_bound.journal)) == family.journal_len_pin

    # Act / Assert: at bound prepares and executes exactly once; a receipt longer
    # than the ceiling shows the ceiling is a journal bound, never a receipt bound.
    prepared = family.prepare(at_bound)
    assert len(prepared.expected_journal_bytes) == family.journal_len_pin
    accepting = _RecordingVerifier()
    marker = family.verify(at_bound, accepting)
    assert accepting.calls == [_expected_request(at_bound)]
    assert marker.receipt_digest == _digest(long_receipt)

    # One below rejects in core and in the shell before any call.
    rejecting = _RecordingVerifier()
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        family.prepare(one_below)
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        family.verify(one_below, rejecting)
    # Paired failures: empty receipt bytes reject before the over-ceiling journal.
    empty_and_over = replace(one_below, receipt=_envelope(b""))
    with pytest.raises(ValueError, match="receipt bytes must be nonempty"):
        family.prepare(empty_and_over)
    with pytest.raises(ValueError, match="receipt bytes must be nonempty"):
        family.verify(empty_and_over, rejecting)
    assert rejecting.calls == []


def test_journal_ceiling_accepts_at_bound_and_rejects_one_below_for_v2_purchase() -> None:
    # Arrange: derive the exact V2 journal length under a loose Spot ceiling first.
    loose = _v2_leaf_with_spot_ceiling(65_536)
    journal_len = len(canonical_global_bytes_v1(loose.journal))
    long_receipt = b"r" * (journal_len + 1)
    at_bound = _v2_leaf_with_spot_ceiling(journal_len, long_receipt)
    one_below = _v2_leaf_with_spot_ceiling(journal_len - 1)
    assert at_bound.module_release.max_journal_bytes == journal_len

    # Act / Assert
    prepared = prep.prepare_zdex_amm_purchase_receipt_v2(at_bound)
    assert len(prepared.expected_journal_bytes) == journal_len
    assert prepared.verified_fields.price_authority_root != ZERO_ROOT_V1
    accepting = _RecordingVerifier()
    marker = shell.verify_zdex_amm_purchase_receipt_v2(at_bound, accepting)
    assert accepting.calls == [_expected_request(at_bound)]
    assert marker.receipt_digest == _digest(long_receipt)
    rejecting = _RecordingVerifier()
    with pytest.raises(ValueError, match="V2 journal exceeds release byte ceiling"):
        prep.prepare_zdex_amm_purchase_receipt_v2(one_below)
    with pytest.raises(ValueError, match="V2 journal exceeds release byte ceiling"):
        shell.verify_zdex_amm_purchase_receipt_v2(one_below, rejecting)
    # Paired failures: the price authority phase precedes the ceiling phase.
    bad_price_and_over = replace(
        one_below, pre_state=replace(one_below.pre_state, height=one_below.pre_state.height + 1)
    )
    with pytest.raises(ZDEXBuybackPriceAuthorityRejectedV1, match="CONTEXT_MISMATCH"):
        shell.verify_zdex_amm_purchase_receipt_v2(bad_price_and_over, rejecting)
    assert rejecting.calls == []


# --- shell execution ---------------------------------------------------------


@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_shell_executes_exactly_the_prepared_receipt_image_and_journal(label: str) -> None:
    # Arrange
    family = _FAMILIES[label]
    candidate = family.candidate()
    prepared = family.prepare(candidate)
    verifier = _RecordingVerifier()

    # Act
    marker = family.verify(candidate, verifier)

    # Assert: one call, exact request, marker minted from exactly those bytes and fields.
    assert verifier.calls == [_expected_request(candidate)]
    assert verifier.calls == [
        (prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes)
    ]
    assert type(marker) is family.marker_type
    assert _marker_fields(marker) == _record_fields(prepared.verified_fields)
    assert marker.receipt_digest == _digest(verifier.calls[0][0])
    assert marker.expected_image_id == verifier.calls[0][1]
    assert marker.expected_image_id == candidate.module_release.guest_image_id
    assert marker.journal_digest == _digest(verifier.calls[0][2])
    assert marker.binding_root == family.binding_root_pin
    with pytest.raises(AttributeError, match="immutable"):
        marker._fields = cast(Any, object())


@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_callback_exception_propagates_and_no_marker_is_returned(label: str) -> None:
    family = _FAMILIES[label]
    candidate = family.candidate()
    verifier = _RecordingVerifier(reject=True)
    outcome: object = None

    try:
        outcome = family.verify(candidate, verifier)
    except ValueError as exc:
        assert str(exc) == "boundary verifier rejection"
    else:
        raise AssertionError("verifier rejection did not propagate")

    assert outcome is None
    assert verifier.calls == [_expected_request(candidate)]


@pytest.mark.parametrize("result", (False, 0, b"", object(), True, b"ok"))
@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_generic_callback_normal_and_falsey_returns_are_ignored(label: str, result: object) -> None:
    family = _FAMILIES[label]
    candidate = family.candidate()
    verifier = _RecordingVerifier(result=result)

    marker = family.verify(candidate, verifier)

    # Historical contract: the generic return value is not an admission condition.
    assert verifier.calls == [_expected_request(candidate)]
    assert _marker_fields(marker) == _record_fields(family.expected_fields(candidate))
    assert marker.binding_root == family.binding_root_pin


@pytest.mark.parametrize("label", _FAMILY_LABELS)
def test_candidate_and_prepared_alias_mutation_during_callback_cannot_relabel_marker(
    label: str,
) -> None:
    # Arrange: the caller keeps every alias the callback could reach.
    family = _FAMILIES[label]
    candidate = family.candidate()
    prepared = family.prepare(candidate)
    expected_fields = _record_fields(prepared.verified_fields)
    expected_request = (prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes)
    forged_fields = replace(
        prepared.verified_fields,
        module_release_id=_root(78_501),
        expected_image_id=_root(78_502),
        writer_epoch=78_503,
        authority_head_root=_root(78_504),
        receipt_digest=_digest(b"mutated-leaf"),
        journal_digest=_digest(b"mutated-journal"),
    )

    class _MutatingVerifier(_RecordingVerifier):
        def verify_succinct_receipt(
            self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            object.__setattr__(prepared, "verified_fields", forged_fields)
            object.__setattr__(prepared, "receipt_bytes", b"mutated-leaf")
            object.__setattr__(prepared, "expected_journal_bytes", b"mutated-journal")
            object.__setattr__(candidate.module_release, "release_id", _root(78_501))
            object.__setattr__(candidate.module_release, "guest_image_id", _root(78_502))
            object.__setattr__(candidate.journal, "writer_epoch", 78_503)
            object.__setattr__(candidate, "effects", GlobalEconomicEffectPlanV1.empty())
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-leaf")
            object.__setattr__(candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)

    verifier = _MutatingVerifier()

    # Act: execute the caller-held prepared alias directly.
    marker = family.execute(prepared, verifier)

    # Assert: the marker is the executed subject, not the mutated alias.
    assert verifier.calls == [expected_request]
    assert _marker_fields(marker) == expected_fields
    assert marker.binding_root == family.binding_root_pin
    assert prepared.verified_fields == forged_fields
    assert not any(name.startswith("bind_verified") for name in (*shell.__all__, *prep.__all__))


# --- governed paths ----------------------------------------------------------


def test_governed_paths_reproduce_pinned_fields_requests_and_authority_roots() -> None:
    fixture, candidate = _candidate()
    head = fixture.authority_head
    bound = fixture.receipt_verifier
    assert head.authority_root == _GOVERNED_HEAD_ROOT_PIN
    assert bound.binding_root == _GOVERNED_VERIFIER_BINDING_ROOT_PIN
    purchase_v1 = _governed_purchase_v1_candidate(fixture, candidate)
    purchase_v2 = _governed_purchase_v2_candidate(fixture, candidate)
    burn = _governed_burn_candidate(fixture, candidate)
    calls_before = len(fixture.backend.calls)

    verified_v1 = shell.verify_governed_zdex_amm_purchase_receipt_shadow_v1(
        purchase_v1, **_governed_kwargs(fixture)
    )
    verified_v2 = shell.verify_governed_zdex_amm_purchase_receipt_shadow_v2(
        purchase_v2, policy_registry=fixture.candidate.policy_registry, **_governed_kwargs(fixture)
    )
    verified_burn = shell.verify_governed_zdex_burn_receipt_shadow_v1(burn, **_governed_kwargs(fixture))

    assert fixture.backend.calls[calls_before:] == [
        _expected_request(purchase_v1),
        _expected_request(purchase_v2),
        _expected_request(burn),
    ]
    for verified, leaf_candidate, pin in (
        (verified_v1, purchase_v1, _GOVERNED_PURCHASE_V1_BINDING_ROOT_PIN),
        (verified_burn, burn, _GOVERNED_BURN_V1_BINDING_ROOT_PIN),
    ):
        expected = replace(
            _expected_fields(leaf_candidate),
            authority_head_root=_GOVERNED_HEAD_ROOT_PIN,
            verifier_binding_root=_GOVERNED_VERIFIER_BINDING_ROOT_PIN,
        )
        assert _marker_fields(verified) == _record_fields(expected)
        assert verified.binding_root == pin
        assert verified.leaf_binding_root != pin
    assert type(verified_v2) is core.GovernedVerifiedZDEXAMMPurchaseV2
    assert _marker_fields(verified_v2.verified_leaf) == _record_fields(
        _FAMILIES["purchase_v2"].expected_fields(purchase_v2)
    )
    assert verified_v2.verified_leaf.binding_root == _PURCHASE_V2_LEAF_BINDING_ROOT_PIN
    assert verified_v2.authority_head_root == _GOVERNED_HEAD_ROOT_PIN
    assert verified_v2.verifier_binding_root == _GOVERNED_VERIFIER_BINDING_ROOT_PIN
    assert verified_v2.policy_registry_root == _GOVERNED_POLICY_REGISTRY_ROOT_PIN
    assert verified_v2.binding_root == _GOVERNED_PURCHASE_V2_BINDING_ROOT_PIN
    assert candidate.verified_purchase.binding_root == _GOVERNED_PURCHASE_V2_BINDING_ROOT_PIN


def _governed_v1_subject(
    fixture: _Fixture,
    candidate: ZDEXAtomicBuybackCandidateV1,
    family_label: str,
    label: str,
) -> tuple[Any, dict[str, Any]]:
    build = (
        _governed_purchase_v1_candidate if family_label == "purchase_v1" else _governed_burn_candidate
    )
    kwargs = _governed_kwargs(fixture)
    receipt = b"" if "empty_receipt" in label else b"governed"
    epoch = 12 if "writer_epoch" in label else None
    subject: Any = build(fixture, candidate, receipt, writer_epoch=epoch)
    if "not_a_candidate" in label:
        subject = object()
    if "head_not_exact" in label:
        kwargs["authority_head"] = object()
    if "verifier_not_bound" in label:
        kwargs["receipt_verifier"] = object()
    if "revoked_head" in label:
        kwargs["authority_head"] = replace(
            fixture.authority_head, status=GlobalEconomicAuthorityStatusV1.REVOKED
        )
    return subject, kwargs


@pytest.mark.parametrize("family_label", ("purchase_v1", "burn_v1"))
@pytest.mark.parametrize(
    ("label", "error", "message"),
    (
        ("not_a_candidate_with_head_not_exact", TypeError, "candidate must be exact typed data"),
        ("head_not_exact_with_verifier_not_bound", TypeError, "authority head must be exact typed data"),
        ("verifier_not_bound", TypeError, "must be a bound capability"),
        ("revoked_head", ValueError, "outside the current governed authority"),
        ("revoked_head_then_writer_epoch", ValueError, "outside the current governed authority"),
        ("writer_epoch", ValueError, "writer epoch is outside the profile"),
        ("writer_epoch_then_empty_receipt", ValueError, "writer epoch is outside the profile"),
        ("empty_receipt", ValueError, "receipt bytes must be nonempty"),
    ),
)
def test_governed_v1_leaf_rejects_candidate_head_verifier_authority_epoch_then_leaf(
    family_label: str, label: str, error: type[Exception], message: str
) -> None:
    fixture, candidate = _candidate()
    subject, kwargs = _governed_v1_subject(fixture, candidate, family_label, label)
    verify = (
        shell.verify_governed_zdex_amm_purchase_receipt_shadow_v1
        if family_label == "purchase_v1"
        else shell.verify_governed_zdex_burn_receipt_shadow_v1
    )
    calls_before = len(fixture.backend.calls)

    with pytest.raises(error, match=message):
        verify(subject, **kwargs)
    assert len(fixture.backend.calls) == calls_before


def _governed_v2_subject(
    fixture: _Fixture, candidate: ZDEXAtomicBuybackCandidateV1, label: str
) -> tuple[Any, dict[str, Any]]:
    kwargs = _governed_kwargs(fixture)
    kwargs["policy_registry"] = fixture.candidate.policy_registry
    receipt = b"" if "empty_receipt" in label else b"governed-v2"
    subject: Any = _governed_purchase_v2_candidate(fixture, candidate, receipt)
    if "registry_mismatch" in label:
        first, *remaining = fixture.candidate.policy_registry.bindings
        kwargs["policy_registry"] = EconomicPolicyRegistryV1(
            tuple(
                sorted(
                    (replace(first, policy_root=_root(0xAC)), *remaining),
                    key=lambda binding: (binding.policy_kind, binding.command_kind),
                )
            )
        )
    if "execution_binding" in label:
        substituted = replace(fixture.candidate.buyback_policy, pool_definition_root=_root(0xAB))
        journal = replace(subject.journal, buyback_execution_policy_root=substituted.policy_root)
        subject = replace(
            subject, execution_policy=substituted, journal=journal, effects=purchase_effects_v2(journal)
        )
    if "price_binding" in label:
        subject = replace(
            subject, price_policy=replace(fixture.candidate.price_policy, maximum_oracle_age_blocks=2)
        )
    if "writer_epoch" in label:
        journal = replace(subject.journal, writer_epoch=12)
        journal = replace(journal, effect_plan_root=purchase_effects_v2(journal).effect_plan_root)
        subject = replace(subject, journal=journal, effects=purchase_effects_v2(journal))
    return subject, kwargs


@pytest.mark.parametrize(
    ("label", "error", "message"),
    (
        ("registry_mismatch", ValueError, "economic policy registry mismatch"),
        ("execution_binding", ValueError, "execution policy binding mismatch"),
        ("price_binding", ValueError, "price policy binding mismatch"),
        ("writer_epoch", ValueError, "V2 receipt writer epoch is outside the profile"),
        ("empty_receipt", ValueError, "receipt bytes must be nonempty"),
        ("registry_mismatch_then_empty_receipt", ValueError, "economic policy registry mismatch"),
        ("execution_binding_then_price_binding", ValueError, "execution policy binding mismatch"),
        ("price_binding_then_writer_epoch", ValueError, "price policy binding mismatch"),
        ("writer_epoch_then_empty_receipt", ValueError, "V2 receipt writer epoch is outside the profile"),
    ),
)
def test_governed_v2_purchase_rejects_registry_bindings_epoch_then_leaf(
    label: str, error: type[Exception], message: str
) -> None:
    fixture, candidate = _candidate()
    subject, kwargs = _governed_v2_subject(fixture, candidate, label)
    calls_before = len(fixture.backend.calls)

    with pytest.raises(error, match=message):
        shell.verify_governed_zdex_amm_purchase_receipt_shadow_v2(subject, **kwargs)
    with pytest.raises(error, match=message):
        prep.prepare_governed_zdex_amm_purchase_receipt_shadow_v2(
            subject,
            profile=kwargs["profile"],
            policy_registry=kwargs["policy_registry"],
            authority_head=kwargs["authority_head"],
            verifier_binding_root=fixture.receipt_verifier.binding_root,
        )
    assert len(fixture.backend.calls) == calls_before


@pytest.mark.parametrize("shape", _GOVERNED_SHAPES)
@pytest.mark.parametrize(
    ("label", "message"),
    (
        # Compatibility controls: candidate first, then exact head type, then exact
        # Bound type, all before the complete head is reconstructed.
        ("not_a_candidate_with_corrupt_head_and_invalid_verifier", "candidate must be exact typed data"),
        ("head_not_exact_with_invalid_verifier", "authority head must be exact typed data"),
        ("corrupt_exact_head_with_invalid_verifier", "must be a bound capability"),
        ("hostile_exact_head_with_invalid_verifier", "must be a bound capability"),
        # Intentional ownership strengthening (recorded for root): at base a corrupted
        # exact head with a valid Bound capability reached one callback and produced a
        # marker; the owned head now reruns its twelve-coordinate checks before I/O.
        ("corrupt_exact_head_with_valid_bound", "generation must be an exact integer"),
        ("hostile_exact_head_with_valid_bound", "activation_id must be exact str"),
    ),
)
def test_governed_exact_type_gates_keep_candidate_head_then_bound_order(
    shape: str, label: str, message: str
) -> None:
    fixture, candidate = _candidate()
    subject, verify, kwargs = _governed_run(fixture, candidate, shape)
    corrupt_head = replace(fixture.authority_head)
    object.__setattr__(corrupt_head, "generation", "7")
    hostile_head = replace(fixture.authority_head)
    object.__setattr__(hostile_head, "activation_id", _HostileRoot(hostile_head.activation_id))
    if "not_a_candidate" in label:
        subject = object()
    if "corrupt" in label:
        kwargs["authority_head"] = corrupt_head
    if "hostile" in label:
        kwargs["authority_head"] = hostile_head
    if "head_not_exact" in label:
        kwargs["authority_head"] = object()
    if "invalid_verifier" in label:
        kwargs["receipt_verifier"] = object()
    calls_before = len(fixture.backend.calls)

    with pytest.raises(TypeError, match=message):
        verify(subject, **kwargs)
    assert len(fixture.backend.calls) == calls_before
    with pytest.raises(TypeError, match="authority head must be exact typed data"):
        prep.snapshot_governed_receipt_authority_head_v1(cast(Any, object()))


def test_bound_authority_source_mutation_during_callback_still_fails_its_own_recheck() -> None:
    """The Bound verifier's post-callback identity recheck is preserved, unchanged.

    Mutating the caller-held head is the retained-alias repair; mutating the
    Bound capability's registered authority source is a different case and must
    still fail the Bound verifier's own recheck with no marker.
    """

    fixture, candidate = _candidate()
    bound = fixture.receipt_verifier
    subject, verify, kwargs = _governed_run(fixture, candidate, "burn_v1")
    registry = deployment._BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1
    with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
        original_authority = registry[bound]
    other_backend = _RecordingVerifier()

    def swap(*_: object) -> None:
        with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
            registry[bound] = replace(
                original_authority,
                backend=other_backend,
                verify_call=other_backend.verify_succinct_receipt,
            )

    fixture.backend.hook = swap
    calls_before = len(fixture.backend.calls)
    try:
        with pytest.raises(ValueError, match="authority changed during verification"):
            verify(subject, **kwargs)
    finally:
        fixture.backend.hook = None
        with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
            registry[bound] = original_authority
    assert fixture.backend.calls[calls_before:] == [_expected_request(subject)]
    assert other_backend.calls == []


def test_bound_verifier_non_none_and_error_outcomes_return_no_governed_marker() -> None:
    fixture, candidate = _candidate()
    purchase_v1 = _governed_purchase_v1_candidate(fixture, candidate)
    purchase_v2 = _governed_purchase_v2_candidate(fixture, candidate)
    burn = _governed_burn_candidate(fixture, candidate)
    runs: tuple[tuple[Callable[[], object], Any], ...] = (
        (
            lambda: shell.verify_governed_zdex_amm_purchase_receipt_shadow_v1(
                purchase_v1, **_governed_kwargs(fixture)
            ),
            purchase_v1,
        ),
        (
            lambda: shell.verify_governed_zdex_amm_purchase_receipt_shadow_v2(
                purchase_v2,
                policy_registry=fixture.candidate.policy_registry,
                **_governed_kwargs(fixture),
            ),
            purchase_v2,
        ),
        (
            lambda: shell.verify_governed_zdex_burn_receipt_shadow_v1(burn, **_governed_kwargs(fixture)),
            burn,
        ),
    )
    for run, leaf in runs:
        # The Bound verifier requires exact None; a falsey reply is a contract violation.
        for reply in (False, 0, b""):
            fixture.backend.result = reply
            calls_before = len(fixture.backend.calls)
            with pytest.raises(ValueError, match="violated success contract"):
                run()
            assert fixture.backend.calls[calls_before:] == [_expected_request(leaf)]
        fixture.backend.result = None
        fixture.backend.error = ValueError("boundary backend rejection")
        calls_before = len(fixture.backend.calls)
        with pytest.raises(ValueError, match="boundary backend rejection"):
            run()
        assert fixture.backend.calls[calls_before:] == [_expected_request(leaf)]
        fixture.backend.error = None


def test_governed_head_profile_and_registry_alias_mutation_during_callback_cannot_relabel() -> None:
    # Arrange: the callback mutates every caller-held authority alias in place.
    fixture, candidate = _candidate()
    head = fixture.authority_head
    profile = fixture.candidate.profile
    registry = fixture.candidate.policy_registry
    purchase_v1 = _governed_purchase_v1_candidate(fixture, candidate)
    purchase_v2 = _governed_purchase_v2_candidate(fixture, candidate)
    burn = _governed_burn_candidate(fixture, candidate)

    def mutate(*_: object) -> None:
        object.__setattr__(head, "generation", 7)
        object.__setattr__(head, "activation_id", _root(0x7777))
        object.__setattr__(profile, "authority_epoch", 99)
        object.__setattr__(registry.bindings[0], "policy_root", _root(0x7778))
        object.__setattr__(purchase_v1.journal, "writer_epoch", 98)
        object.__setattr__(purchase_v2.journal, "writer_epoch", 98)
        object.__setattr__(burn.journal, "writer_epoch", 98)

    def restore() -> None:
        object.__setattr__(head, "generation", 0)
        object.__setattr__(head, "activation_id", _root(0x3A2))
        object.__setattr__(profile, "authority_epoch", 11)
        object.__setattr__(registry.bindings[0], "policy_root", fixture.candidate.buyback_policy.policy_root)
        for leaf in (purchase_v1, purchase_v2, burn):
            object.__setattr__(leaf.journal, "writer_epoch", 11)

    fixture.backend.hook = mutate
    try:
        verified_v1 = shell.verify_governed_zdex_amm_purchase_receipt_shadow_v1(
            purchase_v1, profile=profile, authority_head=head, receipt_verifier=fixture.receipt_verifier
        )
        restore()
        verified_v2 = shell.verify_governed_zdex_amm_purchase_receipt_shadow_v2(
            purchase_v2,
            profile=profile,
            policy_registry=registry,
            authority_head=head,
            receipt_verifier=fixture.receipt_verifier,
        )
        restore()
        verified_burn = shell.verify_governed_zdex_burn_receipt_shadow_v1(
            burn, profile=profile, authority_head=head, receipt_verifier=fixture.receipt_verifier
        )
    finally:
        fixture.backend.hook = None
        restore()

    # Assert: every marker carries the pre-I/O owned head and registry roots.
    assert head.authority_root == _GOVERNED_HEAD_ROOT_PIN
    assert verified_v1.authority_head_root == _GOVERNED_HEAD_ROOT_PIN
    assert verified_v1.writer_epoch == 11
    assert verified_v1.binding_root == _GOVERNED_PURCHASE_V1_BINDING_ROOT_PIN
    assert verified_v2.authority_head_root == _GOVERNED_HEAD_ROOT_PIN
    assert verified_v2.policy_registry_root == _GOVERNED_POLICY_REGISTRY_ROOT_PIN
    assert verified_v2.binding_root == _GOVERNED_PURCHASE_V2_BINDING_ROOT_PIN
    assert verified_burn.authority_head_root == _GOVERNED_HEAD_ROOT_PIN
    assert verified_burn.binding_root == _GOVERNED_BURN_V1_BINDING_ROOT_PIN


def test_governed_prepared_subject_is_detached_from_head_profile_and_candidate() -> None:
    fixture, candidate = _candidate()
    head = replace(fixture.authority_head)
    profile = fixture.candidate.profile
    registry = fixture.candidate.policy_registry
    purchase_v2 = _governed_purchase_v2_candidate(fixture, candidate)
    burn = _governed_burn_candidate(fixture, candidate)
    spare_burn = _governed_burn_candidate(fixture, candidate, b"spare")
    binding_root = fixture.receipt_verifier.binding_root

    prepared_v2 = prep.prepare_governed_zdex_amm_purchase_receipt_shadow_v2(
        purchase_v2,
        profile=profile,
        policy_registry=registry,
        authority_head=head,
        verifier_binding_root=binding_root,
    )
    prepared_burn = prep.prepare_governed_zdex_burn_receipt_shadow_v1(
        burn, profile=profile, authority_head=head, verifier_binding_root=binding_root
    )
    v2_facts = (_prepared_facts(prepared_v2.leaf), prepared_v2.authority_head_root, prepared_v2.policy_registry_root)
    burn_facts = _prepared_facts(prepared_burn)

    object.__setattr__(head, "generation", 5)
    object.__setattr__(purchase_v2.journal, "writer_epoch", 77)
    object.__setattr__(burn.receipt, "receipt_bytes", b"mutated")
    snapshot_v2 = prep.snapshot_prepared_governed_zdex_amm_purchase_receipt_v2(prepared_v2)

    assert (_prepared_facts(prepared_v2.leaf), prepared_v2.authority_head_root, prepared_v2.policy_registry_root) == v2_facts
    assert _prepared_facts(prepared_burn) == burn_facts
    assert prepared_v2.authority_head_root == _GOVERNED_HEAD_ROOT_PIN
    assert prepared_v2.verifier_binding_root == _GOVERNED_VERIFIER_BINDING_ROOT_PIN
    assert prepared_v2.leaf.verified_fields.authority_head_root == ZERO_ROOT_V1
    assert prepared_burn.verified_fields.authority_head_root == _GOVERNED_HEAD_ROOT_PIN
    assert snapshot_v2 == prepared_v2 and snapshot_v2 is not prepared_v2
    # The pure governed preparer refuses a binding root that is not the owned head's.
    with pytest.raises(ValueError, match="verifier binding root is outside the head"):
        prep.prepare_governed_zdex_burn_receipt_shadow_v1(
            spare_burn,
            profile=profile,
            authority_head=fixture.authority_head,
            verifier_binding_root=_root(0x5151),
        )
    with pytest.raises(TypeError, match="verifier binding root must be exact str"):
        prep.prepare_governed_zdex_burn_receipt_shadow_v1(
            spare_burn,
            profile=profile,
            authority_head=fixture.authority_head,
            verifier_binding_root=_HostileRoot(binding_root),
        )


# --- semantic mutants (executed, structure-preserving) -----------------------


def test_execute_before_prepare_mutant_is_killed_by_the_no_call_law() -> None:
    original = shell.verify_zdex_amm_purchase_receipt_v1
    target = "    prepared = prepare_zdex_amm_purchase_receipt_v1(candidate)\n"
    mutant_body = (
        "    receipt_verifier.verify_succinct_receipt(\n"
        "        candidate.receipt.receipt_bytes,\n"
        "        expected_image_id=candidate.module_release.guest_image_id,\n"
        "        expected_journal_bytes=b'',\n"
        "    )\n"
        "    prepared = prepare_zdex_amm_purchase_receipt_v1(candidate)\n"
    )
    mutant = _mutant(shell, original, target, mutant_body)
    tampered = _purchase_v1_candidate(b"conditional")
    tampered = replace(
        tampered, receipt=core.ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional")
    )

    # Control: the ordinary law holds on the unmutated shell.
    control_verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="requires a succinct receipt"):
        original(tampered, control_verifier)
    assert control_verifier.calls == []

    # Mutant: the same rejection is raised, but the no-call assertion is reachable and fails.
    mutant_verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="requires a succinct receipt"):
        mutant(tampered, mutant_verifier)
    assert mutant_verifier.calls == [
        (b"conditional", tampered.module_release.guest_image_id, b"")
    ]
    with pytest.raises(AssertionError):
        assert mutant_verifier.calls == []


def test_route_image_mutant_is_killed_by_the_module_image_observation() -> None:
    candidate = _burn_v1_candidate()
    original = prep.prepare_zdex_burn_receipt_v1
    mutant = _mutant(
        prep,
        original,
        "            owned.module_release.guest_image_id,\n",
        "            owned.route_release.guest_image_id,\n",
    )
    assert candidate.module_release.guest_image_id != candidate.route_release.guest_image_id

    # Control: the unmutated preparation requests the module image.
    control = original(candidate)
    assert control.expected_image_id == candidate.module_release.guest_image_id

    # Mutant: the prepared request names the route image, so the observation fails
    # and a shell executing the mutant subject asks the verifier for the wrong image.
    mutated = mutant(candidate)
    assert mutated.expected_image_id == candidate.route_release.guest_image_id
    with pytest.raises(AssertionError):
        assert mutated.expected_image_id == candidate.module_release.guest_image_id
    verifier = _RecordingVerifier()
    marker = shell._execute_prepared_zdex_burn_receipt_v1(mutated, verifier)
    assert verifier.calls[0][1] == candidate.route_release.guest_image_id
    assert marker.binding_root != _BURN_V1_BINDING_ROOT_PIN


def test_mint_from_caller_alias_mutant_is_killed_by_the_alias_mutation_observation() -> None:
    candidate = _purchase_v1_candidate()
    original = shell._execute_prepared_zdex_amm_purchase_receipt_v1
    mutant = _mutant(
        shell,
        original,
        "    return _build_verified_zdex_amm_purchase_v1(owned)\n",
        "    return _build_verified_zdex_amm_purchase_v1(prepared)\n",
    )
    forged_id = _root(78_601)

    def _run(execute: Callable[..., core.VerifiedZDEXAMMPurchaseV1]) -> str:
        prepared = prep.prepare_zdex_amm_purchase_receipt_v1(candidate)
        forged = replace(prepared.verified_fields, module_release_id=forged_id)

        class _MutatingVerifier(_RecordingVerifier):
            def verify_succinct_receipt(
                self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
            ) -> None:
                super().verify_succinct_receipt(
                    receipt_bytes,
                    expected_image_id=expected_image_id,
                    expected_journal_bytes=expected_journal_bytes,
                )
                object.__setattr__(prepared, "verified_fields", forged)

        return execute(prepared, _MutatingVerifier()).module_release_id

    # Control: the unmutated shell reports the executed subject.
    assert _run(original) == candidate.module_release.release_id
    # Mutant: the caller alias relabels the marker, so the observation fails.
    assert _run(mutant) == forged_id
    with pytest.raises(AssertionError):
        assert _run(mutant) == candidate.module_release.release_id


def test_missing_field_to_request_binding_mutant_is_killed_by_the_digest_observation() -> None:
    candidate = _purchase_v1_candidate()
    original = prep._snapshot_prepared_leaf_receipt_v1
    mutant = _mutant(
        prep,
        original,
        "    _require_prepared_digests_v1(prepared, name=name)\n",
        "    pass\n",
    )
    prepared = prep.prepare_zdex_amm_purchase_receipt_v1(candidate)
    inconsistent = replace(
        prepared, verified_fields=replace(prepared.verified_fields, receipt_digest=_digest(b"other"))
    )

    # Control: the unmutated snapshot refuses a record whose digest is unbound to its bytes.
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        original(inconsistent, prep.PreparedZDEXAMMPurchaseReceiptV1, name="prepared ZDEX purchase")
    # Mutant: the same record is accepted with its digest unbound from its bytes, so the
    # control rejection is unreachable and the shell would execute unbound bytes.
    accepted = mutant(inconsistent, prep.PreparedZDEXAMMPurchaseReceiptV1, name="prepared ZDEX purchase")
    assert accepted == inconsistent
    assert accepted.verified_fields.receipt_digest != _digest(accepted.receipt_bytes)
    verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        shell._execute_prepared_zdex_amm_purchase_receipt_v1(inconsistent, verifier)
    assert verifier.calls == []


def _governed_burn_head_after_callback(
    verify: Callable[..., core.VerifiedZDEXBurnV1],
) -> str:
    fixture, candidate = _candidate()
    head = fixture.authority_head
    burn = _governed_burn_candidate(fixture, candidate)
    fixture.backend.hook = lambda *_: object.__setattr__(head, "generation", 7)
    try:
        verified = verify(
            burn,
            profile=fixture.candidate.profile,
            authority_head=head,
            receipt_verifier=fixture.receipt_verifier,
        )
    finally:
        fixture.backend.hook = None
    assert head.authority_root != _GOVERNED_HEAD_ROOT_PIN
    return verified.authority_head_root


def test_post_io_authority_relabel_mutant_is_killed_by_the_head_mutation_observation() -> None:
    """Failing-first evidence for the named ownership repair.

    The old governed wrapper read ``authority_head.authority_root`` from the
    caller alias after the Bound verifier call.  The mutant restores that read;
    a callback that mutates the caller-held head then relabels the marker.
    """

    original = shell.verify_governed_zdex_burn_receipt_shadow_v1
    target = (
        "    return _execute_prepared_zdex_burn_receipt_v1(\n"
        "        prepared,\n"
        "        _ProfileLaneReceiptVerifierV1(\n"
        "            receipt_verifier,\n"
        "            owned_profile,\n"
        "            LaneIdV1.ZDEX_TOKENOMICS,\n"
        "            prepared.verified_fields.module_release_id,\n"
        "        ),\n"
        "    )\n"
    )
    mutant_body = (
        "    verified = _execute_prepared_zdex_burn_receipt_v1(\n"
        "        prepared,\n"
        "        _ProfileLaneReceiptVerifierV1(\n"
        "            receipt_verifier,\n"
        "            owned_profile,\n"
        "            LaneIdV1.ZDEX_TOKENOMICS,\n"
        "            prepared.verified_fields.module_release_id,\n"
        "        ),\n"
        "    )\n"
        "    return VerifiedZDEXBurnV1(\n"
        "        _VERIFIED_BURN_TOKEN,\n"
        "        replace(verified._fields, authority_head_root=authority_head.authority_root),\n"
        "    )\n"
    )
    mutant = _mutant(
        shell,
        original,
        target,
        mutant_body,
        {"replace": replace, "_VERIFIED_BURN_TOKEN": core._VERIFIED_BURN_TOKEN},
    )

    # Control: the repaired shell reports the owned pre-I/O head root.
    assert _governed_burn_head_after_callback(original) == _GOVERNED_HEAD_ROOT_PIN
    # Mutant: the post-I/O alias read relabels the marker, so the observation fails.
    assert _governed_burn_head_after_callback(mutant) != _GOVERNED_HEAD_ROOT_PIN
    with pytest.raises(AssertionError):
        assert _governed_burn_head_after_callback(mutant) == _GOVERNED_HEAD_ROOT_PIN
