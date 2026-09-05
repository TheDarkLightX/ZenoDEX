"""Bind the derived acquisition-to-burn identity to the running SHADOW route.

`Proofs/ZDEXAcquisitionBurnOccurrenceV2.lean` derives `purchased = burned` from
the conservation obligation instead of assuming it, and proves two limits of
that argument: the accounting rows carry no occurrence burn port, and diverting
acquired ZDEX to an unrelated principal can preserve per-asset conservation.
The runtime plan retains separate occurrence consumption data, outside this
Lean row model.

These tests check the Lean model against the plan and states that
`compose_zdex_atomic_buyback_route_shadow_v2` actually produces, and exercise
`refine_zdex_atomic_buyback_route_state_v2` as the unchanged oracle for the
amount mutants and the ownership limit.
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.global_economic_proof_v1 import RouteCompositionJournalV1
from src.core.global_settlement_types_v1 import (
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
)
from src.core.zdex_atomic_buyback_lane_receipt_v2 import (
    snapshot_verified_zdex_buyback_lane_composition_v2,
)
from src.core.zdex_atomic_buyback_route_composition_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
    ZDEXAtomicBuybackRouteRejectCodeV2,
    ZDEXAtomicBuybackRouteRejectedV2,
    compose_zdex_atomic_buyback_route_shadow_v2,
)
from src.core.zdex_atomic_buyback_route_refinement_v2 import (
    ZDEXAtomicBuybackStateRefinementCandidateV2,
    refine_zdex_atomic_buyback_route_state_v2,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from tests.core.test_zdex_atomic_buyback_route_composition_v2 import (
    _verified_route_candidate,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXAcquisitionBurnOccurrenceV2.lean"

# `_amount_totals_by_asset_v1` folds exactly these three effect tables.
OWNED_KINDS = frozenset(
    {
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        EconomicEffectKindV1.CUSTODY,
        EconomicEffectKindV1.RESERVE,
    }
)
# `_effect_supply_delta_rows_v1` moves supply from exactly these two.
SUPPLY_KINDS = frozenset({EconomicEffectKindV1.ISSUE, EconomicEffectKindV1.BURN})

# Only the standard Lean axioms may appear. `sorryAx` never may.
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

AXIOM_CHECKED_THEOREMS = (
    "conservation_forces_plan_balance",
    "conservation_forces_exact_burn",
    "mismatched_burn_breaks_conservation",
    "acquisition_without_burn_is_unrefinable",
    "route_conservation_forces_exact_burn",
    "route_acquisition_leg_alone_is_unrefinable",
    "conservation_cannot_bind_the_acquisition_occurrence",
    "conservation_admits_owner_diversion",
    "witness_route_is_refinable",
    "witness_burn_is_pinned",
)

REQUIRED_DECLARATIONS = (
    "theorem assetTotal_merge_same_key",
    "theorem assetTotal_drop_zero_row",
    "theorem project_owned",
    "theorem project_supply",
    "theorem conservation_forces_plan_balance",
    "theorem conservation_forces_exact_burn",
    "theorem mismatched_burn_breaks_conservation",
    "theorem acquisition_without_burn_is_unrefinable",
    "theorem acquisition_leg_owned_zdex",
    "theorem acquisition_leg_supply_zdex",
    "theorem burn_leg_owned_zdex",
    "theorem burn_leg_supply_zdex",
    "theorem route_owned_zdex",
    "theorem route_supply_zdex",
    "theorem route_conservation_forces_exact_burn",
    "theorem route_acquisition_leg_alone_is_unrefinable",
    "theorem conservation_cannot_bind_the_acquisition_occurrence",
    "theorem conservation_admits_owner_diversion",
    "theorem witness_route_is_refinable",
    "theorem witness_burn_is_pinned",
)


def _owned_delta(plan: GlobalEconomicEffectPlanV1, asset: str) -> int:
    return sum(
        row.delta_atoms
        for row in plan.rows
        if row.kind in OWNED_KINDS and row.asset == asset
    )


def _supply_delta(plan: GlobalEconomicEffectPlanV1, asset: str) -> int:
    return sum(
        row.delta_atoms
        for row in plan.rows
        if row.kind in SUPPLY_KINDS and row.asset == asset
    )


def _state_owned(state: GlobalEconomicStateV1, asset: str) -> int:
    return sum(
        row.amount_atoms
        for table in (state.balances, state.custody, state.reserves)
        for row in table
        if row.asset == asset
    )


def _state_supply(state: GlobalEconomicStateV1, asset: str) -> int:
    return sum(row.amount_atoms for row in state.supplies if row.asset == asset)


def _plan_assets(plan: GlobalEconomicEffectPlanV1) -> tuple[str, ...]:
    return tuple(sorted({row.asset for row in plan.rows}))


def _pinned_lean_executable() -> Path:
    toolchain = (LEAN_PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected_version = toolchain.rsplit(":v", maxsplit=1)[-1]
    resolved = subprocess.run(
        ["elan", "which", "lean"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    )
    lean = Path(resolved.stdout.strip())
    version = subprocess.run(
        [str(lean), "--version"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert lean.is_file()
    assert f"version {expected_version}" in version
    return lean


def test_proof_has_the_required_surface_and_claim_ceiling() -> None:
    # Arrange
    source = PROOF.read_text(encoding="utf-8")

    # Act / Assert
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source) is None
    for declaration in REQUIRED_DECLARATIONS:
        assert declaration in source, declaration
    for nonclaim in (
        "canonical-byte encoding",
        "no hash injectivity",
        "Python/Rust refinement",
        "RISC0 validity",
        "production authority",
    ):
        assert nonclaim in source, nonclaim


def test_proof_checks_with_pinned_lean() -> None:
    # Arrange
    lean = _pinned_lean_executable()

    # Act
    result = subprocess.run(
        [str(lean), "-DwarningAsError=true", str(PROOF)],
        cwd=LEAN_PROJECT,
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )

    # Assert
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_main_theorems_depend_on_no_unexpected_axioms(
    tmp_path: Path,
) -> None:
    """Compiled and axiom-clean, not merely compiled."""

    # Arrange
    lean = _pinned_lean_executable()
    namespace = "Proofs.ZDEXAcquisitionBurnOccurrenceV2"
    directives = "\n".join(
        f"#print axioms {namespace}.{name}" for name in AXIOM_CHECKED_THEOREMS
    )
    probe = tmp_path / "ZDEXAcquisitionBurnOccurrenceV2Axioms.lean"
    probe.write_text(
        PROOF.read_text(encoding="utf-8") + "\n" + directives + "\n",
        encoding="utf-8",
    )

    # Act
    result = subprocess.run(
        [str(lean), str(probe)],
        cwd=LEAN_PROJECT,
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )

    # Assert
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr.strip() == ""
    report = " ".join(result.stdout.split())
    assert "sorryAx" not in report
    for name in AXIOM_CHECKED_THEOREMS:
        marker = f"'{namespace}.{name}' depends on axioms: ["
        assert marker in report, name
        listed = report.split(marker, 1)[1].split("]", 1)[0]
        axioms = {item.strip() for item in listed.split(",") if item.strip()}
        assert axioms <= ALLOWED_AXIOMS, (name, axioms)
    assert len(re.findall(r"depends on axioms", report)) == len(
        AXIOM_CHECKED_THEOREMS
    )


def test_runtime_route_matches_the_modeled_zdex_row_shape() -> None:
    """The Lean theorem's shape hypotheses hold for the real composed plan."""

    # Arrange
    fixture, candidate = _verified_route_candidate()

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    zdex_asset = fixture.tokenomics.journal.zdex_asset_id
    purchased = fixture.spot.journal.purchased_zdex_atoms
    burned = fixture.tokenomics.journal.burned_zdex_atoms
    assert purchased > 0
    zdex_owned_rows = tuple(
        row
        for row in result.effects.rows
        if row.kind in OWNED_KINDS and row.asset == zdex_asset
    )
    zdex_supply_rows = tuple(
        row
        for row in result.effects.rows
        if row.kind in SUPPLY_KINDS and row.asset == zdex_asset
    )
    assert len(zdex_owned_rows) == 1
    assert len(zdex_supply_rows) == 1
    assert zdex_owned_rows[0].kind is EconomicEffectKindV1.CUSTODY
    assert zdex_owned_rows[0].principal == zdex_pool_reserve_principal_v1(
        pool_id=fixture.spot.journal.selected_pool_id, asset_id=zdex_asset
    )
    assert zdex_owned_rows[0].custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
    assert zdex_owned_rows[0].delta_atoms == -purchased
    assert zdex_supply_rows[0].kind is EconomicEffectKindV1.BURN
    assert zdex_supply_rows[0].principal == ZDEX_SUPPLY_PRINCIPAL_V1
    assert zdex_supply_rows[0].custody_domain == PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1
    assert zdex_supply_rows[0].delta_atoms == -burned
    assert _owned_delta(result.effects, zdex_asset) == -purchased
    assert _supply_delta(result.effects, zdex_asset) == -burned
    # Lane disjointness on ZDEX: the acquisition lane owns the whole owned
    # movement and no supply movement, and the burn lane owns the reverse.
    spot_lane = snapshot_verified_zdex_buyback_lane_composition_v2(
        candidate.verified_spot_lane
    )
    tokenomics_lane = snapshot_verified_zdex_buyback_lane_composition_v2(
        candidate.verified_tokenomics_lane
    )
    assert _owned_delta(spot_lane.effects, zdex_asset) == -purchased
    assert _supply_delta(spot_lane.effects, zdex_asset) == 0
    assert _owned_delta(tokenomics_lane.effects, zdex_asset) == 0
    assert _supply_delta(tokenomics_lane.effects, zdex_asset) == -burned


def test_runtime_projection_matches_the_modeled_projection() -> None:
    """Post totals equal pre totals plus the plan deltas on every touched asset."""

    # Arrange
    fixture, candidate = _verified_route_candidate()

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    pre_state = fixture.global_pre_state
    assets = _plan_assets(result.effects)
    assert len(assets) == 2
    for asset in assets:
        assert _state_owned(result.post_state, asset) == _state_owned(
            pre_state, asset
        ) + _owned_delta(result.effects, asset)
        assert _state_supply(result.post_state, asset) == _state_supply(
            pre_state, asset
        ) + _supply_delta(result.effects, asset)
        # `_require_conservation_refinement_v1` on the pre-state and post-state.
        assert _state_owned(pre_state, asset) == _state_supply(pre_state, asset)
        assert _state_owned(result.post_state, asset) == _state_supply(
            result.post_state, asset
        )
        # The identity the Lean file derives from those four facts.
        assert _owned_delta(result.effects, asset) == _supply_delta(
            result.effects, asset
        )


def test_composed_plan_carries_no_occurrence_burn_port_row() -> None:
    """Row-principal accounting omits the plan's separate occurrence binding."""

    # Arrange
    fixture, candidate = _verified_route_candidate()
    burn_port = zdex_occurrence_burn_port_v1(
        profile_root=fixture.profile.profile_id,
        route_release_id=fixture.route.route_release_id,
        command_occurrence_id=fixture.occurrence.occurrence_id,
    )
    foreign_burn_port = zdex_occurrence_burn_port_v1(
        profile_root=fixture.profile.profile_id,
        route_release_id=fixture.route.route_release_id,
        command_occurrence_id=fixture.route.route_release_id,
    )

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    assert burn_port != foreign_burn_port
    assert result.effects.occurrence_consumptions == (fixture.occurrence.occurrence_id,)
    # The Spot private port names the burn port as the purchased-output sink.
    assert fixture.spot.ports.purchased_output.destination_principal == burn_port
    # No state-bearing row credits it, so no conservation predicate sees it.
    assert all(row.principal != burn_port for row in result.effects.rows)
    assert all(row.owner != burn_port for row in result.post_state.custody)
    assert all(row.owner != burn_port for row in result.post_state.balances)
    assert all(row.owner != burn_port for row in result.post_state.reserves)


def _rebound_burn_mutant(
    result: ZDEXAtomicBuybackRouteAcceptedV2,
    zdex_asset: str,
    extra: int,
) -> tuple[
    GlobalEconomicStateV1, GlobalEconomicEffectPlanV1, RouteCompositionJournalV1
]:
    """Burn `extra` atoms more than acquired, rebinding everything a forger can."""

    rows = tuple(
        EconomicEffectRowV1(
            row.kind,
            row.principal,
            row.asset,
            row.custody_domain,
            row.delta_atoms - extra
            if row.kind is EconomicEffectKindV1.BURN
            else row.delta_atoms,
        )
        for row in result.effects.rows
    )
    conservation = tuple(
        AssetConservationRowV1(
            row.asset,
            row.owned_and_custodied_pre_atoms,
            row.owned_and_custodied_post_atoms - extra
            if row.asset == zdex_asset
            else row.owned_and_custodied_post_atoms,
            row.supply_pre_atoms,
            row.supply_post_atoms - extra
            if row.asset == zdex_asset
            else row.supply_post_atoms,
            row.authorized_issue_atoms,
            row.authorized_burn_atoms + extra
            if row.asset == zdex_asset
            else row.authorized_burn_atoms,
        )
        for row in result.effects.asset_conservation
    )
    mutated_plan = GlobalEconomicEffectPlanV1(
        rows,
        conservation,
        result.effects.fee_conservation,
        result.effects.lane_writes,
        result.effects.occurrence_consumptions,
        result.effects.external_outbox_enqueue,
    )
    mutated_post = replace(
        result.post_state,
        supplies=tuple(
            AssetSupplyV1(
                row.asset,
                row.amount_atoms - extra
                if row.asset == zdex_asset
                else row.amount_atoms,
            )
            for row in result.post_state.supplies
        ),
    )
    mutated_journal = replace(
        result.route_journal,
        post_state_root=mutated_post.state_root,
    )
    return mutated_post, mutated_plan, mutated_journal


@pytest.mark.parametrize("extra", (1, -1))
def test_burn_other_than_the_acquisition_is_killed_by_conservation(extra: int) -> None:
    """Only owned-equals-supply rejects a fully rebound over- or under-burn."""

    # Arrange
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    zdex_asset = fixture.tokenomics.journal.zdex_asset_id
    mutated_post, mutated_plan, mutated_journal = _rebound_burn_mutant(
        result, zdex_asset, extra
    )
    assert _supply_delta(mutated_plan, zdex_asset) == _supply_delta(
        result.effects, zdex_asset
    ) - extra
    assert _owned_delta(mutated_plan, zdex_asset) == _owned_delta(
        result.effects, zdex_asset
    )

    # Act / Assert
    with pytest.raises(ValueError, match="owned total does not equal supply"):
        refine_zdex_atomic_buyback_route_state_v2(
            ZDEXAtomicBuybackStateRefinementCandidateV2(
                fixture.global_pre_state,
                mutated_post,
                mutated_plan,
                fixture.occurrence,
                mutated_journal,
                candidate.verified_spot_leaf,
                candidate.verified_tokenomics_leaf,
            )
        )


def test_unmutated_route_state_refinement_accepts() -> None:
    """The mutant oracle is not vacuously failing."""

    # Arrange
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2

    # Act
    refinement = refine_zdex_atomic_buyback_route_state_v2(
        ZDEXAtomicBuybackStateRefinementCandidateV2(
            fixture.global_pre_state,
            result.post_state,
            result.effects,
            fixture.occurrence,
            result.route_journal,
            candidate.verified_spot_leaf,
            candidate.verified_tokenomics_leaf,
        )
    )

    # Assert
    assert refinement.state_delta_root == result.state_delta_root
    assert refinement.fee_disposition_root == result.fee_disposition_root


def test_conservation_refinement_does_not_pin_the_acquisition_owner() -> None:
    """Runtime counterpart of `conservation_admits_owner_diversion`.

    A plan that debits the governed pool by one atom more and credits that atom
    to an unrelated principal keeps every per-asset owned total identical, so the
    state refinement admits it. Ownership of the acquisition is bound by the
    receipt-authenticated Spot leaf effects, not by this checker. The assertion
    records that scope; it is not a reachable path for the composer, which
    consumes only verified lane handles.
    """

    # Arrange
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    zdex_asset = fixture.tokenomics.journal.zdex_asset_id
    purchased = fixture.spot.journal.purchased_zdex_atoms
    pool_principal = next(
        row.principal
        for row in result.effects.rows
        if row.asset == zdex_asset and row.kind is EconomicEffectKindV1.CUSTODY
    )
    unbound_principal = "0x" + "ab" * 32
    diverted = 1
    diverted_rows = tuple(
        sorted(
            tuple(
                EconomicEffectRowV1(
                    row.kind,
                    row.principal,
                    row.asset,
                    row.custody_domain,
                    row.delta_atoms - diverted
                    if (row.principal == pool_principal and row.asset == zdex_asset)
                    else row.delta_atoms,
                )
                for row in result.effects.rows
            )
            + (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    unbound_principal,
                    zdex_asset,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    diverted,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    diverted_plan = GlobalEconomicEffectPlanV1(
        diverted_rows,
        result.effects.asset_conservation,
        result.effects.fee_conservation,
        result.effects.lane_writes,
        result.effects.occurrence_consumptions,
        result.effects.external_outbox_enqueue,
    )
    diverted_post = replace(
        result.post_state,
        custody=tuple(
            sorted(
                tuple(
                    EconomicAmountV1(
                        row.owner,
                        row.asset,
                        row.custody_domain,
                        row.amount_atoms - diverted
                        if (row.owner == pool_principal and row.asset == zdex_asset)
                        else row.amount_atoms,
                    )
                    for row in result.post_state.custody
                )
                + (
                    EconomicAmountV1(
                        unbound_principal,
                        zdex_asset,
                        AMM_POOL_CUSTODY_DOMAIN_V1,
                        diverted,
                    ),
                ),
                key=lambda row: row.key,
            )
        ),
    )
    diverted_journal = replace(
        result.route_journal,
        post_state_root=diverted_post.state_root,
    )

    # Act
    refinement = refine_zdex_atomic_buyback_route_state_v2(
        ZDEXAtomicBuybackStateRefinementCandidateV2(
            fixture.global_pre_state,
            diverted_post,
            diverted_plan,
            fixture.occurrence,
            diverted_journal,
            candidate.verified_spot_leaf,
            candidate.verified_tokenomics_leaf,
        )
    )

    # Assert
    assert _owned_delta(diverted_plan, zdex_asset) == _owned_delta(
        result.effects, zdex_asset
    )
    assert _supply_delta(diverted_plan, zdex_asset) == _supply_delta(
        result.effects, zdex_asset
    )
    pool_debit = sum(
        row.delta_atoms
        for row in diverted_plan.rows
        if row.principal == pool_principal and row.asset == zdex_asset
    )
    assert pool_debit == -(purchased + diverted)
    assert refinement.state_delta_root != result.state_delta_root


def test_foreign_occurrence_is_refused_before_any_effect_projection() -> None:
    """Occurrence exactness comes from receipt binding, never from conservation."""

    # Arrange
    _, candidate = _verified_route_candidate()
    foreign = replace(
        candidate,
        occurrence=replace(candidate.occurrence, nonce=candidate.occurrence.nonce + 1),
    )

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(foreign)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteRejectedV2
    assert result.code is ZDEXAtomicBuybackRouteRejectCodeV2.RECEIPT_BINDING_MISMATCH
    assert result.post_state is result.pre_state
    assert result.effects.is_empty


def test_acquisition_leg_alone_cannot_reach_a_conserving_state() -> None:
    """Runtime counterpart of `route_acquisition_leg_alone_is_unrefinable`."""

    # Arrange
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    zdex_asset = fixture.tokenomics.journal.zdex_asset_id
    spot_only = GlobalEconomicEffectPlanV1(
        tuple(
            row
            for row in result.effects.rows
            if row.kind is not EconomicEffectKindV1.BURN
        ),
        (),
        result.effects.fee_conservation,
        result.effects.lane_writes,
        result.effects.occurrence_consumptions,
        result.effects.external_outbox_enqueue,
    )
    # Rebind the candidate to the zero-supply-movement plan. This avoids a
    # stale post-supply or journal-root mismatch masking the conservation check.
    acquisition_post = replace(
        result.post_state, supplies=fixture.global_pre_state.supplies
    )
    acquisition_journal = replace(
        result.route_journal, post_state_root=acquisition_post.state_root
    )

    # Act / Assert
    assert _owned_delta(spot_only, zdex_asset) == -fixture.spot.journal.purchased_zdex_atoms
    assert _supply_delta(spot_only, zdex_asset) == 0
    # Owned falls while supply cannot move, so no post-state conserves.
    assert _owned_delta(spot_only, zdex_asset) != _supply_delta(spot_only, zdex_asset)
    with pytest.raises(ValueError, match="owned total does not equal supply"):
        refine_zdex_atomic_buyback_route_state_v2(
            ZDEXAtomicBuybackStateRefinementCandidateV2(
                fixture.global_pre_state,
                acquisition_post,
                spot_only,
                fixture.occurrence,
                acquisition_journal,
                candidate.verified_spot_leaf,
                candidate.verified_tokenomics_leaf,
            )
        )
