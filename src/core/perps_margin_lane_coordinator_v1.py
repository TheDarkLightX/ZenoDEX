"""Fail-closed accounting coordinator for one `PERPS_MARKET` margin leaf.

The coordinator refines candidate module rows into a complete accounting
projection with conservation and terminal-obligation coverage. ABI field names
retain `CUSTODY`; this module calls those rows accounting locations and makes no
legal claim about custodianship or key control. Receipt verification, route
composition, settlement, and publication remain separate boundaries.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

from .global_economic_proof_v1 import (
    LaneCompositionJournalV1,
    LaneModuleTransitionJournalV1,
)
from .global_settlement_types_v1 import (
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    TerminalObligationV1,
    _require_nonnegative_int,
    _require_ordered_objects,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .perps_margin_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PerpsMarginPrivatePortV1,
    PerpsMarginStateV1,
)

PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1: Final = (
    "zenodex/perps-margin-lane-projection/v1"
)
PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1: Final = (
    "zenodex/perps-margin-lane-coordinator/v1"
)


@dataclass(frozen=True, slots=True, order=True)
class PerpsMarginModuleCompatibilityV1:
    module_release_id: str
    module_schema: str

    def __post_init__(self) -> None:
        _require_root(self.module_release_id, name="perps compatible module release")
        _require_token(self.module_schema, name="perps compatible module schema")

    def to_canonical(self) -> dict[str, object]:
        return {
            "module_release_id": self.module_release_id,
            "module_schema": self.module_schema,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneProjectionV1:
    lane_state: PerpsMarginStateV1
    balances: tuple[EconomicAmountV1, ...]
    accounting_locations: tuple[EconomicAmountV1, ...]
    liabilities: tuple[EconomicAmountV1, ...]
    supplies: tuple[AssetSupplyV1, ...]
    terminal_obligations: tuple[TerminalObligationV1, ...]

    def __post_init__(self) -> None:
        if type(self.lane_state) is not PerpsMarginStateV1:
            raise TypeError("perps lane projection state must be exact typed data")
        for field_name in ("balances", "accounting_locations", "liabilities"):
            _require_ordered_objects(
                getattr(self, field_name),
                name=f"perps lane projection {field_name}",
                expected_type=EconomicAmountV1,
                key="key",
            )
        _require_ordered_objects(
            self.supplies,
            name="perps lane projection supplies",
            expected_type=AssetSupplyV1,
            key="asset",
        )
        _require_ordered_objects(
            self.terminal_obligations,
            name="perps lane projection terminal obligations",
            expected_type=TerminalObligationV1,
            key="obligation_id",
        )
        if any(
            row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1
            for row in self.balances
        ):
            raise ValueError("perps projection balances must use accounts domain")
        if any(
            row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V1
            for row in self.accounting_locations
        ):
            raise ValueError("perps accounting locations must exclude accounts domain")
        if any(
            row.amount_atoms == 0
            for row in (
                *self.balances,
                *self.accounting_locations,
                *self.liabilities,
            )
        ):
            raise ValueError("perps lane projection must omit zero amount rows")
        self._require_complete_holdings()
        self._require_perps_accounting_locations()
        self._require_perps_liabilities()
        if self.terminal_obligations != self.lane_state.terminal_obligations:
            raise ValueError("perps lane terminal obligations are incomplete")

    def _require_complete_holdings(self) -> None:
        supply = {row.asset: row.amount_atoms for row in self.supplies}
        owned = {asset: 0 for asset in supply}
        for row in (*self.balances, *self.accounting_locations):
            if row.asset not in owned:
                raise ValueError("perps lane holding references an unnamed supply")
            owned[row.asset] += row.amount_atoms
        if owned != supply:
            raise ValueError("perps lane complete holdings must equal supply")

    def _require_perps_accounting_locations(self) -> None:
        expected = {
            (self.lane_state.collateral_asset, account.account_id, PERPS_MARGIN_CUSTODY_DOMAIN_V1): (
                account.collateral_atoms
            )
            for account in self.lane_state.accounts
            if account.collateral_atoms != 0
        }
        actual = {
            row.key: row.amount_atoms
            for row in self.accounting_locations
            if row.custody_domain == PERPS_MARGIN_CUSTODY_DOMAIN_V1
        }
        if actual != expected:
            raise ValueError("perps accounting locations differ from lane accounts")

    def _require_perps_liabilities(self) -> None:
        expected: dict[tuple[str, str, str], int] = {}
        for account in self.lane_state.accounts:
            if account.collateral_atoms == 0:
                continue
            key = (
                self.lane_state.collateral_asset,
                account.owner,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
            )
            expected[key] = expected.get(key, 0) + account.collateral_atoms
        actual = {
            row.key: row.amount_atoms
            for row in self.liabilities
            if row.custody_domain == PERPS_MARGIN_CUSTODY_DOMAIN_V1
        }
        if actual != expected:
            raise ValueError("perps liabilities differ from claimant entitlements")

    @property
    def state_root(self) -> str:
        return hash_global_v1(
            "perps-margin-lane-projection-v1",
            self.to_canonical(),
        )

    def owned_and_custodied_atoms(self, asset: str) -> int:
        _require_token(asset, name="perps lane holding asset")
        return sum(
            row.amount_atoms
            for row in (*self.balances, *self.accounting_locations)
            if row.asset == asset
        )

    def supply_atoms(self, asset: str) -> int:
        _require_token(asset, name="perps lane supply asset")
        for row in self.supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown perps lane supply")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1,
            "lane_state": self.lane_state,
            "balances": self.balances,
            "accounting_locations": self.accounting_locations,
            "liabilities": self.liabilities,
            "supplies": self.supplies,
            "terminal_obligations": self.terminal_obligations,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneCoordinatorContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    coordinator_release_id: str
    command_occurrence_id: str
    compatible_modules: tuple[PerpsMarginModuleCompatibilityV1, ...]

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="perps coordinator chain")
        for field_name in (
            "deployment_root",
            "profile_root",
            "coordinator_release_id",
            "command_occurrence_id",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"perps coordinator {field_name}",
            )
        _require_nonnegative_int(self.writer_epoch, name="perps coordinator epoch")
        _require_ordered_objects(
            self.compatible_modules,
            name="perps compatible modules",
            expected_type=PerpsMarginModuleCompatibilityV1,
            key="module_release_id",
        )
        if not self.compatible_modules:
            raise ValueError("perps coordinator requires a compatible module")


class PerpsMarginLaneCoordinatorRejectCodeV1(str, Enum):
    CONTEXT_MISMATCH = "CONTEXT_MISMATCH"
    MODULE_NOT_REGISTERED = "MODULE_NOT_REGISTERED"
    MODULE_BINDING_MISMATCH = "MODULE_BINDING_MISMATCH"
    EFFECT_SHAPE_MISMATCH = "EFFECT_SHAPE_MISMATCH"
    PROJECTION_BINDING_MISMATCH = "PROJECTION_BINDING_MISMATCH"
    STATE_EFFECT_MISMATCH = "STATE_EFFECT_MISMATCH"


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneCompositionCandidateV1:
    context: PerpsMarginLaneCoordinatorContextV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: PerpsMarginPrivatePortV1
    pre_state: PerpsMarginLaneProjectionV1
    post_state: PerpsMarginLaneProjectionV1
    module_effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.context, PerpsMarginLaneCoordinatorContextV1),
            (self.module_journal, LaneModuleTransitionJournalV1),
            (self.private_port, PerpsMarginPrivatePortV1),
            (self.pre_state, PerpsMarginLaneProjectionV1),
            (self.post_state, PerpsMarginLaneProjectionV1),
            (self.module_effects, GlobalEconomicEffectPlanV1),
        )
        if any(type(value) is not expected for value, expected in expected_types):
            raise TypeError("perps coordinator requires exact typed inputs")


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneCompositionAcceptedV1:
    post_state: PerpsMarginLaneProjectionV1
    effects: GlobalEconomicEffectPlanV1
    lane_journal: LaneCompositionJournalV1


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneCompositionRejectedV1:
    code: PerpsMarginLaneCoordinatorRejectCodeV1
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if self.pre_state_root != self.post_state_root or not self.effects.is_empty:
            raise ValueError("perps coordinator rejection must be an exact no-op")


PerpsMarginLaneCompositionResultV1: TypeAlias = (
    PerpsMarginLaneCompositionAcceptedV1 | PerpsMarginLaneCompositionRejectedV1
)


def _reject(
    code: PerpsMarginLaneCoordinatorRejectCodeV1,
    pre_state: PerpsMarginLaneProjectionV1,
) -> PerpsMarginLaneCompositionRejectedV1:
    return PerpsMarginLaneCompositionRejectedV1(
        code,
        pre_state.state_root,
        pre_state.state_root,
        GlobalEconomicEffectPlanV1.empty(),
    )


def _context_ok(
    context: PerpsMarginLaneCoordinatorContextV1,
    journal: LaneModuleTransitionJournalV1,
) -> bool:
    return (
        journal.chain_id == context.chain_id
        and journal.deployment_root == context.deployment_root
        and journal.profile_root == context.profile_root
        and journal.writer_epoch == context.writer_epoch
        and journal.lane_id is LaneIdV1.PERPS_MARKET
        and journal.command_occurrence_id == context.command_occurrence_id
    )


def _module_ok(
    context: PerpsMarginLaneCoordinatorContextV1,
    journal: LaneModuleTransitionJournalV1,
    port: PerpsMarginPrivatePortV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    compatibility = next(
        (
            row
            for row in context.compatible_modules
            if row.module_release_id == journal.module_release_id
        ),
        None,
    )
    return bool(
        compatibility is not None
        and compatibility.module_schema == port.producer_module_schema
        and port.module_release_id == journal.module_release_id
        and port.command_occurrence_id == context.command_occurrence_id
        and journal.private_port_root == port.port_root
        and journal.effect_plan_root == effects.effect_plan_root
        and port.module_effect_plan_root == effects.effect_plan_root
        and journal.terminal_obligations_root == port.terminal_obligations_root
    )


def _effect_shape_ok(
    context: PerpsMarginLaneCoordinatorContextV1,
    journal: LaneModuleTransitionJournalV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    return (
        effects.asset_conservation == ()
        and effects.fee_conservation == ()
        and effects.external_outbox_enqueue == ()
        and effects.occurrence_consumptions == (context.command_occurrence_id,)
        and effects.lane_writes
        == (
            LaneWriteV1(
                LaneIdV1.PERPS_MARKET,
                journal.pre_lane_root,
                journal.post_lane_root,
            ),
        )
        and all(
            row.kind
            in {
                EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                EconomicEffectKindV1.CUSTODY,
                EconomicEffectKindV1.LIABILITY,
            }
            for row in effects.rows
        )
    )


def _projection_ok(
    journal: LaneModuleTransitionJournalV1,
    port: PerpsMarginPrivatePortV1,
    pre_state: PerpsMarginLaneProjectionV1,
    post_state: PerpsMarginLaneProjectionV1,
) -> bool:
    return (
        journal.pre_lane_root == pre_state.lane_state.state_root
        and journal.post_lane_root == post_state.lane_state.state_root
        and port.market_id == pre_state.lane_state.market_id
        and port.market_id == post_state.lane_state.market_id
        and port.terminal_obligations_root
        == post_state.lane_state.terminal_obligations_root
    )


def _projected_effect_rows(
    state: PerpsMarginLaneProjectionV1,
) -> dict[tuple[str, str, str, str], int]:
    rows: dict[tuple[str, str, str, str], int] = {}
    for kind, values in (
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, state.balances),
        (EconomicEffectKindV1.CUSTODY, state.accounting_locations),
        (EconomicEffectKindV1.LIABILITY, state.liabilities),
    ):
        for row in values:
            rows[(kind.value, row.asset, row.owner, row.custody_domain)] = row.amount_atoms
    return rows


def _state_effects_match(
    pre_state: PerpsMarginLaneProjectionV1,
    post_state: PerpsMarginLaneProjectionV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    pre = _projected_effect_rows(pre_state)
    post = _projected_effect_rows(post_state)
    expected = {
        key: post.get(key, 0) - pre.get(key, 0)
        for key in pre.keys() | post.keys()
        if post.get(key, 0) != pre.get(key, 0)
    }
    actual = {
        (row.kind.value, row.asset, row.principal, row.custody_domain): row.delta_atoms
        for row in effects.rows
    }
    return actual == expected


def _changed_assets(
    pre_state: PerpsMarginLaneProjectionV1,
    post_state: PerpsMarginLaneProjectionV1,
) -> tuple[str, ...]:
    pre = _projected_effect_rows(pre_state)
    post = _projected_effect_rows(post_state)
    assets = {
        key[1]
        for key in pre.keys() | post.keys()
        if pre.get(key, 0) != post.get(key, 0)
    }
    return tuple(sorted(assets))


def _normalized_effects(
    context: PerpsMarginLaneCoordinatorContextV1,
    pre_state: PerpsMarginLaneProjectionV1,
    post_state: PerpsMarginLaneProjectionV1,
    module_effects: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    conservation = tuple(
        AssetConservationRowV1(
            asset=asset,
            owned_and_custodied_pre_atoms=pre_state.owned_and_custodied_atoms(asset),
            owned_and_custodied_post_atoms=post_state.owned_and_custodied_atoms(asset),
            supply_pre_atoms=pre_state.supply_atoms(asset),
            supply_post_atoms=post_state.supply_atoms(asset),
            authorized_issue_atoms=0,
            authorized_burn_atoms=0,
        )
        for asset in _changed_assets(pre_state, post_state)
    )
    return GlobalEconomicEffectPlanV1(
        rows=module_effects.rows,
        asset_conservation=conservation,
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.PERPS_MARKET,
                pre_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=(context.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _coordinator_rejection_code_v1(
    candidate: PerpsMarginLaneCompositionCandidateV1,
) -> PerpsMarginLaneCoordinatorRejectCodeV1 | None:
    context = candidate.context
    journal = candidate.module_journal
    if not _context_ok(context, journal):
        return PerpsMarginLaneCoordinatorRejectCodeV1.CONTEXT_MISMATCH
    if not any(
        row.module_release_id == journal.module_release_id
        for row in context.compatible_modules
    ):
        return PerpsMarginLaneCoordinatorRejectCodeV1.MODULE_NOT_REGISTERED
    if not _module_ok(context, journal, candidate.private_port, candidate.module_effects):
        return PerpsMarginLaneCoordinatorRejectCodeV1.MODULE_BINDING_MISMATCH
    if not _effect_shape_ok(context, journal, candidate.module_effects):
        return PerpsMarginLaneCoordinatorRejectCodeV1.EFFECT_SHAPE_MISMATCH
    if not _projection_ok(
        journal,
        candidate.private_port,
        candidate.pre_state,
        candidate.post_state,
    ):
        return PerpsMarginLaneCoordinatorRejectCodeV1.PROJECTION_BINDING_MISMATCH
    if not _state_effects_match(
        candidate.pre_state,
        candidate.post_state,
        candidate.module_effects,
    ):
        return PerpsMarginLaneCoordinatorRejectCodeV1.STATE_EFFECT_MISMATCH
    return None


def compose_perps_margin_lane_single_v1(
    candidate: PerpsMarginLaneCompositionCandidateV1,
) -> PerpsMarginLaneCompositionResultV1:
    """Refine one exact perps module into a complete accounting projection."""

    if type(candidate) is not PerpsMarginLaneCompositionCandidateV1:
        raise TypeError("perps coordinator candidate must have the exact type")
    rejection = _coordinator_rejection_code_v1(candidate)
    if rejection is not None:
        return _reject(rejection, candidate.pre_state)
    effects = _normalized_effects(
        candidate.context,
        candidate.pre_state,
        candidate.post_state,
        candidate.module_effects,
    )
    context = candidate.context
    journal = LaneCompositionJournalV1(
        chain_id=context.chain_id,
        deployment_root=context.deployment_root,
        profile_root=context.profile_root,
        writer_epoch=context.writer_epoch,
        lane_id=LaneIdV1.PERPS_MARKET,
        coordinator_release_id=context.coordinator_release_id,
        command_occurrence_id=context.command_occurrence_id,
        ordered_module_journal_roots=(candidate.module_journal.journal_root,),
        pre_lane_root=candidate.pre_state.state_root,
        post_lane_root=candidate.post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=(
            candidate.post_state.lane_state.terminal_obligations_root
        ),
    )
    return PerpsMarginLaneCompositionAcceptedV1(
        candidate.post_state,
        effects,
        journal,
    )


__all__ = [
    "PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1",
    "PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1",
    "PerpsMarginModuleCompatibilityV1",
    "PerpsMarginLaneProjectionV1",
    "PerpsMarginLaneCoordinatorContextV1",
    "PerpsMarginLaneCoordinatorRejectCodeV1",
    "PerpsMarginLaneCompositionCandidateV1",
    "PerpsMarginLaneCompositionAcceptedV1",
    "PerpsMarginLaneCompositionRejectedV1",
    "PerpsMarginLaneCompositionResultV1",
    "compose_perps_margin_lane_single_v1",
]
