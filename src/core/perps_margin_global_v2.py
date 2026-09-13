"""Pure joint margin/asset successor under GlobalSettlementABI V2.

The existing margin core decides economics. This producer binds its complete
command, reconciles account claims and synchronizes the existing asset frame.
Outputs are unmounted candidates with authority NONE. Authentication, oracle
provenance, route admission and publication belong to separate verifier shells.
"""

from dataclasses import dataclass, replace
from enum import Enum

from .asset_lane_custody_global_v2 import _require_complete_projection
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    custody_policy_origins_hold_v2,
    snapshot_asset_lane_custody_state_v2,
)
from .asset_transfer_types_v2 import AssetClassV2, AssetTransferStateV2
from .global_economic_lifecycle_plan_v2 import derive_global_terminal_obligation_plan_v2
from .global_economic_proof_v2 import EconomicCommandOccurrenceV2, _snapshot_occurrence_v2
from .global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
    refine_global_economic_state_effects_v2,
)
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    ReplayStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_atoms_u128_v2,
    _require_root_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)
from .perps_margin_claims_v2 import advance_margin_claims_v2, require_margin_claim_projection_v2
from .perps_margin_module_v1 import transition_perps_margin_v1
from .perps_margin_state_v2 import PerpsMarginStateV2
from .perps_margin_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PerpsMarginAcceptedV1,
    PerpsMarginCommandV1,
    PerpsMarginContextV1,
    PerpsMarginRejectCodeV1,
    PerpsMarginRejectedV1,
    PerpsMarginStateV1,
)


class PerpsMarginGlobalRejectCodeV2(str, Enum):
    OCCURRENCE_CONTEXT_MISMATCH = "OCCURRENCE_CONTEXT_MISMATCH"
    REPLAY_ALREADY_CONSUMED = "REPLAY_ALREADY_CONSUMED"
    OCCURRENCE_COMMAND_MISMATCH = "OCCURRENCE_COMMAND_MISMATCH"
    PROJECTION_MISMATCH = "PROJECTION_MISMATCH"
    ASSET_ORIGIN_MISMATCH = "ASSET_ORIGIN_MISMATCH"
    UNKNOWN_COLLATERAL = "UNKNOWN_COLLATERAL"
    DISABLED_COLLATERAL = "DISABLED_COLLATERAL"
    UNSUPPORTED_COLLATERAL = "UNSUPPORTED_COLLATERAL"
    INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
    SUCCESSOR_REJECTED = "SUCCESSOR_REJECTED"


@dataclass(frozen=True, slots=True)
class PerpsMarginOracleV2:
    """Explicit candidate oracle data; the constructor does not authenticate it."""

    authority_root: str
    occurrence_root: str
    price_e8: int

    def __post_init__(self) -> None:
        _require_root_v2(self.authority_root, name="margin oracle authority")
        _require_root_v2(self.occurrence_root, name="margin oracle occurrence")
        _require_atoms_u128_v2(self.price_e8, name="margin oracle price")
        if self.price_e8 == 0:
            raise ValueError("margin oracle price must be positive")

    def to_canonical(self) -> dict[str, object]:
        return {
            "authority_root": self.authority_root,
            "occurrence_root": self.occurrence_root,
            "price_e8": self.price_e8,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginGlobalRejectedV2:
    code: PerpsMarginGlobalRejectCodeV2 | PerpsMarginRejectCodeV1
    pre_state_root: str
    post_state_root: str

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return GlobalEconomicEffectPlanV2.empty()

    @property
    def terminal_plan(self) -> GlobalTerminalObligationPlanV2:
        return GlobalTerminalObligationPlanV2.empty()

    @property
    def oracle_plan(self) -> GlobalOracleOccurrencePlanV2:
        return GlobalOracleOccurrencePlanV2.empty()


@dataclass(frozen=True, slots=True, init=False)
class PerpsMarginGlobalAcceptedV2:
    _post_assets: AssetLaneCustodyStateV2
    _post_margin: PerpsMarginStateV2
    _post_state: GlobalEconomicStateV2
    _effects: GlobalEconomicEffectPlanV2
    _terminal_plan: GlobalTerminalObligationPlanV2
    refinement: GlobalEconomicStateEffectRefinementV2
    statement_root: str

    def __init__(
        self,
        post_assets: AssetLaneCustodyStateV2,
        post_margin: PerpsMarginStateV2,
        post_state: GlobalEconomicStateV2,
        effects: GlobalEconomicEffectPlanV2,
        terminal_plan: GlobalTerminalObligationPlanV2,
        refinement: GlobalEconomicStateEffectRefinementV2,
        statement_root: str,
    ) -> None:
        for value, expected in ((post_margin, PerpsMarginStateV2),
                                (effects, GlobalEconomicEffectPlanV2),
                                (terminal_plan, GlobalTerminalObligationPlanV2),
                                (refinement, GlobalEconomicStateEffectRefinementV2)):
            if type(value) is not expected:
                raise TypeError("margin successor fields must have exact declared types")
        assets = snapshot_asset_lane_custody_state_v2(post_assets)
        margin = PerpsMarginStateV2(post_margin.economic_state, post_margin.active_claims)
        state = snapshot_global_economic_state_v2(post_state)
        owned_effects, plan = replace(effects), replace(terminal_plan)
        _require_root_v2(statement_root, name="margin input statement root")
        if (refinement.post_state_root, refinement.effect_plan_root, refinement.terminal_plan_root) != (
            state.state_root, owned_effects.effect_plan_root, plan.plan_root,
        ):
            raise ValueError("margin successor differs from its global refinement")
        _require_complete_projection(assets, state)
        require_margin_claim_projection_v2(margin, state)
        object.__setattr__(self, "_post_assets", assets)
        object.__setattr__(self, "_post_margin", margin)
        object.__setattr__(self, "_post_state", state)
        object.__setattr__(self, "_effects", owned_effects)
        object.__setattr__(self, "_terminal_plan", plan)
        object.__setattr__(self, "refinement", refinement)
        object.__setattr__(self, "statement_root", statement_root)

    @property
    def post_assets(self) -> AssetLaneCustodyStateV2:
        return snapshot_asset_lane_custody_state_v2(self._post_assets)

    @property
    def post_margin(self) -> PerpsMarginStateV2:
        return PerpsMarginStateV2(self._post_margin.economic_state, self._post_margin.active_claims)

    @property
    def post_state(self) -> GlobalEconomicStateV2:
        return snapshot_global_economic_state_v2(self._post_state)

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return replace(self._effects)

    @property
    def terminal_plan(self) -> GlobalTerminalObligationPlanV2:
        return replace(self._terminal_plan)


def _reject(
    state: GlobalEconomicStateV2,
    code: PerpsMarginGlobalRejectCodeV2 | PerpsMarginRejectCodeV1,
) -> PerpsMarginGlobalRejectedV2:
    root = state.state_root
    return PerpsMarginGlobalRejectedV2(code, root, root)


def _context_reject(
    state: GlobalEconomicStateV2,
    command: PerpsMarginCommandV1,
    occurrence: EconomicCommandOccurrenceV2,
) -> PerpsMarginGlobalRejectCodeV2 | None:
    if (
        occurrence.chain_id, occurrence.deployment_root, occurrence.profile_root,
        occurrence.pre_state_root, occurrence.height,
    ) != (
        state.chain_id, state.deployment_root, state.profile_root,
        state.state_root, state.height + 1,
    ):
        return PerpsMarginGlobalRejectCodeV2.OCCURRENCE_CONTEXT_MISMATCH
    if any(row.replay_id == occurrence.replay_id or row.occurrence_id == occurrence.occurrence_id
           for row in state.replay_state):
        return PerpsMarginGlobalRejectCodeV2.REPLAY_ALREADY_CONSUMED
    if occurrence.consumed_object_ids or (occurrence.command_kind, occurrence.command_body_hash) != (
        command.command_kind, hash_economic_command_body_v2(command.command_kind, command),
    ):
        return PerpsMarginGlobalRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH
    return None


def _collateral_reject(
    assets: AssetLaneCustodyStateV2, margin: PerpsMarginStateV2,
) -> PerpsMarginGlobalRejectCodeV2 | None:
    if not custody_policy_origins_hold_v2(assets):
        return PerpsMarginGlobalRejectCodeV2.ASSET_ORIGIN_MISMATCH
    policy = next((row for row in assets.transfer_state.policies
                   if row.asset == margin.economic_state.collateral_asset), None)
    if policy is None:
        return PerpsMarginGlobalRejectCodeV2.UNKNOWN_COLLATERAL
    if not policy.enabled:
        return PerpsMarginGlobalRejectCodeV2.DISABLED_COLLATERAL
    if policy.asset_class is AssetClassV2.TAU_NATIVE_COIN or policy.atom_decimals != 8:
        return PerpsMarginGlobalRejectCodeV2.UNSUPPORTED_COLLATERAL
    return None


def _economic_context(
    state: GlobalEconomicStateV2,
    margin: PerpsMarginStateV2,
    occurrence: EconomicCommandOccurrenceV2,
    oracle: PerpsMarginOracleV2 | None,
) -> PerpsMarginContextV1:
    return PerpsMarginContextV1(
        state.chain_id, state.deployment_root, state.profile_root, state.writer_epoch,
        margin.economic_state.module_release_id, occurrence.occurrence_id,
        occurrence.subject_id, occurrence.grant_root,
        ZERO_ROOT_V2 if oracle is None else oracle.authority_root,
        ZERO_ROOT_V2 if oracle is None else oracle.occurrence_root,
        0 if oracle is None else oracle.price_e8,
    )


def _command_effect_rows(command: PerpsMarginCommandV1) -> tuple[EconomicEffectRowV2, ...]:
    if command.command_kind == PERPS_MARGIN_CLOSE_COMMAND_KIND_V1:
        return ()
    delta = command.amount_atoms if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 \
        else -command.amount_atoms
    # The selected policy determines these three rows. Complete post-projection
    # checks independently relate their amounts to the economic core's output.
    return (
        EconomicEffectRowV2(EconomicEffectKindV2.ACCOUNT_MOVEMENT, command.owner,
                           command.asset, ACCOUNT_CUSTODY_DOMAIN_V1, -delta),
        EconomicEffectRowV2(EconomicEffectKindV2.CUSTODY, command.account_id,
                           command.asset, PERPS_MARGIN_CUSTODY_DOMAIN_V1, delta),
        EconomicEffectRowV2(EconomicEffectKindV2.LIABILITY, command.owner,
                           command.asset, PERPS_MARGIN_CUSTODY_DOMAIN_V1, delta),
    )


def _apply_amount_rows(
    table: tuple[EconomicAmountV2, ...],
    rows: tuple[EconomicEffectRowV2, ...],
    kind: EconomicEffectKindV2,
) -> tuple[EconomicAmountV2, ...]:
    values = {row.key: row.amount_atoms for row in table}
    for row in rows:
        if row.kind is kind:
            key = (row.asset, row.principal, row.custody_domain)
            value = values.get(key, 0) + row.delta_atoms
            if not 0 <= value <= MAX_ATOMS_V2:
                raise ValueError("margin amount update exceeds its range")
            values[key] = value
    return tuple(EconomicAmountV2(principal, asset, domain, amount)
                 for (asset, principal, domain), amount in sorted(values.items()) if amount)


def _project_successor(
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    state: GlobalEconomicStateV2,
    command: PerpsMarginCommandV1,
    occurrence: EconomicCommandOccurrenceV2,
    economic_post: PerpsMarginStateV1,
) -> tuple[
    AssetLaneCustodyStateV2, PerpsMarginStateV2, GlobalEconomicStateV2,
    GlobalEconomicEffectPlanV2, GlobalTerminalObligationPlanV2,
    GlobalEconomicStateEffectRefinementV2,
]:
    rows = _command_effect_rows(command)
    balances = _apply_amount_rows(state.balances, rows, EconomicEffectKindV2.ACCOUNT_MOVEMENT)
    custody = _apply_amount_rows(state.custody, rows, EconomicEffectKindV2.CUSTODY)
    liabilities = _apply_amount_rows(state.liabilities, rows, EconomicEffectKindV2.LIABILITY)
    post_margin, terminals = advance_margin_claims_v2(
        margin, economic_post, state.terminal_obligations, command.account_id,
        occurrence.occurrence_id,
    )
    leaf = assets.transfer_state
    post_assets = AssetLaneCustodyStateV2(
        AssetTransferStateV2(leaf.module_release_id, leaf.policies, balances, leaf.supplies),
        assets.origin_registry, assets.managed_policies, custody,
    )
    roots = {LaneIdV2.ASSET_TRANSFER: post_assets.state_root,
             LaneIdV2.PERPS_MARKET: post_margin.state_root}
    lane_roots = tuple(replace(row, state_root=roots[row.lane_id])
                       if row.lane_id in roots else row for row in state.lane_roots)
    replay = ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id)
    post = replace(
        state, balances=balances, custody=custody, liabilities=liabilities,
        terminal_obligations=terminals, lane_roots=lane_roots, height=state.height + 1,
        replay_state=tuple(sorted((*state.replay_state, replay), key=lambda row: row.replay_id)),
    )
    writes = tuple(LaneWriteV2(before.lane_id, before.state_root, after.state_root)
                   for before, after in zip(state.lane_roots, lane_roots, strict=True)
                   if before.state_root != after.state_root)
    supply = state.supply_atoms_by_asset().get(command.asset, 0)
    conservation = (AssetConservationRowV2(command.asset, supply, supply, supply, supply, 0, 0),) \
        if rows else ()
    effects = GlobalEconomicEffectPlanV2(rows, conservation, (), writes,
                                        (occurrence.occurrence_id,), ())
    plan = derive_global_terminal_obligation_plan_v2(state.terminal_obligations, terminals)
    _require_complete_projection(post_assets, post)
    require_margin_claim_projection_v2(post_margin, post)
    refinement = refine_global_economic_state_effects_v2(
        GlobalEconomicStateEffectRefinementCandidateV2(
            state, post, effects, (occurrence,), plan, GlobalOracleOccurrencePlanV2.empty(),
        )
    )
    return post_assets, post_margin, post, effects, plan, refinement


def transition_perps_margin_global_v2(
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    state: GlobalEconomicStateV2,
    command: PerpsMarginCommandV1,
    occurrence: EconomicCommandOccurrenceV2,
    oracle: PerpsMarginOracleV2 | None = None,
) -> PerpsMarginGlobalAcceptedV2 | PerpsMarginGlobalRejectedV2:
    """Recompute one complete joint candidate with ordered, exact no-op rejects.

    The account nonce is in the body; the outer occurrence nonce independently
    names the subject's replay attempt. Historical V1 outputs are never admitted
    here as receipts. All inputs are pure values requiring external provenance.
    """

    for value, expected in ((assets, AssetLaneCustodyStateV2), (margin, PerpsMarginStateV2),
                            (state, GlobalEconomicStateV2), (command, PerpsMarginCommandV1),
                            (occurrence, EconomicCommandOccurrenceV2)):
        if type(value) is not expected:
            raise TypeError("margin global input must have its exact declared type")
    if oracle is not None and type(oracle) is not PerpsMarginOracleV2:
        raise TypeError("margin oracle must be an exact value or absent")
    assets = snapshot_asset_lane_custody_state_v2(assets)
    margin = PerpsMarginStateV2(margin.economic_state, margin.active_claims)
    state = snapshot_global_economic_state_v2(state)
    command, occurrence = replace(command), _snapshot_occurrence_v2(occurrence)
    oracle = None if oracle is None else replace(oracle)
    context_reject = _context_reject(state, command, occurrence)
    if context_reject is not None:
        return _reject(state, context_reject)
    try:
        _require_complete_projection(assets, state)
        require_margin_claim_projection_v2(margin, state)
    except ValueError:
        return _reject(state, PerpsMarginGlobalRejectCodeV2.PROJECTION_MISMATCH)
    collateral_reject = _collateral_reject(assets, margin)
    if collateral_reject is not None:
        return _reject(state, collateral_reject)
    economic = transition_perps_margin_v1(
        _economic_context(state, margin, occurrence, oracle), margin.economic_state, command,
    )
    if isinstance(economic, PerpsMarginRejectedV1):
        return _reject(state, economic.code)
    if type(economic) is not PerpsMarginAcceptedV1:
        raise TypeError("margin core returned an unexpected result")
    if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1:
        balance = next((row.amount_atoms for row in state.balances
                        if row.key == (command.asset, command.owner, ACCOUNT_CUSTODY_DOMAIN_V1)), 0)
        if balance < command.amount_atoms:
            return _reject(state, PerpsMarginGlobalRejectCodeV2.INSUFFICIENT_BALANCE)
    try:
        projected = _project_successor(assets, margin, state, command, occurrence, economic.post_state)
    except ValueError:
        return _reject(state, PerpsMarginGlobalRejectCodeV2.SUCCESSOR_REJECTED)
    statement_root = hash_global_v2("perps-margin-global-statement-v2", {
        "schema": "zenodex/perps-margin-global-input/v2",
        "pre_state_root": state.state_root,
        "command": command,
        "occurrence": occurrence,
        "oracle": oracle,
    })
    return PerpsMarginGlobalAcceptedV2(*projected, statement_root)
