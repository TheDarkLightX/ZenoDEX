"""Pure custody-backed Spot/asset composition; all outputs have authority NONE.

The existing swap kernel owns arithmetic. This adapter owns complete state,
command and nonce binding. Authentication, time provenance, proof admission
and publication remain shell obligations. No candidate is a receipt.
"""

from dataclasses import dataclass, fields, replace
from enum import Enum

from ..state.intents import SwapIntent, _require_owned_intent_fields
from .asset_lane_custody_global_v2 import _require_complete_projection
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    custody_policy_origins_hold_v2,
    snapshot_asset_lane_custody_state_v2,
)
from .asset_transfer_types_v2 import AssetClassV2, AssetTransferStateV2
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
    MAX_U64_V2,
    AssetConservationRowV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    FeeConservationRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_root_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)
from .spot_swap_plan_v2 import (
    SpotSwapContextV2,
    SpotSwapPlanV2,
    SpotSwapRejectCodeV2,
    SpotSwapRejectedV2,
    _integer,
    _snapshot_intent,
    plan_spot_swap_v2,
)
from .spot_swap_state_v2 import (
    SpotIntentNonceV2,
    SpotSwapStateV2,
    _require_spot_owner_v2,
    snapshot_spot_swap_state_v2,
)

SPOT_POOL_CUSTODY_DOMAIN_V2 = "spot_pool"


class SpotSwapGlobalRejectCodeV2(str, Enum):
    OCCURRENCE_CONTEXT_MISMATCH = "OCCURRENCE_CONTEXT_MISMATCH"
    OCCURRENCE_COMMAND_MISMATCH = "OCCURRENCE_COMMAND_MISMATCH"
    REPLAY_ALREADY_CONSUMED = "REPLAY_ALREADY_CONSUMED"
    PROJECTION_MISMATCH = "PROJECTION_MISMATCH"
    ASSET_ORIGIN_MISMATCH = "ASSET_ORIGIN_MISMATCH"
    UNSUPPORTED_ASSET_POLICY = "UNSUPPORTED_ASSET_POLICY"
    SUCCESSOR_REJECTED = "SUCCESSOR_REJECTED"


@dataclass(frozen=True, slots=True)
class SpotSwapGlobalRejectedV2:
    code: SpotSwapGlobalRejectCodeV2 | SpotSwapRejectCodeV2
    pre_state_root: str

    @property
    def post_state_root(self) -> str:
        return self.pre_state_root

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return GlobalEconomicEffectPlanV2.empty()


@dataclass(frozen=True, slots=True, init=False)
class SpotSwapGlobalAcceptedV2:
    _post_assets: AssetLaneCustodyStateV2
    _post_spot: SpotSwapStateV2
    _post_state: GlobalEconomicStateV2
    _effects: GlobalEconomicEffectPlanV2
    refinement: GlobalEconomicStateEffectRefinementV2
    statement_root: str

    def __init__(self, post_assets: AssetLaneCustodyStateV2, post_spot: SpotSwapStateV2,
                 candidate: GlobalEconomicStateEffectRefinementCandidateV2, statement_root: str) -> None:
        if type(candidate) is not GlobalEconomicStateEffectRefinementCandidateV2:
            raise TypeError("Spot refinement candidate must be exact")
        _require_root_v2(statement_root, name="Spot input statement root")
        assets, spot = snapshot_asset_lane_custody_state_v2(post_assets), snapshot_spot_swap_state_v2(post_spot)
        owned = replace(candidate)
        state = owned.post_state
        _require_complete_projection(assets, state)
        require_spot_swap_projection_v2(spot, state)
        refinement = refine_global_economic_state_effects_v2(owned)
        object.__setattr__(self, "_post_assets", assets)
        object.__setattr__(self, "_post_spot", spot)
        object.__setattr__(self, "_post_state", state)
        object.__setattr__(self, "_effects", owned.effect_plan)
        object.__setattr__(self, "refinement", refinement)
        object.__setattr__(self, "statement_root", statement_root)

    @property
    def post_assets(self) -> AssetLaneCustodyStateV2:
        return snapshot_asset_lane_custody_state_v2(self._post_assets)

    @property
    def post_spot(self) -> SpotSwapStateV2:
        return snapshot_spot_swap_state_v2(self._post_spot)

    @property
    def post_state(self) -> GlobalEconomicStateV2:
        return snapshot_global_economic_state_v2(self._post_state)

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return replace(self._effects)


def _pool_holdings(spot: SpotSwapStateV2) -> tuple[EconomicAmountV2, ...]:
    pool = spot.pool
    return tuple(EconomicAmountV2(pool.pool_id, asset, SPOT_POOL_CUSTODY_DOMAIN_V2, amount)
                 for asset, amount in ((pool.asset0, pool.reserve0), (pool.asset1, pool.reserve1)))


def require_spot_swap_projection_v2(spot: SpotSwapStateV2, state: GlobalEconomicStateV2) -> None:
    """Single-pool custody is exact; share claims live only in the Spot root."""
    lane = next(row for row in state.lane_roots if row.lane_id is LaneIdV2.SPOT_LIQUIDITY)
    if (lane.module_release_id, lane.enabled, lane.state_root) != (spot.module_release_id, True, spot.state_root):
        raise ValueError("Spot lane root, release or enablement differs")
    if tuple(row for row in state.custody if row.custody_domain == SPOT_POOL_CUSTODY_DOMAIN_V2) != _pool_holdings(spot):
        raise ValueError("Spot pool custody must equal its two reserves exactly")
    if (any(row.custody_domain == SPOT_POOL_CUSTODY_DOMAIN_V2 for row in state.liabilities)
            or any(row.liability_domain == SPOT_POOL_CUSTODY_DOMAIN_V2 for row in state.terminal_obligations)):
        raise ValueError("Spot share rights cannot coexist with nominal pool atom claims")


def _intent_body(intent: SwapIntent) -> dict[str, object]:
    # Only called after the exact owned SwapIntent snapshot. Include every wire
    # field, including id, salt, deadline, recipient and inner nonce.
    return {field.name: dict(_require_owned_intent_fields(intent.fields)) if field.name == "fields" else getattr(intent, field.name)
            for field in fields(SwapIntent)}


def spot_swap_command_body_v2(intent: SwapIntent) -> dict[str, object]:
    owned = _snapshot_intent(intent)
    if isinstance(owned, SpotSwapRejectedV2):
        raise ValueError("unsupported Spot intent fields")
    return _intent_body(owned)


def _context_reject(state: GlobalEconomicStateV2, intent: SwapIntent,
                    occurrence: EconomicCommandOccurrenceV2) -> SpotSwapGlobalRejectCodeV2 | None:
    code = SpotSwapGlobalRejectCodeV2
    if (occurrence.chain_id, occurrence.deployment_root, occurrence.profile_root,
        occurrence.pre_state_root, occurrence.height) != (
        state.chain_id, state.deployment_root, state.profile_root, state.state_root, state.height + 1,
    ):
        return code.OCCURRENCE_CONTEXT_MISMATCH
    if any(row.replay_id == occurrence.replay_id or row.occurrence_id == occurrence.occurrence_id
           for row in state.replay_state):
        return code.REPLAY_ALREADY_CONSUMED
    if occurrence.consumed_object_ids or occurrence.command_kind != intent.kind.value or (
        occurrence.command_body_hash != hash_economic_command_body_v2(intent.kind.value, _intent_body(intent))
    ):
        return code.OCCURRENCE_COMMAND_MISMATCH
    return None


def _policy_reject(assets: AssetLaneCustodyStateV2, spot: SpotSwapStateV2) -> SpotSwapGlobalRejectCodeV2 | None:
    if not custody_policy_origins_hold_v2(assets):
        return SpotSwapGlobalRejectCodeV2.ASSET_ORIGIN_MISMATCH
    policies = {row.asset: row for row in assets.transfer_state.policies}
    for asset in (spot.pool.asset0, spot.pool.asset1):
        policy = policies.get(asset)
        if policy is None or not policy.enabled or policy.asset_class is AssetClassV2.TAU_NATIVE_COIN \
                or policy.atom_decimals != 8 or policy.transfer_fee_atoms:
            return SpotSwapGlobalRejectCodeV2.UNSUPPORTED_ASSET_POLICY
    return None


def _project_successor(assets: AssetLaneCustodyStateV2, spot: SpotSwapStateV2,
                       state: GlobalEconomicStateV2, plan: SpotSwapPlanV2,
                       occurrence: EconomicCommandOccurrenceV2, statement_root: str) -> SpotSwapGlobalAcceptedV2:
    nonces = {row.owner: row.last_nonce for row in spot.intent_nonces}
    nonces[plan.sender] = plan.intent.get_field("nonce")
    post_spot = SpotSwapStateV2(spot.module_release_id, plan.post_pool, spot.lp_positions,
                              tuple(SpotIntentNonceV2(owner, nonce) for owner, nonce in sorted(nonces.items())))
    asset_in, asset_out = plan.intent.get_field("asset_in"), plan.intent.get_field("asset_out")
    amounts = {row.key: row.amount_atoms for row in state.balances}
    amounts[(asset_in, plan.sender, "accounts")] = plan.post_sender_input_atoms
    amounts[(asset_out, plan.recipient, "accounts")] = plan.post_recipient_output_atoms
    balances = tuple(EconomicAmountV2(owner, asset, domain, value)
                     for (asset, owner, domain), value in sorted(amounts.items()) if value)
    custody = tuple(sorted((*_pool_holdings(post_spot), *(row for row in state.custody
                            if row.custody_domain != SPOT_POOL_CUSTODY_DOMAIN_V2)), key=lambda row: row.key))
    leaf = assets.transfer_state
    post_assets = AssetLaneCustodyStateV2(
        AssetTransferStateV2(leaf.module_release_id, leaf.policies, balances, leaf.supplies),
        assets.origin_registry, assets.managed_policies, custody,
    )
    roots = {LaneIdV2.ASSET_TRANSFER: post_assets.state_root, LaneIdV2.SPOT_LIQUIDITY: post_spot.state_root}
    lane_roots = tuple(replace(row, state_root=roots[row.lane_id]) if row.lane_id in roots else row
                       for row in state.lane_roots)
    post = replace(state, balances=balances, custody=custody, lane_roots=lane_roots, height=state.height + 1,
                   replay_state=tuple(sorted((*state.replay_state, ReplayStateV2(occurrence.replay_id,
                       occurrence.occurrence_id)), key=lambda row: row.replay_id)))
    kinds = EconomicEffectKindV2
    pool_id, domain = spot.pool.pool_id, SPOT_POOL_CUSTODY_DOMAIN_V2
    rows: tuple[EconomicEffectRowV2, ...] = (EconomicEffectRowV2(kinds.ACCOUNT_MOVEMENT, plan.sender, asset_in, "accounts", -plan.amount_in_atoms),
            EconomicEffectRowV2(kinds.ACCOUNT_MOVEMENT, plan.recipient, asset_out, "accounts", plan.amount_out_atoms),
            EconomicEffectRowV2(kinds.CUSTODY, pool_id, asset_in, domain, plan.amount_in_atoms),
            EconomicEffectRowV2(kinds.CUSTODY, pool_id, asset_out, domain, -plan.amount_out_atoms))
    fees: tuple[FeeConservationRowV2, ...] = ()
    if plan.fee_atoms:
        rows += (EconomicEffectRowV2(kinds.FEE_ALLOCATION, pool_id, asset_in, domain, plan.fee_atoms),)
        fees = (FeeConservationRowV2(asset_in, plan.fee_atoms, plan.fee_atoms, 0),)
    supplies = state.supply_atoms_by_asset()
    conservation = tuple(AssetConservationRowV2(asset, supplies[asset], supplies[asset],
                         supplies[asset], supplies[asset], 0, 0) for asset in sorted((asset_in, asset_out)))
    writes = tuple(LaneWriteV2(before.lane_id, before.state_root, after.state_root)
                   for before, after in zip(state.lane_roots, lane_roots, strict=True)
                   if before.state_root != after.state_root)
    effects = GlobalEconomicEffectPlanV2(tuple(sorted(rows, key=lambda row: row.key)), conservation,
                                        fees, writes, (occurrence.occurrence_id,), ())
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        state, post, effects, (occurrence,), GlobalTerminalObligationPlanV2.empty(), GlobalOracleOccurrencePlanV2.empty(),
    )
    return SpotSwapGlobalAcceptedV2(post_assets, post_spot, candidate, statement_root)


def transition_spot_swap_global_v2(assets: AssetLaneCustodyStateV2, spot: SpotSwapStateV2,
                                   state: GlobalEconomicStateV2, intent: SwapIntent,
                                   occurrence: EconomicCommandOccurrenceV2,
                                   block_timestamp: int) -> SpotSwapGlobalAcceptedV2 | SpotSwapGlobalRejectedV2:
    """Derive a complete candidate or logical no-op; malformed values raise.

    Inner intent nonces require last+1. Outer replay nonces remain independent,
    allowing ordinary asset commands between swaps. Neither nonce is consumed
    on rejection. Timestamp provenance must be checked by the future shell.
    """
    assets, spot = snapshot_asset_lane_custody_state_v2(assets), snapshot_spot_swap_state_v2(spot)
    state, occurrence = snapshot_global_economic_state_v2(state), _snapshot_occurrence_v2(occurrence)
    _integer(block_timestamp, "block timestamp", MAX_U64_V2)
    owned = _snapshot_intent(intent)
    if isinstance(owned, SpotSwapRejectedV2):
        return SpotSwapGlobalRejectedV2(owned.code, state.state_root)
    reason = _context_reject(state, owned, occurrence)
    if reason is not None:
        return SpotSwapGlobalRejectedV2(reason, state.state_root)
    try:
        _require_complete_projection(assets, state)
        require_spot_swap_projection_v2(spot, state)
    except ValueError:
        return SpotSwapGlobalRejectedV2(SpotSwapGlobalRejectCodeV2.PROJECTION_MISMATCH, state.state_root)
    reason = _policy_reject(assets, spot)
    if reason is not None:
        return SpotSwapGlobalRejectedV2(reason, state.state_root)
    sender, recipient = owned.sender_pubkey, owned.get_field("recipient", owned.sender_pubkey)
    _require_spot_owner_v2(sender)
    _require_spot_owner_v2(recipient)
    amounts = {row.key: row.amount_atoms for row in state.balances}
    context = SpotSwapContextV2(occurrence.subject_id, block_timestamp,
        amounts.get((owned.get_field("asset_in"), sender, "accounts"), 0),
        amounts.get((owned.get_field("asset_out"), recipient, "accounts"), 0))
    plan = plan_spot_swap_v2(context, spot.pool, owned)
    if isinstance(plan, SpotSwapRejectedV2):
        return SpotSwapGlobalRejectedV2(plan.code, state.state_root)
    if owned.get_field("nonce") != spot.intent_nonce(sender) + 1:
        return SpotSwapGlobalRejectedV2(SpotSwapRejectCodeV2.INVALID_NONCE, state.state_root)
    statement_root = hash_global_v2("spot-swap-global-statement-v2", {
        "pre_state_root": state.state_root, "command": _intent_body(owned),
        "occurrence": occurrence, "block_timestamp": block_timestamp,
    })
    try:
        return _project_successor(assets, spot, state, plan, occurrence, statement_root)
    except ValueError:
        return SpotSwapGlobalRejectedV2(SpotSwapGlobalRejectCodeV2.SUCCESSOR_REJECTED, state.state_root)
