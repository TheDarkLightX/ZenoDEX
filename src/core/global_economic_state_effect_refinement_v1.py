"""Exact state/effect refinement for the supported GlobalSettlementABI V1 fields.

This deterministic checker binds full pre/post global economic states to the
canonical effect plan. It derives replay insertion from disclosed command
occurrences. Whole-epoch refinement advances state height exactly once for a
nonempty epoch. Per-route refinement requires the first route to reach the
occurrence epoch height and permits later routes to preserve that height. The
zero-occurrence static relation preserves height. Each pre/post state must also
pass state-visible necessary checks: claimant liabilities do not exceed custody
in the same asset and accounting domain, and OPEN terminal obligations do not
exceed the claimant's aggregate liabilities. Balances and reserves cannot back
liabilities. These checks cannot recover omitted terminal domains or validate
the private projection behind an opaque lane root. Oracle occurrences, terminal
obligation transitions, history, exact lane allocation evidence, and external
outbox commit binding remain outside this refinement and cannot change here.

The returned value is an opaque structural witness.  It verifies no receipt,
selects no active profile, applies no durable write, and grants no settlement
or publication authority.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from enum import Enum
from typing import Final, NoReturn

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, RouteCompositionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_tuple_items,
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
    _snapshot_route_journal_v1,
    _snapshot_state_v1,
)
from .global_economic_replay_refinement_v1 import _derive_replay_insertions_v1
from .global_economic_state_delta_v1 import (
    _derive_global_economic_state_delta_v1,
    _DerivedGlobalEconomicStateDeltaV1,
)
from .global_settlement_types_v1 import (
    FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    MIN_DELTA_ATOMS_V1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    TerminalObligationStatusV1,
    _require_atoms_u128,
    _require_root,
    _require_token,
    hash_global_v1,
)

GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1: Final = (
    "zenodex/global-economic-state-effect-refinement/v1"
)
_REFINEMENT_TOKEN = object()
_STATE_BEARING_FEE_KINDS: Final = frozenset(
    {
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        EconomicEffectKindV1.CUSTODY,
        EconomicEffectKindV1.RESERVE,
    }
)


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateEffectRefinementCandidateV1:
    pre_state: GlobalEconomicStateV1
    post_state: GlobalEconomicStateV1
    effect_plan: GlobalEconomicEffectPlanV1
    consumed_occurrences: tuple[EconomicCommandOccurrenceV1, ...] = ()
    route_journals: tuple[RouteCompositionJournalV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.pre_state) is not GlobalEconomicStateV1:
            raise TypeError("economic refinement pre-state must be typed")
        if type(self.post_state) is not GlobalEconomicStateV1:
            raise TypeError("economic refinement post-state must be typed")
        if type(self.effect_plan) is not GlobalEconomicEffectPlanV1:
            raise TypeError("economic refinement effect plan must be typed")
        _require_exact_tuple_items(
            self.consumed_occurrences,
            EconomicCommandOccurrenceV1,
            "consumed occurrences",
        )
        _require_exact_tuple_items(
            self.route_journals,
            RouteCompositionJournalV1,
            "route journals",
        )


@dataclass(frozen=True, slots=True)
class _RefinementFieldsV1:
    pre_state_root: str
    post_state_root: str
    effect_plan_root: str
    state_delta_root: str


class GlobalEconomicStateEffectRefinementV1:
    """Opaque witness produced only after exact state/effect checks pass."""

    _fields: _RefinementFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _RefinementFieldsV1) -> None:
        if token is not _REFINEMENT_TOKEN:
            raise TypeError("GlobalEconomicStateEffectRefinementV1 is checker-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("GlobalEconomicStateEffectRefinementV1 is immutable")

    @property
    def pre_state_root(self) -> str:
        return self._fields.pre_state_root

    @property
    def post_state_root(self) -> str:
        return self._fields.post_state_root

    @property
    def effect_plan_root(self) -> str:
        return self._fields.effect_plan_root

    @property
    def state_delta_root(self) -> str:
        return self._fields.state_delta_root

    @property
    def refinement_root(self) -> str:
        return hash_global_v1(
            "global-economic-state-effect-refinement-v1",
            {
                "schema": GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1,
                "pre_state_root": self._fields.pre_state_root,
                "post_state_root": self._fields.post_state_root,
                "effect_plan_root": self._fields.effect_plan_root,
                "state_delta_root": self._fields.state_delta_root,
            },
        )


def _snapshot_global_economic_state_effect_refinement_v1(
    refinement: GlobalEconomicStateEffectRefinementV1,
) -> GlobalEconomicStateEffectRefinementV1:
    if type(refinement) is not GlobalEconomicStateEffectRefinementV1:
        raise TypeError("economic refinement snapshot requires the exact witness type")
    roots = (
        refinement.pre_state_root,
        refinement.post_state_root,
        refinement.effect_plan_root,
        refinement.state_delta_root,
    )
    if any(type(root) is not str for root in roots):
        raise TypeError("economic refinement snapshot roots must be exact str")
    fields = _RefinementFieldsV1(
        pre_state_root=_require_root(
            refinement.pre_state_root,
            name="economic refinement pre-state root",
        ),
        post_state_root=_require_root(
            refinement.post_state_root,
            name="economic refinement post-state root",
        ),
        effect_plan_root=_require_root(
            refinement.effect_plan_root,
            name="economic refinement effect-plan root",
        ),
        state_delta_root=_require_root(
            refinement.state_delta_root,
            name="economic refinement state-delta root",
        ),
    )
    return GlobalEconomicStateEffectRefinementV1(_REFINEMENT_TOKEN, fields)


def _snapshot_candidate_v1(
    candidate: GlobalEconomicStateEffectRefinementCandidateV1,
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    return GlobalEconomicStateEffectRefinementCandidateV1(
        pre_state=_snapshot_state_v1(candidate.pre_state),
        post_state=_snapshot_state_v1(candidate.post_state),
        effect_plan=_snapshot_effect_plan_v1(candidate.effect_plan),
        consumed_occurrences=tuple(
            _snapshot_occurrence_v1(occurrence)
            for occurrence in _require_exact_tuple_items(
                candidate.consumed_occurrences,
                EconomicCommandOccurrenceV1,
                "consumed occurrences",
            )
        ),
        route_journals=tuple(
            _snapshot_route_journal_v1(journal)
            for journal in _require_exact_tuple_items(
                candidate.route_journals,
                RouteCompositionJournalV1,
                "route journals",
            )
        ),
    )


def _require_fixed_context_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    *,
    expected_post_height: int,
) -> None:
    fixed_fields = (
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "profile_root",
        "oracle_occurrences",
        "terminal_obligations",
        "history_root",
        "outbox",
    )
    if any(getattr(pre_state, field) != getattr(post_state, field) for field in fixed_fields):
        raise ValueError("economic refinement unsupported global field changed")
    if post_state.height != expected_post_height:
        raise ValueError("economic refinement state height progression mismatch")


def _require_nonzero_sparse_amounts_v1(state: GlobalEconomicStateV1) -> None:
    for field in ("balances", "custody", "liabilities", "reserves"):
        if any(row.amount_atoms == 0 for row in getattr(state, field)):
            raise ValueError("economic refinement zero economic amount is non-canonical")


def _require_supported_effects_v1(effect_plan: GlobalEconomicEffectPlanV1) -> None:
    if effect_plan.external_outbox_enqueue:
        raise ValueError("economic refinement external outbox refinement is unavailable")
    if any(
        row.kind in {EconomicEffectKindV1.REWARD, EconomicEffectKindV1.SLASH}
        for row in effect_plan.rows
    ):
        raise ValueError("economic refinement reward and slash labels are unmapped")


class ClaimantBackingRejectCodeV1(str, Enum):
    """Closed reject codes of the state-visible necessary claimant-backing checks.

    Precedence is fixed: any checked-u128 overflow while folding the custody,
    entitlement, or OPEN-terminal tables rejects first; then R1 (entitlements in
    a control domain exceed custody there); then R2 (a claimant's OPEN terminal
    total exceeds that claimant's entitlements). Python and Rust share the
    codes and the exact message strings below.
    """

    CLAIMANT_BACKING_TOTAL_OVERFLOW = "CLAIMANT_BACKING_TOTAL_OVERFLOW"
    LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING = (
        "LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING"
    )
    OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS = (
        "OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS"
    )


CLAIMANT_BACKING_MESSAGE_BY_CODE_V1: Final[Mapping[ClaimantBackingRejectCodeV1, str]] = {
    ClaimantBackingRejectCodeV1.CLAIMANT_BACKING_TOTAL_OVERFLOW: (
        "economic refinement claimant backing total overflows"
    ),
    ClaimantBackingRejectCodeV1.LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING: (
        "economic refinement liabilities exceed same-domain custody backing"
    ),
    ClaimantBackingRejectCodeV1.OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS: (
        "economic refinement open terminal obligations exceed claimant liabilities"
    ),
}
_CLAIMANT_BACKING_CODE_BY_MESSAGE_V1: Final = {
    message: code for code, message in CLAIMANT_BACKING_MESSAGE_BY_CODE_V1.items()
}
CLAIMANT_BACKING_VIEW_SCHEMA_V1: Final = "zenodex/claimant-backing-view/v1"
CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1: Final = "claimant-backing-view-v1"


def _reject_claimant_backing_v1(code: ClaimantBackingRejectCodeV1) -> NoReturn:
    raise ValueError(CLAIMANT_BACKING_MESSAGE_BY_CODE_V1[code])


@dataclass(frozen=True, slots=True, order=True)
class BackingTotalV1:
    """One folded (asset, key) atom total; ``key`` is a control domain or a claimant."""

    asset: str
    key: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="backing total asset")
        _require_token(self.key, name="backing total key")
        _require_atoms_u128(self.amount_atoms, name="backing total atoms")

    def to_canonical(self) -> list[object]:
        return [self.asset, self.key, self.amount_atoms]


def _require_backing_totals_v1(rows: tuple[BackingTotalV1, ...], name: str) -> None:
    if any(type(row) is not BackingTotalV1 for row in rows):
        raise TypeError(f"{name} totals must be exact BackingTotalV1 rows")
    keys = [(row.asset, row.key) for row in rows]
    if keys != sorted(set(keys)):
        raise ValueError(f"{name} totals are not canonically ordered and unique")


@dataclass(frozen=True, slots=True)
class ClaimantBackingViewV1:
    """Owned aggregate of exactly the columns the necessary checks read.

    The view has no reserve or balance column, so reserve or balance masking of
    a claimant entitlement is unrepresentable in the checked input. ``view_root``
    is the shared Python/Rust commitment to the folded totals.
    """

    custody_by_control_domain: tuple[BackingTotalV1, ...]
    entitlements_by_control_domain: tuple[BackingTotalV1, ...]
    entitlements_by_claimant: tuple[BackingTotalV1, ...]
    open_terminals_by_claimant: tuple[BackingTotalV1, ...]

    def __post_init__(self) -> None:
        _require_backing_totals_v1(self.custody_by_control_domain, "custody")
        _require_backing_totals_v1(self.entitlements_by_control_domain, "entitlement domain")
        _require_backing_totals_v1(self.entitlements_by_claimant, "entitlement claimant")
        _require_backing_totals_v1(self.open_terminals_by_claimant, "open terminal")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": CLAIMANT_BACKING_VIEW_SCHEMA_V1,
            "custody_by_control_domain": [
                row.to_canonical() for row in self.custody_by_control_domain
            ],
            "entitlements_by_control_domain": [
                row.to_canonical() for row in self.entitlements_by_control_domain
            ],
            "entitlements_by_claimant": [
                row.to_canonical() for row in self.entitlements_by_claimant
            ],
            "open_terminals_by_claimant": [
                row.to_canonical() for row in self.open_terminals_by_claimant
            ],
        }

    @property
    def view_root(self) -> str:
        return hash_global_v1(CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1, self.to_canonical())


def _fold_backing_totals_v1(
    rows: Iterable[tuple[str, str, int]],
) -> tuple[BackingTotalV1, ...]:
    totals: dict[tuple[str, str], int] = {}
    for asset, key, amount_atoms in rows:
        total = totals.get((asset, key), 0) + amount_atoms
        if total > MAX_ATOMS_V1:
            _reject_claimant_backing_v1(
                ClaimantBackingRejectCodeV1.CLAIMANT_BACKING_TOTAL_OVERFLOW
            )
        totals[(asset, key)] = total
    return tuple(
        BackingTotalV1(asset, key, amount) for (asset, key), amount in sorted(totals.items())
    )


def derive_claimant_backing_view_v1(state: GlobalEconomicStateV1) -> ClaimantBackingViewV1:
    """Fold the V1 custody, liability, and OPEN terminal tables into the backing view.

    Reserves and balances are never read. Every fold uses checked u128
    arithmetic and rejects with the overflow code before any inequality is
    evaluated.
    """

    open_terminals = [
        (obligation.asset, obligation.claimant, obligation.amount_atoms)
        for obligation in state.terminal_obligations
        if obligation.status is TerminalObligationStatusV1.OPEN
    ]
    return ClaimantBackingViewV1(
        custody_by_control_domain=_fold_backing_totals_v1(
            (row.asset, row.custody_domain, row.amount_atoms) for row in state.custody
        ),
        entitlements_by_control_domain=_fold_backing_totals_v1(
            (row.asset, row.custody_domain, row.amount_atoms) for row in state.liabilities
        ),
        entitlements_by_claimant=_fold_backing_totals_v1(
            (row.asset, row.owner, row.amount_atoms) for row in state.liabilities
        ),
        open_terminals_by_claimant=_fold_backing_totals_v1(open_terminals),
    )


def _exceeds_backing_v1(
    claims: tuple[BackingTotalV1, ...], backing: tuple[BackingTotalV1, ...]
) -> bool:
    available = {(row.asset, row.key): row.amount_atoms for row in backing}
    return any(row.amount_atoms > available.get((row.asset, row.key), 0) for row in claims)


def require_claimant_backing_v1(view: ClaimantBackingViewV1) -> None:
    """Reject R1 (same-control-domain backing) then R2 (claimant coverage), in that order."""

    if _exceeds_backing_v1(view.entitlements_by_control_domain, view.custody_by_control_domain):
        _reject_claimant_backing_v1(
            ClaimantBackingRejectCodeV1.LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING
        )
    if _exceeds_backing_v1(view.open_terminals_by_claimant, view.entitlements_by_claimant):
        _reject_claimant_backing_v1(
            ClaimantBackingRejectCodeV1.OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS
        )


def classify_claimant_backing_error_v1(
    error: BaseException,
) -> ClaimantBackingRejectCodeV1 | None:
    """Map an exact claimant-backing message to its closed code; None for any other error."""

    if type(error) is not ValueError:
        return None
    return _CLAIMANT_BACKING_CODE_BY_MESSAGE_V1.get(str(error))


def _require_state_only_necessary_claimant_backing_v1(
    state: GlobalEconomicStateV1,
) -> None:
    """Reject necessary backing failures visible in V1 state bytes.

    This check cannot bind an opaque lane root to its private claimant
    projection or recover a terminal obligation's omitted control domain and
    principal. Exact reconciliation therefore still requires verifier-derived,
    root-bound allocation evidence. Passing this guard grants no authority.
    """

    require_claimant_backing_v1(derive_claimant_backing_view_v1(state))


def _require_fee_mirror_v1(effect_plan: GlobalEconomicEffectPlanV1) -> None:
    state_rows: dict[tuple[str, str, str], int] = {}
    for row in effect_plan.rows:
        if row.kind not in _STATE_BEARING_FEE_KINDS:
            continue
        key = (row.principal, row.asset, row.custody_domain)
        total = state_rows.get(key, 0) + row.delta_atoms
        if not MIN_DELTA_ATOMS_V1 <= total <= MAX_DELTA_ATOMS_V1:
            raise ValueError("economic refinement fee mirror aggregate overflow")
        state_rows[key] = total
    for row in effect_plan.rows:
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION:
            mirrored_delta = state_rows.get(
                (row.principal, row.asset, row.custody_domain),
                0,
            )
            if mirrored_delta < row.delta_atoms:
                raise ValueError("economic refinement fee allocation is not mirrored")
    if any(row.fee_charged_atoms == 0 for row in effect_plan.fee_conservation):
        raise ValueError("economic refinement zero fee conservation row is non-canonical")
    residue_effects = {
        row.asset: row.delta_atoms
        for row in effect_plan.rows
        if row.kind is EconomicEffectKindV1.RESERVE
        and row.principal == FEE_RESIDUE_PRINCIPAL_V1
        and row.custody_domain == FEE_RESIDUE_CONTROL_DOMAIN_V1
        and row.delta_atoms > 0
    }
    expected_residue = {
        row.asset: row.carried_residue_atoms
        for row in effect_plan.fee_conservation
        if row.carried_residue_atoms > 0
    }
    if residue_effects != expected_residue:
        raise ValueError("economic refinement fee residue state mapping mismatch")


def _amount_totals_by_asset_v1(
    state: GlobalEconomicStateV1,
) -> dict[str, int]:
    totals: dict[str, int] = {}
    for field in ("balances", "custody", "reserves"):
        for row in getattr(state, field):
            total = totals.get(row.asset, 0) + row.amount_atoms
            if total > MAX_ATOMS_V1:
                raise ValueError("economic refinement owned total exceeds unsigned 128-bit bounds")
            totals[row.asset] = total
    return totals


def _require_conservation_refinement_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
    state_delta: _DerivedGlobalEconomicStateDeltaV1,
) -> None:
    pre_owned = _amount_totals_by_asset_v1(pre_state)
    post_owned = _amount_totals_by_asset_v1(post_state)
    pre_supply = {row.asset: row.amount_atoms for row in pre_state.supplies}
    post_supply = {row.asset: row.amount_atoms for row in post_state.supplies}
    all_state_assets = set(pre_owned) | set(post_owned) | set(pre_supply) | set(post_supply)
    if any(
        pre_owned.get(asset, 0) != pre_supply.get(asset, 0)
        or post_owned.get(asset, 0) != post_supply.get(asset, 0)
        for asset in all_state_assets
    ):
        raise ValueError("economic refinement owned total does not equal supply")
    touched_assets = set(state_delta.touched_assets) | {
        row.asset
        for row in effect_plan.rows
        if row.kind in {EconomicEffectKindV1.ISSUE, EconomicEffectKindV1.BURN}
    }
    conservation = {row.asset: row for row in effect_plan.asset_conservation}
    if set(conservation) != touched_assets:
        raise ValueError("economic refinement conservation asset set mismatch")
    for asset in touched_assets:
        row = conservation[asset]
        expected = (
            pre_owned.get(asset, 0),
            post_owned.get(asset, 0),
            pre_supply.get(asset, 0),
            post_supply.get(asset, 0),
        )
        actual = (
            row.owned_and_custodied_pre_atoms,
            row.owned_and_custodied_post_atoms,
            row.supply_pre_atoms,
            row.supply_post_atoms,
        )
        if actual != expected:
            raise ValueError("economic refinement conservation state mismatch")


def _refine_snapshot_v1(
    snapshot: GlobalEconomicStateEffectRefinementCandidateV1,
    *,
    expected_post_height: int,
) -> GlobalEconomicStateEffectRefinementV1:
    pre_state = snapshot.pre_state
    post_state = snapshot.post_state
    effect_plan = snapshot.effect_plan
    if bool(effect_plan.occurrence_consumptions) != bool(snapshot.consumed_occurrences):
        raise ValueError("economic refinement occurrence disclosure mismatch")
    _require_fixed_context_v1(
        pre_state,
        post_state,
        expected_post_height=expected_post_height,
    )
    _require_nonzero_sparse_amounts_v1(pre_state)
    _require_nonzero_sparse_amounts_v1(post_state)
    _require_state_only_necessary_claimant_backing_v1(pre_state)
    _require_state_only_necessary_claimant_backing_v1(post_state)
    _require_supported_effects_v1(effect_plan)
    replay_insertions = _derive_replay_insertions_v1(snapshot)
    _require_fee_mirror_v1(effect_plan)
    state_delta = _derive_global_economic_state_delta_v1(
        pre_state, post_state, effect_plan, replay_insertions
    )
    _require_conservation_refinement_v1(
        pre_state,
        post_state,
        effect_plan,
        state_delta,
    )
    return GlobalEconomicStateEffectRefinementV1(
        _REFINEMENT_TOKEN,
        _RefinementFieldsV1(
            pre_state_root=pre_state.state_root,
            post_state_root=post_state.state_root,
            effect_plan_root=effect_plan.effect_plan_root,
            state_delta_root=state_delta.delta_root,
        ),
    )


def refine_global_economic_state_effects_v1(
    candidate: GlobalEconomicStateEffectRefinementCandidateV1,
) -> GlobalEconomicStateEffectRefinementV1:
    """Return an opaque witness for one complete epoch endpoint refinement."""

    if type(candidate) is not GlobalEconomicStateEffectRefinementCandidateV1:
        raise TypeError("economic refinement candidate must be typed")
    snapshot = _snapshot_candidate_v1(candidate)
    has_occurrences = bool(snapshot.effect_plan.occurrence_consumptions)
    if has_occurrences and snapshot.pre_state.height == MAX_U64_V1:
        raise ValueError("economic refinement state height overflow")
    return _refine_snapshot_v1(
        snapshot,
        expected_post_height=snapshot.pre_state.height + int(has_occurrences),
    )


def refine_route_global_economic_state_effects_v1(
    candidate: GlobalEconomicStateEffectRefinementCandidateV1,
) -> GlobalEconomicStateEffectRefinementV1:
    """Refine one route inside an epoch, including its exact intermediate state."""

    if type(candidate) is not GlobalEconomicStateEffectRefinementCandidateV1:
        raise TypeError("route economic refinement candidate must be typed")
    snapshot = _snapshot_candidate_v1(candidate)
    if (
        len(snapshot.consumed_occurrences) != 1
        or len(snapshot.route_journals) != 1
        or len(snapshot.effect_plan.occurrence_consumptions) != 1
    ):
        raise ValueError("route economic refinement requires exactly one occurrence")
    occurrence = snapshot.consumed_occurrences[0]
    post_height = snapshot.post_state.height
    allowed_pre_heights = {post_height}
    if post_height > 0:
        allowed_pre_heights.add(post_height - 1)
    if occurrence.height != post_height or snapshot.pre_state.height not in allowed_pre_heights:
        raise ValueError("route economic refinement epoch height context mismatch")
    return _refine_snapshot_v1(
        snapshot,
        expected_post_height=post_height,
    )


__all__ = [
    "CLAIMANT_BACKING_MESSAGE_BY_CODE_V1",
    "CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1",
    "CLAIMANT_BACKING_VIEW_SCHEMA_V1",
    "GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1",
    "BackingTotalV1",
    "ClaimantBackingRejectCodeV1",
    "ClaimantBackingViewV1",
    "GlobalEconomicStateEffectRefinementCandidateV1",
    "GlobalEconomicStateEffectRefinementV1",
    "classify_claimant_backing_error_v1",
    "derive_claimant_backing_view_v1",
    "require_claimant_backing_v1",
    "_snapshot_global_economic_state_effect_refinement_v1",
    "refine_global_economic_state_effects_v1",
    "refine_route_global_economic_state_effects_v1",
]
