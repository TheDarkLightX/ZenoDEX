"""Route-bound Oracle occurrence authority for GlobalSettlementABI V1.

The verifier derives authority from an exact global pre-state, a route-bound
Oracle policy, and the command's explicit consumed-object set.  The returned
witness grants no publication authority and does not select an active profile
or verify a proof receipt.  Those checks remain with the route and epoch
verifiers plus the atomic commit port.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _require_exact_tuple_items,
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    EvidenceStatusV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    RouteReleaseV1,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

GLOBAL_ORACLE_OCCURRENCE_AUTHORITY_SCHEMA_V1 = (
    "zenodex/global-oracle-occurrence-authority/v1"
)
_AUTHORITY_TOKEN = object()


@dataclass(frozen=True, slots=True)
class GlobalOracleOccurrencePolicyV1:
    """Route-selected Oracle object and maximum observation age in blocks."""

    oracle_id: str
    max_observation_age_blocks: int

    def __post_init__(self) -> None:
        _require_token(self.oracle_id, name="global oracle policy oracle id")
        if type(self.max_observation_age_blocks) is not int:
            raise TypeError("max observation age blocks must be an int")
        _require_nonnegative_int(
            self.max_observation_age_blocks,
            name="global oracle policy max observation age blocks",
        )

    @property
    def policy_root(self) -> str:
        return hash_global_v1(
            "global-oracle-occurrence-policy-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "oracle_id": self.oracle_id,
            "max_observation_age_blocks": self.max_observation_age_blocks,
        }


@dataclass(frozen=True, slots=True)
class GlobalOracleOccurrenceAuthorityCandidateV1:
    pre_state: GlobalEconomicStateV1
    route: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    policy: GlobalOracleOccurrencePolicyV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.pre_state, GlobalEconomicStateV1, "pre-state"),
            (self.route, RouteReleaseV1, "route"),
            (self.occurrence, EconomicCommandOccurrenceV1, "command occurrence"),
            (self.policy, GlobalOracleOccurrencePolicyV1, "Oracle policy"),
        )
        for value, expected_type, name in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"global Oracle authority {name} must be exact typed data")


@dataclass(frozen=True, slots=True)
class _AuthorityFieldsV1:
    pre_state_root: str
    route_release_id: str
    command_occurrence_id: str
    policy_root: str
    oracle_id: str
    occurrence_root: str
    observed_height: int
    state_height: int
    observation_age_blocks: int


class GlobalOracleOccurrenceAuthorityV1:
    """Opaque witness for one governed Oracle occurrence in one exact head."""

    _fields: _AuthorityFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: object) -> None:
        if token is not _AUTHORITY_TOKEN or type(fields) is not _AuthorityFieldsV1:
            raise TypeError("GlobalOracleOccurrenceAuthorityV1 is checker-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("GlobalOracleOccurrenceAuthorityV1 is immutable")

    @property
    def pre_state_root(self) -> str:
        return self._fields.pre_state_root

    @property
    def route_release_id(self) -> str:
        return self._fields.route_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def policy_root(self) -> str:
        return self._fields.policy_root

    @property
    def oracle_id(self) -> str:
        return self._fields.oracle_id

    @property
    def occurrence_root(self) -> str:
        return self._fields.occurrence_root

    @property
    def observed_height(self) -> int:
        return self._fields.observed_height

    @property
    def state_height(self) -> int:
        return self._fields.state_height

    @property
    def observation_age_blocks(self) -> int:
        return self._fields.observation_age_blocks

    @property
    def authority_root(self) -> str:
        return hash_global_v1(
            "global-oracle-occurrence-authority-v1",
            {
                "schema": GLOBAL_ORACLE_OCCURRENCE_AUTHORITY_SCHEMA_V1,
                "pre_state_root": self.pre_state_root,
                "route_release_id": self.route_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "policy_root": self.policy_root,
                "oracle_id": self.oracle_id,
                "occurrence_root": self.occurrence_root,
                "observed_height": self.observed_height,
                "state_height": self.state_height,
                "observation_age_blocks": self.observation_age_blocks,
            },
        )


def _snapshot_route_v1(route: RouteReleaseV1) -> RouteReleaseV1:
    tuple_fields = frozenset(
        {
            "ordered_lanes",
            "module_release_ids",
            "dependency_roles",
            "port_schema_roots",
            "evidence_statuses",
        }
    )
    _require_exact_dataclass_scalars_v1(
        route,
        name="global Oracle authority route",
        tuple_fields=tuple_fields,
    )
    return replace(
        route,
        ordered_lanes=tuple(
            _require_exact_tuple_items(
                route.ordered_lanes,
                LaneIdV1,
                "global Oracle authority route lanes",
            )
        ),
        module_release_ids=tuple(
            _require_exact_tuple_items(
                route.module_release_ids,
                str,
                "global Oracle authority route module release ids",
            )
        ),
        dependency_roles=tuple(
            _require_exact_tuple_items(
                route.dependency_roles,
                str,
                "global Oracle authority route dependency roles",
            )
        ),
        port_schema_roots=tuple(
            _require_exact_tuple_items(
                route.port_schema_roots,
                str,
                "global Oracle authority route port schema roots",
            )
        ),
        evidence_statuses=tuple(
            _require_exact_tuple_items(
                route.evidence_statuses,
                EvidenceStatusV1,
                "global Oracle authority route evidence statuses",
            )
        ),
    )


def _snapshot_policy_v1(
    policy: GlobalOracleOccurrencePolicyV1,
) -> GlobalOracleOccurrencePolicyV1:
    _require_exact_dataclass_scalars_v1(
        policy,
        name="global Oracle authority policy",
    )
    return replace(policy)


def _require_exact_context_v1(
    state: GlobalEconomicStateV1,
    route: RouteReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    policy: GlobalOracleOccurrencePolicyV1,
) -> None:
    if route.oracle_policy_root != policy.policy_root:
        raise ValueError("route oracle policy root mismatch")
    if state.height == (1 << 64) - 1 or occurrence.height != state.height + 1:
        raise ValueError("command occurrence height does not follow pre-state")
    bindings = (
        (occurrence.chain_id, state.chain_id, "command chain mismatch"),
        (
            occurrence.deployment_root,
            state.deployment_root,
            "command deployment mismatch",
        ),
        (occurrence.profile_root, state.profile_root, "command profile mismatch"),
        (occurrence.pre_state_root, state.state_root, "command pre-state root mismatch"),
        (
            occurrence.route_release_id,
            route.route_release_id,
            "command route release mismatch",
        ),
        (occurrence.command_kind, route.command_kind, "command kind mismatch"),
    )
    for actual, expected, error in bindings:
        if actual != expected:
            raise ValueError(error)


def verify_global_oracle_occurrence_authority_v1(
    candidate: GlobalOracleOccurrenceAuthorityCandidateV1,
) -> GlobalOracleOccurrenceAuthorityV1:
    """Check route policy, exact-head consumption, finality, and freshness."""

    if type(candidate) is not GlobalOracleOccurrenceAuthorityCandidateV1:
        raise TypeError("global Oracle authority candidate must be exact typed data")
    state = _snapshot_state_v1(candidate.pre_state)
    route = _snapshot_route_v1(candidate.route)
    occurrence = _snapshot_occurrence_v1(candidate.occurrence)
    policy = _snapshot_policy_v1(candidate.policy)
    _require_exact_context_v1(state, route, occurrence, policy)
    if policy.oracle_id not in occurrence.consumed_object_ids:
        raise ValueError("command does not consume route-bound oracle occurrence")
    oracle_occurrence = next(
        (
            item
            for item in state.oracle_occurrences
            if item.oracle_id == policy.oracle_id
        ),
        None,
    )
    if oracle_occurrence is None:
        raise ValueError("route-bound oracle occurrence is absent from pre-state")
    if not oracle_occurrence.finalized:
        raise ValueError("oracle occurrence is not finalized")
    if oracle_occurrence.observed_height > state.height:
        raise ValueError("oracle occurrence observed height is in the future")
    observation_age_blocks = state.height - oracle_occurrence.observed_height
    if observation_age_blocks > policy.max_observation_age_blocks:
        raise ValueError("oracle occurrence exceeds governed freshness policy")
    fields = _AuthorityFieldsV1(
        pre_state_root=state.state_root,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        policy_root=policy.policy_root,
        oracle_id=policy.oracle_id,
        occurrence_root=oracle_occurrence.occurrence_root,
        observed_height=oracle_occurrence.observed_height,
        state_height=state.height,
        observation_age_blocks=observation_age_blocks,
    )
    for field_name in (
        "pre_state_root",
        "route_release_id",
        "command_occurrence_id",
        "policy_root",
        "occurrence_root",
    ):
        _require_root(getattr(fields, field_name), name=f"Oracle authority {field_name}")
    return GlobalOracleOccurrenceAuthorityV1(_AUTHORITY_TOKEN, fields)


__all__ = [
    "GLOBAL_ORACLE_OCCURRENCE_AUTHORITY_SCHEMA_V1",
    "GlobalOracleOccurrenceAuthorityCandidateV1",
    "GlobalOracleOccurrenceAuthorityV1",
    "GlobalOracleOccurrencePolicyV1",
    "verify_global_oracle_occurrence_authority_v1",
]
