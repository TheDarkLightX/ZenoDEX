"""Route-bound Oracle occurrence authority for GlobalSettlementABI V1.

The verifier derives authority from an exact global pre-state and a route-bound
Oracle policy. Finalized Oracle observations are reusable authenticated reads;
they are not single-use consumed objects. The returned witness grants no
publication authority and does not select an active profile or verify a proof
receipt. Those checks remain with the route and epoch verifiers plus the atomic
commit port.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from threading import Lock
from weakref import WeakKeyDictionary

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
    evaluation_height: int
    observation_age_blocks: int


class GlobalOracleOccurrenceAuthorityV1:
    """Opaque witness for one governed Oracle occurrence in one exact head."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, fields: object) -> None:
        if token is not _AUTHORITY_TOKEN or type(fields) is not _AuthorityFieldsV1:
            raise TypeError("GlobalOracleOccurrenceAuthorityV1 is checker-constructed")
        _register_authority_v1(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("GlobalOracleOccurrenceAuthorityV1 is immutable")

    @property
    def pre_state_root(self) -> str:
        return _authority_fields_v1(self).pre_state_root

    @property
    def route_release_id(self) -> str:
        return _authority_fields_v1(self).route_release_id

    @property
    def command_occurrence_id(self) -> str:
        return _authority_fields_v1(self).command_occurrence_id

    @property
    def policy_root(self) -> str:
        return _authority_fields_v1(self).policy_root

    @property
    def oracle_id(self) -> str:
        return _authority_fields_v1(self).oracle_id

    @property
    def occurrence_root(self) -> str:
        return _authority_fields_v1(self).occurrence_root

    @property
    def observed_height(self) -> int:
        return _authority_fields_v1(self).observed_height

    @property
    def state_height(self) -> int:
        return _authority_fields_v1(self).state_height

    @property
    def evaluation_height(self) -> int:
        return _authority_fields_v1(self).evaluation_height

    @property
    def observation_age_blocks(self) -> int:
        return _authority_fields_v1(self).observation_age_blocks

    @property
    def authority_root(self) -> str:
        fields = _authority_fields_v1(self)
        return hash_global_v1(
            "global-oracle-occurrence-authority-v1",
            {
                "schema": GLOBAL_ORACLE_OCCURRENCE_AUTHORITY_SCHEMA_V1,
                "pre_state_root": fields.pre_state_root,
                "route_release_id": fields.route_release_id,
                "command_occurrence_id": fields.command_occurrence_id,
                "policy_root": fields.policy_root,
                "oracle_id": fields.oracle_id,
                "occurrence_root": fields.occurrence_root,
                "observed_height": fields.observed_height,
                "state_height": fields.state_height,
                "evaluation_height": fields.evaluation_height,
                "observation_age_blocks": fields.observation_age_blocks,
            },
        )


_AUTHORITY_LOCK_V1 = Lock()
_AUTHORITIES_V1: WeakKeyDictionary[
    GlobalOracleOccurrenceAuthorityV1,
    _AuthorityFieldsV1,
] = WeakKeyDictionary()


def _snapshot_authority_fields_v1(fields: _AuthorityFieldsV1) -> _AuthorityFieldsV1:
    if type(fields) is not _AuthorityFieldsV1:
        raise TypeError("global Oracle authority fields must be exact typed data")
    for name, root_value in (
        ("pre-state root", fields.pre_state_root),
        ("route release id", fields.route_release_id),
        ("command occurrence id", fields.command_occurrence_id),
        ("policy root", fields.policy_root),
        ("occurrence root", fields.occurrence_root),
    ):
        if type(root_value) is not str:
            raise TypeError(f"global Oracle authority {name} must be exact text")
        _require_root(root_value, name=f"global Oracle authority {name}")
    if type(fields.oracle_id) is not str:
        raise TypeError("global Oracle authority oracle id must be exact text")
    _require_token(fields.oracle_id, name="global Oracle authority oracle id")
    for name, height_value in (
        ("observed height", fields.observed_height),
        ("state height", fields.state_height),
        ("evaluation height", fields.evaluation_height),
        ("observation age", fields.observation_age_blocks),
    ):
        if type(height_value) is not int:
            raise TypeError(f"global Oracle authority {name} must be an exact int")
        _require_nonnegative_int(
            height_value,
            name=f"global Oracle authority {name}",
        )
    if fields.observed_height > fields.state_height:
        raise ValueError("global Oracle authority observation is in the future")
    if fields.evaluation_height != fields.state_height + 1:
        raise ValueError("global Oracle authority evaluation height mismatch")
    if fields.observation_age_blocks != fields.evaluation_height - fields.observed_height:
        raise ValueError("global Oracle authority observation age mismatch")
    return replace(fields)


def _register_authority_v1(
    authority: GlobalOracleOccurrenceAuthorityV1,
    fields: _AuthorityFieldsV1,
) -> None:
    owned = _snapshot_authority_fields_v1(fields)
    with _AUTHORITY_LOCK_V1:
        if authority in _AUTHORITIES_V1:
            raise RuntimeError("global Oracle authority is already registered")
        _AUTHORITIES_V1[authority] = owned


def _authority_fields_v1(
    authority: GlobalOracleOccurrenceAuthorityV1,
) -> _AuthorityFieldsV1:
    if type(authority) is not GlobalOracleOccurrenceAuthorityV1:
        raise TypeError("global Oracle authority type is not closed")
    with _AUTHORITY_LOCK_V1:
        fields = _AUTHORITIES_V1.get(authority)
    if fields is None:
        raise TypeError("global Oracle authority is not checker-registered")
    return _snapshot_authority_fields_v1(fields)


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
    """Check route policy, exact-head read binding, finality, and freshness."""

    if type(candidate) is not GlobalOracleOccurrenceAuthorityCandidateV1:
        raise TypeError("global Oracle authority candidate must be exact typed data")
    state = _snapshot_state_v1(candidate.pre_state)
    route = _snapshot_route_v1(candidate.route)
    occurrence = _snapshot_occurrence_v1(candidate.occurrence)
    policy = _snapshot_policy_v1(candidate.policy)
    _require_exact_context_v1(state, route, occurrence, policy)
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
    observation_age_blocks = occurrence.height - oracle_occurrence.observed_height
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
        evaluation_height=occurrence.height,
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
