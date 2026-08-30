"""Exact committed-state and Oracle authority for one ZDEX buyback price."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import NoReturn

from .global_economic_profile_snapshot_v1 import _snapshot_route_release_v1
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    MAX_U64_V1,
    GlobalEconomicStateV1,
    RouteReleaseV1,
    _require_atoms_u128,
    hash_global_v1,
)
from .zdex_buyback_price_safety_v1 import (
    VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyObservationV1,
    ZDEXBuybackPriceSafetyPolicyV1,
    ZDEXBuybackPriceSafetyRejectedV1,
    verify_zdex_buyback_price_safety_v1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_pool_reserve_principal_v1,
)

VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_SCHEMA_V1 = (
    "zenodex/verified-zdex-buyback-price-authority/v1"
)
_VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_TOKEN_V1 = object()


class ZDEXBuybackPriceAuthorityRejectCodeV1(str, Enum):
    HEIGHT_OVERFLOW = "HEIGHT_OVERFLOW"
    CONTEXT_MISMATCH = "CONTEXT_MISMATCH"
    ORACLE_AUTHORITY_MISMATCH = "ORACLE_AUTHORITY_MISMATCH"
    QUOTE_RESERVE_ABSENT = "QUOTE_RESERVE_ABSENT"
    ZDEX_RESERVE_ABSENT = "ZDEX_RESERVE_ABSENT"
    RESERVE_AMOUNT_MISMATCH = "RESERVE_AMOUNT_MISMATCH"
    PRICE_ENVELOPE_REJECTED = "PRICE_ENVELOPE_REJECTED"


class ZDEXBuybackPriceAuthorityRejectedV1(ValueError):
    """Typed fail-closed rejection from committed price authority."""

    code: ZDEXBuybackPriceAuthorityRejectCodeV1

    def __init__(
        self,
        code: ZDEXBuybackPriceAuthorityRejectCodeV1,
        detail: str,
    ) -> None:
        if type(code) is not ZDEXBuybackPriceAuthorityRejectCodeV1:
            raise TypeError("ZDEX buyback price authority reject code is not closed")
        self.code = code
        super().__init__(f"{code.value}: {detail}")


def _reject(
    code: ZDEXBuybackPriceAuthorityRejectCodeV1,
    detail: str,
) -> NoReturn:
    raise ZDEXBuybackPriceAuthorityRejectedV1(code, detail)


@dataclass(frozen=True, slots=True)
class ZDEXBuybackPriceAuthorityCandidateV1:
    pre_state: GlobalEconomicStateV1
    route: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    execution_policy: ZDEXBuybackExecutionPolicyV1
    price_policy: ZDEXBuybackPriceSafetyPolicyV1
    price_occurrence: ZDEXBuybackOraclePriceOccurrenceV1
    route_safe_quote_limit_atoms: int
    minimum_output_atoms: int
    expected_quote_reserve_atoms: int
    expected_zdex_reserve_atoms: int
    quote_amount_in_atoms: int
    purchased_zdex_atoms: int

    def __post_init__(self) -> None:
        expected = (
            (self.pre_state, GlobalEconomicStateV1),
            (self.route, RouteReleaseV1),
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.execution_policy, ZDEXBuybackExecutionPolicyV1),
            (self.price_policy, ZDEXBuybackPriceSafetyPolicyV1),
            (self.price_occurrence, ZDEXBuybackOraclePriceOccurrenceV1),
        )
        if any(type(value) is not expected_type for value, expected_type in expected):
            raise TypeError("ZDEX buyback price authority requires exact typed data")
        for name in (
            "route_safe_quote_limit_atoms",
            "minimum_output_atoms",
            "expected_quote_reserve_atoms",
            "expected_zdex_reserve_atoms",
            "quote_amount_in_atoms",
            "purchased_zdex_atoms",
        ):
            _require_atoms_u128(
                getattr(self, name),
                name=f"ZDEX buyback price authority {name}",
            )


def _snapshot_candidate_v1(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
) -> ZDEXBuybackPriceAuthorityCandidateV1:
    if type(candidate) is not ZDEXBuybackPriceAuthorityCandidateV1:
        raise TypeError("ZDEX buyback price authority candidate must be exact typed data")
    candidate.__post_init__()
    for value, name in (
        (candidate.execution_policy, "execution policy"),
        (candidate.price_policy, "price policy"),
        (candidate.price_occurrence, "price occurrence"),
    ):
        _require_exact_dataclass_scalars_v1(
            value,
            name=f"ZDEX buyback price authority {name}",
        )
    return replace(
        candidate,
        pre_state=_snapshot_state_v1(candidate.pre_state),
        route=_snapshot_route_release_v1(candidate.route),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        execution_policy=replace(candidate.execution_policy),
        price_policy=replace(candidate.price_policy),
        price_occurrence=replace(candidate.price_occurrence),
    )


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackPriceAuthorityFieldsV1:
    pre_state_root: str
    command_occurrence_id: str
    execution_policy_root: str
    price_policy_root: str
    price_occurrence_root: str
    price_safety: VerifiedZDEXBuybackPriceSafetyV1


class VerifiedZDEXBuybackPriceAuthorityV1:
    """Opaque witness for one price envelope tied to committed state."""

    __slots__ = ("_fields",)
    _fields: _VerifiedZDEXBuybackPriceAuthorityFieldsV1

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXBuybackPriceAuthorityFieldsV1,
    ) -> None:
        if token is not _VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_TOKEN_V1:
            raise TypeError("VerifiedZDEXBuybackPriceAuthorityV1 is verifier-constructed")
        if type(fields) is not _VerifiedZDEXBuybackPriceAuthorityFieldsV1:
            raise TypeError("verified ZDEX buyback price authority fields are not closed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXBuybackPriceAuthorityV1 is immutable")

    @property
    def pre_state_root(self) -> str:
        return self._fields.pre_state_root

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def execution_policy_root(self) -> str:
        return self._fields.execution_policy_root

    @property
    def price_policy_root(self) -> str:
        return self._fields.price_policy_root

    @property
    def price_occurrence_root(self) -> str:
        return self._fields.price_occurrence_root

    @property
    def price_safety(self) -> VerifiedZDEXBuybackPriceSafetyV1:
        return self._fields.price_safety

    @property
    def price_safety_binding_root(self) -> str:
        return self.price_safety.binding_root

    @property
    def authority_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-buyback-price-authority-v1",
            {
                "schema": VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_SCHEMA_V1,
                "pre_state_root": self.pre_state_root,
                "command_occurrence_id": self.command_occurrence_id,
                "execution_policy_root": self.execution_policy_root,
                "price_policy_root": self.price_policy_root,
                "price_occurrence_root": self.price_occurrence_root,
                "price_safety_binding_root": self.price_safety_binding_root,
            },
        )


def _require_context_v1(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
    *,
    pre_state_root: str,
    execution_policy_root: str,
    price_policy_root: str,
) -> str:
    if candidate.pre_state.height == MAX_U64_V1:
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.HEIGHT_OVERFLOW,
            "command height exceeds unsigned 64-bit",
        )
    expected_height = candidate.pre_state.height + 1
    occurrence = candidate.occurrence
    if (
        candidate.route.oracle_policy_root != price_policy_root
        or occurrence.chain_id != candidate.pre_state.chain_id
        or occurrence.deployment_root != candidate.pre_state.deployment_root
        or occurrence.profile_root != candidate.pre_state.profile_root
        or occurrence.pre_state_root != pre_state_root
        or occurrence.route_release_id != candidate.route.route_release_id
        or occurrence.command_kind != candidate.route.command_kind
        or occurrence.height != expected_height
        or candidate.price_occurrence.oracle_id != candidate.price_policy.oracle_id
        or candidate.price_occurrence.quote_asset_id
        != candidate.execution_policy.quote_asset_id
        or candidate.price_occurrence.zdex_asset_id
        != candidate.execution_policy.zdex_asset_id
        or candidate.execution_policy.policy_root != execution_policy_root
    ):
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.CONTEXT_MISMATCH,
            "price authority context mismatch",
        )
    return occurrence.occurrence_id


def _require_finalized_oracle_v1(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
    *,
    price_occurrence_root: str,
) -> None:
    occurrence = next(
        (
            row
            for row in candidate.pre_state.oracle_occurrences
            if row.oracle_id == candidate.price_policy.oracle_id
        ),
        None,
    )
    if (
        occurrence is None
        or not occurrence.finalized
        or occurrence.occurrence_root != price_occurrence_root
        or occurrence.observed_height != candidate.price_occurrence.observed_height
        or occurrence.observed_height > candidate.pre_state.height
        or candidate.occurrence.height - occurrence.observed_height
        > candidate.price_policy.maximum_oracle_age_blocks
    ):
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.ORACLE_AUTHORITY_MISMATCH,
            "Oracle occurrence authority mismatch",
        )


def _require_committed_reserves_v1(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
) -> tuple[int, int]:
    quote_principal = zdex_pool_reserve_principal_v1(
        pool_id=candidate.execution_policy.pool_id,
        asset_id=candidate.execution_policy.quote_asset_id,
    )
    zdex_principal = zdex_pool_reserve_principal_v1(
        pool_id=candidate.execution_policy.pool_id,
        asset_id=candidate.execution_policy.zdex_asset_id,
    )

    def amount(principal: str, asset: str) -> int | None:
        return next(
            (
                row.amount_atoms
                for row in candidate.pre_state.custody
                if row.owner == principal
                and row.asset == asset
                and row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
            ),
            None,
        )

    quote_reserve = amount(quote_principal, candidate.execution_policy.quote_asset_id)
    zdex_reserve = amount(zdex_principal, candidate.execution_policy.zdex_asset_id)
    if quote_reserve is None:
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.QUOTE_RESERVE_ABSENT,
            "quote reserve is absent",
        )
    if zdex_reserve is None:
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.ZDEX_RESERVE_ABSENT,
            "ZDEX reserve is absent",
        )
    return quote_reserve, zdex_reserve


def verify_zdex_buyback_price_authority_v1(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
) -> VerifiedZDEXBuybackPriceAuthorityV1:
    """Bind an accepted price envelope to exact committed economic state."""

    candidate = _snapshot_candidate_v1(candidate)
    pre_state_root = candidate.pre_state.state_root
    execution_policy_root = candidate.execution_policy.policy_root
    price_policy_root = candidate.price_policy.policy_root
    price_occurrence_root = candidate.price_occurrence.occurrence_root
    occurrence_id = _require_context_v1(
        candidate,
        pre_state_root=pre_state_root,
        execution_policy_root=execution_policy_root,
        price_policy_root=price_policy_root,
    )
    _require_finalized_oracle_v1(
        candidate,
        price_occurrence_root=price_occurrence_root,
    )
    quote_reserve_atoms, zdex_reserve_atoms = _require_committed_reserves_v1(candidate)
    if (
        quote_reserve_atoms != candidate.expected_quote_reserve_atoms
        or zdex_reserve_atoms != candidate.expected_zdex_reserve_atoms
    ):
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.RESERVE_AMOUNT_MISMATCH,
            "committed reserve amount mismatch",
        )
    price_safety = verify_zdex_buyback_price_safety_v1(
        candidate.price_policy,
        ZDEXBuybackPriceSafetyObservationV1(
            oracle_occurrence_root=price_occurrence_root,
            current_height=candidate.occurrence.height,
            oracle_observed_height=candidate.price_occurrence.observed_height,
            oracle_quote_numerator_atoms=(
                candidate.price_occurrence.quote_numerator_atoms
            ),
            oracle_zdex_denominator_atoms=(
                candidate.price_occurrence.zdex_denominator_atoms
            ),
            quote_reserve_atoms=quote_reserve_atoms,
            zdex_reserve_atoms=zdex_reserve_atoms,
            quote_amount_in_atoms=candidate.quote_amount_in_atoms,
            purchased_zdex_atoms=candidate.purchased_zdex_atoms,
            claimed_route_safe_quote_limit_atoms=(
                candidate.route_safe_quote_limit_atoms
            ),
            claimed_minimum_output_atoms=candidate.minimum_output_atoms,
        ),
    )
    if type(price_safety) is ZDEXBuybackPriceSafetyRejectedV1:
        _reject(
            ZDEXBuybackPriceAuthorityRejectCodeV1.PRICE_ENVELOPE_REJECTED,
            f"price envelope rejected with {price_safety.code.value}",
        )
    if type(price_safety) is not VerifiedZDEXBuybackPriceSafetyV1:
        raise TypeError("ZDEX buyback price-safety result is not closed")
    return VerifiedZDEXBuybackPriceAuthorityV1(
        _VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_TOKEN_V1,
        _VerifiedZDEXBuybackPriceAuthorityFieldsV1(
            pre_state_root=pre_state_root,
            command_occurrence_id=occurrence_id,
            execution_policy_root=execution_policy_root,
            price_policy_root=price_policy_root,
            price_occurrence_root=price_occurrence_root,
            price_safety=price_safety,
        ),
    )


__all__ = [
    "VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_SCHEMA_V1",
    "VerifiedZDEXBuybackPriceAuthorityV1",
    "ZDEXBuybackPriceAuthorityCandidateV1",
    "ZDEXBuybackPriceAuthorityRejectCodeV1",
    "ZDEXBuybackPriceAuthorityRejectedV1",
    "verify_zdex_buyback_price_authority_v1",
]
