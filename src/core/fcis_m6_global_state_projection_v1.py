"""Closed vocabularies for M6 application-state content projection.

The values in this module describe deterministic content coverage.  They carry
no source authenticity, current-head, writer, publication, or settlement
authority.  Source adapters may use them to state which application-state
leaves were freshly derived and which M6 obligations remain unresolved.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, final

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

M6_APP_CONTENT_COVERAGE_SCHEMA_V1: Final = "zenodex/fcis/m6/application-content-coverage/v1"
M6_STRUCTURAL_COVERAGE_WITNESS_SCHEMA_V1: Final = "zenodex/fcis/m6/structural-coverage-witness/v1"

_LOWER_HEX = frozenset("0123456789abcdef")


class M6ApplicationStateComponentV1(str, Enum):
    """Closed leaves derivable from the current Tau application carrier."""

    ACCOUNT_BALANCES = "account_balances"
    AMM_POOLS = "amm_pools"
    LP_OWNERSHIP = "lp_ownership"
    LP_MINT_AGE = "lp_mint_age"
    LP_DURATION_RISK = "lp_duration_risk"
    NONCES = "nonces"
    LEGACY_FEE_ACCUMULATOR = "legacy_fee_accumulator"
    VAULT_REWARD_STATE = "vault_reward_state"
    ORACLE_FRESHNESS_STATE = "oracle_freshness_state"
    PERPS_STATE = "perps_state"
    PROOF_MINING_STATE = "proof_mining_state"
    ZUSD_MONETARY_STATE = "zusd_monetary_state"
    ZUSD_CORE_STATE = "zusd_core_state"
    ZUSD_PROTOCOL_FEE_SCALAR_CLAIM = "zusd_protocol_fee_scalar_claim"


M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1: Final = tuple(M6ApplicationStateComponentV1)

# Exact subset committed by ``zeno_ledger_v0.dex_state_root_v0``.  A shared
# Tau/ZenoLedger comparison may cover only these leaves until ZenoLedger gains a
# sovereign carrier for the remaining application state.
M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1: Final = (
    M6ApplicationStateComponentV1.ACCOUNT_BALANCES,
    M6ApplicationStateComponentV1.AMM_POOLS,
    M6ApplicationStateComponentV1.LP_OWNERSHIP,
    M6ApplicationStateComponentV1.LP_MINT_AGE,
    M6ApplicationStateComponentV1.LP_DURATION_RISK,
    M6ApplicationStateComponentV1.NONCES,
    M6ApplicationStateComponentV1.LEGACY_FEE_ACCUMULATOR,
)


class M6GlobalProjectionGapV1(str, Enum):
    """Known state families outside the current application carrier."""

    MANAGED_ASSET_POLICY = "managed_asset_policy"
    FEE_ROLE_CLAIM_STATE = "fee_role_claim_state"
    FEE_APPORTIONMENT_STATE = "fee_apportionment_state"
    FEE_AUTHORITY_CONFIGURATION = "fee_authority_configuration"
    AUTHENTICATED_EXECUTION_CONTEXT = "authenticated_execution_context"
    HOST_NATIVE_CUSTODY = "host_native_custody"
    FEATURE_ACTIVATION_PROFILE = "feature_activation_profile"
    ORACLE_REPORTER_AUTHORITY = "oracle_reporter_authority"
    BUY_AND_BURN_LIFECYCLE = "buy_and_burn_lifecycle"
    SEALED_BID_LIFECYCLE = "sealed_bid_lifecycle"
    SOVEREIGN_LEDGER_CARRIERS = "sovereign_ledger_carriers"
    WRITER_EPOCH_AND_MIGRATION = "writer_epoch_and_migration"
    HISTORY_NULLIFIER_RECEIPT = "history_nullifier_receipt"
    OUTBOX_AND_ACKNOWLEDGMENT = "outbox_and_acknowledgment"


M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1: Final = tuple(M6GlobalProjectionGapV1)


class M6ProjectionAuthorityObligationV1(str, Enum):
    """Authority/coherence facts that content comparison cannot establish."""

    TAU_STABLE_COMMITTED_VIEW = "tau_stable_committed_view"
    LEDGER_SELECTED_HEAD = "ledger_selected_head"
    LEDGER_EXECUTION_ANCESTRY = "ledger_execution_ancestry"
    CROSS_SOURCE_HANDOFF = "cross_source_handoff"
    DEPLOYMENT_BINDING = "deployment_binding"
    CURRENT_WRITER_BINDING = "current_writer_binding"
    GLOBAL_ECONOMIC_COHERENCE = "global_economic_coherence"
    SOVEREIGN_CARRIER_REFINEMENT = "sovereign_carrier_refinement"
    REQUIREMENTS_REGISTRY_COMPLETENESS = "requirements_registry_completeness"


M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1: Final = tuple(M6ProjectionAuthorityObligationV1)


class M6GlobalStateProjectionRejectCodeV1(str, Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_SOURCE = "invalid_source"
    NON_CANONICAL_SOURCE = "non_canonical_source"
    UNSUPPORTED_SOURCE_SCHEMA = "unsupported_source_schema"
    SOURCE_COMMITMENT_MISMATCH = "source_commitment_mismatch"
    SOURCE_LINEAGE_MISMATCH = "source_lineage_mismatch"
    INCOMPLETE_APPLICATION_CONTENT = "incomplete_application_content"
    INCOMPLETE_GLOBAL_STATE = "incomplete_global_state"
    UNMET_AUTHORITY_OBLIGATIONS = "unmet_authority_obligations"
    PROJECTION_MISMATCH = "projection_mismatch"


def _digest32(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in _LOWER_HEX for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 0x-prefixed 32-byte digest")
    return value


def _ordered_enum_tuple(
    value: object,
    *,
    enum_type: type[Enum],
    canonical_order: tuple[Enum, ...],
    name: str,
) -> tuple[Enum, ...]:
    if type(value) is not tuple:
        raise TypeError(f"{name} must be an exact tuple")
    entries = value
    if any(type(entry) is not enum_type for entry in entries):
        raise TypeError(f"{name} contains a wrong exact enum type")
    ordered = tuple(entry for entry in canonical_order if entry in entries)
    if entries != ordered:
        raise ValueError(f"{name} must be unique and in canonical order")
    return entries


def _component_tuple(value: object, name: str) -> tuple[M6ApplicationStateComponentV1, ...]:
    return _ordered_enum_tuple(
        value,
        enum_type=M6ApplicationStateComponentV1,
        canonical_order=M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1,
        name=name,
    )  # type: ignore[return-value]


def _component_roots(
    value: object,
) -> tuple[tuple[M6ApplicationStateComponentV1, str], ...]:
    if type(value) is not tuple:
        raise TypeError("component_roots must be an exact tuple")
    roots = value
    previous_index = -1
    seen: set[M6ApplicationStateComponentV1] = set()
    for entry in roots:
        if type(entry) is not tuple or len(entry) != 2:
            raise TypeError("component_roots entries must be exact pairs")
        component, root = entry
        if type(component) is not M6ApplicationStateComponentV1:
            raise TypeError("component root key must be exact")
        _digest32(root, f"component root {component.value}")
        if component in seen:
            raise ValueError("component_roots must be unique")
        index = M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1.index(component)
        if index <= previous_index:
            raise ValueError("component_roots must be in canonical component order")
        previous_index = index
        seen.add(component)
    return roots


def _coverage_body_v1(value: M6ProjectionCoverageV1) -> dict[str, object]:
    return {
        "schema": M6_APP_CONTENT_COVERAGE_SCHEMA_V1,
        "component_roots": [
            {"component": component.value, "root": root}
            for component, root in value.component_roots
        ],
        "covered_components": [component.value for component in value.covered_components],
        "missing_components": [component.value for component in value.missing_components],
    }


@final
@dataclass(frozen=True, slots=True)
class M6ProjectionCoverageV1:
    """Source-neutral content leaves and explicit absence markers."""

    component_roots: tuple[tuple[M6ApplicationStateComponentV1, str], ...]
    covered_components: tuple[M6ApplicationStateComponentV1, ...]
    missing_components: tuple[M6ApplicationStateComponentV1, ...]

    def __post_init__(self) -> None:
        roots = _component_roots(self.component_roots)
        covered = _component_tuple(self.covered_components, "covered_components")
        missing = _component_tuple(self.missing_components, "missing_components")
        if set(covered).intersection(missing):
            raise ValueError("covered and missing components must be disjoint")
        if set(covered).union(missing) != set(M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1):
            raise ValueError("coverage must partition the application component registry")
        if tuple(component for component, _root in roots) != covered:
            raise ValueError("component roots must exactly cover the covered component tuple")

    @property
    def complete(self) -> bool:
        self.__post_init__()
        return not self.missing_components

    @property
    def coverage_root(self) -> str:
        self.__post_init__()
        return sha256_hex(
            domain_sep_bytes("fcis_m6_application_content_coverage", version=1)
            + canonical_json_bytes(_coverage_body_v1(self))
        )


@final
@dataclass(frozen=True, slots=True)
class M6GlobalStateProjectionRejectV1:
    code: M6GlobalStateProjectionRejectCodeV1
    path: tuple[str, ...]
    missing_components: tuple[M6ApplicationStateComponentV1, ...] = ()
    global_gaps: tuple[M6GlobalProjectionGapV1, ...] = ()
    unmet_obligations: tuple[M6ProjectionAuthorityObligationV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.code) is not M6GlobalStateProjectionRejectCodeV1:
            raise TypeError("projection rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("projection rejection path must be an exact string tuple")
        if len(self.path) > 8 or any(
            not part or len(part.encode("utf-8")) > 64 for part in self.path
        ):
            raise ValueError("projection rejection path is outside its bound")
        _component_tuple(self.missing_components, "missing_components")
        _ordered_enum_tuple(
            self.global_gaps,
            enum_type=M6GlobalProjectionGapV1,
            canonical_order=M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1,
            name="global_gaps",
        )
        _ordered_enum_tuple(
            self.unmet_obligations,
            enum_type=M6ProjectionAuthorityObligationV1,
            canonical_order=M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
            name="unmet_obligations",
        )


@final
@dataclass(frozen=True, slots=True)
class M6StructuralCoverageWitnessV1:
    """Caller-replayable bookkeeping witness with zero runtime authority."""

    coverage: M6ProjectionCoverageV1
    witness_root: str

    def __post_init__(self) -> None:
        if type(self.coverage) is not M6ProjectionCoverageV1 or not self.coverage.complete:
            raise ValueError("structural coverage witness requires complete coverage")
        _digest32(self.witness_root, "witness_root")
        if self.witness_root != _structural_witness_root_v1(self.coverage):
            raise ValueError("witness_root does not rederive")


M6StructuralCoverageResultV1: TypeAlias = (
    M6StructuralCoverageWitnessV1 | M6GlobalStateProjectionRejectV1
)


def _structural_witness_root_v1(coverage: M6ProjectionCoverageV1) -> str:
    return sha256_hex(
        domain_sep_bytes("fcis_m6_structural_coverage", version=1)
        + canonical_json_bytes(
            {
                "schema": M6_STRUCTURAL_COVERAGE_WITNESS_SCHEMA_V1,
                "coverage_root": coverage.coverage_root,
            }
        )
    )


def require_complete_structural_coverage_v1(
    coverage: object,
) -> M6StructuralCoverageResultV1:
    """Check registry bookkeeping; this function deliberately grants no authority."""

    if type(coverage) is not M6ProjectionCoverageV1:
        return M6GlobalStateProjectionRejectV1(
            M6GlobalStateProjectionRejectCodeV1.WRONG_EXACT_TYPE,
            ("coverage",),
        )
    try:
        coverage.__post_init__()
    except (TypeError, ValueError, ArithmeticError, OverflowError):
        return M6GlobalStateProjectionRejectV1(
            M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE,
            ("coverage",),
        )
    if coverage.missing_components:
        return M6GlobalStateProjectionRejectV1(
            M6GlobalStateProjectionRejectCodeV1.INCOMPLETE_APPLICATION_CONTENT,
            ("coverage", "missing_components"),
            missing_components=coverage.missing_components,
        )
    return M6StructuralCoverageWitnessV1(
        coverage=coverage,
        witness_root=_structural_witness_root_v1(coverage),
    )


__all__ = (
    "M6_APP_CONTENT_COVERAGE_SCHEMA_V1",
    "M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1",
    "M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1",
    "M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1",
    "M6_STRUCTURAL_COVERAGE_WITNESS_SCHEMA_V1",
    "M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1",
    "M6ApplicationStateComponentV1",
    "M6GlobalProjectionGapV1",
    "M6GlobalStateProjectionRejectCodeV1",
    "M6GlobalStateProjectionRejectV1",
    "M6ProjectionAuthorityObligationV1",
    "M6ProjectionCoverageV1",
    "M6StructuralCoverageResultV1",
    "M6StructuralCoverageWitnessV1",
    "require_complete_structural_coverage_v1",
)
