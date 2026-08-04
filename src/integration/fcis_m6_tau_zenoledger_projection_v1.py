"""Research-only Tau/ZenoLedger application-content comparison.

The adapters rederive canonical application leaves from supplied content and
check the supplied content commitments.  The resulting observations and parity
receipt are explicitly non-authoritative.  They do not establish source
authenticity, currentness, finality, execution ancestry, writer authority, or
global economic coherence.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final, Mapping

from ..core.fcis_m6_global_state_projection_v1 import (
    M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
    M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1,
    M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1,
    M6ApplicationStateComponentV1,
    M6GlobalStateProjectionRejectCodeV1,
    M6GlobalStateProjectionRejectV1,
    M6ProjectionAuthorityObligationV1,
    M6ProjectionCoverageV1,
)
from ..core.zusd_authenticated_borrow_fee_occurrence_roots_v1 import (
    canonical_zusd_state_root_v1,
)
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .dex_snapshot import snapshot_from_state, state_from_snapshot
from .fcis_m6_projection_receipts_v1 import (
    M6ContentObservationResultV1,
    M6ProjectionSourceDescriptorV1,
    M6ProjectionSourceKindV1,
    _build_observation_v1,
)
from .fcis_m6_projection_values_v1 import (
    MAX_M6_APP_STATE_BYTES_V1,
    M6ApplicationContentV1,
    _build_content_v1,
)
from .proof_mining_runtime import (
    proof_mining_runtime_state_from_obj,
    proof_mining_runtime_state_to_obj,
)
from .zeno_ledger_v0 import (
    canonical_header_hash_v0,
    dex_state_root_v0,
    validate_header_body_roots_v0,
)
from .zusd_monetary_bridge import (
    zusd_monetary_state_from_obj,
    zusd_monetary_state_to_obj,
)

TAU_APP_STATE_SCHEMA_V1: Final = "zenodex/tau_app_state/v1"
TAU_APP_STATE_VERSION_V1: Final = 1
DEX_SNAPSHOT_SOURCE_SCHEMA_V1: Final = "zenodex/dex_snapshot"

_LOWER_HEX = frozenset("0123456789abcdef")

M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1: Final = (
    ("balances", M6ApplicationStateComponentV1.ACCOUNT_BALANCES),
    ("pools", M6ApplicationStateComponentV1.AMM_POOLS),
    ("lp_balances", M6ApplicationStateComponentV1.LP_OWNERSHIP),
    ("lp_mint_timestamps", M6ApplicationStateComponentV1.LP_MINT_AGE),
    ("lp_duration_risk", M6ApplicationStateComponentV1.LP_DURATION_RISK),
    ("nonces", M6ApplicationStateComponentV1.NONCES),
    ("fee_accumulator", M6ApplicationStateComponentV1.LEGACY_FEE_ACCUMULATOR),
    ("vault", M6ApplicationStateComponentV1.VAULT_REWARD_STATE),
    ("oracle", M6ApplicationStateComponentV1.ORACLE_FRESHNESS_STATE),
    ("perps", M6ApplicationStateComponentV1.PERPS_STATE),
)
M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1: Final = ("version",)

_TAU_UNMET_OBLIGATIONS_V1: Final = tuple(
    obligation
    for obligation in M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1
    if obligation
    in {
        M6ProjectionAuthorityObligationV1.TAU_STABLE_COMMITTED_VIEW,
        M6ProjectionAuthorityObligationV1.DEPLOYMENT_BINDING,
        M6ProjectionAuthorityObligationV1.CURRENT_WRITER_BINDING,
        M6ProjectionAuthorityObligationV1.GLOBAL_ECONOMIC_COHERENCE,
        M6ProjectionAuthorityObligationV1.REQUIREMENTS_REGISTRY_COMPLETENESS,
    }
)

_LEDGER_UNMET_OBLIGATIONS_V1: Final = tuple(
    obligation
    for obligation in M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1
    if obligation
    in {
        M6ProjectionAuthorityObligationV1.LEDGER_SELECTED_HEAD,
        M6ProjectionAuthorityObligationV1.LEDGER_EXECUTION_ANCESTRY,
        M6ProjectionAuthorityObligationV1.DEPLOYMENT_BINDING,
        M6ProjectionAuthorityObligationV1.CURRENT_WRITER_BINDING,
        M6ProjectionAuthorityObligationV1.GLOBAL_ECONOMIC_COHERENCE,
        M6ProjectionAuthorityObligationV1.SOVEREIGN_CARRIER_REFINEMENT,
        M6ProjectionAuthorityObligationV1.REQUIREMENTS_REGISTRY_COMPLETENESS,
    }
)


class _NonCanonicalSourceError(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class _NormalizedApplicationContentV1:
    canonical_source_bytes: bytes
    source_schema: str
    source_version: int
    spot_state_root: str
    component_roots: tuple[tuple[M6ApplicationStateComponentV1, str], ...]


def _sha256_digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _LOWER_HEX for character in value)
    ):
        raise TypeError(f"{name} must be a lowercase SHA-256 digest")
    return value


def _component_root(component: M6ApplicationStateComponentV1, value: object) -> str:
    return sha256_hex(
        domain_sep_bytes(f"fcis_m6_app_component/{component.value}", version=1)
        + canonical_json_bytes(value)
    )


def _normalize_dex_snapshot_v1(
    dex_obj: object,
) -> tuple[dict[str, object], dict[M6ApplicationStateComponentV1, str], str]:
    if not isinstance(dex_obj, Mapping):
        raise TypeError("DEX snapshot must be a mapping")
    dex_state = state_from_snapshot(dex_obj)
    normalized = snapshot_from_state(dex_state).data
    if canonical_json_bytes(dex_obj) != canonical_json_bytes(normalized):
        raise _NonCanonicalSourceError("DEX snapshot is not canonical")
    declared_fields = {field for field, _component in M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1}.union(
        M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1
    )
    if set(normalized) != declared_fields:
        raise ValueError("DEX snapshot field/component registry mismatch")
    roots: dict[M6ApplicationStateComponentV1, str] = {}
    required_fields = (
        "balances",
        "pools",
        "lp_balances",
        "lp_mint_timestamps",
        "lp_duration_risk",
        "nonces",
        "fee_accumulator",
    )
    for field, component in M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1:
        if field in required_fields or normalized.get(field) is not None:
            roots[component] = _component_root(component, normalized[field])
    return normalized, roots, dex_state_root_v0(dex_state)


def _normalize_proof_mining_v1(
    proof_obj: object,
    roots: dict[M6ApplicationStateComponentV1, str],
) -> object:
    if proof_obj is None:
        return None
    if not isinstance(proof_obj, Mapping):
        raise TypeError("app_state.proof_mining must be a mapping or null")
    proof_state = proof_mining_runtime_state_from_obj(proof_obj)
    normalized = proof_mining_runtime_state_to_obj(proof_state)
    if canonical_json_bytes(proof_obj) != canonical_json_bytes(normalized):
        raise _NonCanonicalSourceError("app_state.proof_mining is not canonical")
    component = M6ApplicationStateComponentV1.PROOF_MINING_STATE
    roots[component] = _component_root(component, normalized)
    return normalized


def _normalize_zusd_v1(
    zusd_obj: object,
    roots: dict[M6ApplicationStateComponentV1, str],
) -> object:
    if zusd_obj is None:
        return None
    if not isinstance(zusd_obj, Mapping):
        raise TypeError("app_state.zusd_monetary must be a mapping or null")
    zusd_state = zusd_monetary_state_from_obj(zusd_obj)
    normalized = zusd_monetary_state_to_obj(zusd_state)
    if canonical_json_bytes(zusd_obj) != canonical_json_bytes(normalized):
        raise _NonCanonicalSourceError("app_state.zusd_monetary is not canonical")
    roots[M6ApplicationStateComponentV1.ZUSD_MONETARY_STATE] = _component_root(
        M6ApplicationStateComponentV1.ZUSD_MONETARY_STATE,
        normalized,
    )
    roots[M6ApplicationStateComponentV1.ZUSD_CORE_STATE] = canonical_zusd_state_root_v1(
        zusd_state.core
    )
    if zusd_state.protocol_fee_claim is not None:
        roots[M6ApplicationStateComponentV1.ZUSD_PROTOCOL_FEE_SCALAR_CLAIM] = (
            zusd_state.protocol_fee_claim.state_root
        )
    return normalized


def _ordered_component_roots_v1(
    roots: Mapping[M6ApplicationStateComponentV1, str],
) -> tuple[tuple[M6ApplicationStateComponentV1, str], ...]:
    return tuple(
        (component, roots[component])
        for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
        if component in roots
    )


def _normalize_application_content_v1(app_state: object) -> _NormalizedApplicationContentV1:
    if not isinstance(app_state, Mapping):
        raise TypeError("app_state must be a mapping")
    obj = dict(app_state)
    is_wrapper = (
        "schema" in obj or "dex_state" in obj or "proof_mining" in obj or "zusd_monetary" in obj
    )
    if not is_wrapper:
        normalized_dex, roots, spot_state_root = _normalize_dex_snapshot_v1(obj)
        canonical = canonical_json_bytes(normalized_dex)
        version = normalized_dex.get("version")
        if type(version) is not int or version <= 0:
            raise TypeError("DEX snapshot version must be an exact positive integer")
        normalized = _NormalizedApplicationContentV1(
            canonical_source_bytes=canonical,
            source_schema=DEX_SNAPSHOT_SOURCE_SCHEMA_V1,
            source_version=version,
            spot_state_root=spot_state_root,
            component_roots=_ordered_component_roots_v1(roots),
        )
    else:
        expected_fields = {
            "schema",
            "version",
            "dex_state",
            "proof_mining",
            "zusd_monetary",
        }
        if set(obj) != expected_fields:
            raise ValueError("app_state field set mismatch")
        if obj.get("schema") != TAU_APP_STATE_SCHEMA_V1:
            raise ValueError("unsupported app_state schema")
        if type(obj.get("version")) is not int or obj["version"] != TAU_APP_STATE_VERSION_V1:
            raise ValueError("unsupported app_state version")
        proof_obj = obj.get("proof_mining")
        zusd_obj = obj.get("zusd_monetary")
        if proof_obj is None and zusd_obj is None:
            raise _NonCanonicalSourceError(
                "Tau serializes a state without optional subsystems as a bare DEX snapshot"
            )
        normalized_dex, roots, spot_state_root = _normalize_dex_snapshot_v1(obj.get("dex_state"))
        normalized_proof = _normalize_proof_mining_v1(proof_obj, roots)
        normalized_zusd = _normalize_zusd_v1(zusd_obj, roots)
        normalized_obj = {
            "schema": TAU_APP_STATE_SCHEMA_V1,
            "version": TAU_APP_STATE_VERSION_V1,
            "dex_state": normalized_dex,
            "proof_mining": normalized_proof,
            "zusd_monetary": normalized_zusd,
        }
        normalized = _NormalizedApplicationContentV1(
            canonical_source_bytes=canonical_json_bytes(normalized_obj),
            source_schema=TAU_APP_STATE_SCHEMA_V1,
            source_version=TAU_APP_STATE_VERSION_V1,
            spot_state_root=spot_state_root,
            component_roots=_ordered_component_roots_v1(roots),
        )
    if len(normalized.canonical_source_bytes) > MAX_M6_APP_STATE_BYTES_V1:
        raise ValueError("app_state exceeds the byte bound")
    return normalized


def _shared_spot_content_from_app_state_v1(
    app_state: object,
) -> tuple[_NormalizedApplicationContentV1, M6ApplicationContentV1]:
    normalized = _normalize_application_content_v1(app_state)
    shared_roots = tuple(
        (component, root)
        for component, root in normalized.component_roots
        if component in M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1
    )
    covered = tuple(component for component, _root in shared_roots)
    if covered != M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1:
        raise ValueError("application state lacks a ZenoLedger-committed spot component")
    missing = tuple(
        component
        for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
        if component not in covered
    )
    coverage = M6ProjectionCoverageV1(
        component_roots=shared_roots,
        covered_components=covered,
        missing_components=missing,
    )
    content = _build_content_v1(
        canonical_source_bytes=normalized.canonical_source_bytes,
        coverage=coverage,
    )
    return normalized, content


def _reject(
    code: M6GlobalStateProjectionRejectCodeV1,
    *path: str,
) -> M6GlobalStateProjectionRejectV1:
    return M6GlobalStateProjectionRejectV1(code, tuple(path))


def project_tau_claimed_shared_spot_content_v1(
    *,
    app_state: object,
    claimed_app_hash: object,
    claimed_source_position: object,
) -> M6ContentObservationResultV1:
    """Check caller-supplied Tau content; no stable-view authority is implied."""

    try:
        app_hash = _sha256_digest(claimed_app_hash, "claimed_app_hash")
        if type(claimed_source_position) is not int or claimed_source_position < 0:
            raise TypeError("claimed_source_position must be exact and nonnegative")
        normalized, content_obj = _shared_spot_content_from_app_state_v1(app_state)
    except _NonCanonicalSourceError:
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.NON_CANONICAL_SOURCE,
            "tau",
            "app_state",
        )
    except TypeError:
        return _reject(M6GlobalStateProjectionRejectCodeV1.WRONG_EXACT_TYPE, "tau")
    except (ValueError, ArithmeticError, OverflowError):
        return _reject(M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE, "tau", "app_state")
    source_state_root = "0x" + hashlib.sha256(normalized.canonical_source_bytes).hexdigest()
    if source_state_root != "0x" + app_hash:
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.SOURCE_COMMITMENT_MISMATCH,
            "tau",
            "claimed_app_hash",
        )
    return _build_observation_v1(
        source=M6ProjectionSourceDescriptorV1(
            source_kind=M6ProjectionSourceKindV1.TAU_CLAIMED_VIEW,
            source_schema=normalized.source_schema,
            source_version=normalized.source_version,
            source_state_root=source_state_root,
            source_commitment_root=source_state_root,
            source_chain_id=None,
            claimed_source_position=claimed_source_position,
        ),
        content=content_obj,
        unmet_authority_obligations=_TAU_UNMET_OBLIGATIONS_V1,
    )


def project_zeno_ledger_header_shared_spot_content_v1(
    *,
    app_state: object,
    header: object,
    body: object,
) -> M6ContentObservationResultV1:
    """Check a header/state commitment; execution ancestry remains unresolved."""

    if type(header) is not dict or type(body) is not dict:
        return _reject(M6GlobalStateProjectionRejectCodeV1.WRONG_EXACT_TYPE, "zeno_ledger")
    try:
        validate_header_body_roots_v0(header, body)
        normalized, content_obj = _shared_spot_content_from_app_state_v1(app_state)
        source_commitment_root = canonical_header_hash_v0(header)
        source_position = header["height"]
        chain_id = header["chain_id"]
        if type(source_position) is not int or source_position < 0:
            raise TypeError("header height must be exact and nonnegative")
        if type(chain_id) is not str or not chain_id:
            raise TypeError("header chain_id must be an exact nonempty string")
    except _NonCanonicalSourceError:
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.NON_CANONICAL_SOURCE,
            "zeno_ledger",
            "app_state",
        )
    except TypeError:
        return _reject(M6GlobalStateProjectionRejectCodeV1.WRONG_EXACT_TYPE, "zeno_ledger")
    except (KeyError, ValueError, ArithmeticError, OverflowError):
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE,
            "zeno_ledger",
            "header_body",
        )
    if header["post_state_root"] != normalized.spot_state_root:
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.SOURCE_COMMITMENT_MISMATCH,
            "zeno_ledger",
            "post_state_root",
        )
    return _build_observation_v1(
        source=M6ProjectionSourceDescriptorV1(
            source_kind=M6ProjectionSourceKindV1.ZENO_LEDGER_HEADER_STATE_COMMITMENT,
            source_schema=normalized.source_schema,
            source_version=normalized.source_version,
            source_state_root=normalized.spot_state_root,
            source_commitment_root=source_commitment_root,
            source_chain_id=chain_id,
            claimed_source_position=source_position,
        ),
        content=content_obj,
        unmet_authority_obligations=_LEDGER_UNMET_OBLIGATIONS_V1,
    )


__all__ = (
    "DEX_SNAPSHOT_SOURCE_SCHEMA_V1",
    "M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1",
    "M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1",
    "TAU_APP_STATE_SCHEMA_V1",
    "TAU_APP_STATE_VERSION_V1",
    "project_tau_claimed_shared_spot_content_v1",
    "project_zeno_ledger_header_shared_spot_content_v1",
)
