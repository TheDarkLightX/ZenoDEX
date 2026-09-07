"""Prepare release-image-bound receipt requests for accepted lane modules.

The deterministic core recomputes the structural release-route binding, selects
the expected guest image from the active lane release, and prepares exact
canonical module journal bytes. A measured integration port executes that
request, and only :func:`bind_verified_lane_module_receipt_v1` can mint the
final :class:`VerifiedLaneModuleTransitionV1`.

This module does not select or authenticate a verifier implementation, execute
the guest verifier, coordinate lanes, compose routes, or publish ledger state.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from .asset_transfer_lane_module_custody_v1 import (
    recompute_asset_transfer_lane_module_custody_v1,
)
from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    _recompute_asset_transfer_lane_module_accepted_v1,
    _snapshot_asset_transfer_lane_module_accepted_v1,
    _snapshot_asset_transfer_lane_module_input_v1,
)
from .asset_transfer_policy_registry_v1 import (
    AssetTransferPolicyRegistryV1,
    snapshot_asset_transfer_policy_registry_v1,
)
from .economic_command_authentication_v1 import AuthenticatedEconomicCommandV1
from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import (
    LaneModuleTransitionJournalV1,
    ReceiptKindV1,
)
from .global_economic_refinement_snapshot_v1 import _require_exact_dataclass_scalars_v1
from .global_oracle_price_occurrence_v1 import VerifiedGlobalOraclePriceV1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ReleaseStatusV1,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .lane_capability_registry_v1 import (
    resolve_perps_margin_command_capability_v1,
)
from .lane_module_release_route_binding_v1 import (
    AssetTransferReleaseRouteBindingCandidateV1,
    ManagedAssetLifecycleReleaseRouteBindingCandidateV1,
    PerpsMarginReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    _bind_asset_transfer_custody_output_structural_v1,
    _bind_asset_transfer_lane_output_structural_v1,
    _bind_managed_asset_lifecycle_lane_output_structural_v1,
    bind_perps_margin_lane_output_to_release_route_v1,
)
from .managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    _recompute_managed_asset_lifecycle_lane_module_accepted_v1,
    _snapshot_managed_asset_lifecycle_lane_module_accepted_v1,
    _snapshot_managed_asset_lifecycle_lane_module_input_v1,
)
from .managed_asset_policy_registry_v1 import (
    ManagedAssetPolicyRegistryV1,
    snapshot_exact_economic_policy_registry_v1,
    snapshot_managed_asset_policy_registry_v1,
)
from .perps_margin_lane_module_v1 import (
    PerpsMarginLaneModuleInputV1,
    _recompute_perps_margin_accepted_v1,
    _snapshot_perps_margin_lane_module_input_v1,
)
from .perps_margin_types_v1 import PerpsMarginAcceptedV1
from .perps_market_policy_v1 import (
    PerpsMarketPolicyV1,
    snapshot_perps_market_policy_v1,
)

VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1: Final = (
    "zenodex/verified-lane-module-transition/v1"
)
MAX_LANE_MODULE_RECEIPT_BYTES_V1: Final = 16 * 1024 * 1024
_VERIFIED_LANE_MODULE_TRANSITION_TOKEN = object()
_PREPARED_LANE_MODULE_RECEIPT_TOKEN_V1 = object()
_VERIFIED_LANE_MODULE_RECEIPT_EXECUTION_TOKEN_V1 = object()


@dataclass(frozen=True, slots=True)
class LaneModuleReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("lane module receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("lane module receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class AssetTransferLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    asset_policy_registry: AssetTransferPolicyRegistryV1
    authenticated_command: AuthenticatedEconomicCommandV1
    module_input: AssetTransferLaneModuleInputV1
    accepted: AssetTransferLaneModuleAcceptedV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    receipt: LaneModuleReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "economic policy registry"),
            (
                self.asset_policy_registry,
                AssetTransferPolicyRegistryV1,
                "asset transfer policy registry",
            ),
            (
                self.authenticated_command,
                AuthenticatedEconomicCommandV1,
                "authenticated economic command",
            ),
            (self.module_input, AssetTransferLaneModuleInputV1, "asset transfer input"),
            (self.accepted, AssetTransferLaneModuleAcceptedV1, "asset transfer output"),
            (
                self.release_route_binding,
                ReleaseRouteBoundLaneTransitionV1,
                "release-route binding",
            ),
            (self.receipt, LaneModuleReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane module {label} must be typed")


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    asset_policy_registry: ManagedAssetPolicyRegistryV1
    authenticated_command: AuthenticatedEconomicCommandV1
    module_input: ManagedAssetLifecycleLaneModuleInputV1
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    receipt: LaneModuleReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "economic policy registry"),
            (
                self.asset_policy_registry,
                ManagedAssetPolicyRegistryV1,
                "managed asset policy registry",
            ),
            (
                self.authenticated_command,
                AuthenticatedEconomicCommandV1,
                "authenticated economic command",
            ),
            (
                self.module_input,
                ManagedAssetLifecycleLaneModuleInputV1,
                "managed lifecycle input",
            ),
            (
                self.accepted,
                ManagedAssetLifecycleLaneModuleAcceptedV1,
                "managed lifecycle output",
            ),
            (
                self.release_route_binding,
                ReleaseRouteBoundLaneTransitionV1,
                "release-route binding",
            ),
            (self.receipt, LaneModuleReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane module {label} must be typed")


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    market_policy: PerpsMarketPolicyV1
    authenticated_command: AuthenticatedEconomicCommandV1
    module_input: PerpsMarginLaneModuleInputV1
    accepted: PerpsMarginAcceptedV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    verified_price: VerifiedGlobalOraclePriceV1 | None
    receipt: LaneModuleReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "economic policy registry"),
            (self.market_policy, PerpsMarketPolicyV1, "perps market policy"),
            (
                self.authenticated_command,
                AuthenticatedEconomicCommandV1,
                "authenticated economic command",
            ),
            (self.module_input, PerpsMarginLaneModuleInputV1, "perps margin input"),
            (self.accepted, PerpsMarginAcceptedV1, "perps margin output"),
            (
                self.release_route_binding,
                ReleaseRouteBoundLaneTransitionV1,
                "release-route binding",
            ),
            (self.receipt, LaneModuleReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane module {label} must be typed")
        if self.verified_price is not None and (
            type(self.verified_price) is not VerifiedGlobalOraclePriceV1
        ):
            raise TypeError("lane module verified Oracle price must be exact typed data")


@dataclass(frozen=True, slots=True)
class _VerifiedLaneModuleTransitionFieldsV1:
    authenticated_command_binding_root: str
    release_route_binding_root: str
    expected_image_id: str
    module_journal_root: str
    module_journal_digest: str
    statement_root: str
    command_occurrence_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1


def require_verified_lane_module_transition_scalars_v1(witness: object) -> None:
    """Refuse a witness whose exported scalars are not the exact primitives the mint path writes.

    The witness is token-minted, but ``object.__new__`` can plant a fields record carrying
    ``None`` or subclass scalars; a consumer that compares or exports those scalars calls
    this first so a forged witness cannot smuggle them through (Opus P30 NEW-1).
    """

    if type(witness) is not VerifiedLaneModuleTransitionV1:
        raise TypeError("lane module witness must be the exact typed value")
    fields = object.__getattribute__(witness, "_fields")
    if type(fields) is not _VerifiedLaneModuleTransitionFieldsV1:
        raise TypeError("lane module witness fields must be the exact typed record")
    _require_exact_dataclass_scalars_v1(fields, name="lane module witness")
    for name in (
        "authenticated_command_binding_root",
        "release_route_binding_root",
        "module_journal_root",
        "statement_root",
        "command_occurrence_id",
    ):
        _require_root(getattr(fields, name), name=f"lane module witness {name}")
    for name in ("expected_image_id", "module_journal_digest", "receipt_digest"):
        if not getattr(fields, name):
            raise TypeError(f"lane module witness {name} must be non-empty")
    if type(fields.receipt_kind) is not ReceiptKindV1:
        raise TypeError("lane module witness receipt kind is not closed")


class VerifiedLaneModuleTransitionV1:
    """Opaque module-proof authority produced only after receipt verification."""

    _fields: _VerifiedLaneModuleTransitionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedLaneModuleTransitionFieldsV1,
    ) -> None:
        if token is not _VERIFIED_LANE_MODULE_TRANSITION_TOKEN:
            raise TypeError("VerifiedLaneModuleTransitionV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedLaneModuleTransitionV1 is immutable")

    @property
    def authenticated_command_binding_root(self) -> str:
        return self._fields.authenticated_command_binding_root

    @property
    def release_route_binding_root(self) -> str:
        return self._fields.release_route_binding_root

    @property
    def expected_image_id(self) -> str:
        return self._fields.expected_image_id

    @property
    def module_journal_root(self) -> str:
        return self._fields.module_journal_root

    @property
    def module_journal_digest(self) -> str:
        return self._fields.module_journal_digest

    @property
    def statement_root(self) -> str:
        return self._fields.statement_root

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def receipt_digest(self) -> str:
        return self._fields.receipt_digest

    @property
    def receipt_kind(self) -> ReceiptKindV1:
        return self._fields.receipt_kind

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-lane-module-transition-v1",
            {
                "schema": VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1,
                "authenticated_command_binding_root": (
                    self.authenticated_command_binding_root
                ),
                "release_route_binding_root": self.release_route_binding_root,
                "expected_image_id": self.expected_image_id,
                "module_journal_root": self.module_journal_root,
                "module_journal_digest": self.module_journal_digest,
                "statement_root": self.statement_root,
                "command_occurrence_id": self.command_occurrence_id,
                "receipt_digest": self.receipt_digest,
                "receipt_kind": self.receipt_kind,
            },
        )


@dataclass(frozen=True, slots=True)
class _PreparedLaneModuleReceiptRequestV1:
    profile_root: str
    lane_id: LaneIdV1
    module_release_id: str
    expected_image_id: str
    receipt_bytes: bytes
    expected_journal_bytes: bytes


@dataclass(frozen=True, slots=True)
class _PreparedLaneModuleReceiptFieldsV1:
    request: _PreparedLaneModuleReceiptRequestV1
    transition_fields: _VerifiedLaneModuleTransitionFieldsV1


def _require_prepared_lane_module_receipt_request_v1(
    request: object,
) -> _PreparedLaneModuleReceiptRequestV1:
    if type(request) is not _PreparedLaneModuleReceiptRequestV1:
        raise TypeError("prepared lane module receipt request must be exact typed data")
    _require_root(request.profile_root, name="prepared lane module profile root")
    if type(request.lane_id) is not LaneIdV1:
        raise TypeError("prepared lane module lane id must be the exact lane enum")
    _require_root(
        request.module_release_id,
        name="prepared lane module release id",
    )
    _require_root(
        request.expected_image_id,
        name="prepared lane module expected image id",
    )
    if type(request.receipt_bytes) is not bytes or not request.receipt_bytes:
        raise TypeError("prepared lane module receipt bytes must be non-empty exact bytes")
    if len(request.receipt_bytes) > MAX_LANE_MODULE_RECEIPT_BYTES_V1:
        raise ValueError("prepared lane module receipt bytes exceed the ABI V1 byte ceiling")
    if type(request.expected_journal_bytes) is not bytes or not request.expected_journal_bytes:
        raise TypeError("prepared lane module journal bytes must be non-empty exact bytes")
    return request


def _require_prepared_lane_module_transition_fields_v1(
    fields: object,
) -> _VerifiedLaneModuleTransitionFieldsV1:
    if type(fields) is not _VerifiedLaneModuleTransitionFieldsV1:
        raise TypeError("prepared lane module transition fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields, name="prepared lane module transition")
    for name in (
        "authenticated_command_binding_root",
        "release_route_binding_root",
        "expected_image_id",
        "module_journal_root",
        "statement_root",
        "command_occurrence_id",
    ):
        _require_root(
            getattr(fields, name),
            name=f"prepared lane module transition {name}",
        )
    for name in ("module_journal_digest", "receipt_digest"):
        _require_root(
            getattr(fields, name),
            name=f"prepared lane module transition {name}",
            allow_zero=True,
        )
    if type(fields.receipt_kind) is not ReceiptKindV1:
        raise TypeError("prepared lane module transition receipt kind is not closed")
    return fields


def _require_prepared_lane_module_receipt_fields_v1(
    fields: object,
) -> _PreparedLaneModuleReceiptFieldsV1:
    if type(fields) is not _PreparedLaneModuleReceiptFieldsV1:
        raise TypeError("prepared lane module receipt fields must be exact typed data")
    request = _require_prepared_lane_module_receipt_request_v1(fields.request)
    transition_fields = _require_prepared_lane_module_transition_fields_v1(
        fields.transition_fields
    )
    if transition_fields.expected_image_id != request.expected_image_id:
        raise ValueError("prepared lane module expected image mismatch")
    if transition_fields.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("prepared lane module receipt kind must be succinct")
    return fields


def _validate_prepared_lane_module_receipt_content_digests_v1(
    fields: _PreparedLaneModuleReceiptFieldsV1,
) -> None:
    request = fields.request
    transition_fields = fields.transition_fields
    if transition_fields.receipt_digest != _sha256_root_v1(request.receipt_bytes):
        raise ValueError("prepared lane module receipt digest mismatch")
    if transition_fields.module_journal_digest != _sha256_root_v1(
        request.expected_journal_bytes
    ):
        raise ValueError("prepared lane module journal digest mismatch")


def _snapshot_prepared_lane_module_receipt_fields_v1(
    fields: object,
) -> _PreparedLaneModuleReceiptFieldsV1:
    prepared = _require_prepared_lane_module_receipt_fields_v1(
        fields,
    )
    request = prepared.request
    transition_fields = prepared.transition_fields
    return _PreparedLaneModuleReceiptFieldsV1(
        _PreparedLaneModuleReceiptRequestV1(
            request.profile_root,
            request.lane_id,
            request.module_release_id,
            request.expected_image_id,
            request.receipt_bytes,
            request.expected_journal_bytes,
        ),
        _VerifiedLaneModuleTransitionFieldsV1(
            transition_fields.authenticated_command_binding_root,
            transition_fields.release_route_binding_root,
            transition_fields.expected_image_id,
            transition_fields.module_journal_root,
            transition_fields.module_journal_digest,
            transition_fields.statement_root,
            transition_fields.command_occurrence_id,
            transition_fields.receipt_digest,
            transition_fields.receipt_kind,
        ),
    )


class PreparedLaneModuleReceiptV1:
    """Opaque, immutable exact request for a measured module verifier port."""

    _fields: _PreparedLaneModuleReceiptFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _PreparedLaneModuleReceiptFieldsV1,
    ) -> None:
        if token is not _PREPARED_LANE_MODULE_RECEIPT_TOKEN_V1:
            raise TypeError("PreparedLaneModuleReceiptV1 is core-constructed")
        object.__setattr__(
            self,
            "_fields",
            _snapshot_prepared_lane_module_receipt_fields_v1(fields),
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("PreparedLaneModuleReceiptV1 is immutable")

    @property
    def profile_root(self) -> str:
        return self._fields.request.profile_root

    @property
    def lane_id(self) -> LaneIdV1:
        return self._fields.request.lane_id

    @property
    def module_release_id(self) -> str:
        return self._fields.request.module_release_id

    @property
    def expected_image_id(self) -> str:
        return self._fields.request.expected_image_id

    @property
    def receipt_bytes(self) -> bytes:
        return self._fields.request.receipt_bytes

    @property
    def expected_journal_bytes(self) -> bytes:
        return self._fields.request.expected_journal_bytes


def _prepared_lane_module_receipt_fields_v1(
    prepared: object,
) -> _PreparedLaneModuleReceiptFieldsV1:
    if type(prepared) is not PreparedLaneModuleReceiptV1:
        raise TypeError("prepared lane module receipt must be the exact typed value")
    fields = object.__getattribute__(prepared, "_fields")
    return _require_prepared_lane_module_receipt_fields_v1(
        fields,
    )


def snapshot_prepared_lane_module_receipt_v1(
    prepared: PreparedLaneModuleReceiptV1,
) -> PreparedLaneModuleReceiptV1:
    """Return a validated detached request snapshot for measured verifier I/O."""

    fields = _prepared_lane_module_receipt_fields_v1(prepared)
    return PreparedLaneModuleReceiptV1(
        _PREPARED_LANE_MODULE_RECEIPT_TOKEN_V1,
        fields,
    )


@dataclass(frozen=True, slots=True)
class _VerifiedLaneModuleReceiptExecutionFieldsV1:
    prepared_fields: _PreparedLaneModuleReceiptFieldsV1
    verifier_binding_root: str


class VerifiedLaneModuleReceiptExecutionV1:
    """Opaque evidence that a measured port executed one exact request.

    The private token disciplines ordinary Python construction. It does not
    establish protection against a compromised interpreter or process.
    """

    _fields: _VerifiedLaneModuleReceiptExecutionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        prepared: PreparedLaneModuleReceiptV1,
        verifier_binding_root: str,
    ) -> None:
        if token is not _VERIFIED_LANE_MODULE_RECEIPT_EXECUTION_TOKEN_V1:
            raise TypeError("VerifiedLaneModuleReceiptExecutionV1 is port-constructed")
        prepared_fields = _prepared_lane_module_receipt_fields_v1(
            prepared,
        )
        _require_root(
            verifier_binding_root,
            name="lane module receipt verifier binding root",
        )
        object.__setattr__(
            self,
            "_fields",
            _VerifiedLaneModuleReceiptExecutionFieldsV1(
                _snapshot_prepared_lane_module_receipt_fields_v1(prepared_fields),
                verifier_binding_root,
            ),
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedLaneModuleReceiptExecutionV1 is immutable")

    @property
    def verifier_binding_root(self) -> str:
        return self._fields.verifier_binding_root


def _verified_lane_module_receipt_execution_fields_v1(
    execution: object,
) -> _VerifiedLaneModuleReceiptExecutionFieldsV1:
    if type(execution) is not VerifiedLaneModuleReceiptExecutionV1:
        raise TypeError("lane module receipt execution must be the exact typed value")
    fields = object.__getattribute__(execution, "_fields")
    if type(fields) is not _VerifiedLaneModuleReceiptExecutionFieldsV1:
        raise TypeError("lane module receipt execution fields must be exact typed data")
    _require_prepared_lane_module_receipt_fields_v1(
        fields.prepared_fields,
    )
    _require_root(
        fields.verifier_binding_root,
        name="lane module receipt execution verifier binding root",
    )
    return fields


def bind_verified_lane_module_receipt_v1(
    prepared: PreparedLaneModuleReceiptV1,
    execution: VerifiedLaneModuleReceiptExecutionV1,
    *,
    expected_verifier_binding_root: str,
) -> VerifiedLaneModuleTransitionV1:
    """Mint the existing transition witness from exact measured execution evidence."""

    prepared_fields = _prepared_lane_module_receipt_fields_v1(
        prepared,
    )
    execution_fields = _verified_lane_module_receipt_execution_fields_v1(execution)
    _require_root(
        expected_verifier_binding_root,
        name="expected lane module receipt verifier binding root",
    )
    if execution_fields.prepared_fields != prepared_fields:
        raise ValueError("lane module receipt execution subject mismatch")
    if execution_fields.verifier_binding_root != expected_verifier_binding_root:
        raise ValueError("lane module receipt verifier binding mismatch")
    _validate_prepared_lane_module_receipt_content_digests_v1(prepared_fields)
    transition_fields = prepared_fields.transition_fields
    return VerifiedLaneModuleTransitionV1(
        _VERIFIED_LANE_MODULE_TRANSITION_TOKEN,
        _VerifiedLaneModuleTransitionFieldsV1(
            transition_fields.authenticated_command_binding_root,
            transition_fields.release_route_binding_root,
            transition_fields.expected_image_id,
            transition_fields.module_journal_root,
            transition_fields.module_journal_digest,
            transition_fields.statement_root,
            transition_fields.command_occurrence_id,
            transition_fields.receipt_digest,
            transition_fields.receipt_kind,
        ),
    )


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


@dataclass(frozen=True, slots=True)
class _ReboundLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    authenticated_command_binding_root: str
    module_journal: LaneModuleTransitionJournalV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    rebound: ReleaseRouteBoundLaneTransitionV1
    receipt: LaneModuleReceiptEnvelopeV1


def _prepare_rebound_module_receipt_v1(
    candidate: _ReboundLaneModuleReceiptCandidateV1,
) -> PreparedLaneModuleReceiptV1:
    if candidate.release_route_binding.binding_root != candidate.rebound.binding_root:
        raise ValueError("lane module structural binding mismatch")
    if candidate.receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("lane module verification requires a succinct receipt")
    if not candidate.receipt.receipt_bytes:
        raise ValueError("lane module receipt bytes must be non-empty bytes")
    if len(candidate.receipt.receipt_bytes) > MAX_LANE_MODULE_RECEIPT_BYTES_V1:
        raise ValueError("lane module receipt bytes exceed the ABI V1 byte ceiling")

    release = candidate.profile.lane_registry.release_for(candidate.rebound.lane_id)
    if release.release_id != candidate.rebound.module_release_id:
        raise ValueError("lane module verified release mismatch")
    if release.status is not ReleaseStatusV1.ACTIVE_NEW or not release.accepts_new_objects:
        raise ValueError("lane module release is not ACTIVE_NEW")

    journal_bytes = canonical_global_bytes_v1(candidate.module_journal)
    if len(journal_bytes) > release.max_journal_bytes:
        raise ValueError("lane module canonical journal exceeds its release byte ceiling")
    module_journal_digest = _sha256_root_v1(journal_bytes)
    receipt_digest = _sha256_root_v1(candidate.receipt.receipt_bytes)
    return PreparedLaneModuleReceiptV1(
        _PREPARED_LANE_MODULE_RECEIPT_TOKEN_V1,
        _PreparedLaneModuleReceiptFieldsV1(
            _PreparedLaneModuleReceiptRequestV1(
                candidate.profile.profile_id,
                candidate.rebound.lane_id,
                candidate.rebound.module_release_id,
                release.guest_image_id,
                candidate.receipt.receipt_bytes,
                journal_bytes,
            ),
            _VerifiedLaneModuleTransitionFieldsV1(
                candidate.authenticated_command_binding_root,
                candidate.rebound.binding_root,
                release.guest_image_id,
                candidate.rebound.module_journal_root,
                module_journal_digest,
                candidate.rebound.statement_root,
                candidate.rebound.command_occurrence_id,
                receipt_digest,
                candidate.receipt.receipt_kind,
            ),
        ),
    )


def prepare_asset_transfer_lane_module_receipt_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
) -> PreparedLaneModuleReceiptV1:
    """Prepare one transfer receipt under its governed policy and release image.

    The governed transfer policy and supplied structural binding are checked
    before one deterministic transition recomputation and the exact measured
    verifier request is returned.
    """

    owned = _snapshot_asset_transfer_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = _bind_asset_transfer_lane_output_structural_v1(
        AssetTransferReleaseRouteBindingCandidateV1(
            owned.profile,
            owned.policy_registry,
            owned.asset_policy_registry,
            occurrence,
            owned.module_input,
            owned.accepted,
        )
    )
    if owned.release_route_binding.binding_root != rebound.binding_root:
        raise ValueError("lane module structural binding mismatch")
    _, expected = _recompute_asset_transfer_lane_module_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    return _prepare_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        )
    )


def prepare_asset_transfer_lane_module_custody_receipt_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
) -> PreparedLaneModuleReceiptV1:
    """Prepare one custody-complete transfer receipt under the selected successor.

    One owned candidate snapshot supplies the custody semantic selector,
    structural binding, and exactly one custody-complete recomputation. Unknown
    or mixed custody roots reject before recomputation. The prepared request
    commits the active successor image, canonical journal bounds, and succinct
    envelope; this function grants no release activation or publication authority.
    """

    owned = _snapshot_asset_transfer_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = _bind_asset_transfer_custody_output_structural_v1(
        AssetTransferReleaseRouteBindingCandidateV1(
            owned.profile,
            owned.policy_registry,
            owned.asset_policy_registry,
            occurrence,
            owned.module_input,
            owned.accepted,
        )
    )
    if owned.release_route_binding.binding_root != rebound.binding_root:
        raise ValueError("lane module structural binding mismatch")
    expected = recompute_asset_transfer_lane_module_custody_v1(
        owned.module_input,
        owned.accepted,
    )
    return _prepare_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        )
    )


def prepare_managed_asset_lifecycle_lane_module_receipt_v1(
    candidate: ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
) -> PreparedLaneModuleReceiptV1:
    """Prepare one ordinary-token issue or burn receipt under its release image.

    The governed policy and supplied structural binding are checked before one
    deterministic transition recomputation and the exact measured verifier
    request is returned.
    """

    owned = _snapshot_managed_lifecycle_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = _bind_managed_asset_lifecycle_lane_output_structural_v1(
        ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
            owned.profile,
            owned.policy_registry,
            owned.asset_policy_registry,
            occurrence,
            owned.module_input,
            owned.accepted,
        )
    )
    if owned.release_route_binding.binding_root != rebound.binding_root:
        raise ValueError("lane module structural binding mismatch")
    _, expected = _recompute_managed_asset_lifecycle_lane_module_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    return _prepare_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        )
    )


def prepare_perps_margin_lane_module_receipt_v1(
    candidate: PerpsMarginLaneModuleReceiptCandidateV1,
) -> PreparedLaneModuleReceiptV1:
    """Prepare one perps-margin receipt under command and Oracle authority."""

    owned = _snapshot_perps_margin_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = bind_perps_margin_lane_output_to_release_route_v1(
        PerpsMarginReleaseRouteBindingCandidateV1(
            owned.profile,
            owned.policy_registry,
            owned.market_policy,
            occurrence,
            owned.module_input,
            owned.accepted,
            owned.verified_price,
        )
    )
    _, expected = _recompute_perps_margin_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    return _prepare_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        )
    )


def _snapshot_asset_transfer_receipt_candidate_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
) -> AssetTransferLaneModuleReceiptCandidateV1:
    if type(candidate) is not AssetTransferLaneModuleReceiptCandidateV1:
        raise TypeError("asset transfer receipt candidate must have the exact type")
    return AssetTransferLaneModuleReceiptCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=snapshot_exact_economic_policy_registry_v1(candidate.policy_registry),
        asset_policy_registry=snapshot_asset_transfer_policy_registry_v1(
            candidate.asset_policy_registry
        ),
        authenticated_command=candidate.authenticated_command,
        module_input=_snapshot_asset_transfer_lane_module_input_v1(
            candidate.module_input
        ),
        accepted=_snapshot_asset_transfer_lane_module_accepted_v1(candidate.accepted),
        release_route_binding=candidate.release_route_binding,
        receipt=_snapshot_lane_module_receipt_envelope_v1(candidate.receipt),
    )


def _snapshot_managed_lifecycle_receipt_candidate_v1(
    candidate: ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
) -> ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
    if type(candidate) is not ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
        raise TypeError("managed lifecycle receipt candidate must have the exact type")
    return ManagedAssetLifecycleLaneModuleReceiptCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=snapshot_economic_policy_registry_v1(candidate.policy_registry),
        asset_policy_registry=snapshot_managed_asset_policy_registry_v1(
            candidate.asset_policy_registry
        ),
        authenticated_command=candidate.authenticated_command,
        module_input=_snapshot_managed_asset_lifecycle_lane_module_input_v1(
            candidate.module_input
        ),
        accepted=_snapshot_managed_asset_lifecycle_lane_module_accepted_v1(
            candidate.accepted
        ),
        release_route_binding=candidate.release_route_binding,
        receipt=_snapshot_lane_module_receipt_envelope_v1(candidate.receipt),
    )


def _snapshot_perps_margin_receipt_candidate_v1(
    candidate: PerpsMarginLaneModuleReceiptCandidateV1,
) -> PerpsMarginLaneModuleReceiptCandidateV1:
    if type(candidate) is not PerpsMarginLaneModuleReceiptCandidateV1:
        raise TypeError("perps margin receipt candidate must have the exact type")
    module_input = _snapshot_perps_margin_lane_module_input_v1(candidate.module_input)
    resolve_perps_margin_command_capability_v1(module_input.command.command_kind)
    _, accepted = _recompute_perps_margin_accepted_v1(
        module_input,
        candidate.accepted,
    )
    return PerpsMarginLaneModuleReceiptCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=snapshot_economic_policy_registry_v1(
            candidate.policy_registry
        ),
        market_policy=snapshot_perps_market_policy_v1(candidate.market_policy),
        authenticated_command=candidate.authenticated_command,
        module_input=module_input,
        accepted=accepted,
        release_route_binding=candidate.release_route_binding,
        verified_price=candidate.verified_price,
        receipt=_snapshot_lane_module_receipt_envelope_v1(candidate.receipt),
    )


def _snapshot_lane_module_receipt_envelope_v1(
    receipt: LaneModuleReceiptEnvelopeV1,
) -> LaneModuleReceiptEnvelopeV1:
    if type(receipt) is not LaneModuleReceiptEnvelopeV1:
        raise TypeError("lane module receipt envelope must have the exact type")
    return LaneModuleReceiptEnvelopeV1(receipt.receipt_kind, receipt.receipt_bytes)


__all__ = [
    "AssetTransferLaneModuleReceiptCandidateV1",
    "LaneModuleReceiptEnvelopeV1",
    "ManagedAssetLifecycleLaneModuleReceiptCandidateV1",
    "PerpsMarginLaneModuleReceiptCandidateV1",
    "PreparedLaneModuleReceiptV1",
    "VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1",
    "VerifiedLaneModuleReceiptExecutionV1",
    "VerifiedLaneModuleTransitionV1",
    "bind_verified_lane_module_receipt_v1",
    "prepare_asset_transfer_lane_module_custody_receipt_v1",
    "prepare_asset_transfer_lane_module_receipt_v1",
    "prepare_managed_asset_lifecycle_lane_module_receipt_v1",
    "prepare_perps_margin_lane_module_receipt_v1",
    "snapshot_prepared_lane_module_receipt_v1",
]
