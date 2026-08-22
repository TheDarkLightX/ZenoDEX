"""Receipt-bound genesis or migration admission for the global publisher."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1,
    snapshot_economic_initial_state_source_manifest_v1,
    validate_economic_initial_state_atom_coverage_profile_binding_v1,
    validate_economic_initial_state_atom_coverage_v1,
    validate_economic_initial_state_explicit_row_count_v1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import ReceiptKindV1, SuccinctReceiptVerifierV1
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_CYCLE_BUDGET_V1,
    MAX_JOURNAL_BYTES_V1,
    ZERO_ROOT_V1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    ProfileStatusV1,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
    hash_global_v1,
    validate_global_state_profile_v1,
)
from .m6_asset_precision_policy_v1 import (
    validate_m6_asset_precision_profile_binding_v1,
)
from .m6_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
    validate_m6_capability_profile_binding_v1,
)


def _require_exact_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return _require_root(value, name=name, allow_zero=allow_zero)


def _require_exact_u64(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= (1 << 64) - 1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


@dataclass(frozen=True, slots=True)
class EconomicInitialStateCertificateV1:
    kind: EconomicInitialStateKindV1
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    height: int
    state_root: str
    source_profile_root: str
    source_state_root: str
    source_writer_epoch: int
    source_height: int
    state_atom_coverage_root: str
    lane_object_coverage_root: str
    replay_continuity_root: str
    terminal_continuity_root: str
    outbox_continuity_root: str
    source_manifest_root: str
    toolchain_manifest_root: str
    root_image_id: str
    receipt_root: str
    receipt_kind: ReceiptKindV1
    journal_bytes: int
    cycle_budget: int

    def __post_init__(self) -> None:
        if type(self.kind) is not EconomicInitialStateKindV1:
            raise TypeError("initial state kind is not closed")
        if type(self.chain_id) is not str:
            raise TypeError("initial state chain id must be exact str")
        _require_token(self.chain_id, name="initial state certificate chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "state_root",
            "state_atom_coverage_root",
            "lane_object_coverage_root",
            "replay_continuity_root",
            "terminal_continuity_root",
            "outbox_continuity_root",
            "source_manifest_root",
            "toolchain_manifest_root",
            "root_image_id",
            "receipt_root",
        ):
            _require_exact_root(
                getattr(self, field_name),
                name=f"initial state certificate {field_name}",
            )
        for field_name in (
            "writer_epoch",
            "height",
            "source_writer_epoch",
            "source_height",
            "journal_bytes",
            "cycle_budget",
        ):
            _require_exact_u64(
                getattr(self, field_name),
                name=f"initial state certificate {field_name}",
            )
        if self.journal_bytes == 0 or self.journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("initial state journal byte count is outside ABI V1 bounds")
        if self.cycle_budget == 0 or self.cycle_budget > MAX_CYCLE_BUDGET_V1:
            raise ValueError("initial state cycle budget is outside ABI V1 bounds")
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("initial state receipt kind is not closed")
        if self.receipt_kind is not ReceiptKindV1.SUCCINCT:
            raise ValueError("initial state authority requires a succinct receipt")
        source_roots = (self.source_profile_root, self.source_state_root)
        if self.kind is EconomicInitialStateKindV1.GENESIS:
            for index, root in enumerate(source_roots):
                _require_exact_root(
                    root,
                    name=f"genesis source root[{index}]",
                    allow_zero=True,
                )
            if source_roots != (ZERO_ROOT_V1, ZERO_ROOT_V1):
                raise ValueError("genesis must not declare a predecessor")
            if self.source_writer_epoch != 0 or self.source_height != 0:
                raise ValueError("genesis predecessor coordinates must be zero")
            if self.height != 0:
                raise ValueError("genesis target height must be zero")
        else:
            for index, root in enumerate(source_roots):
                _require_exact_root(root, name=f"migration source root[{index}]")
            if self.source_profile_root == self.profile_root:
                raise ValueError("migration target profile must differ from its source")
            if self.source_writer_epoch == (1 << 64) - 1:
                raise ValueError("migration source writer epoch cannot advance")
            if self.writer_epoch != self.source_writer_epoch + 1:
                raise ValueError("migration must rotate the writer epoch exactly once")
            if self.source_height == (1 << 64) - 1:
                raise ValueError("migration source height cannot advance")
            if self.height != self.source_height + 1:
                raise ValueError("migration must occupy exactly one transition height")

    def journal_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "kind": self.kind,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "height": self.height,
            "state_root": self.state_root,
            "source_profile_root": self.source_profile_root,
            "source_state_root": self.source_state_root,
            "source_writer_epoch": self.source_writer_epoch,
            "source_height": self.source_height,
            "state_atom_coverage_root": self.state_atom_coverage_root,
            "lane_object_coverage_root": self.lane_object_coverage_root,
            "replay_continuity_root": self.replay_continuity_root,
            "terminal_continuity_root": self.terminal_continuity_root,
            "outbox_continuity_root": self.outbox_continuity_root,
            "source_manifest_root": self.source_manifest_root,
            "toolchain_manifest_root": self.toolchain_manifest_root,
            "root_image_id": self.root_image_id,
        }

    @property
    def canonical_journal_bytes(self) -> bytes:
        return canonical_global_bytes_v1(self.journal_canonical())

    @property
    def certificate_root(self) -> str:
        return hash_global_v1("economic-initial-state-certificate-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            **self.journal_canonical(),
            "receipt_root": self.receipt_root,
            "receipt_kind": self.receipt_kind,
            "journal_bytes": self.journal_bytes,
            "cycle_budget": self.cycle_budget,
        }


@dataclass(frozen=True, slots=True)
class EconomicInitialStateAdmissionV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    state: GlobalEconomicStateV1
    predecessor_state: GlobalEconomicStateV1 | None
    source_manifest: EconomicInitialStateSourceManifestV1
    certificate: EconomicInitialStateCertificateV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.profile) is not EconomicProfileSnapshotV1:
            raise TypeError("initial state admission profile type is not closed")
        if type(self.policy_registry) is not EconomicPolicyRegistryV1:
            raise TypeError("initial state admission policy registry type is not closed")
        if type(self.state) is not GlobalEconomicStateV1:
            raise TypeError("initial state admission state type is not closed")
        if self.predecessor_state is not None and type(
            self.predecessor_state
        ) is not GlobalEconomicStateV1:
            raise TypeError("initial state admission predecessor state type is not closed")
        if type(self.source_manifest) is not EconomicInitialStateSourceManifestV1:
            raise TypeError("initial state admission source manifest type is not closed")
        if type(self.certificate) is not EconomicInitialStateCertificateV1:
            raise TypeError("initial state admission certificate type is not closed")
        if self.certificate.kind is EconomicInitialStateKindV1.GENESIS:
            if self.predecessor_state is not None:
                raise ValueError("genesis initial state must not include a predecessor state")
        elif self.predecessor_state is None:
            raise ValueError("migration initial state requires a predecessor state")
        if type(self.receipt_bytes) is not bytes or not self.receipt_bytes:
            raise TypeError("initial state admission receipt must be nonempty exact bytes")


@dataclass(frozen=True, slots=True)
class _VerifiedEconomicInitialStateV1:
    profile: EconomicProfileSnapshotV1
    state: GlobalEconomicStateV1
    certificate_root: str


@dataclass(frozen=True, slots=True)
class _OwnedEconomicInitialStateAdmissionV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    state: GlobalEconomicStateV1
    predecessor_state: GlobalEconomicStateV1 | None
    source_manifest: EconomicInitialStateSourceManifestV1
    certificate: EconomicInitialStateCertificateV1
    receipt_bytes: bytes


def _snapshot_economic_initial_state_admission_v1(
    admission: EconomicInitialStateAdmissionV1,
) -> _OwnedEconomicInitialStateAdmissionV1:
    if type(admission) is not EconomicInitialStateAdmissionV1:
        raise TypeError("commit port initial admission type is not closed")
    validate_economic_initial_state_explicit_row_count_v1(admission.state)
    if admission.predecessor_state is not None:
        validate_economic_initial_state_explicit_row_count_v1(
            admission.predecessor_state
        )
    return _OwnedEconomicInitialStateAdmissionV1(
        profile=snapshot_economic_profile_v1(admission.profile),
        policy_registry=snapshot_economic_policy_registry_v1(
            admission.policy_registry
        ),
        state=_snapshot_state_v1(admission.state),
        predecessor_state=(
            None
            if admission.predecessor_state is None
            else _snapshot_state_v1(admission.predecessor_state)
        ),
        source_manifest=snapshot_economic_initial_state_source_manifest_v1(
            admission.source_manifest
        ),
        certificate=replace(admission.certificate),
        receipt_bytes=admission.receipt_bytes,
    )


def _validate_economic_initial_state_predecessor_binding_v1(
    target_state: GlobalEconomicStateV1,
    predecessor_state: GlobalEconomicStateV1 | None,
    certificate: EconomicInitialStateCertificateV1,
) -> None:
    if certificate.kind is EconomicInitialStateKindV1.GENESIS:
        if predecessor_state is not None:
            raise ValueError("genesis initial state must not include a predecessor state")
        return
    if predecessor_state is None:
        raise ValueError("migration initial state requires a predecessor state")
    bindings = (
        (predecessor_state.chain_id, target_state.chain_id, "chain id"),
        (
            predecessor_state.deployment_root,
            target_state.deployment_root,
            "deployment root",
        ),
        (
            predecessor_state.profile_root,
            certificate.source_profile_root,
            "profile root",
        ),
        (
            predecessor_state.state_root,
            certificate.source_state_root,
            "state root",
        ),
        (
            predecessor_state.writer_epoch,
            certificate.source_writer_epoch,
            "writer epoch",
        ),
        (predecessor_state.height, certificate.source_height, "height"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"initial state predecessor {label} mismatch")


def _validate_owned_economic_initial_state_admission_v1(
    owned: _OwnedEconomicInitialStateAdmissionV1,
) -> bytes:
    profile = owned.profile
    policy_registry = owned.policy_registry
    state = owned.state
    source_manifest = owned.source_manifest
    certificate = owned.certificate
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("initial state admission requires an ACTIVE profile")
    validate_m6_capability_profile_binding_v1(profile, policy_registry)
    validate_m6_asset_precision_profile_binding_v1(profile, policy_registry)
    validate_economic_initial_state_atom_coverage_profile_binding_v1(
        profile,
        policy_registry,
        source_manifest,
    )
    validate_global_state_profile_v1(state, profile)
    _validate_economic_initial_state_predecessor_binding_v1(
        state,
        owned.predecessor_state,
        certificate,
    )
    if certificate.kind is not source_manifest.kind:
        raise ValueError("initial state certificate and source manifest kind mismatch")
    coverage_root = validate_economic_initial_state_atom_coverage_v1(
        state,
        source_manifest,
    )
    if certificate.state_atom_coverage_root != coverage_root:
        raise ValueError("initial state atom coverage root mismatch")
    bindings = (
        (certificate.chain_id, state.chain_id, "chain id"),
        (certificate.deployment_root, state.deployment_root, "deployment root"),
        (certificate.profile_root, profile.profile_id, "profile root"),
        (certificate.profile_root, state.profile_root, "state profile root"),
        (certificate.writer_epoch, profile.authority_epoch, "profile writer epoch"),
        (certificate.writer_epoch, state.writer_epoch, "state writer epoch"),
        (certificate.height, state.height, "state height"),
        (certificate.state_root, state.state_root, "state root"),
        (certificate.root_image_id, profile.root_image_id, "root image id"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"initial state {label} mismatch")
    journal_bytes = certificate.canonical_journal_bytes
    if certificate.journal_bytes != len(journal_bytes):
        raise ValueError("initial state canonical journal byte count mismatch")
    receipt_digest = "0x" + hashlib.sha256(owned.receipt_bytes).hexdigest()
    if certificate.receipt_root != receipt_digest:
        raise ValueError("initial state receipt root mismatch")
    return journal_bytes


def _verify_economic_initial_state_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Verify and own the initial state before constructing a publisher."""

    owned = _snapshot_economic_initial_state_admission_v1(admission)
    journal_bytes = _validate_owned_economic_initial_state_admission_v1(owned)
    receipt_verifier.verify_succinct_receipt(
        owned.receipt_bytes,
        expected_image_id=owned.profile.root_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return _VerifiedEconomicInitialStateV1(
        profile=snapshot_economic_profile_v1(owned.profile),
        state=_snapshot_state_v1(owned.state),
        certificate_root=owned.certificate.certificate_root,
    )


__all__ = [
    "EconomicInitialStateKindV1",
    "EconomicInitialStateCertificateV1",
    "EconomicInitialStateAdmissionV1",
]
