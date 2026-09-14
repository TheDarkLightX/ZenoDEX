"""Single-store custody publication for a fresh, isolated ABI V2 deployment.

Trusted genesis/configuration and an honest publisher/SQLite/filesystem are
premises. This adapter has no live effect mount, migration, external monotonic
anchor or production activation. Recovery replays economics and bindings;
ordinary recovery relies on publication-time cryptographic success. The
separate read-only audit rechecks retained evidence against selected policy
and checkpoint inputs; its result grants no writer or finality authority.
"""

from __future__ import annotations

import fcntl
import os
import sqlite3
import stat
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from threading import Lock
from typing import Literal, cast

from ..core.asset_lane_coordinator_v2 import _route_and_owned_command_v2
from ..core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from ..core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from ..core.asset_lane_custody_global_v2 import _require_complete_projection
from ..core.asset_lane_custody_guest_role_v2 import (
    AssetLaneCustodyGuestRoleBindingV2,
    snapshot_asset_lane_custody_guest_role_binding_v2,
)
from ..core.asset_lane_custody_input_v2 import prepare_asset_lane_custody_global_prover_input_v2
from ..core.asset_lane_custody_profile_binding_v2 import _require_global_predecessor_binding_v2
from ..core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from ..core.asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from ..core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    snapshot_command_authentication_candidate_v2,
)
from ..core.economic_command_authentication_v2 import (
    prepare_isolated_economic_command_authentication_v2,
)
from ..core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    _snapshot_signature_verifier_manifest_v1,
)
from ..core.global_economic_authority_head_v2 import (
    GlobalEconomicAuthorityHeadV2,
    GlobalEconomicAuthorityStatusV2,
    decode_global_economic_authority_head_v2,
)
from ..core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from ..core.global_economic_state_v2 import GlobalEconomicStateV2
from ..core.global_settlement_primitives_v2 import (
    _require_root_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from ..core.global_settlement_types_v1 import EconomicProfileSnapshotV1, ProfileStatusV1
from ..core.global_settlement_types_v2 import LaneIdV2
from ..core.perps_margin_claims_v2 import require_margin_claim_projection_v2
from ..core.perps_margin_global_v2 import PerpsMarginGlobalRejectedV2
from ..core.perps_margin_guest_role_v2 import PerpsMarginGuestRoleBindingV2
from ..core.perps_margin_receipt_v2 import encode_perps_margin_frame_v2
from ..core.perps_margin_state_v2 import PerpsMarginStateV2
from ..core.perps_margin_types_v1 import PerpsMarginCommandV1
from ..core.perps_margin_wire_v2 import PerpsMarginRequestV2
from .custody_publication_record_v2 import (
    CustodyPublicationRecordV2,
    CustodyPublicationReplayV2,
    custody_request_id_v2,
    decode_custody_global_state_v2,
    decode_joint_margin_genesis_v2,
    encode_joint_margin_genesis_v2,
    frame_joint_margin_publication_v2,
    joint_margin_request_id_v2,
    raw_root_v2,
    replay_custody_publication_frame_v2,
)
from .global_receipt_verifier_v1 import MAX_RECEIPT_BYTES_V1
from .profiled_asset_lane_custody_receipt_v2 import (
    verify_isolated_profiled_asset_lane_custody_receipt_v2,
)
from .profiled_perps_margin_receipt_v2 import verify_isolated_profiled_perps_margin_receipt_v2

# Operational bounds for this reference store, not protocol population limits.
MAX_CUSTODY_PUBLICATIONS_V2 = 64
MAX_CUSTODY_HISTORY_BYTES_V2 = 64 * 1024 * 1024
_MINT = object()
_TABLES = {
    "genesis": "CREATE TABLE genesis (singleton INTEGER PRIMARY KEY CHECK(singleton=1), global_bytes BLOB NOT NULL, lane_bytes BLOB NOT NULL, authority_bytes BLOB NOT NULL) STRICT",
    "authority_history": "CREATE TABLE authority_history (generation INTEGER PRIMARY KEY, authority_bytes BLOB NOT NULL UNIQUE) STRICT",
    "publications": "CREATE TABLE publications (sequence INTEGER PRIMARY KEY, publication_id TEXT NOT NULL UNIQUE, request_id TEXT NOT NULL UNIQUE, source_publication_id TEXT NOT NULL, authority_root TEXT NOT NULL, frame BLOB NOT NULL, statement BLOB NOT NULL, authentication_message BLOB NOT NULL, signature BLOB NOT NULL, receipt BLOB NOT NULL) STRICT",
    "heads": "CREATE TABLE heads (singleton INTEGER PRIMARY KEY CHECK(singleton=1), publication_id TEXT NOT NULL, sequence INTEGER NOT NULL, authority_generation INTEGER NOT NULL) STRICT",
}


class CustodyPublicationStatusV2(str, Enum):
    COMMITTED = "COMMITTED"
    ALREADY_COMMITTED = "ALREADY_COMMITTED"
    STALE_HEAD = "STALE_HEAD"
    AUTHORITY_STALE = "AUTHORITY_STALE"
    CAPACITY_EXCEEDED = "CAPACITY_EXCEEDED"


class CustodyPublicationIndeterminateV2(RuntimeError):
    """A commit was attempted; retry or retained history must resolve knowledge."""


@dataclass(frozen=True, slots=True)
class CustodyPublicationConfigurationV2:
    profile: EconomicProfileSnapshotV1
    guest_role_binding: AssetLaneCustodyGuestRoleBindingV2
    signature_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1
    receipt_executable_path: str
    signature_artifact_path: Path
    receipt_timeout_ms: int = 5_000
    signature_timeout_ms: int = 5_000

    def __post_init__(self) -> None:
        object.__setattr__(self, "profile", snapshot_economic_profile_v1(self.profile))
        object.__setattr__(
            self,
            "guest_role_binding",
            snapshot_asset_lane_custody_guest_role_binding_v2(self.guest_role_binding),
        )
        object.__setattr__(
            self,
            "signature_manifest",
            _snapshot_signature_verifier_manifest_v1(self.signature_manifest),
        )
        if type(self.receipt_executable_path) is not str or type(
            self.signature_artifact_path
        ) is not type(Path()):
            raise TypeError("custody verifier paths must be exact str and platform Path")
        if self.profile.status is not ProfileStatusV1.ACTIVE:
            raise ValueError("isolated custody configuration requires ACTIVE profile")
        if (self.guest_role_binding.profile_root, self.guest_role_binding.authority_epoch) != (
            self.profile.profile_id,
            self.profile.authority_epoch,
        ):
            raise ValueError("custody configuration role and profile mismatch")
        for timeout in (self.receipt_timeout_ms, self.signature_timeout_ms):
            if type(timeout) is not int or not 1 <= timeout <= 60_000:
                raise ValueError("custody verifier timeout is outside the bound")


@dataclass(frozen=True, slots=True)
class JointMarginPublicationConfigurationV2:
    """Independently selected fixed pair of custody and margin receipt roles."""

    custody: CustodyPublicationConfigurationV2
    margin_role: PerpsMarginGuestRoleBindingV2
    margin_receipt_executable_path: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "custody", _configuration_copy(self.custody))
        if type(self.margin_role) is not PerpsMarginGuestRoleBindingV2:
            raise TypeError("joint margin role must be exact")
        role = PerpsMarginGuestRoleBindingV2(
            self.margin_role.profile_root, self.margin_role.authority_epoch,
            self.margin_role.evidence_manifest,
        )
        object.__setattr__(self, "margin_role", role)
        if (role.profile_root, role.authority_epoch) != (
            self.custody.profile.profile_id, self.custody.profile.authority_epoch,
        ):
            raise ValueError("joint margin role and custody profile differ")
        if type(self.margin_receipt_executable_path) is not str:
            raise TypeError("margin receipt executable path must be exact str")

    @property
    def binding_root(self) -> str:
        return hash_global_v2("isolated-joint-margin-roles-v2", {
            "custody": self.custody.guest_role_binding.binding_root,
            "margin": self.margin_role.binding_root,
        })


PublicationConfigurationV2 = CustodyPublicationConfigurationV2 | JointMarginPublicationConfigurationV2


@dataclass(frozen=True, slots=True)
class CustodyPublicationSnapshotV2:
    publication_id: str
    sequence: int
    authority: GlobalEconomicAuthorityHeadV2
    global_state: GlobalEconomicStateV2
    custody_state: AssetLaneCustodyStateV2
    margin_state: PerpsMarginStateV2 | None = None


@dataclass(frozen=True, slots=True)
class CustodyPublicationOutcomeV2:
    status: CustodyPublicationStatusV2
    head: CustodyPublicationSnapshotV2
    committed_publication_id: str | None = None


@dataclass(frozen=True, slots=True)
class CustodyPublicationRequestV2:
    """One defensively owned custody context and closed asset-lane command."""

    context: AssetLaneContextV2
    command: AssetLaneCommandV2

    def __post_init__(self) -> None:
        if type(self.context) is not AssetLaneContextV2:
            raise TypeError("custody publication context must be exact")
        object.__setattr__(self, "context", _snapshot_asset_lane_context_v2(self.context))
        _, command = _route_and_owned_command_v2(self.command)
        object.__setattr__(self, "command", command)


def _private_inode(path: Path, expected_links: int = 1) -> os.stat_result:
    metadata = path.lstat()
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_uid != os.geteuid():
        raise PermissionError("custody store requires a process-owned regular file")
    if stat.S_IMODE(metadata.st_mode) != 0o600 or metadata.st_nlink != expected_links:
        raise PermissionError("custody store mode or exact link count is invalid")
    if metadata.st_size > 96 * 1024 * 1024:
        raise ValueError("custody store file exceeds its operational byte bound")
    for suffix in ("-wal", "-shm"):
        if os.path.lexists(str(path) + suffix):
            raise ValueError("custody store WAL or SHM artifact is unsupported")
    return metadata


def _configuration_copy(
    value: CustodyPublicationConfigurationV2,
) -> CustodyPublicationConfigurationV2:
    if type(value) is not CustodyPublicationConfigurationV2:
        raise TypeError("custody publication configuration must have the exact type")
    return CustodyPublicationConfigurationV2(
        value.profile,
        value.guest_role_binding,
        value.signature_manifest,
        value.receipt_executable_path,
        value.signature_artifact_path,
        value.receipt_timeout_ms,
        value.signature_timeout_ms,
    )


def _complete_predecessor_matches_v2(
    replay: CustodyPublicationReplayV2, head: CustodyPublicationSnapshotV2,
) -> bool:
    return all(canonical_global_bytes_v2(before) == canonical_global_bytes_v2(current)
               for before, current in (
                   (replay.global_pre, head.global_state),
                   (replay.lane_pre, head.custody_state),
                   (replay.margin_pre, head.margin_state),
               ))


def _owned_perps_margin_request_v2(request: PerpsMarginRequestV2) -> PerpsMarginRequestV2:
    """Copy a margin request already accepted by exact route dispatch."""
    return PerpsMarginRequestV2(request.command, request.occurrence, request.oracle)


def _owned_publication_request_v2(
    request: CustodyPublicationRequestV2 | PerpsMarginRequestV2,
    *,
    joint: bool,
) -> CustodyPublicationRequestV2 | PerpsMarginRequestV2:
    if type(request) is CustodyPublicationRequestV2:
        return CustodyPublicationRequestV2(request.context, request.command)
    if type(request) is PerpsMarginRequestV2:
        if not joint:
            raise TypeError("margin publication needs a joint deployment and one owned request")
        return _owned_perps_margin_request_v2(request)
    raise TypeError("publication request must have its exact route-owned type")


class IsolatedCustodyPublisherV2:
    """Own admission and the sole write path of one isolated custody ledger."""

    def __init__(
        self,
        mint: object,
        path: Path,
        global_raw: bytes,
        lane_raw: bytes,
        configuration: PublicationConfigurationV2,
    ) -> None:
        if mint is not _MINT:
            raise TypeError("custody publisher requires create/open admission")
        self._path = path
        self._joint_configuration: JointMarginPublicationConfigurationV2 | None = None
        if type(configuration) is JointMarginPublicationConfigurationV2:
            self._joint_configuration = JointMarginPublicationConfigurationV2(
                configuration.custody, configuration.margin_role,
                configuration.margin_receipt_executable_path,
            )
            self._configuration = self._joint_configuration.custody
        elif type(configuration) is CustodyPublicationConfigurationV2:
            self._configuration = _configuration_copy(configuration)
        else:
            raise TypeError("publication configuration must have an exact supported type")
        self._global_raw, self._lane_raw = global_raw, lane_raw
        global_state = decode_custody_global_state_v2(global_raw)
        self._initial_margin: PerpsMarginStateV2 | None = None
        if self._joint_configuration is not None:
            lane_state, self._initial_margin = decode_joint_margin_genesis_v2(lane_raw)
            require_margin_claim_projection_v2(self._initial_margin, global_state)
            if {row.lane_id for row in global_state.lane_roots if row.enabled} != {
                LaneIdV2.ASSET_TRANSFER, LaneIdV2.PERPS_MARKET,
            }:
                raise ValueError("joint isolated genesis supports exactly custody and margin lanes")
            if any(account.position_base != 0 for account in self._initial_margin.economic_state.accounts):
                raise ValueError("joint isolated genesis requires flat margin accounts")
        else:
            lane_state = decode_asset_lane_custody_state_v2(lane_raw)
        _require_complete_projection(lane_state, global_state)
        _require_global_predecessor_binding_v2(global_state, self._configuration.profile)
        self._genesis_id = hash_global_v2(
            "isolated-joint-margin-genesis-v2" if self._joint_configuration is not None
            else "isolated-custody-genesis-v2",
            {
                "global_state": raw_root_v2(global_raw),
                "custody_state": raw_root_v2(lane_raw),
            },
        )
        self._expected_authority = GlobalEconomicAuthorityHeadV2(
            generation=0,
            genesis_id=self._genesis_id,
            chain_id=global_state.chain_id,
            deployment_root=global_state.deployment_root,
            epoch_store_root=hash_global_v2("isolated-custody-store-v2", {"file_name": path.name}),
            profile_root=global_state.profile_root,
            writer_epoch=global_state.writer_epoch,
            guest_role_binding_root=(self._joint_configuration.binding_root
                                     if self._joint_configuration is not None
                                     else self._configuration.guest_role_binding.binding_root),
            signature_manifest_root=self._configuration.signature_manifest.manifest_root,
            status=GlobalEconomicAuthorityStatusV2.ACTIVE,
        )
        self._lock = Lock()
        self._closed = False

    @classmethod
    def create(
        cls,
        path: str | Path,
        global_state: GlobalEconomicStateV2,
        custody_state: AssetLaneCustodyStateV2,
        configuration: PublicationConfigurationV2,
        *,
        margin_state: PerpsMarginStateV2 | None = None,
    ) -> IsolatedCustodyPublisherV2:
        publisher = cls._prepare(path, global_state, custody_state, configuration, margin_state)
        try:
            _install_genesis_v2(publisher)
        finally:
            publisher.close()
        return cls.open(path, global_state, custody_state, configuration, margin_state=margin_state)

    @classmethod
    def open(
        cls,
        path: str | Path,
        global_state: GlobalEconomicStateV2,
        custody_state: AssetLaneCustodyStateV2,
        configuration: PublicationConfigurationV2,
        *,
        margin_state: PerpsMarginStateV2 | None = None,
    ) -> IsolatedCustodyPublisherV2:
        publisher = cls._prepare(path, global_state, custody_state, configuration, margin_state)
        try:
            publisher._connect()
            head = publisher.snapshot()
            if head.authority != publisher._expected_authority:
                raise PermissionError("custody writer authority is no longer current")
            return publisher
        except BaseException:
            publisher.close()
            raise

    @classmethod
    def audit(
        cls,
        path: str | Path,
        global_state: GlobalEconomicStateV2,
        custody_state: AssetLaneCustodyStateV2,
        configuration: PublicationConfigurationV2,
        *,
        authentication_candidates: tuple[EconomicCommandAuthenticationCandidateV2, ...],
        expected_publication_id: str,
        expected_authority_root: str,
        margin_state: PerpsMarginStateV2 | None = None,
    ) -> CustodyPublicationSnapshotV2:
        """Reauthenticate a copied history without acquiring a writer connection.

        Select genesis, configuration and both checkpoint roots independently
        of the copy. Candidates supply the historical policy witnesses; their
        complete prepared messages and signatures must match retained records.
        The returned detached snapshot says nothing about subsequent writes,
        finality, revocation provenance or freshness of the selected checkpoint.
        """
        _require_root_v2(expected_publication_id, name="audit publication checkpoint")
        _require_root_v2(expected_authority_root, name="audit authority checkpoint")
        if type(authentication_candidates) is not tuple:
            raise TypeError("audit authentication candidates must be an exact tuple")
        if len(authentication_candidates) > MAX_CUSTODY_PUBLICATIONS_V2:
            raise ValueError("audit authentication candidates exceed history capacity")
        candidates = tuple(map(snapshot_command_authentication_candidate_v2, authentication_candidates))
        reader = cls._prepare(path, global_state, custody_state, configuration, margin_state)
        try:
            reader._connect(access="ro")
            head, records = reader._read()
        finally:
            reader.close()
        if (head.publication_id, head.authority.authority_root) != (
            expected_publication_id, expected_authority_root,
        ):
            raise ValueError("audit history differs from independently selected checkpoint")
        if len(candidates) != len(records):
            raise ValueError("audit requires exactly one authentication candidate per record")
        reader._audit_records(records, candidates)
        return head

    def _audit_records(
        self, records: tuple[CustodyPublicationRecordV2, ...],
        candidates: tuple[EconomicCommandAuthenticationCandidateV2, ...],
    ) -> None:
        # The read transaction and connection are already closed. Reuse the
        # publication verifier on detached values, never its commit closure.
        for record, candidate in zip(records, candidates, strict=True):
            owned, _, message = prepare_isolated_economic_command_authentication_v2(candidate)
            if (
                canonical_global_bytes_v2(owned.profile) != canonical_global_bytes_v2(self._configuration.profile)
                or message != record.authentication_message
                or owned.envelope.signature_bytes != record.signature
            ):
                raise ValueError("audit authentication witness differs from retained record or profile")
            replay = record.replay()
            request: CustodyPublicationRequestV2 | PerpsMarginRequestV2
            if type(replay.context) is PerpsMarginRequestV2:
                request = replay.context
            elif type(replay.context) is AssetLaneContextV2:
                request = CustodyPublicationRequestV2(
                    replay.context, cast(AssetLaneCommandV2, replay.command)
                )
            else:
                raise ValueError("audit replay does not have an exact publication request")
            request = _owned_publication_request_v2(
                request, joint=self._joint_configuration is not None
            )
            predecessor = CustodyPublicationSnapshotV2(
                record.source_publication_id, record.sequence - 1, self._expected_authority,
                replay.global_pre, replay.lane_pre, replay.margin_pre,
            )
            frame, statement = self._verify_request_v2(owned, request, predecessor, record.receipt)
            if frame != record.frame or statement != record.statement:
                raise ValueError("audit verified statement differs from retained publication")

    @classmethod
    def _prepare(
        cls,
        path: str | Path,
        global_state: GlobalEconomicStateV2,
        custody_state: AssetLaneCustodyStateV2,
        configuration: PublicationConfigurationV2,
        margin_state: PerpsMarginStateV2 | None,
    ) -> IsolatedCustodyPublisherV2:
        if cls is not IsolatedCustodyPublisherV2:
            raise TypeError("custody publisher class must be exact")
        if type(path) is not str and type(path) is not type(Path()):
            raise TypeError("custody store path must be exact str or platform Path")
        normalized = Path(path).absolute()
        if not normalized.name or not normalized.parent.is_dir():
            raise ValueError("custody store requires an existing parent directory")
        if (
            type(global_state) is not GlobalEconomicStateV2
            or type(custody_state) is not AssetLaneCustodyStateV2
        ):
            raise TypeError("custody genesis requires both exact state types")
        joint = type(configuration) is JointMarginPublicationConfigurationV2
        if joint != (type(margin_state) is PerpsMarginStateV2):
            raise TypeError("joint configuration requires the complete margin genesis")
        if not joint and margin_state is not None:
            raise TypeError("custody-only configuration cannot take margin state")
        lane_raw = (encode_joint_margin_genesis_v2(custody_state, margin_state)
                    if joint and margin_state is not None else canonical_global_bytes_v2(custody_state))
        return cls(
            _MINT,
            normalized,
            canonical_global_bytes_v2(global_state),
            lane_raw,
            configuration,
        )

    def _connect(
        self, storage_path: Path | None = None, expected_links: int = 1,
        *, access: Literal["ro", "rw"] = "rw",
    ) -> None:
        self._storage_path = self._path if storage_path is None else storage_path
        self._expected_links = expected_links
        self._inode = _private_inode(self._storage_path, expected_links)
        self._identity_fd = os.open(self._storage_path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC)
        self._connection = sqlite3.connect(
            self._storage_path.as_uri() + "?mode=" + access,
            uri=True,
            isolation_level=None,
            check_same_thread=False,
        )
        if self._connection.execute("PRAGMA journal_mode").fetchone() != ("delete",):
            raise ValueError("custody store requires DELETE journal mode")
        self._connection.execute("PRAGMA synchronous=FULL")
        self._connection.execute("PRAGMA trusted_schema=OFF")
        self._connection.execute("PRAGMA foreign_keys=ON")
        self._require_identity()

    def _require_identity(self) -> None:
        if self._closed:
            raise RuntimeError("custody publisher is closed")
        current = _private_inode(self._storage_path, self._expected_links)
        descriptor = os.fstat(self._identity_fd)
        expected = (self._inode.st_dev, self._inode.st_ino)
        if (current.st_dev, current.st_ino) != expected or (
            descriptor.st_dev,
            descriptor.st_ino,
        ) != expected:
            raise PermissionError("custody store identity changed")

    def close(self) -> None:
        with self._lock:
            if not self._closed:
                connection = getattr(self, "_connection", None)
                if connection is not None:
                    connection.close()
                identity = getattr(self, "_identity_fd", None)
                if identity is not None:
                    os.close(identity)
                self._closed = True

    def __enter__(self) -> IsolatedCustodyPublisherV2:
        self._require_identity()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    def _validate(
        self,
    ) -> tuple[CustodyPublicationSnapshotV2, tuple[CustodyPublicationRecordV2, ...]]:
        self._require_identity()
        connection = self._connection
        schema = connection.execute(
            "SELECT name, sql FROM sqlite_master WHERE name NOT LIKE 'sqlite_%' ORDER BY name"
        ).fetchall()
        if schema != sorted(_TABLES.items()):
            raise ValueError("custody store schema is not exact")
        lengths = connection.execute(
            "SELECT singleton, length(global_bytes), length(lane_bytes), length(authority_bytes) FROM genesis"
        ).fetchall()
        if lengths != [
            (
                1,
                len(self._global_raw),
                len(self._lane_raw),
                len(self._expected_authority.canonical_bytes),
            )
        ]:
            raise ValueError("custody genesis size differs from selected configuration")
        genesis = connection.execute(
            "SELECT singleton, global_bytes, lane_bytes, authority_bytes FROM genesis"
        ).fetchall()
        if genesis != [
            (1, self._global_raw, self._lane_raw, self._expected_authority.canonical_bytes)
        ]:
            raise ValueError("custody genesis or independently selected configuration mismatch")
        count, maximum = connection.execute(
            "SELECT COUNT(*), MAX(length(authority_bytes)) FROM authority_history"
        ).fetchone()
        if count not in (1, 2) or maximum > 4096:
            raise ValueError("custody authority history exceeds its bound")
        authority_rows = connection.execute(
            "SELECT generation, authority_bytes FROM authority_history ORDER BY generation"
        ).fetchall()
        expected = [(0, self._expected_authority.canonical_bytes)]
        if len(authority_rows) == 2:
            expected.append((1, self._expected_authority.revoked_successor().canonical_bytes))
        if authority_rows != expected:
            raise ValueError("custody authority history is invalid")
        authority = decode_global_economic_authority_head_v2(authority_rows[-1][1])
        count, size = connection.execute(
            "SELECT COUNT(*), COALESCE(SUM(length(frame)+length(statement)+length(authentication_message)+length(signature)+length(receipt)),0) FROM publications"
        ).fetchone()
        if count > MAX_CUSTODY_PUBLICATIONS_V2 or size > MAX_CUSTODY_HISTORY_BYTES_V2:
            raise ValueError("custody stored history exceeds operational capacity")
        identifiers = connection.execute(
            "SELECT COUNT(*) FROM publications WHERE length(publication_id)!=66 OR length(request_id)!=66 OR length(source_publication_id)!=66 OR length(authority_root)!=66"
        ).fetchone()
        if identifiers != (0,):
            raise ValueError("custody history identifier length is invalid")
        if connection.execute("SELECT singleton, length(publication_id) FROM heads").fetchall() != [
            (1, 66)
        ]:
            raise ValueError("custody current head exceeds its shape bound")
        if self._joint_configuration is None:
            assets, margin = decode_asset_lane_custody_state_v2(self._lane_raw), None
        else:
            assets, margin = decode_joint_margin_genesis_v2(self._lane_raw)
        initial = CustodyPublicationSnapshotV2(
            self._genesis_id,
            0,
            authority,
            decode_custody_global_state_v2(self._global_raw),
            assets,
            margin,
        )
        head, records = self._validate_history(initial)
        if connection.execute(
            "SELECT singleton, publication_id, sequence, authority_generation FROM heads"
        ).fetchall() != [(1, head.publication_id, head.sequence, authority.generation)]:
            raise ValueError("custody head does not match complete history")
        self._require_identity()
        return head, records

    def _validate_history(
        self, head: CustodyPublicationSnapshotV2
    ) -> tuple[CustodyPublicationSnapshotV2, tuple[CustodyPublicationRecordV2, ...]]:
        rows = self._connection.execute(
            "SELECT sequence, publication_id, request_id, source_publication_id, authority_root, frame, statement, authentication_message, signature, receipt FROM publications ORDER BY sequence"
        ).fetchall()
        records = []
        for row in rows:
            record = CustodyPublicationRecordV2(row[0], *row[3:])
            if record.is_joint_margin != (self._joint_configuration is not None):
                raise ValueError("custody record frame does not match the selected deployment")
            replay = record.replay()
            if (
                row[1],
                row[2],
                record.sequence,
                record.source_publication_id,
                record.authority_root,
            ) != (
                record.publication_id,
                record.request_id,
                head.sequence + 1,
                head.publication_id,
                self._expected_authority.authority_root,
            ):
                raise ValueError("custody record lineage or identity mismatch")
            if not _complete_predecessor_matches_v2(replay, head):
                raise ValueError("custody record predecessor is not the complete committed source")
            head = CustodyPublicationSnapshotV2(
                record.publication_id,
                record.sequence,
                head.authority,
                replay.global_post,
                replay.lane_post,
                replay.margin_post,
            )
            records.append(record)
        return head, tuple(records)

    def _read(self) -> tuple[CustodyPublicationSnapshotV2, tuple[CustodyPublicationRecordV2, ...]]:
        with self._lock:
            self._require_identity()
            self._connection.execute("BEGIN")
            try:
                result = self._validate()
                self._connection.execute("COMMIT")
                return result
            finally:
                if self._connection.in_transaction:
                    self._connection.execute("ROLLBACK")

    def snapshot(self) -> CustodyPublicationSnapshotV2:
        return self._read()[0]

    def publish(
        self,
        candidate: EconomicCommandAuthenticationCandidateV2,
        request: CustodyPublicationRequestV2 | PerpsMarginRequestV2,
        *,
        receipt_bytes: bytes,
    ) -> CustodyPublicationOutcomeV2 | AssetLaneRejectedV2 | PerpsMarginGlobalRejectedV2:
        owned, _, message = prepare_isolated_economic_command_authentication_v2(candidate)
        request = _owned_publication_request_v2(
            request, joint=self._joint_configuration is not None
        )
        owned_context: AssetLaneContextV2 | PerpsMarginRequestV2
        owned_command: AssetLaneCommandV2 | PerpsMarginCommandV1
        if type(request) is PerpsMarginRequestV2:
            margin_request: PerpsMarginRequestV2 = request
            owned_context = margin_request
            owned_command = margin_request.command
            requested_pre_root = margin_request.occurrence.pre_state_root
        elif type(request) is CustodyPublicationRequestV2:
            owned_context = request.context
            owned_command = request.command
            requested_pre_root = request.context.global_pre_state_root
        else:
            raise TypeError("publication request must have its exact route-owned type")
        if type(receipt_bytes) is not bytes:
            raise TypeError("custody publication receipt must be exact bytes")
        if len(receipt_bytes) > MAX_RECEIPT_BYTES_V1:
            raise ValueError("custody publication receipt exceeds the byte bound")
        config = self._configuration
        if canonical_global_bytes_v2(owned.profile) != canonical_global_bytes_v2(config.profile):
            raise ValueError("custody request profile differs from selected configuration")
        request_parts = (
            canonical_global_bytes_v2(owned_context),
            canonical_global_bytes_v2(owned_command),
            message,
            owned.envelope.signature_bytes,
            receipt_bytes,
        )
        identify = joint_margin_request_id_v2 if self._joint_configuration is not None else custody_request_id_v2
        request_id = identify(*request_parts)
        head, records = self._read()
        expected = (
            head.publication_id,
            head.sequence,
            head.authority.authority_root,
            head.authority.generation,
        )
        for prior in records:
            if prior.request_id == request_id:
                if prior.request_parts != request_parts:
                    raise ValueError("custody retry bytes differ from committed request")
                return CustodyPublicationOutcomeV2(
                    CustodyPublicationStatusV2.ALREADY_COMMITTED, head, prior.publication_id
                )
        if head.authority != self._expected_authority:
            return CustodyPublicationOutcomeV2(CustodyPublicationStatusV2.AUTHORITY_STALE, head)
        if requested_pre_root != head.global_state.state_root:
            return CustodyPublicationOutcomeV2(CustodyPublicationStatusV2.STALE_HEAD, head)
        frame, statement = self._verify_request_v2(owned, request, head, receipt_bytes)
        if type(statement) is AssetLaneRejectedV2:
            return statement
        if type(statement) is PerpsMarginGlobalRejectedV2:
            return statement
        if type(frame) is not bytes:
            raise ValueError("custody accepted statement lacks its frame")
        record = CustodyPublicationRecordV2(
            head.sequence + 1,
            head.publication_id,
            head.authority.authority_root,
            frame,
            cast(bytes, statement),
            message,
            owned.envelope.signature_bytes,
            receipt_bytes,
        )

        # Keep the only economic write closure local to this verified occurrence.
        # It cannot accept a caller-created record or escape as a reusable capability.
        def commit_verified() -> CustodyPublicationOutcomeV2:
            with self._lock:
                self._require_identity()
                connection = self._connection
                connection.execute("BEGIN IMMEDIATE")
                commit_attempted = False
                try:
                    head, records = self._validate()
                    for prior in records:
                        if prior.request_id == record.request_id:
                            if prior != record:
                                raise ValueError("custody retry bytes differ from committed bundle")
                            return CustodyPublicationOutcomeV2(
                                CustodyPublicationStatusV2.ALREADY_COMMITTED,
                                head,
                                prior.publication_id,
                            )
                    if head.authority != self._expected_authority or expected[2:] != (
                        head.authority.authority_root,
                        head.authority.generation,
                    ):
                        return CustodyPublicationOutcomeV2(
                            CustodyPublicationStatusV2.AUTHORITY_STALE, head
                        )
                    if expected[:2] != (head.publication_id, head.sequence) or (
                        record.source_publication_id,
                        record.sequence,
                    ) != (head.publication_id, head.sequence + 1):
                        return CustodyPublicationOutcomeV2(
                            CustodyPublicationStatusV2.STALE_HEAD, head
                        )
                    replay = record.replay()
                    if (
                        record.authority_root != head.authority.authority_root
                        or record.is_joint_margin != (self._joint_configuration is not None)
                        or not _complete_predecessor_matches_v2(replay, head)
                    ):
                        raise ValueError(
                            "custody record source or authority differs from acquired snapshot"
                        )
                    if (
                        len(records) >= MAX_CUSTODY_PUBLICATIONS_V2
                        or sum(row.byte_count for row in records) + record.byte_count
                        > MAX_CUSTODY_HISTORY_BYTES_V2
                    ):
                        return CustodyPublicationOutcomeV2(
                            CustodyPublicationStatusV2.CAPACITY_EXCEEDED, head
                        )
                    self._require_identity()
                    connection.execute(
                        "INSERT INTO publications VALUES (?,?,?,?,?,?,?,?,?,?)",
                        (
                            record.sequence,
                            record.publication_id,
                            record.request_id,
                            record.source_publication_id,
                            record.authority_root,
                            record.frame,
                            record.statement,
                            record.authentication_message,
                            record.signature,
                            record.receipt,
                        ),
                    )
                    cursor = connection.execute(
                        "UPDATE heads SET publication_id=?, sequence=? WHERE singleton=1 AND publication_id=? AND sequence=? AND authority_generation=?",
                        (
                            record.publication_id,
                            record.sequence,
                            head.publication_id,
                            head.sequence,
                            head.authority.generation,
                        ),
                    )
                    if cursor.rowcount != 1:
                        raise RuntimeError("custody head CAS failed within transaction")
                    self._require_identity()
                    commit_attempted = True
                    connection.execute("COMMIT")
                    self._require_identity()
                    post = CustodyPublicationSnapshotV2(
                        record.publication_id,
                        record.sequence,
                        head.authority,
                        replay.global_post,
                        replay.lane_post,
                        replay.margin_post,
                    )
                    return CustodyPublicationOutcomeV2(
                        CustodyPublicationStatusV2.COMMITTED, post, record.publication_id
                    )
                except (OSError, sqlite3.Error, RuntimeError, ValueError) as exc:
                    if commit_attempted:
                        raise CustodyPublicationIndeterminateV2(
                            "custody commit acknowledgment is indeterminate"
                        ) from exc
                    raise
                finally:
                    _rollback_or_indeterminate_v2(connection)

        return commit_verified()

    def _verify_request_v2(
        self, candidate: EconomicCommandAuthenticationCandidateV2,
        request: CustodyPublicationRequestV2 | PerpsMarginRequestV2,
        head: CustodyPublicationSnapshotV2, receipt: bytes,
    ) -> tuple[bytes | AssetLaneRejectedV2, bytes | AssetLaneRejectedV2 | PerpsMarginGlobalRejectedV2]:
        """Select one fixed verifier path; all economic writes stay in publish()."""
        config = self._configuration
        if type(request) is PerpsMarginRequestV2:
            joint = self._joint_configuration
            if joint is None or head.margin_state is None:
                raise ValueError("margin publication requires complete store-owned margin state")
            frame = encode_perps_margin_frame_v2(
                head.custody_state, head.margin_state, head.global_state, request
            )
            statement = verify_isolated_profiled_perps_margin_receipt_v2(
                candidate, head.custody_state, head.margin_state, head.global_state, request,
                guest_role_binding=joint.margin_role,
                expected_guest_role_binding_root=joint.margin_role.binding_root,
                receipt_executable_path=joint.margin_receipt_executable_path,
                receipt_timeout_ms=config.receipt_timeout_ms,
                signature_artifact_path=config.signature_artifact_path,
                signature_evidence_manifest=config.signature_manifest,
                signature_timeout_ms=config.signature_timeout_ms,
                receipt_bytes=receipt,
            )
            return frame_joint_margin_publication_v2(frame, None), statement
        if type(request) is not CustodyPublicationRequestV2:
            raise TypeError("publication request must have its exact route-owned type")
        asset_context = request.context
        asset_command = request.command
        custody_frame = prepare_asset_lane_custody_global_prover_input_v2(
            asset_context, head.custody_state, asset_command, head.global_state,
        )
        post = head.global_state
        if type(custody_frame) is bytes:
            post = replay_custody_publication_frame_v2(custody_frame).global_post
        custody_statement = verify_isolated_profiled_asset_lane_custody_receipt_v2(
            candidate, asset_context, head.custody_state, asset_command, head.global_state, post,
            guest_role_binding=config.guest_role_binding,
            expected_guest_role_binding_root=config.guest_role_binding.binding_root,
            receipt_executable_path=config.receipt_executable_path,
            receipt_timeout_ms=config.receipt_timeout_ms,
            signature_artifact_path=config.signature_artifact_path,
            signature_evidence_manifest=config.signature_manifest,
            signature_timeout_ms=config.signature_timeout_ms,
            receipt_bytes=receipt,
        )
        if type(custody_frame) is bytes and head.margin_state is not None:
            custody_frame = frame_joint_margin_publication_v2(custody_frame, head.margin_state)
        return custody_frame, custody_statement

    def revoke(self) -> GlobalEconomicAuthorityHeadV2:
        """Terminal local operator revocation; this is no governance authority."""
        with self._lock:
            self._require_identity()
            self._connection.execute("BEGIN IMMEDIATE")
            commit_attempted = False
            try:
                head, _ = self._validate()
                if head.authority.status is GlobalEconomicAuthorityStatusV2.REVOKED:
                    return head.authority
                successor = head.authority.revoked_successor()
                self._connection.execute(
                    "INSERT INTO authority_history VALUES (?,?)",
                    (successor.generation, successor.canonical_bytes),
                )
                self._connection.execute(
                    "UPDATE heads SET authority_generation=? WHERE singleton=1",
                    (successor.generation,),
                )
                self._require_identity()
                commit_attempted = True
                self._connection.execute("COMMIT")
                self._require_identity()
                return successor
            except (OSError, sqlite3.Error, RuntimeError, ValueError) as exc:
                if commit_attempted:
                    raise CustodyPublicationIndeterminateV2(
                        "custody authority acknowledgment is indeterminate"
                    ) from exc
                raise
            finally:
                _rollback_or_indeterminate_v2(self._connection)


def _rollback_or_indeterminate_v2(connection: sqlite3.Connection) -> None:
    try:
        if connection.in_transaction:
            connection.execute("ROLLBACK")
    except sqlite3.Error as exc:
        raise CustodyPublicationIndeterminateV2(
            "custody transaction rollback is unresolved"
        ) from exc


def _initialize_genesis_v2(publisher: IsolatedCustodyPublisherV2) -> None:
    connection = publisher._connection
    connection.execute("BEGIN IMMEDIATE")
    try:
        for sql in _TABLES.values():
            connection.execute(sql)
        authority = publisher._expected_authority.canonical_bytes
        connection.execute(
            "INSERT INTO genesis VALUES (1, ?, ?, ?)",
            (
                publisher._global_raw,
                publisher._lane_raw,
                authority,
            ),
        )
        connection.execute("INSERT INTO authority_history VALUES (0, ?)", (authority,))
        connection.execute("INSERT INTO heads VALUES (1, ?, 0, 0)", (publisher._genesis_id,))
        publisher._require_identity()
        connection.execute("COMMIT")
    finally:
        if connection.in_transaction:
            connection.execute("ROLLBACK")


def _same_bootstrap_inode_v2(
    publisher: IsolatedCustodyPublisherV2, candidate: Path, links: int
) -> None:
    descriptor = os.fstat(publisher._identity_fd)
    expected = (descriptor.st_dev, descriptor.st_ino)
    for path in (candidate, publisher._path):
        metadata = _private_inode(path, links)
        if (metadata.st_dev, metadata.st_ino) != expected:
            raise PermissionError("custody bootstrap inode changed")


def _install_genesis_v2(publisher: IsolatedCustodyPublisherV2) -> None:
    """Install only a validated genesis; resume our candidate or exact link pair.

    A failed candidate remains available for validation on retry. Foreign or
    mismatched files are never removed, and the final name is never replaced.
    """
    path = publisher._path
    candidate = path.with_name("." + path.name + ".custody-bootstrap-v2")
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        fcntl.flock(directory, fcntl.LOCK_EX | fcntl.LOCK_NB)
        linked = os.path.lexists(path)
        if linked:
            if not os.path.lexists(candidate):
                raise FileExistsError(
                    "custody store already exists; use open with its configuration"
                )
            left, right = _private_inode(path, 2), _private_inode(candidate, 2)
            if (left.st_dev, left.st_ino) != (right.st_dev, right.st_ino):
                raise PermissionError("custody bootstrap names do not share one inode")
        elif not os.path.lexists(candidate):
            descriptor = os.open(
                candidate, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600
            )
            os.close(descriptor)
        publisher._connect(candidate, 2 if linked else 1)
        # SQLite rolls an interrupted initialization back to the empty schema.
        schema = publisher._connection.execute("SELECT name FROM sqlite_master").fetchall()
        if not schema:
            if linked:
                raise ValueError("an empty custody candidate was linked before validation")
            _initialize_genesis_v2(publisher)
        head = publisher.snapshot()
        if head.sequence != 0 or head.authority != publisher._expected_authority:
            raise ValueError("custody bootstrap candidate is not the selected genesis")
        if not linked:
            publisher._require_identity()
            os.link(candidate, path, follow_symlinks=False)
        _same_bootstrap_inode_v2(publisher, candidate, 2)
        os.fsync(directory)
        _same_bootstrap_inode_v2(publisher, candidate, 2)
        candidate.unlink()
        os.fsync(directory)
        publisher._storage_path = path
        publisher._expected_links = 1
        publisher._require_identity()
    finally:
        os.close(directory)
