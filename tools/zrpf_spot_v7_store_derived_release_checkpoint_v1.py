"""Derive one authority-neutral checkpoint directly from replayed Store V3 state."""

from __future__ import annotations

import hashlib
from typing import Final, NoReturn, SupportsIndex, final

from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools.zrpf_spot_v7_release_state_checkpoint_v1 import (
    ZERO_DIGEST_HEX_V1,
    SpotV7ReleaseStateCheckpointRejectV1,
    SpotV7ReleaseStateCheckpointV1,
    build_spot_v7_release_state_checkpoint_v1,
    parse_exact_spot_v7_release_state_checkpoint_v1,
    validate_spot_v7_release_state_checkpoint_successor_v1,
)


class StoreDerivedReleaseCheckpointRejectV1(ValueError):
    """Stable rejection at the Store V3 to checkpoint provenance boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


class _StoreDerivedCheckpointSealV1:
    __slots__ = ()


_STORE_DERIVED_CHECKPOINT_SEAL_V1: Final = _StoreDerivedCheckpointSealV1()


@final
class _StoreDerivedReleaseStateCheckpointV1:
    """Opaque local-replay provenance for one exact checkpoint document."""

    __slots__ = ("_canonical_bytes", "_canonical_sha256", "_checkpoint_hash")
    _canonical_bytes: bytes
    _canonical_sha256: bytes
    _checkpoint_hash: str

    def __new__(cls) -> _StoreDerivedReleaseStateCheckpointV1:
        raise TypeError("Store-derived checkpoint requires direct Store V3 replay")

    @classmethod
    def _from_store_replay(
        cls,
        *,
        canonical_bytes: bytes,
        seal: _StoreDerivedCheckpointSealV1,
    ) -> _StoreDerivedReleaseStateCheckpointV1:
        if seal is not _STORE_DERIVED_CHECKPOINT_SEAL_V1:
            raise TypeError("Store-derived checkpoint requires direct Store V3 replay")
        document = parse_exact_spot_v7_release_state_checkpoint_v1(canonical_bytes)
        value = object.__new__(cls)
        object.__setattr__(value, "_canonical_bytes", canonical_bytes)
        object.__setattr__(value, "_canonical_sha256", hashlib.sha256(canonical_bytes).digest())
        object.__setattr__(value, "_checkpoint_hash", document.release_checkpoint_hash)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("Store-derived checkpoint cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Store-derived checkpoint is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("Store-derived checkpoint is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("Store-derived checkpoint cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Store-derived checkpoint cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Store-derived checkpoint cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Store-derived checkpoint cannot be serialized")

    def __getstate__(self) -> NoReturn:
        raise TypeError("Store-derived checkpoint cannot be serialized")

    def _verified_document_for_finality_v1(self) -> SpotV7ReleaseStateCheckpointV1:
        raw = self._canonical_bytes
        if type(raw) is not bytes:
            raise _reject("DERIVED_CANONICAL_INTEGRITY", "checkpoint bytes changed type")
        if hashlib.sha256(raw).digest() != self._canonical_sha256:
            raise _reject("DERIVED_CANONICAL_INTEGRITY", "checkpoint bytes changed")
        try:
            document = parse_exact_spot_v7_release_state_checkpoint_v1(raw)
        except SpotV7ReleaseStateCheckpointRejectV1 as exc:
            raise _reject("DERIVED_CANONICAL_INTEGRITY", str(exc)) from exc
        if document.release_checkpoint_hash != self._checkpoint_hash:
            raise _reject("DERIVED_CANONICAL_INTEGRITY", "checkpoint hash changed")
        return document

    @property
    def canonical_bytes(self) -> bytes:
        return self._verified_document_for_finality_v1().canonical_bytes

    @property
    def checkpoint_hash(self) -> str:
        return self._verified_document_for_finality_v1().release_checkpoint_hash

    @property
    def parent_checkpoint_hash(self) -> str:
        return self._verified_document_for_finality_v1().parent_release_checkpoint_hash

    @property
    def store_replay_currentness_at_use_verified(self) -> bool:
        return False

    @property
    def external_monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def external_finality_authenticated(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def derive_store_release_state_checkpoint_v1(
    store: store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
) -> _StoreDerivedReleaseStateCheckpointV1:
    """Replay an exact Store V3 and reconstruct its complete checkpoint head."""

    if (
        not isinstance(store, store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3)
        or type(store) is not store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3
    ):
        raise TypeError("checkpoint derivation requires the exact Store V3 type")
    identity = store.identity
    if type(identity) is not store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3:
        raise _reject("DERIVED_IDENTITY_TYPE", "Store V3 returned an unexpected identity type")
    cursors = store._release_state_cursor_history_for_checkpoint_v1()
    if type(cursors) is not tuple or not cursors:
        raise _reject("DERIVED_CURSOR_HISTORY_TYPE", "Store V3 returned no cursor history")

    parent_document: SpotV7ReleaseStateCheckpointV1 | None = None
    raw = b""
    for revision, cursor in enumerate(cursors):
        if type(cursor) is not store_v3.SpotV7AuthenticatedReleaseStateCursorV3:
            raise _reject(
                "DERIVED_CURSOR_TYPE",
                "Store V3 returned an unexpected cursor type",
            )
        if cursor.database_revision != revision:
            raise _reject(
                "DERIVED_CURSOR_SEQUENCE",
                "Store V3 cursor history is not contiguous",
            )
        parent_hash = (
            ZERO_DIGEST_HEX_V1
            if parent_document is None
            else parent_document.release_checkpoint_hash
        )
        raw = _build_checkpoint_bytes(identity, cursor, parent_hash=parent_hash)
        document = parse_exact_spot_v7_release_state_checkpoint_v1(raw)
        if parent_document is not None:
            try:
                validate_spot_v7_release_state_checkpoint_successor_v1(
                    parent_document,
                    document,
                )
            except SpotV7ReleaseStateCheckpointRejectV1 as exc:
                raise _reject("DERIVED_SUCCESSOR_INVALID", str(exc)) from exc
        parent_document = document

    if parent_document is None or not raw:
        raise _reject("DERIVED_CURSOR_HISTORY_EMPTY", "Store V3 cursor history is empty")
    return _StoreDerivedReleaseStateCheckpointV1._from_store_replay(
        canonical_bytes=raw,
        seal=_STORE_DERIVED_CHECKPOINT_SEAL_V1,
    )


def _build_checkpoint_bytes(
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    cursor: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
    *,
    parent_hash: str,
) -> bytes:
    return build_spot_v7_release_state_checkpoint_v1(
        application_id=identity.application_id,
        chain_id=identity.chain_id,
        domain_id=identity.domain_id,
        release_profile=identity.release_profile,
        store_identity_hash=identity.identity_sha256.hex(),
        database_revision=cursor.database_revision,
        last_evaluation_epoch=(
            0 if cursor.last_evaluation_epoch is None else cursor.last_evaluation_epoch
        ),
        release_state_root=cursor.state_root.hex(),
        current_candidate_id=_optional_digest_text(cursor.current_candidate_id),
        current_candidate_sha256=_optional_digest_text(cursor.current_candidate_sha256),
        current_release_revision=cursor.current_release_revision,
        current_select_input_id=_optional_digest_text(cursor.current_select_input_id),
        current_revocation_record_id=_optional_digest_text(cursor.current_revocation_record_id),
        parent_release_checkpoint_hash=parent_hash,
        release_checkpoint_sequence=cursor.database_revision,
    )


def _optional_digest_text(value: bytes | None) -> str | None:
    return None if value is None else value.hex()


def _reject(code: str, detail: str) -> StoreDerivedReleaseCheckpointRejectV1:
    return StoreDerivedReleaseCheckpointRejectV1(code, detail)


__all__ = [
    "StoreDerivedReleaseCheckpointRejectV1",
    "derive_store_release_state_checkpoint_v1",
]
