"""Characterization corpus for ``evaluate_perps_wallet_encrypted_sss_backup_v1``.

This locks the CURRENT behavior of the encrypted-SSS backup readiness
evaluator (full returned status dict, including the exact accumulated
``errors`` strings and their ORDER) before/after any refactor of the
evaluator body. The evaluator is error-ACCUMULATING: ~11 sequential
sections append human-readable strings to one shared ``errors`` list, and
several readiness flags are computed by prefix-scanning that list at fixed
sequence points. The corpus pins:

* the full ``_status(...)`` dict per case (every field, list orders,
  ``status_hash``),
* cross-section threading (``threshold``/``share_count`` from the sss
  section feed envelope/drill/replay checks; envelope indexes feed
  delivery/drill/replay),
* the prefix-scan flags (``recovery_drill_ready`` /
  ``hostile_share_tests_ready``) including their stay-``False``-on-exception
  behavior,
* the delivery section's local ``delivery_errors`` list semantics (a
  ``TypeError`` raised mid-loop DISCARDS earlier receipt errors —
  ``delivery_item_not_object_swallows_earlier_error`` locks this),
* the replay section's single try/except over BOTH replay calls (an
  exception in the recovery replay skips the hostile replay),
* the ``audit_status`` fallback chain (top-level str -> "unknown" ->
  overridden by ``audit_evidence.audit_status``).

Corpus regeneration (byte-identical when behavior is preserved)::

    PYTHONPATH=. python3 tests/integration/test_perps_wallet_encrypted_sss_backup_characterization.py --regen

All inputs are derived from fixed seeds and the module's own builders, so
the corpus is deterministic. Reachability notes (verified against this
base):

* No error emitted by a section BEFORE the recovery-drill section can start
  with ``"encrypted SSS recovery drill"``, and none emitted before the
  hostile-share section can start with ``"encrypted SSS hostile-share"``
  (the f-string families embed user content mid-string, never at the
  start), so the whole-list prefix scans are observationally section-local
  at this base. The corpus locks the scan points via the drill/hostile
  exception and error cases.
* Four defensive strings are unreachable with real AES-GCM/Shamir
  primitives and are NOT corpus-locked: "encrypted SSS hostile replay
  accepted tampered ciphertext", "... accepted wrong recipient key",
  "... accepted duplicate share" (each needs the crypto rejection to fail)
  and "... used too many insufficient shares" (the insufficient-share list
  is sliced to ``threshold - 1`` entries, so its length can never reach
  ``threshold`` for any positive threshold).
* At this base ``perps_wallet_encrypted_sss_audit_evidence`` is missing
  from ``SUPPORTED_PAYLOAD_KINDS_V0`` in ``zeno_ledger_signature``, so an
  ``external_audit_ready`` backup can never validate its signature
  envelope; ``audit_external_ready_unverifiable_signature_base_quirk``
  locks the resulting "signature invalid: payload_kind is not supported"
  error rather than hiding it.
"""

from __future__ import annotations

import base64
import copy
import hashlib
import json
import sys
from dataclasses import dataclass, replace
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Mapping

import pytest

from src.integration.perps_wallet_authority import (
    PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    build_perps_wallet_authority_profile_v1,
)
from src.integration.perps_wallet_encrypted_sss_backup import (
    SssBackupRecipient,
    _decrypt_share_envelope,
    build_perps_wallet_encrypted_sss_backup_v1,
    build_perps_wallet_encrypted_sss_live_delivery_receipt_v1,
    build_perps_wallet_encrypted_sss_recipient_keys_v1,
    evaluate_perps_wallet_encrypted_sss_backup_v1,
    perps_wallet_encrypted_sss_audit_evidence_hash_v1,
    perps_wallet_encrypted_sss_audit_subject_hash_v1,
    perps_wallet_encrypted_sss_backup_hash_v1,
    perps_wallet_encrypted_sss_delivery_hash_v1,
    perps_wallet_encrypted_sss_envelope_hash_v1,
    perps_wallet_encrypted_sss_hostile_suite_hash_v1,
    perps_wallet_encrypted_sss_recovery_drill_hash_v1,
    recipient_root_keys_from_fixture_v1,
    recover_secret_shamir_gf256,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.integration.zeno_key_manager import (
    KeyRef,
    RecoveryGuardian,
    SocialRecoveryPolicy,
    ZenoKeyManager,
)
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0

try:  # same guarded import as tools/zenoctl_testnet_local/fixtures.py
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except Exception:  # pragma: no cover - exercised only when py_ecc is absent
    _BLS12_381_CURVE_ORDER = None


CORPUS_SCHEMA = "zenodex/tests/perps-wallet-encrypted-sss-backup-characterization/v1"
CORPUS_TARGET = (
    "src.integration.perps_wallet_encrypted_sss_backup."
    "evaluate_perps_wallet_encrypted_sss_backup_v1"
)
CORPUS_PATH = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "perps_wallet_encrypted_sss_backup_characterization.json"
)

CHAIN_ID = "zeno-ledger-localtest-v0"
OTHER_CHAIN_ID = "zeno-ledger-othertest-v0"
_SEED = bytes.fromhex("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff")
_AUDIT_SCHEMA = "zenodex/perps-wallet-encrypted-sss-audit-evidence/v1"


# ---------------------------------------------------------------------------
# Deterministic base artifacts (same recipe as tools/zenoctl_testnet_local)
# ---------------------------------------------------------------------------


def _derive_role_privkey(seed: bytes, role: str) -> bytes:
    domain = f"zenodex.local_testnet.role.{role}.v1".encode("utf-8")
    raw = hashlib.blake2b(seed + b"|" + domain, digest_size=32).digest()
    if _BLS12_381_CURVE_ORDER is None:  # pragma: no cover - py_ecc present in CI
        return raw
    raw_int = int.from_bytes(raw, "big")
    sk_int = (raw_int % (int(_BLS12_381_CURVE_ORDER) - 1)) + 1
    return sk_int.to_bytes(32, "big")


def _root_key(label: str) -> bytes:
    return hashlib.blake2b(_SEED + b"|sss-recipient-root|" + label.encode("utf-8"), digest_size=32).digest()


def _dest_hash(label: str) -> str:
    return "0x" + hashlib.sha256(b"dest|" + label.encode("utf-8")).hexdigest()


@lru_cache(maxsize=1)
def _role_keys() -> dict[str, bytes]:
    return {role: _derive_role_privkey(_SEED, role) for role in ("alice", "bob", "guardian_1", "guardian_2")}


@lru_cache(maxsize=1)
def _base_profile() -> dict[str, Any]:
    keys = _role_keys()
    pubs = {role: "0x" + bls_pubkey_hex_from_privkey(privkey) for role, privkey in keys.items()}
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=pubs["alice"], recovery_policy_id="recovery-perps-wallet-a"),
            KeyRef(key_id="perps-wallet-b", public_key=pubs["bob"], recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-a",
                subject_key_id="perps-wallet-a",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=pubs["guardian_1"]),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=pubs["guardian_2"]),
                ),
            ),
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=pubs["guardian_1"]),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=pubs["guardian_2"]),
                ),
            ),
        ),
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id="perps-wallet-authority-v1",
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
        threshold=1,
        signers=(
            {
                "signer_id": "wallet-a",
                "key_id": "perps-wallet-a",
                "public_key": pubs["alice"],
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "wallet-b",
                "key_id": "perps-wallet-b",
                "public_key": pubs["bob"],
                "weight": 1,
                "status": "active",
            },
        ),
    )
    return build_perps_wallet_authority_profile_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=CHAIN_ID,
        stage="production",
        enabled=True,
        key_manager=key_manager,
        signer_registry=signer_registry,
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
            "replay_protection_required": True,
            "recovery_policy_required": True,
        },
        proof_profile={
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": True,
            "zk_or_proof_required": True,
            "runtime_proof_profile": "perps-stream8-risc0-or-equivalent-v1",
        },
        transaction_scope={
            "stream_key": "8",
            "allowed_actions": [
                "init_market_2p",
                "deposit_collateral",
                "withdraw_collateral",
                "set_position_pair",
                "advance_epoch",
                "publish_clearing_price",
                "settle_epoch",
                "partial_liquidate",
            ],
        },
    )


def _base_recipients() -> tuple[SssBackupRecipient, ...]:
    return (
        SssBackupRecipient(
            recipient_id="recipient-email-1",
            provider_kind="recovery_email",
            provider_id="local-imap-fixture",
            transport_kind="smtp",
            destination_hash=_dest_hash("email-1"),
            recipient_root_key=_root_key("email-1"),
        ),
        SssBackupRecipient(
            recipient_id="recipient-drive-1",
            provider_kind="cloud_drive",
            provider_id="local-drive-fixture",
            transport_kind="https",
            destination_hash=_dest_hash("drive-1"),
            recipient_root_key=_root_key("drive-1"),
        ),
        SssBackupRecipient(
            recipient_id="recipient-offline-1",
            provider_kind="offline_export",
            provider_id="local-offline-fixture",
            transport_kind="file",
            destination_hash=_dest_hash("offline-1"),
            recipient_root_key=_root_key("offline-1"),
        ),
    )


def _build_backup_and_keys(
    *,
    recipients: tuple[SssBackupRecipient, ...],
    secret_material: bytes,
    seed_label: str,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    backup = build_perps_wallet_encrypted_sss_backup_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=CHAIN_ID,
        wallet_authority_hash=str(_base_profile()["wallet_authority_hash"]),
        subject_key_id="perps-wallet-a",
        secret_material=secret_material,
        recipients=recipients,
        threshold=3,
        coefficient_seed=hashlib.blake2b(_SEED + b"|coefficient-seed|" + seed_label.encode(), digest_size=32).digest(),
        encryption_salt=hashlib.blake2b(_SEED + b"|encryption-salt|" + seed_label.encode(), digest_size=32).digest(),
    )
    keys_fixture = build_perps_wallet_encrypted_sss_recipient_keys_v1(backup=backup, recipients=recipients)
    return backup, recipient_root_keys_from_fixture_v1(keys_fixture)


@lru_cache(maxsize=1)
def _base_backup_and_keys() -> tuple[dict[str, Any], dict[str, bytes]]:
    return _build_backup_and_keys(
        recipients=_base_recipients(),
        secret_material=_role_keys()["alice"],
        seed_label="base",
    )


@lru_cache(maxsize=1)
def _non_bls_secret_backup_and_keys() -> tuple[dict[str, Any], dict[str, bytes]]:
    """secret >= BLS12-381 curve order: decrypts/recovers fine, fails SkToPk."""
    return _build_backup_and_keys(
        recipients=_base_recipients(),
        secret_material=b"\xff" * 32,
        seed_label="non-bls-secret",
    )


@lru_cache(maxsize=3)
def _provider_variant_backup_and_keys(replaced_kind: str) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Rebuild with one provider kind replaced so a required kind is absent."""
    replacement = {
        "recovery_email": ("cloud_drive", "local-drive-fixture-b"),
        "cloud_drive": ("recovery_email", "local-imap-fixture-b"),
        "offline_export": ("cloud_drive", "local-drive-fixture-c"),
    }[replaced_kind]
    recipients = tuple(
        replace(recipient, provider_kind=replacement[0], provider_id=replacement[1])
        if recipient.provider_kind == replaced_kind
        else recipient
        for recipient in _base_recipients()
    )
    return _build_backup_and_keys(
        recipients=recipients,
        secret_material=_role_keys()["alice"],
        seed_label=f"providers-without-{replaced_kind}",
    )


_AUDITOR_PRIVKEY_HEX = "0x" + _derive_role_privkey(_SEED, "sss_auditor").hex()


@lru_cache(maxsize=1)
def _auditor_public_key() -> str:
    return bls_public_key_hex_from_private_key_v0(_AUDITOR_PRIVKEY_HEX)


# ---------------------------------------------------------------------------
# Case construction helpers
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CaseInputs:
    profile: Mapping[str, Any] | None
    backup: Mapping[str, Any] | None
    expected_chain_id: str | None
    recipient_root_keys: Mapping[str, bytes] | None


def _fresh(
    *,
    backup_source: Callable[[], tuple[dict[str, Any], dict[str, bytes]]] = _base_backup_and_keys,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, bytes]]:
    backup, root_keys = backup_source()
    return copy.deepcopy(dict(_base_profile())), copy.deepcopy(backup), dict(root_keys)


def _reseal_backup(backup: dict[str, Any]) -> None:
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)


def _reseal_envelope(backup: dict[str, Any], index: int) -> None:
    """Recompute envelope_hash + the matching delivery receipt's envelope binding."""
    envelope = backup["envelopes"][index]
    envelope["envelope_hash"] = perps_wallet_encrypted_sss_envelope_hash_v1(envelope)
    for delivery in backup["delivery_evidence"]:
        if delivery.get("envelope_id") == envelope.get("envelope_id"):
            delivery["envelope_hash"] = envelope["envelope_hash"]
            delivery["delivery_hash"] = perps_wallet_encrypted_sss_delivery_hash_v1(delivery)


def _reseal_delivery(backup: dict[str, Any], index: int) -> None:
    delivery = backup["delivery_evidence"][index]
    delivery["delivery_hash"] = perps_wallet_encrypted_sss_delivery_hash_v1(delivery)


def _reseal_drill(backup: dict[str, Any]) -> None:
    backup["recovery_drill"]["drill_hash"] = perps_wallet_encrypted_sss_recovery_drill_hash_v1(
        backup["recovery_drill"]
    )


def _reseal_suite(backup: dict[str, Any]) -> None:
    backup["hostile_share_tests"]["suite_hash"] = perps_wallet_encrypted_sss_hostile_suite_hash_v1(
        backup["hostile_share_tests"]
    )


def _valid_inputs(
    *,
    backup_source: Callable[[], tuple[dict[str, Any], dict[str, bytes]]] = _base_backup_and_keys,
) -> CaseInputs:
    profile, backup, root_keys = _fresh(backup_source=backup_source)
    return CaseInputs(profile=profile, backup=backup, expected_chain_id=CHAIN_ID, recipient_root_keys=root_keys)


def _mutated_backup(
    mutate: Callable[[dict[str, Any]], None],
    *,
    backup_source: Callable[[], tuple[dict[str, Any], dict[str, bytes]]] = _base_backup_and_keys,
    reseal: bool = True,
) -> CaseInputs:
    profile, backup, root_keys = _fresh(backup_source=backup_source)
    mutate(backup)
    if reseal:
        _reseal_backup(backup)
    return CaseInputs(profile=profile, backup=backup, expected_chain_id=CHAIN_ID, recipient_root_keys=root_keys)


def _with_root_keys(root_keys_for: Callable[[dict[str, bytes]], Mapping[str, bytes] | None]) -> CaseInputs:
    profile, backup, root_keys = _fresh()
    return CaseInputs(
        profile=profile,
        backup=backup,
        expected_chain_id=CHAIN_ID,
        recipient_root_keys=root_keys_for(root_keys),
    )


def _audit_backup(
    *,
    top_level_audit_status: Any = "external-audit-completed",
    drop_top_level_audit_status: bool = False,
    overrides: Mapping[str, Any] | None = None,
    drop: tuple[str, ...] = (),
    reseal_audit_hash: bool = True,
    signature_envelope: Any = "_default",
) -> CaseInputs:
    """Backup with a fully-populated audit_evidence block (external audit path)."""
    profile, backup, root_keys = _fresh()
    if drop_top_level_audit_status:
        backup.pop("audit_status", None)
    else:
        backup["audit_status"] = top_level_audit_status
    audit: dict[str, Any] = {
        "schema": _AUDIT_SCHEMA,
        "audit_id": "audit-localtest-1",
        "auditor_id": "auditor-zeno-1",
        "auditor_public_key": _auditor_public_key(),
        "wallet_authority_hash": backup["wallet_authority_hash"],
        "findings_status": "no-critical-open",
        "issued_at_epoch": 21,
        "audit_report_hash": "0x" + "ab" * 32,
        "external_audit_ready": True,
        "audit_status": "external-audit-completed",
        "audit_required_for_production": True,
    }
    backup["audit_evidence"] = audit
    audit["audit_subject_hash"] = perps_wallet_encrypted_sss_audit_subject_hash_v1(backup)
    audit.update(dict(overrides or {}))
    for key in drop:
        audit.pop(key, None)
    if reseal_audit_hash:
        audit["audit_hash"] = perps_wallet_encrypted_sss_audit_evidence_hash_v1(audit)
    if signature_envelope == "_default":
        audit["signature_envelope"] = {
            "signer_id": "auditor-1",
            "key_id": "auditor-key-1",
            "payload_kind": "perps_wallet_encrypted_sss_audit_evidence",
            "payload_hash": audit.get("audit_hash"),
            "algorithm": "bls12-381-g2-basic-v0",
            "public_key": _auditor_public_key(),
            "signature": "0x" + "00" * 96,
            "envelope_hash": "0x" + "cd" * 32,
        }
    else:
        audit["signature_envelope"] = signature_envelope
    _reseal_backup(backup)
    return CaseInputs(profile=profile, backup=backup, expected_chain_id=CHAIN_ID, recipient_root_keys=root_keys)


def _decrypted_share(backup: Mapping[str, Any], root_keys: Mapping[str, bytes], index: int) -> tuple[int, bytes]:
    envelope = backup["envelopes"][index]
    return (
        int(envelope["x"]),
        _decrypt_share_envelope(
            backup_id=str(backup["backup_id"]),
            wallet_authority_hash=str(backup["wallet_authority_hash"]),
            envelope=envelope,
            recipient_root_key=root_keys[str(envelope["recipient_id"])],
        ),
    )


# ---------------------------------------------------------------------------
# Case catalogue (ordered; ids are stable corpus keys)
# ---------------------------------------------------------------------------


def _case_factories() -> list[tuple[str, Callable[[], CaseInputs]]]:
    cases: list[tuple[str, Callable[[], CaseInputs]]] = []

    def add(case_id: str, factory: Callable[[], CaseInputs]) -> None:
        cases.append((case_id, factory))

    # ---- valid + call-shape variants ----
    add("valid_ready", _valid_inputs)
    add(
        "valid_no_expected_chain_id",
        lambda: replace(_valid_inputs(), expected_chain_id=None),
    )

    def _live_delivery() -> CaseInputs:
        profile, backup, root_keys = _fresh()
        modes = {"recipient-email-1": "smtp", "recipient-drive-1": "dropbox", "recipient-offline-1": "offline_export"}
        receipts = []
        for envelope in backup["envelopes"]:
            mode = modes[str(envelope["recipient_id"])]
            extra: dict[str, Any] = {}
            if mode == "smtp":
                extra["smtp_message_id"] = "<sss-share-1@localtest>"
            elif mode == "dropbox":
                extra["provider_file_id"] = "id:sss-share-fixture"
                extra["provider_revision"] = "rev-1"
            else:
                extra["offline_export_manifest_hash"] = "0x" + "ee" * 32
            receipts.append(
                build_perps_wallet_encrypted_sss_live_delivery_receipt_v1(
                    envelope,
                    delivery_mode=mode,
                    delivered_at_epoch=13,
                    receipt_reference=f"live-{mode}:{envelope['share_id']}",
                    provider_response_hash="0x" + "fa" * 32,
                    **extra,
                )
            )
        backup["delivery_evidence"] = receipts
        _reseal_backup(backup)
        return CaseInputs(profile=profile, backup=backup, expected_chain_id=CHAIN_ID, recipient_root_keys=root_keys)

    add("valid_live_delivery_receipts", _live_delivery)
    add(
        "backup_none",
        lambda: CaseInputs(
            profile=copy.deepcopy(dict(_base_profile())),
            backup=None,
            expected_chain_id=CHAIN_ID,
            recipient_root_keys=None,
        ),
    )
    add(
        "backup_none_profile_none",
        lambda: CaseInputs(profile=None, backup=None, expected_chain_id=None, recipient_root_keys=None),
    )
    add(
        "profile_none_with_valid_backup",
        lambda: replace(_valid_inputs(), profile=None),
    )
    add(
        "expected_chain_id_mismatch",
        lambda: replace(_valid_inputs(), expected_chain_id=OTHER_CHAIN_ID),
    )
    add("replay_keys_none", lambda: replace(_valid_inputs(), recipient_root_keys=None))
    add("replay_keys_empty", lambda: replace(_valid_inputs(), recipient_root_keys={}))

    def _profile_not_ready() -> CaseInputs:
        inputs = _valid_inputs()
        return replace(inputs, profile={**dict(inputs.profile or {}), "enabled": False})

    add("profile_not_ready_tampered_enabled", _profile_not_ready)

    def _profile_hash_field_tampered() -> CaseInputs:
        inputs = _valid_inputs()
        return replace(inputs, profile={**dict(inputs.profile or {}), "wallet_authority_hash": "0x" + "77" * 32})

    add("profile_wallet_authority_hash_field_tampered", _profile_hash_field_tampered)

    # ---- header + forbidden raw fields ----
    add("schema_mismatch", lambda: _mutated_backup(lambda b: b.update(schema="zenodex/other/v1")))
    add(
        "backup_hash_tampered",
        lambda: _mutated_backup(lambda b: b.update(backup_hash="0x" + "11" * 32), reseal=False),
    )

    def _chain_field_mutated(b: dict[str, Any]) -> None:
        b["chain_id"] = OTHER_CHAIN_ID

    add("chain_id_field_mutated", lambda: _mutated_backup(_chain_field_mutated))
    add(
        "forbidden_top_level_privkey_field",
        lambda: _mutated_backup(lambda b: b.update(privkey_hint="redacted")),
    )

    def _forbidden_nested(b: dict[str, Any]) -> None:
        b["recovery_drill"]["seed_phrase_backup"] = "none"
        _reseal_drill(b)

    add("forbidden_nested_drill_seed_phrase", lambda: _mutated_backup(_forbidden_nested))

    def _forbidden_envelope(b: dict[str, Any]) -> None:
        b["envelopes"][0]["mnemonic_hint"] = "none"
        _reseal_envelope(b, 0)

    add("forbidden_envelope_list_mnemonic", lambda: _mutated_backup(_forbidden_envelope))

    # ---- sss section ----
    add("sss_not_mapping", lambda: _mutated_backup(lambda b: b.update(sss=7)))
    add(
        "sss_algorithm_mismatch",
        lambda: _mutated_backup(lambda b: b["sss"].update(algorithm="shamir-gf65536-v9")),
    )
    add(
        "sss_threshold_not_int_ripples_to_replay",
        lambda: _mutated_backup(lambda b: b["sss"].update(threshold="3")),
    )
    add(
        "sss_threshold_below_two",
        lambda: _mutated_backup(lambda b: b["sss"].update(threshold=1)),
    )
    add(
        "sss_share_count_not_positive",
        lambda: _mutated_backup(lambda b: b["sss"].update(share_count=0)),
    )
    add(
        "sss_share_count_below_threshold",
        lambda: _mutated_backup(lambda b: b["sss"].update(share_count=2, x_coordinates=[1, 2])),
    )
    add(
        "sss_x_coordinates_wrong_length",
        lambda: _mutated_backup(lambda b: b["sss"].update(x_coordinates=[1, 2, 3, 4])),
    )
    add(
        "sss_x_coordinates_duplicate",
        lambda: _mutated_backup(lambda b: b["sss"].update(x_coordinates=[1, 2, 2])),
    )
    add(
        "sss_x_coordinates_not_list",
        lambda: _mutated_backup(lambda b: b["sss"].update(x_coordinates="123")),
    )
    add(
        "sss_x_coordinates_item_not_int",
        lambda: _mutated_backup(lambda b: b["sss"].update(x_coordinates=[1, "2", 3])),
    )

    # ---- envelopes section ----
    add("envelopes_not_list", lambda: _mutated_backup(lambda b: b.update(envelopes=None)))

    def _envelope_item_not_object(b: dict[str, Any]) -> None:
        b["envelopes"][1] = 5

    add("envelopes_item_not_object_aborts_loop", lambda: _mutated_backup(_envelope_item_not_object))

    def _drop_last_envelope(b: dict[str, Any]) -> None:
        b["envelopes"].pop()
        b["delivery_evidence"].pop()

    add("envelopes_dropped_one", lambda: _mutated_backup(_drop_last_envelope))

    def _duplicate_envelope(b: dict[str, Any]) -> None:
        b["envelopes"].append(copy.deepcopy(b["envelopes"][0]))
        b["delivery_evidence"].append(copy.deepcopy(b["delivery_evidence"][0]))

    add("envelopes_duplicated_one", lambda: _mutated_backup(_duplicate_envelope))

    def _envelope_field_removed(field: str) -> Callable[[], CaseInputs]:
        def factory() -> CaseInputs:
            def mutate(b: dict[str, Any]) -> None:
                b["envelopes"][0].pop(field, None)
                _reseal_envelope(b, 0)

            return _mutated_backup(mutate)

        return factory

    add("envelope_missing_backup_id", _envelope_field_removed("backup_id"))
    add("envelope_missing_recipient_id", _envelope_field_removed("recipient_id"))

    def _envelope_set(field: str, value: Any) -> Callable[[], CaseInputs]:
        def factory() -> CaseInputs:
            def mutate(b: dict[str, Any]) -> None:
                b["envelopes"][0][field] = value
                _reseal_envelope(b, 0)

            return _mutated_backup(mutate)

        return factory

    add("envelope_x_zero", _envelope_set("x", 0))
    add("envelope_x_not_int", _envelope_set("x", "1"))
    add("envelope_aad_hash_invalid_format", _envelope_set("aad_hash", "zz"))
    add("envelope_aad_hash_wrong", _envelope_set("aad_hash", "0x" + "33" * 32))
    add("envelope_share_sha256_invalid_format", _envelope_set("share_sha256", "zz"))
    add("envelope_share_sha256_wrong", _envelope_set("share_sha256", "0x" + "44" * 32))

    def _envelope_hash_tampered(b: dict[str, Any]) -> None:
        b["envelopes"][0]["envelope_hash"] = "0x" + "22" * 32

    add("envelope_hash_tampered", lambda: _mutated_backup(_envelope_hash_tampered))
    add("envelope_salt_wrong_length", _envelope_set("envelope_salt_b64", base64.b64encode(b"\x01" * 16).decode("ascii")))
    add("envelope_salt_bad_b64", _envelope_set("envelope_salt_b64", "!!notb64!!"))
    add("envelope_nonce_wrong_length", _envelope_set("nonce_b64", base64.b64encode(b"\x02" * 8).decode("ascii")))
    add("envelope_nonce_bad_b64", _envelope_set("nonce_b64", "!!notb64!!"))
    add("envelope_ciphertext_empty", _envelope_set("ciphertext_b64", ""))
    add("envelope_ciphertext_bad_b64", _envelope_set("ciphertext_b64", "!!notb64!!"))

    # ---- storage_policy section ----
    add("storage_policy_not_mapping", lambda: _mutated_backup(lambda b: b.update(storage_policy=None)))
    add(
        "storage_policy_min_kinds_not_int_skips_rest",
        lambda: _mutated_backup(lambda b: b["storage_policy"].update(min_provider_kinds="3")),
    )
    add(
        "storage_policy_min_kinds_above_available",
        lambda: _mutated_backup(lambda b: b["storage_policy"].update(min_provider_kinds=4)),
    )
    add(
        "providers_missing_recovery_email",
        lambda: _valid_inputs(backup_source=lambda: _provider_variant_backup_and_keys("recovery_email")),
    )
    add(
        "providers_missing_cloud_drive",
        lambda: _valid_inputs(backup_source=lambda: _provider_variant_backup_and_keys("cloud_drive")),
    )
    add(
        "providers_missing_offline_export",
        lambda: _valid_inputs(backup_source=lambda: _provider_variant_backup_and_keys("offline_export")),
    )

    # ---- delivery_evidence section ----
    add("delivery_not_list", lambda: _mutated_backup(lambda b: b.update(delivery_evidence=None)))

    def _delivery_swallow(b: dict[str, Any]) -> None:
        # Receipt 0 carries a REAL error (schema mismatch), receipt 1 raises a
        # TypeError mid-loop: the local delivery_errors list (holding receipt
        # 0's error) is DISCARDED and only the TypeError reaches `errors`.
        b["delivery_evidence"][0]["schema"] = "zenodex/wrong/v1"
        _reseal_delivery(b, 0)
        b["delivery_evidence"][1] = 3

    add("delivery_item_not_object_swallows_earlier_error", lambda: _mutated_backup(_delivery_swallow))

    def _delivery_extra_duplicate(b: dict[str, Any]) -> None:
        b["delivery_evidence"].append(copy.deepcopy(b["delivery_evidence"][0]))

    add("delivery_count_extra_duplicate", lambda: _mutated_backup(_delivery_extra_duplicate))

    def _delivery_set(field: str, value: Any) -> Callable[[], CaseInputs]:
        def factory() -> CaseInputs:
            def mutate(b: dict[str, Any]) -> None:
                b["delivery_evidence"][0][field] = value
                _reseal_delivery(b, 0)

            return _mutated_backup(mutate)

        return factory

    add("delivery_schema_mismatch", _delivery_set("schema", "zenodex/wrong/v1"))

    def _delivery_missing_receipt_reference() -> CaseInputs:
        def mutate(b: dict[str, Any]) -> None:
            b["delivery_evidence"][0].pop("receipt_reference", None)
            _reseal_delivery(b, 0)

        return _mutated_backup(mutate)

    add("delivery_missing_receipt_reference", _delivery_missing_receipt_reference)
    add("delivery_unsupported_mode", _delivery_set("delivery_mode", "pigeon"))
    add("delivery_not_delivered", _delivery_set("delivery_status", "pending"))
    add("delivery_bad_epoch", _delivery_set("delivered_at_epoch", -1))
    add("delivery_destination_hash_invalid", _delivery_set("destination_hash", "zz"))
    add("delivery_envelope_hash_invalid", _delivery_set("envelope_hash", "zz"))

    def _delivery_hash_tampered(b: dict[str, Any]) -> None:
        b["delivery_evidence"][0]["delivery_hash"] = "0x" + "55" * 32

    add("delivery_hash_tampered", lambda: _mutated_backup(_delivery_hash_tampered))
    add("delivery_unknown_envelope", _delivery_set("envelope_id", "no-such-envelope"))
    add("delivery_share_id_mismatch", _delivery_set("share_id", "share-02"))

    def _delivery_missing_coverage(b: dict[str, Any]) -> None:
        b["delivery_evidence"][0] = copy.deepcopy(b["delivery_evidence"][1])

    add("delivery_missing_coverage", lambda: _mutated_backup(_delivery_missing_coverage))
    add("delivery_live_smtp_missing_fields", _delivery_set("delivery_mode", "smtp"))
    add("delivery_live_dropbox_missing_fields", _delivery_set("delivery_mode", "dropbox"))
    add("delivery_live_offline_missing_manifest", _delivery_set("delivery_mode", "offline_export"))

    # ---- recovery_drill section ----
    add("drill_not_mapping", lambda: _mutated_backup(lambda b: b.update(recovery_drill=None)))

    def _drill_set(field: str, value: Any, *, reseal_drill: bool = True) -> Callable[[], CaseInputs]:
        def factory() -> CaseInputs:
            def mutate(b: dict[str, Any]) -> None:
                b["recovery_drill"][field] = value
                if reseal_drill:
                    _reseal_drill(b)

            return _mutated_backup(mutate)

        return factory

    add("drill_selected_not_list", _drill_set("selected_share_ids", None))
    add("drill_selected_item_empty", _drill_set("selected_share_ids", [""]))
    add("drill_selected_two_shares", _drill_set("selected_share_ids", ["share-01", "share-02"]))
    add(
        "drill_unknown_share_id",
        _drill_set("selected_share_ids", ["share-01", "share-02", "share-99"]),
    )
    add("drill_threshold_not_satisfied", _drill_set("threshold_satisfied", False))
    add("drill_key_not_reconstituted", _drill_set("reconstituted_key_matches", False))
    add("drill_no_rotation_required", _drill_set("new_key_rotation_required", False))
    add("drill_old_key_not_invalidated", _drill_set("old_key_invalidated_on_completion", False))
    add("drill_hash_tampered", _drill_set("drill_hash", "0x" + "66" * 32, reseal_drill=False))
    add("drill_fingerprint_invalid_format", _drill_set("reconstituted_key_fingerprint", "zz"))

    def _drill_fingerprint_crafted_partial() -> CaseInputs:
        # Forge the drill fingerprint to the value recovered from threshold-1
        # shares: the hostile replay must flag "recovered subject key from
        # insufficient shares" (and the recovery replay flags the mismatch).
        profile, backup, root_keys = _fresh()
        partial = recover_secret_shamir_gf256(
            [_decrypted_share(backup, root_keys, 0), _decrypted_share(backup, root_keys, 1)]
        )
        backup["recovery_drill"]["reconstituted_key_fingerprint"] = "0x" + hashlib.sha256(partial).hexdigest()
        _reseal_drill(backup)
        _reseal_backup(backup)
        return CaseInputs(profile=profile, backup=backup, expected_chain_id=CHAIN_ID, recipient_root_keys=root_keys)

    add("drill_fingerprint_crafted_partial_recovery", _drill_fingerprint_crafted_partial)

    # ---- replay key variants ----
    add(
        "replay_keys_wrong_email_key",
        lambda: _with_root_keys(lambda keys: {**keys, "recipient-email-1": b"\x42" * 32}),
    )
    add(
        "replay_keys_missing_drive",
        lambda: _with_root_keys(
            lambda keys: {key: value for key, value in keys.items() if key != "recipient-drive-1"}
        ),
    )
    add(
        "replay_keys_only_email",
        lambda: _with_root_keys(lambda keys: {"recipient-email-1": keys["recipient-email-1"]}),
    )
    add(
        "replay_keys_missing_email",
        lambda: _with_root_keys(
            lambda keys: {key: value for key, value in keys.items() if key != "recipient-email-1"}
        ),
    )
    add(
        "secret_not_bls_key",
        lambda: _valid_inputs(backup_source=_non_bls_secret_backup_and_keys),
    )

    # ---- hostile_share_tests section ----
    add("hostile_not_mapping", lambda: _mutated_backup(lambda b: b.update(hostile_share_tests=None)))

    def _hostile_all_false(b: dict[str, Any]) -> None:
        for key in (
            "insufficient_shares_rejected",
            "tampered_ciphertext_rejected",
            "wrong_recipient_key_rejected",
            "duplicate_share_rejected",
        ):
            b["hostile_share_tests"][key] = False
        _reseal_suite(b)

    add("hostile_all_flags_false", lambda: _mutated_backup(_hostile_all_false))

    def _hostile_suite_hash_tampered(b: dict[str, Any]) -> None:
        b["hostile_share_tests"]["suite_hash"] = "0x" + "88" * 32

    add("hostile_suite_hash_tampered", lambda: _mutated_backup(_hostile_suite_hash_tampered))

    # ---- raw_material_exposure section ----
    add("raw_material_not_mapping", lambda: _mutated_backup(lambda b: b.update(raw_material_exposure=None)))
    add(
        "raw_material_server_reconstitute_true",
        lambda: _mutated_backup(lambda b: b["raw_material_exposure"].update(server_can_reconstitute=True)),
    )

    # ---- audit_evidence section ----
    add("audit_evidence_not_mapping", lambda: _mutated_backup(lambda b: b.update(audit_evidence=None)))
    add(
        "audit_status_unsupported_in_evidence",
        lambda: _mutated_backup(lambda b: b["audit_evidence"].update(audit_status="weird-status")),
    )

    def _audit_status_fallback_unknown(b: dict[str, Any]) -> None:
        b["audit_status"] = 12
        b["audit_evidence"].pop("audit_status", None)

    add("audit_status_top_level_non_str_fallback_unknown", lambda: _mutated_backup(_audit_status_fallback_unknown))
    add(
        "audit_status_in_progress_ready",
        lambda: _mutated_backup(lambda b: b["audit_evidence"].update(audit_status="external-audit-in-progress")),
    )
    add(
        "audit_completed_but_not_ready",
        lambda: _mutated_backup(lambda b: b["audit_evidence"].update(audit_status="external-audit-completed")),
    )
    add("audit_external_ready_unverifiable_signature_base_quirk", lambda: _audit_backup())
    add(
        "audit_schema_mismatch",
        lambda: _audit_backup(overrides={"schema": "zenodex/wrong-audit/v1"}),
    )
    add("audit_missing_auditor_id", lambda: _audit_backup(drop=("auditor_id",)))
    add(
        "audit_subject_hash_invalid_format",
        lambda: _audit_backup(overrides={"audit_subject_hash": "0xzz"}),
    )
    add(
        "audit_subject_hash_wrong",
        lambda: _audit_backup(overrides={"audit_subject_hash": "0x" + "99" * 32}),
    )
    add("audit_issued_at_negative", lambda: _audit_backup(overrides={"issued_at_epoch": -5}))
    add("audit_findings_unsupported", lambda: _audit_backup(overrides={"findings_status": "open"}))
    add(
        "audit_wallet_authority_hash_mismatch",
        lambda: _audit_backup(overrides={"wallet_authority_hash": "0x" + "aa" * 32}),
    )
    add(
        "audit_hash_tampered",
        lambda: _audit_backup(overrides={"audit_hash": "0x" + "bb" * 32}, reseal_audit_hash=False),
    )
    add("audit_envelope_missing", lambda: _audit_backup(signature_envelope="not-an-object"))
    add(
        "audit_pubkey_invalid_format",
        lambda: _audit_backup(overrides={"auditor_public_key": "0x1234"}),
    )
    add(
        "audit_report_hash_none_when_ready",
        lambda: _audit_backup(overrides={"audit_report_hash": None}),
    )
    add(
        "audit_ready_status_not_completed",
        lambda: _audit_backup(
            top_level_audit_status="local-fixture-unaudited",
            overrides={"audit_status": "local-fixture-unaudited"},
        ),
    )

    # ---- production claim ----
    add(
        "production_claim_true",
        lambda: _mutated_backup(lambda b: b.update(production_security_claim=True)),
    )

    def _production_claim_missing(b: dict[str, Any]) -> None:
        b.pop("production_security_claim", None)

    add("production_claim_missing", lambda: _mutated_backup(_production_claim_missing))

    # ---- designed multi-fault accumulation cases ----
    def _multi_header_and_final(b: dict[str, Any]) -> None:
        b["schema"] = "zenodex/other/v1"
        b["production_security_claim"] = True

    add("multi_header_and_final", lambda: _mutated_backup(_multi_header_and_final))

    def _multi_storage_and_audit(b: dict[str, Any]) -> None:
        b["storage_policy"]["min_provider_kinds"] = 4
        b["audit_evidence"]["audit_status"] = "weird-status"

    add("multi_storage_and_audit", lambda: _mutated_backup(_multi_storage_and_audit))

    def _multi_envelope_and_drill(b: dict[str, Any]) -> None:
        b["envelopes"][0]["envelope_salt_b64"] = "!!notb64!!"
        _reseal_envelope(b, 0)
        b["recovery_drill"]["threshold_satisfied"] = False
        _reseal_drill(b)

    add("multi_envelope_and_drill", lambda: _mutated_backup(_multi_envelope_and_drill))

    def _multi_delivery_and_hostile(b: dict[str, Any]) -> None:
        b["delivery_evidence"][0]["schema"] = "zenodex/wrong/v1"
        _reseal_delivery(b, 0)
        b["hostile_share_tests"]["insufficient_shares_rejected"] = False
        _reseal_suite(b)

    add("multi_delivery_and_hostile", lambda: _mutated_backup(_multi_delivery_and_hostile))

    def _multi_profile_none_and_exposure() -> CaseInputs:
        inputs = _mutated_backup(lambda b: b["raw_material_exposure"].update(server_can_reconstitute=True))
        return replace(inputs, profile=None)

    add("multi_profile_none_and_exposure", _multi_profile_none_and_exposure)

    def _multi_forbidden_schema_hostile(b: dict[str, Any]) -> None:
        b["privkey_hint"] = "redacted"
        b["schema"] = "zenodex/other/v1"
        b["hostile_share_tests"]["tampered_ciphertext_rejected"] = False
        _reseal_suite(b)

    add("multi_forbidden_schema_hostile", lambda: _mutated_backup(_multi_forbidden_schema_hostile))

    def _multi_three_sections_order(b: dict[str, Any]) -> None:
        b["sss"]["algorithm"] = "shamir-gf65536-v9"
        b["storage_policy"]["min_provider_kinds"] = 4
        b["production_security_claim"] = True

    add("multi_three_sections_order", lambda: _mutated_backup(_multi_three_sections_order))

    # Adjacent-section ORDER locks (mutation testing showed a section-order
    # swap survives unless some case accumulates errors in BOTH neighbours).
    def _multi_header_unsealed_and_sss(b: dict[str, Any]) -> None:
        # No reseal: locks the in-orchestrator header order
        # schema -> chain_id -> wallet_authority_hash -> backup_hash, then the
        # sss section, then the envelope/replay ripples of the header fields.
        b["schema"] = "zenodex/other/v1"
        b["chain_id"] = OTHER_CHAIN_ID
        b["wallet_authority_hash"] = "0x" + "77" * 32
        b["sss"]["algorithm"] = "shamir-gf65536-v9"

    add(
        "multi_header_unsealed_and_sss",
        lambda: _mutated_backup(_multi_header_unsealed_and_sss, reseal=False),
    )

    def _multi_replay_and_hostile_order() -> CaseInputs:
        # Errors in BOTH the replay section and the hostile_share_tests
        # section: locks that replay errors land before hostile-suite errors.
        inputs = _mutated_backup(_hostile_all_false)
        return replace(inputs, recipient_root_keys=None)

    add("multi_replay_and_hostile_order", _multi_replay_and_hostile_order)

    def _multi_hostile_raw_audit_claim_order(b: dict[str, Any]) -> None:
        # Errors in four consecutive trailing sections: hostile suite ->
        # raw-material exposure -> audit status -> production claim.
        b["hostile_share_tests"]["suite_hash"] = "0x" + "88" * 32
        b["raw_material_exposure"]["server_can_reconstitute"] = True
        b["audit_evidence"]["audit_status"] = "weird-status"
        b["production_security_claim"] = True

    add(
        "multi_hostile_raw_audit_claim_order",
        lambda: _mutated_backup(_multi_hostile_raw_audit_claim_order),
    )

    return cases


# ---------------------------------------------------------------------------
# Corpus build / IO
# ---------------------------------------------------------------------------


def _input_sha256(inputs: CaseInputs) -> str:
    canonical = {
        "backup": None if inputs.backup is None else dict(inputs.backup),
        "expected_chain_id": inputs.expected_chain_id,
        "profile": None if inputs.profile is None else dict(inputs.profile),
        "recipient_root_keys": None
        if inputs.recipient_root_keys is None
        else {
            recipient_id: base64.b64encode(root_key).decode("ascii")
            for recipient_id, root_key in inputs.recipient_root_keys.items()
        },
    }
    payload = json.dumps(canonical, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _evaluate(inputs: CaseInputs) -> dict[str, Any]:
    return evaluate_perps_wallet_encrypted_sss_backup_v1(
        inputs.profile,
        inputs.backup,
        expected_chain_id=inputs.expected_chain_id,
        recipient_root_keys=inputs.recipient_root_keys,
    )


def build_corpus() -> dict[str, Any]:
    cases = []
    for case_id, factory in _case_factories():
        inputs = factory()
        cases.append(
            {
                "case_id": case_id,
                "input_sha256": _input_sha256(inputs),
                "expected": _evaluate(inputs),
            }
        )
    return {
        "schema": CORPUS_SCHEMA,
        "target": CORPUS_TARGET,
        "case_count": len(cases),
        "cases": cases,
    }


def corpus_bytes() -> bytes:
    return (json.dumps(build_corpus(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


@lru_cache(maxsize=1)
def _committed_corpus() -> dict[str, Any]:
    return json.loads(CORPUS_PATH.read_text(encoding="utf-8"))


def _committed_case_ids() -> list[str]:
    return [case["case_id"] for case in _committed_corpus()["cases"]]


# ---------------------------------------------------------------------------
# Targeted error strings (coverage guard)
# ---------------------------------------------------------------------------

# Exact fixed literals appended by the evaluator body and the validators it
# calls, plus the _require_* TypeError texts captured by the per-section
# try/except blocks.
TARGETED_EXACT_ERRORS: tuple[str, ...] = (
    "encrypted SSS backup artifact is missing",
    "wallet authority profile is not ready",
    "encrypted SSS backup schema mismatch",
    "encrypted SSS backup chain_id mismatch",
    "encrypted SSS backup wallet_authority_hash mismatch",
    "encrypted SSS backup hash mismatch",
    "encrypted SSS backup algorithm mismatch",
    "encrypted SSS backup threshold must be at least 2",
    "encrypted SSS backup share_count must be >= threshold",
    "encrypted SSS x_coordinates length must equal share_count",
    "encrypted SSS x_coordinates must be unique",
    "encrypted SSS envelope count must equal share_count",
    "encrypted SSS envelope ids must be unique",
    "encrypted SSS share ids must be unique",
    "encrypted SSS x coordinates must be unique per envelope",
    "encrypted SSS envelope x must be in 1..255",
    "encrypted SSS envelope aad_hash is invalid",
    "encrypted SSS envelope aad_hash mismatch",
    "encrypted SSS envelope share_sha256 is invalid",
    "encrypted SSS envelope hash mismatch",
    "encrypted SSS envelope salt must be 32 bytes",
    "encrypted SSS envelope nonce must be 12 bytes",
    "encrypted SSS envelope ciphertext must be non-empty",
    "encrypted SSS backup does not meet provider-kind diversity",
    "encrypted SSS backup is missing a recovery email provider",
    "encrypted SSS backup is missing a cloud-drive provider",
    "encrypted SSS backup is missing an offline export provider",
    "encrypted SSS backup is missing required provider kinds",
    "encrypted SSS delivery evidence count must equal envelope count",
    "encrypted SSS delivery evidence schema mismatch",
    "encrypted SSS delivery evidence has unsupported delivery_mode",
    "encrypted SSS delivery evidence is not delivered",
    "encrypted SSS delivery evidence delivered_at_epoch must be a non-negative int",
    "encrypted SSS delivery evidence destination_hash is invalid",
    "encrypted SSS delivery evidence envelope_hash is invalid",
    "encrypted SSS live delivery evidence provider_response_hash is invalid",
    "encrypted SSS smtp delivery evidence missing smtp_message_id",
    "encrypted SSS cloud delivery evidence missing provider_file_id",
    "encrypted SSS cloud delivery evidence missing provider_revision",
    "encrypted SSS offline export delivery evidence manifest hash is invalid",
    "encrypted SSS delivery evidence hash mismatch",
    "encrypted SSS delivery evidence references unknown envelope",
    "encrypted SSS delivery evidence must cover every envelope",
    "encrypted SSS delivery evidence is missing required provider kinds",
    "encrypted SSS recovery drill selected fewer than threshold shares",
    "encrypted SSS recovery drill references unknown share ids",
    "encrypted SSS recovery drill did not satisfy threshold",
    "encrypted SSS recovery drill did not reconstitute the key",
    "encrypted SSS recovery drill does not require new-key rotation",
    "encrypted SSS recovery drill does not invalidate the old key",
    "encrypted SSS recovery drill hash mismatch",
    "encrypted SSS trusted recipient replay keys are missing",
    "encrypted SSS replay selected fewer than threshold shares",
    "encrypted SSS replay recovered key fingerprint mismatch",
    "encrypted SSS replay recovered key does not match subject public key",
    "encrypted SSS hostile replay keys are missing",
    "encrypted SSS hostile replay selected fewer than threshold envelopes",
    "encrypted SSS hostile replay missing first recipient key",
    "encrypted SSS hostile replay needs a second recipient key",
    "encrypted SSS hostile replay missing recipient key for insufficient-share check",
    "encrypted SSS hostile replay recovered subject key from insufficient shares",
    "encrypted SSS hostile replay has no insufficient shares to test",
    "encrypted SSS hostile-share suite hash mismatch",
    "encrypted SSS backup exposes raw key/share material or server-side reconstitution",
    "encrypted SSS audit status is unsupported",
    "encrypted SSS audit evidence is ready but audit_report_hash is invalid",
    "encrypted SSS external audit readiness requires completed audit status",
    "encrypted SSS audit status cannot be completed when audit is not ready",
    "encrypted SSS external audit evidence schema mismatch",
    "encrypted SSS external audit evidence issued_at_epoch must be a non-negative int",
    "encrypted SSS external audit evidence findings_status is unsupported",
    "encrypted SSS external audit evidence wallet_authority_hash mismatch",
    "encrypted SSS external audit evidence subject hash mismatch",
    "encrypted SSS external audit evidence hash mismatch",
    "encrypted SSS external audit evidence signature envelope is missing",
    "encrypted SSS backup must not make a production security claim in local-testnet",
    # _require_* TypeError texts captured by the per-section try/except blocks
    "sss must be an object",
    "sss.threshold must be a positive int",
    "sss.share_count must be a positive int",
    "sss.x_coordinates must be a list",
    "sss.x_coordinates[1] must be an int",
    "envelopes must be a list",
    "envelopes[1] must be an object",
    "storage_policy must be an object",
    "storage_policy.min_provider_kinds must be a positive int",
    "delivery_evidence must be a list",
    "delivery_evidence[1] must be an object",
    "recovery_drill must be an object",
    "recovery_drill.selected_share_ids must be a list",
    "recovery_drill.selected_share_ids[0] must be a non-empty string",
    "hostile_share_tests must be an object",
    "raw_material_exposure must be an object",
    "audit_evidence must be an object",
)

# Parametrized f-string families: at least one corpus error must start with
# each prefix.
TARGETED_ERROR_PREFIXES: tuple[str, ...] = (
    "encrypted SSS backup contains forbidden raw-material field: ",
    "encrypted SSS envelope missing string field: ",
    "encrypted SSS delivery evidence missing string field: ",
    "encrypted SSS hostile-share test failed: ",
    "encrypted SSS replay references unknown share id: ",
    "encrypted SSS replay key missing for recipient: ",
    "encrypted SSS replay decrypt failed for ",
    "encrypted SSS replay recovered key is not a valid BLS key: ",
    "encrypted SSS replay failed: ",
    "encrypted SSS external audit evidence missing string field: ",
    "encrypted SSS external audit evidence signature invalid: ",
    "envelope_salt_b64 must be valid base64: ",
    "nonce_b64 must be valid base64: ",
    "ciphertext_b64 must be valid base64: ",
)

# Substring families for per-key f-strings whose key varies inside the text.
TARGETED_ERROR_SUBSTRINGS: tuple[str, ...] = (
    "encrypted SSS envelope chain_id mismatch",
    "encrypted SSS envelope backup_id mismatch",
    "encrypted SSS delivery evidence share_id mismatch",
    "encrypted SSS external audit evidence audit_subject_hash is invalid",
    "encrypted SSS external audit evidence audit_report_hash is invalid",
)


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_corpus_file_exists() -> None:
    assert CORPUS_PATH.is_file(), (
        f"missing characterization corpus {CORPUS_PATH}; regenerate with: "
        "PYTHONPATH=. python3 tests/integration/"
        "test_perps_wallet_encrypted_sss_backup_characterization.py --regen"
    )


def test_corpus_is_byte_identical_to_generator() -> None:
    committed = CORPUS_PATH.read_bytes()
    regenerated = corpus_bytes()
    assert committed == regenerated, (
        "characterization corpus drifted from evaluator behavior; inspect the "
        "diff before EVER regenerating (--regen) — a diff means the refactor "
        "changed observable behavior"
    )


@pytest.mark.parametrize("case_id", [case_id for case_id, _ in _case_factories()])
def test_case_reproduces_expected(case_id: str) -> None:
    committed = {case["case_id"]: case for case in _committed_corpus()["cases"]}
    assert case_id in committed, f"case {case_id} missing from committed corpus (run --regen?)"
    factory = dict(_case_factories())[case_id]
    inputs = factory()
    assert _input_sha256(inputs) == committed[case_id]["input_sha256"], (
        f"case {case_id}: regenerated INPUT drifted from corpus (builder/seed drift)"
    )
    result = _evaluate(inputs)
    assert result == committed[case_id]["expected"], (
        f"case {case_id}: evaluator output drifted from characterization corpus"
    )


def test_case_ids_unique_and_match_committed() -> None:
    generated_ids = [case_id for case_id, _ in _case_factories()]
    assert len(generated_ids) == len(set(generated_ids)), "duplicate case ids in catalogue"
    assert generated_ids == _committed_case_ids(), "case catalogue diverged from committed corpus"


def test_corpus_covers_all_targeted_error_strings() -> None:
    all_errors: list[str] = []
    for case in _committed_corpus()["cases"]:
        all_errors.extend(case["expected"]["errors"])
    error_set = set(all_errors)
    missing_exact = [target for target in TARGETED_EXACT_ERRORS if target not in error_set]
    missing_prefix = [
        prefix
        for prefix in TARGETED_ERROR_PREFIXES
        if not any(error.startswith(prefix) for error in error_set)
    ]
    missing_substring = [
        fragment
        for fragment in TARGETED_ERROR_SUBSTRINGS
        if not any(fragment in error for error in error_set)
    ]
    assert not missing_exact, f"corpus does not exercise exact errors: {missing_exact}"
    assert not missing_prefix, f"corpus does not exercise error families: {missing_prefix}"
    assert not missing_substring, f"corpus does not exercise error fragments: {missing_substring}"


def test_corpus_has_green_and_multi_fault_cases() -> None:
    cases = {case["case_id"]: case["expected"] for case in _committed_corpus()["cases"]}
    assert cases["valid_ready"]["encrypted_sss_backup_ready"] is True
    assert cases["valid_ready"]["errors"] == []
    assert cases["valid_live_delivery_receipts"]["live_provider_delivery_ready"] is True
    assert cases["audit_status_in_progress_ready"]["encrypted_sss_backup_ready"] is True
    multi_fault = [case_id for case_id, expected in cases.items() if len(expected["errors"]) >= 2]
    assert len(multi_fault) >= 6, f"need >= 6 multi-error accumulation cases, have {len(multi_fault)}"


def _main(argv: list[str]) -> int:
    if argv == ["--regen"]:
        CORPUS_PATH.parent.mkdir(parents=True, exist_ok=True)
        payload = corpus_bytes()
        CORPUS_PATH.write_bytes(payload)
        corpus = json.loads(payload)
        sys.stderr.write(
            f"wrote {CORPUS_PATH} ({corpus['case_count']} cases, {len(payload)} bytes)\n"
        )
        return 0
    sys.stderr.write(
        "usage: PYTHONPATH=. python3 tests/integration/"
        "test_perps_wallet_encrypted_sss_backup_characterization.py --regen\n"
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(_main(sys.argv[1:]))
