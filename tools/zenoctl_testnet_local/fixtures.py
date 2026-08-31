"""Deterministic key + profile fixture generator for local-testnet stacks.

Per-`out_dir` deterministic by default:

    seed = blake2b(abspath(out_dir).encode() + chain_id.encode(), digest_size=32)

so re-running `up` on the same out-dir reproduces the same identities (good
for test reruns and debugging) while different out-dirs produce different
identities (no accidental key reuse across stacks). `--seed <hex>` overrides;
`--random` derives a fresh seed from os.urandom each run.

These are LOCAL-TESTNET FIXTURE keys. They are NOT production keys, and
this module refuses to generate any seed that matches a known production
key registry (best-effort denylist).
"""

from __future__ import annotations

import hashlib
import json
import secrets
import time
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Mapping

from src.integration.autotrader_supervisor_profile import build_autotrader_supervisor_profile_v1
from src.integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from src.integration.perps_wallet_authority import (
    PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
    build_perps_wallet_authority_profile_v1,
    build_perps_wallet_device_approval_environment_policy_v1,
    build_perps_wallet_device_approval_exercise_v1,
    build_perps_wallet_device_approval_use_policy_v1,
    build_perps_wallet_signer_device_integration_v1,
    build_perps_wallet_signer_execution_exercise_v1,
    build_perps_wallet_signer_prompt_capture_v1,
    perps_wallet_recovery_exercise_hash_v1,
    perps_wallet_rotation_exercise_hash_v1,
)
from src.integration.perps_wallet_encrypted_sss_backup import (
    SssBackupRecipient,
    build_perps_wallet_encrypted_sss_backup_v1,
    build_perps_wallet_encrypted_sss_recipient_keys_v1,
)
from src.integration.zeno_key_manager import (
    KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
    KeyExecutionEnvironment,
    KeyRef,
    RecoveryGuardian,
    SocialRecoveryPolicy,
    ZenoKeyManager,
)
from src.integration.zeno_key_manager_v0 import (
    BACKEND_HARDWARE_WALLET_PLACEHOLDER,
    KeyBackendDescriptor,
)
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_oracle_authority import (
    ORACLE_AUTHORITY_PAYLOAD_KIND,
    build_oracle_authority_profile_v1,
)

try:
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except Exception:  # pragma: no cover - exercised only when py_ecc is absent
    _BLS12_381_CURVE_ORDER = None


# Roles that get a derived 32-byte private-key seed. Each role uses a
# distinct domain string so swapping the role list never silently rotates
# keys for other roles.
KEY_ROLES: tuple[str, ...] = (
    "operator",
    "oracle_authority",
    "perps_wallet_authority",
    "autotrader_supervisor",
    "guardian_1",
    "guardian_2",
    "guardian_3",
    "alice",
    "bob",
    "carol",
)

GUARDIAN_ROLES: tuple[str, ...] = ("guardian_1", "guardian_2", "guardian_3")

# Sanity denylist: refuse to write a fixture if any derived key matches a
# pinned production registry. Currently a placeholder — production key
# hashes (sha256 of the raw 32-byte seed) would be pinned here. Keep this
# list tiny and committed; rotation needs a deliberate code change.
PRODUCTION_KEY_DENYLIST_SHA256: frozenset[str] = frozenset()


class FixtureOutputPathMode(str, Enum):
    RESOLVED = "resolved"
    DESCRIPTOR_ANCHORED = "descriptor_anchored"


SCHEMA_KEY_BUNDLE = "zenodex.local_testnet.key_bundle.v0"
SCHEMA_ROLE_PUBKEY_BUNDLE = "zenodex.local_testnet.role_pubkeys.v0"
SCHEMA_GUARDIAN_QUORUM = "zenodex.local_testnet.guardian_quorum.v0"
SCHEMA_ORACLE_HOME = "zenodex.local_testnet.oracle_home_seed.v0"
LOCAL_FIXTURE_POLICY_HASH = "0x" + "11" * 32
LOCAL_FIXTURE_CHALLENGE_HASH = "0x" + "22" * 32
LOCAL_PERPS_AUTHORITY_ID = "perps-wallet-authority-v1"


@dataclass(frozen=True)
class FixtureBundle:
    """Paths to the per-fixture artifacts persisted on disk."""

    key_bundle: Path
    role_pubkeys: Path
    oracle_authority_profile: Path
    perps_wallet_authority_profile: Path
    autotrader_supervisor_profile: Path
    guardian_quorum: Path
    perps_wallet_recovery_exercise: Path
    perps_wallet_rotation_exercise: Path
    perps_wallet_device_approval_exercise: Path
    perps_wallet_signer_device_integration: Path
    perps_wallet_signer_prompt_capture: Path
    perps_wallet_signer_execution_exercise: Path
    perps_wallet_encrypted_sss_backup: Path
    perps_wallet_encrypted_sss_recipient_keys: Path

    def as_manifest_paths(self) -> dict[str, str]:
        return {
            "key_bundle": str(self.key_bundle),
            "role_pubkeys": str(self.role_pubkeys),
            "oracle_authority_profile": str(self.oracle_authority_profile),
            "perps_wallet_authority_profile": str(self.perps_wallet_authority_profile),
            "autotrader_supervisor_profile": str(self.autotrader_supervisor_profile),
            "guardian_quorum": str(self.guardian_quorum),
            "perps_wallet_recovery_exercise": str(self.perps_wallet_recovery_exercise),
            "perps_wallet_rotation_exercise": str(self.perps_wallet_rotation_exercise),
            "perps_wallet_device_approval_exercise": str(self.perps_wallet_device_approval_exercise),
            "perps_wallet_signer_device_integration": str(self.perps_wallet_signer_device_integration),
            "perps_wallet_signer_prompt_capture": str(self.perps_wallet_signer_prompt_capture),
            "perps_wallet_signer_execution_exercise": str(self.perps_wallet_signer_execution_exercise),
            "perps_wallet_encrypted_sss_backup": str(self.perps_wallet_encrypted_sss_backup),
            "perps_wallet_encrypted_sss_recipient_keys": str(self.perps_wallet_encrypted_sss_recipient_keys),
        }


def derive_seed(*, out_dir: Path | str, chain_id: str) -> bytes:
    """Per-out-dir deterministic 32-byte seed."""
    abs_path = str(Path(out_dir).resolve()).encode("utf-8")
    cid = chain_id.encode("utf-8")
    return hashlib.blake2b(abs_path + b"|" + cid, digest_size=32).digest()


def derive_role_privkey(seed: bytes, role: str) -> bytes:
    """Derive a stable 32-byte BLS12-381-safe private-key seed for `role`.

    Each role uses a domain string so role list changes don't silently
    rotate other roles' keys. The raw blake2b output (32 bytes) can fall
    above the BLS12-381 curve order; we map it into [1, curve_order) via
    `(raw % (order - 1)) + 1` so every derived key is a valid BLS private
    key. When py_ecc is unavailable, fall back to the raw bytes (the
    consumer will reject non-BLS keys downstream)."""
    if not isinstance(seed, (bytes, bytearray)) or len(seed) != 32:
        raise ValueError("seed must be exactly 32 bytes")
    if not isinstance(role, str) or not role:
        raise ValueError("role must be a non-empty string")
    domain = f"zenodex.local_testnet.role.{role}.v1".encode("utf-8")
    raw = hashlib.blake2b(seed + b"|" + domain, digest_size=32).digest()
    if _BLS12_381_CURVE_ORDER is None:
        return raw
    raw_int = int.from_bytes(raw, "big")
    sk_int = (raw_int % (int(_BLS12_381_CURVE_ORDER) - 1)) + 1
    return sk_int.to_bytes(32, "big")


def derive_writer_token(seed: bytes) -> str:
    """Derive a writer bearer token from the fixture seed. The token is
    held in memory + injected by nginx; never written to the manifest
    in cleartext (manifest stores only sha256)."""
    if not isinstance(seed, (bytes, bytearray)) or len(seed) != 32:
        raise ValueError("seed must be exactly 32 bytes")
    domain = b"zenodex.local_testnet.writer_token.v1"
    raw = hashlib.blake2b(seed + b"|" + domain, digest_size=32).digest()
    return raw.hex()


def _privkey_hex(privkey: bytes) -> str:
    return "0x" + bytes(privkey).hex()


def _pubkey_hex(privkey: bytes) -> str:
    return "0x" + bls_pubkey_hex_from_privkey(privkey)


def _key_sha256(privkey: bytes) -> str:
    return "sha256:" + hashlib.sha256(privkey).hexdigest()


def _ensure_no_production_collision(keys: Mapping[str, bytes]) -> None:
    """Best-effort guard. Refuses if any generated seed's sha256 matches
    the pinned production denylist."""
    if not PRODUCTION_KEY_DENYLIST_SHA256:
        return
    leaked = []
    for role, privkey in keys.items():
        digest = hashlib.sha256(privkey).hexdigest()
        if digest in PRODUCTION_KEY_DENYLIST_SHA256:
            leaked.append(role)
    if leaked:
        raise ValueError(
            f"refusing to write fixture: roles {leaked} collide with the production "
            "key denylist (PRODUCTION_KEY_DENYLIST_SHA256). Rotate the out-dir or "
            "use --random."
        )


def generate_fixture_bundle(
    *,
    out_dir: Path,
    chain_id: str,
    network_id: str,
    seed_override_hex: str | None = None,
    use_random: bool = False,
    created_at_ms: int | None = None,
    output_path_mode: FixtureOutputPathMode = FixtureOutputPathMode.RESOLVED,
) -> FixtureBundle:
    """Generate and persist the full fixture bundle for a local-testnet
    stack. Returns paths to the written artifacts.

    Determinism (priority order):
      1. `use_random=True` → seed = os.urandom(32)
      2. `seed_override_hex` set → seed = bytes.fromhex(seed_override_hex)
      3. Default → seed = derive_seed(out_dir, chain_id)
    """
    if use_random and seed_override_hex is not None:
        raise ValueError("--random and --seed are mutually exclusive")

    if use_random:
        seed = secrets.token_bytes(32)
    elif seed_override_hex is not None:
        try:
            seed = bytes.fromhex(seed_override_hex)
        except ValueError as exc:
            raise ValueError(f"--seed must be 64 hex chars: {exc}") from None
        if len(seed) != 32:
            raise ValueError(f"--seed must be 32 bytes, got {len(seed)}")
    else:
        seed = derive_seed(out_dir=out_dir, chain_id=chain_id)

    keys = {role: derive_role_privkey(seed, role) for role in KEY_ROLES}
    _ensure_no_production_collision(keys)

    if created_at_ms is None:
        created_at_ms = int(time.time() * 1000)

    output_root = Path(out_dir)
    if output_path_mode is FixtureOutputPathMode.DESCRIPTOR_ANCHORED:
        if (
            output_root.parts[:4] != ("/", "proc", "self", "fd")
            or len(output_root.parts) != 5
            or not output_root.name.isdigit()
        ):
            raise ValueError("descriptor-anchored fixture root must be /proc/self/fd/N")
    elif output_path_mode is FixtureOutputPathMode.RESOLVED:
        output_root = output_root.resolve()
    else:
        raise ValueError("unsupported fixture output path mode")
    fixtures_dir = output_root / "fixtures"
    fixtures_dir.mkdir(parents=True, exist_ok=True)

    role_pubkeys = {role: _pubkey_hex(privkey) for role, privkey in keys.items()}

    # 1) key bundle (records seed sha256, not the raw seed; records role
    # private keys in hex since these are local-only fixtures).
    key_bundle = {
        "schema": SCHEMA_KEY_BUNDLE,
        "chain_id": chain_id,
        "network_id": network_id,
        "seed_sha256": _key_sha256(seed),
        "created_at_ms": created_at_ms,
        "roles": {
            role: {
                "privkey_hex": _privkey_hex(privkey),
                "privkey_sha256": _key_sha256(privkey),
                "public_key": role_pubkeys[role],
            }
            for role, privkey in keys.items()
        },
        "non_claims": [
            "These are deterministic local-testnet fixture keys, not production keys.",
            "Do not reuse this bundle on a public network.",
            "The seed is derived from the absolute out_dir + chain_id; same dir = same keys.",
        ],
    }
    role_pubkey_bundle = {
        "schema": SCHEMA_ROLE_PUBKEY_BUNDLE,
        "chain_id": chain_id,
        "network_id": network_id,
        "created_at_ms": created_at_ms,
        "roles": {
            role: {
                "public_key": role_pubkeys[role],
            }
            for role in keys
        },
        "non_claims": [
            "Public local-testnet fixture role identities only.",
            "No private key material is present in this file.",
        ],
    }

    # 2) guardian quorum
    guardian_quorum = {
        "schema": SCHEMA_GUARDIAN_QUORUM,
        "chain_id": chain_id,
        "threshold": 2,
        "members": [
            {
                "role": role,
                "privkey_sha256": _key_sha256(keys[role]),
            }
            for role in GUARDIAN_ROLES
        ],
        "non_claims": [
            "Local-testnet quorum; not a production guardian set.",
        ],
    }

    oracle_authority = _oracle_authority_profile(
        chain_id=chain_id,
        oracle_pubkey=role_pubkeys["oracle_authority"],
        operator_pubkey=role_pubkeys["operator"],
        oracle_privkey=keys["oracle_authority"],
        operator_privkey=keys["operator"],
    )

    perps_authority_bundle = _perps_wallet_authority_fixture_bundle(
        chain_id=chain_id,
        account_a_pubkey=role_pubkeys["alice"],
        account_b_pubkey=role_pubkeys["bob"],
        account_c_pubkey=role_pubkeys["carol"],
        account_a_privkey=keys["alice"],
        fixture_seed=seed,
        guardian_a_pubkey=role_pubkeys["guardian_1"],
        guardian_b_pubkey=role_pubkeys["guardian_2"],
        guardian_a_privkey=keys["guardian_1"],
        guardian_b_privkey=keys["guardian_2"],
    )
    perps_authority = perps_authority_bundle["profile"]

    autotrader = build_autotrader_supervisor_profile_v1(
        supervisor_id="autotrader.supervisor.localtest.v1",
        chain_id=chain_id,
        stage="local-testnet",
        enabled=True,
        external_signed_payload_required=True,
        execution_id_required=True,
        release_certificate_required=True,
        stage_certificate_required=True,
        require_testnet_submission=True,
        require_local_preparation=True,
        max_actions_per_tick=1,
        max_runs_per_process=16,
        allowed_templates=["dca"],
        allowed_actions=["PLACE_SWAP_EXACT_IN"],
    )

    paths = FixtureBundle(
        key_bundle=output_root / "secrets" / "keys.json",
        role_pubkeys=fixtures_dir / "role_pubkeys.json",
        oracle_authority_profile=fixtures_dir / "oracle_authority_profile.json",
        perps_wallet_authority_profile=fixtures_dir / "perps_wallet_authority_profile.json",
        autotrader_supervisor_profile=fixtures_dir / "autotrader_supervisor_profile.json",
        guardian_quorum=fixtures_dir / "guardians.json",
        perps_wallet_recovery_exercise=fixtures_dir / "perps_wallet_recovery_exercise.json",
        perps_wallet_rotation_exercise=fixtures_dir / "perps_wallet_rotation_exercise.json",
        perps_wallet_device_approval_exercise=fixtures_dir / "perps_wallet_device_approval_exercise.json",
        perps_wallet_signer_device_integration=fixtures_dir / "perps_wallet_signer_device_integration.json",
        perps_wallet_signer_prompt_capture=fixtures_dir / "perps_wallet_signer_prompt_capture.json",
        perps_wallet_signer_execution_exercise=fixtures_dir / "perps_wallet_signer_execution_exercise.json",
        perps_wallet_encrypted_sss_backup=fixtures_dir / "perps_wallet_encrypted_sss_backup.json",
        perps_wallet_encrypted_sss_recipient_keys=fixtures_dir / "perps_wallet_encrypted_sss_recipient_keys.json",
    )

    _write_json(paths.key_bundle, key_bundle)
    _write_public_json(paths.role_pubkeys, role_pubkey_bundle)
    _write_json(paths.oracle_authority_profile, oracle_authority)
    _write_json(paths.perps_wallet_authority_profile, perps_authority)
    _write_json(paths.autotrader_supervisor_profile, autotrader)
    _write_json(paths.guardian_quorum, guardian_quorum)
    _write_json(paths.perps_wallet_recovery_exercise, perps_authority_bundle["recovery_exercise"])
    _write_json(paths.perps_wallet_rotation_exercise, perps_authority_bundle["rotation_exercise"])
    _write_json(paths.perps_wallet_device_approval_exercise, perps_authority_bundle["device_approval_exercise"])
    _write_json(paths.perps_wallet_signer_device_integration, perps_authority_bundle["signer_device_integration"])
    _write_json(paths.perps_wallet_signer_prompt_capture, perps_authority_bundle["signer_prompt_capture"])
    _write_json(paths.perps_wallet_signer_execution_exercise, perps_authority_bundle["signer_execution_exercise"])
    _write_json(paths.perps_wallet_encrypted_sss_backup, perps_authority_bundle["encrypted_sss_backup"])
    _write_json(paths.perps_wallet_encrypted_sss_recipient_keys, perps_authority_bundle["encrypted_sss_recipient_keys"])

    return paths


def _write_json(path: Path, body: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    # Fixture JSON carries private key material; restrict to the owner.
    try:
        path.chmod(0o600)
    except OSError:
        # Best effort for filesystems without chmod semantics (e.g., Windows).
        pass


def _write_public_json(path: Path, body: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    try:
        path.chmod(0o644)
    except OSError:
        pass


def _oracle_authority_profile(
    *,
    chain_id: str,
    oracle_pubkey: str,
    operator_pubkey: str,
    oracle_privkey: bytes,
    operator_privkey: bytes,
) -> dict[str, Any]:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=oracle_pubkey),
            KeyRef(key_id="oracle-authority-b", public_key=operator_pubkey),
        )
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id="oracle-production-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=2,
        signers=(
            {
                "signer_id": "oracle-a",
                "key_id": "oracle-authority-a",
                "public_key": oracle_pubkey,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "oracle-b",
                "key_id": "oracle-authority-b",
                "public_key": operator_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )
    profile = build_oracle_authority_profile_v1(
        authority_id="oracle-production-authority-v1",
        chain_id=chain_id,
        stage="production",
        enabled=True,
        key_manager=key_manager,
        signer_registry=signer_registry,
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
        },
        proof_profile={
            "zk_or_proof_required": True,
            "oracle_receipt_replay_required": True,
            "runtime_proof_profile": "zenooracle-o3-replay-zk-profile-v1",
        },
    )
    profile["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-a",
            key_id="oracle-authority-a",
            private_key_hex=_privkey_hex(oracle_privkey),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-b",
            key_id="oracle-authority-b",
            private_key_hex=_privkey_hex(operator_privkey),
        ),
    ]
    return profile


def _perps_wallet_authority_fixture_bundle(
    *,
    chain_id: str,
    account_a_pubkey: str,
    account_b_pubkey: str,
    account_c_pubkey: str,
    account_a_privkey: bytes,
    fixture_seed: bytes,
    guardian_a_pubkey: str,
    guardian_b_pubkey: str,
    guardian_a_privkey: bytes,
    guardian_b_privkey: bytes,
) -> dict[str, Any]:
    profile = _perps_wallet_authority_profile(
        chain_id=chain_id,
        key_specs=(
            ("wallet-a", "perps-wallet-a", account_a_pubkey, "recovery-perps-wallet-a"),
            ("wallet-b", "perps-wallet-b", account_b_pubkey, "recovery-perps-wallet-b"),
        ),
        guardian_a_pubkey=guardian_a_pubkey,
        guardian_b_pubkey=guardian_b_pubkey,
    )
    next_profile = _perps_wallet_authority_profile(
        chain_id=chain_id,
        key_specs=(
            ("wallet-c", "perps-wallet-c", account_c_pubkey, "recovery-perps-wallet-c"),
            ("wallet-b", "perps-wallet-b", account_b_pubkey, "recovery-perps-wallet-b"),
        ),
        guardian_a_pubkey=guardian_a_pubkey,
        guardian_b_pubkey=guardian_b_pubkey,
    )
    encrypted_sss_bundle = _perps_wallet_encrypted_sss_backup_bundle(
        chain_id=chain_id,
        wallet_authority_hash=str(profile["wallet_authority_hash"]),
        subject_key_id="perps-wallet-a",
        subject_privkey=account_a_privkey,
        fixture_seed=fixture_seed,
    )
    return {
        "profile": profile,
        "recovery_exercise": _perps_wallet_recovery_exercise(
            chain_id=chain_id,
            guardian_a_privkey=guardian_a_privkey,
            guardian_b_privkey=guardian_b_privkey,
        ),
        "rotation_exercise": _perps_wallet_rotation_exercise(
            chain_id=chain_id,
            next_profile=next_profile,
            guardian_a_privkey=guardian_a_privkey,
            guardian_b_privkey=guardian_b_privkey,
        ),
        "device_approval_exercise": _perps_wallet_device_approval_exercise(chain_id=chain_id),
        "signer_device_integration": _perps_wallet_signer_device_integration(chain_id=chain_id),
        "signer_prompt_capture": _perps_wallet_signer_prompt_capture(chain_id=chain_id),
        "signer_execution_exercise": _perps_wallet_signer_execution_exercise(chain_id=chain_id),
        "encrypted_sss_backup": encrypted_sss_bundle["backup"],
        "encrypted_sss_recipient_keys": encrypted_sss_bundle["recipient_keys"],
    }


def _perps_wallet_authority_profile(
    *,
    chain_id: str,
    key_specs: tuple[tuple[str, str, str, str], ...],
    guardian_a_pubkey: str,
    guardian_b_pubkey: str,
) -> dict[str, Any]:
    key_refs: list[KeyRef] = []
    recovery_policies: list[SocialRecoveryPolicy] = []
    signers: list[dict[str, Any]] = []
    for signer_id, key_id, public_key, recovery_policy_id in key_specs:
        key_refs.append(KeyRef(key_id=key_id, public_key=public_key, recovery_policy_id=recovery_policy_id))
        recovery_policies.append(
            SocialRecoveryPolicy(
                policy_id=recovery_policy_id,
                subject_key_id=key_id,
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
                ),
            )
        )
        signers.append(
            {
                "signer_id": signer_id,
                "key_id": key_id,
                "public_key": public_key,
                "weight": 1,
                "status": "active",
            }
        )
    key_manager = ZenoKeyManager(
        key_refs=tuple(key_refs),
        recovery_policies=tuple(recovery_policies),
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id=LOCAL_PERPS_AUTHORITY_ID,
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
        threshold=2,
        signers=tuple(signers),
    )
    return build_perps_wallet_authority_profile_v1(
        authority_id=LOCAL_PERPS_AUTHORITY_ID,
        chain_id=chain_id,
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


def _perps_wallet_encrypted_sss_backup(
    *,
    chain_id: str,
    wallet_authority_hash: str,
    subject_key_id: str,
    subject_privkey: bytes,
    fixture_seed: bytes,
) -> dict[str, Any]:
    return _perps_wallet_encrypted_sss_backup_bundle(
        chain_id=chain_id,
        wallet_authority_hash=wallet_authority_hash,
        subject_key_id=subject_key_id,
        subject_privkey=subject_privkey,
        fixture_seed=fixture_seed,
    )["backup"]


def _perps_wallet_encrypted_sss_backup_bundle(
    *,
    chain_id: str,
    wallet_authority_hash: str,
    subject_key_id: str,
    subject_privkey: bytes,
    fixture_seed: bytes,
) -> dict[str, Any]:
    recipients = _perps_wallet_encrypted_sss_recipients(fixture_seed)
    coefficient_seed = hashlib.blake2b(
        fixture_seed
        + b"|zenodex-localtest-sss-private-coefficients-v2|"
        + wallet_authority_hash.encode("utf-8")
        + b"|"
        + subject_key_id.encode("utf-8"),
        digest_size=32,
    ).digest()
    encryption_salt = hashlib.blake2b(
        fixture_seed
        + b"|zenodex-localtest-sss-private-encryption-salt-v2|"
        + wallet_authority_hash.encode("utf-8")
        + b"|"
        + subject_key_id.encode("utf-8")
        + b"|"
        + hashlib.sha256(subject_privkey).digest(),
        digest_size=32,
    ).digest()
    backup = build_perps_wallet_encrypted_sss_backup_v1(
        authority_id=LOCAL_PERPS_AUTHORITY_ID,
        chain_id=chain_id,
        wallet_authority_hash=wallet_authority_hash,
        subject_key_id=subject_key_id,
        secret_material=subject_privkey,
        recipients=recipients,
        threshold=3,
        created_at_epoch=13,
        drill_epoch=14,
        coefficient_seed=coefficient_seed,
        encryption_salt=encryption_salt,
    )
    return {
        "backup": backup,
        "recipient_keys": build_perps_wallet_encrypted_sss_recipient_keys_v1(
            backup=backup,
            recipients=recipients,
        ),
    }


def _perps_wallet_encrypted_sss_recipients(fixture_seed: bytes) -> tuple[SssBackupRecipient, ...]:
    return (
        _sss_recipient(
            fixture_seed,
            recipient_id="guardian-a-email",
            provider_kind="recovery_email",
            provider_id="email:guardian-a@local.test",
            transport_kind="email",
        ),
        _sss_recipient(
            fixture_seed,
            recipient_id="guardian-b-email",
            provider_kind="recovery_email",
            provider_id="email:guardian-b@local.test",
            transport_kind="email",
        ),
        _sss_recipient(
            fixture_seed,
            recipient_id="owner-dropbox",
            provider_kind="cloud_drive",
            provider_id="dropbox:zenodex-localtest-backups",
            transport_kind="dropbox",
        ),
        _sss_recipient(
            fixture_seed,
            recipient_id="owner-box",
            provider_kind="cloud_drive",
            provider_id="box:zenodex-localtest-backups",
            transport_kind="box",
        ),
        _sss_recipient(
            fixture_seed,
            recipient_id="owner-offline-export",
            provider_kind="offline_export",
            provider_id="offline:printed-or-hardware-export",
            transport_kind="manual_export",
        ),
    )


def _sss_recipient(
    fixture_seed: bytes,
    *,
    recipient_id: str,
    provider_kind: str,
    provider_id: str,
    transport_kind: str,
) -> SssBackupRecipient:
    return SssBackupRecipient(
        recipient_id=recipient_id,
        provider_kind=provider_kind,
        provider_id=provider_id,
        transport_kind=transport_kind,
        destination_hash="0x" + hashlib.sha256(provider_id.encode("utf-8")).hexdigest(),
        recipient_root_key=hashlib.blake2b(
            fixture_seed
            + b"|zenodex-localtest-sss-recipient-root-v1|"
            + recipient_id.encode("utf-8"),
            digest_size=32,
        ).digest(),
    )


def _perps_wallet_recovery_exercise(
    *,
    chain_id: str,
    guardian_a_privkey: bytes,
    guardian_b_privkey: bytes,
) -> dict[str, Any]:
    exercise: dict[str, Any] = {
        "schema": PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
        "chain_id": chain_id,
        "authority_id": LOCAL_PERPS_AUTHORITY_ID,
        "subject_key_id": "perps-wallet-a",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "current_epoch": 13,
        "approvals": ["guardian-a", "guardian-b"],
    }
    exercise_hash = perps_wallet_recovery_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = _guardian_signature_envelopes(
        payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
        payload_hash=exercise_hash,
        guardian_a_privkey=guardian_a_privkey,
        guardian_b_privkey=guardian_b_privkey,
    )
    return exercise


def _perps_wallet_rotation_exercise(
    *,
    chain_id: str,
    next_profile: Mapping[str, Any],
    guardian_a_privkey: bytes,
    guardian_b_privkey: bytes,
) -> dict[str, Any]:
    exercise: dict[str, Any] = {
        "schema": PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
        "chain_id": chain_id,
        "authority_id": LOCAL_PERPS_AUTHORITY_ID,
        "rotated_key_id": "perps-wallet-a",
        "replacement_key_id": "perps-wallet-c",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "broadcast_at_epoch": 13,
        "broadcast_reference": "local-testnet-fixture:perps-wallet-rotation-1",
        "approvals": ["guardian-a", "guardian-b"],
        "next_wallet_authority_profile": dict(next_profile),
    }
    exercise_hash = perps_wallet_rotation_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = _guardian_signature_envelopes(
        payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
        payload_hash=exercise_hash,
        guardian_a_privkey=guardian_a_privkey,
        guardian_b_privkey=guardian_b_privkey,
    )
    return exercise


def _guardian_signature_envelopes(
    *,
    payload_kind: str,
    payload_hash: str,
    guardian_a_privkey: bytes,
    guardian_b_privkey: bytes,
) -> list[dict[str, Any]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=payload_kind,
            payload_hash=payload_hash,
            signer_id="guardian-a",
            key_id="guardian-a",
            private_key_hex=_privkey_hex(guardian_a_privkey),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=payload_kind,
            payload_hash=payload_hash,
            signer_id="guardian-b",
            key_id="guardian-b",
            private_key_hex=_privkey_hex(guardian_b_privkey),
        ),
    ]


def _perps_wallet_backend_descriptor() -> dict[str, Any]:
    return KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        backend_id="local-testnet-hardware-wallet-a",
        policy_hash=LOCAL_FIXTURE_POLICY_HASH,
        metadata={
            "provider": "local-testnet-fixture",
            "device_approval_mode": "local_user_presence",
            "custody_mode": "local_testnet_fixture",
            "production_security_claim": False,
        },
    ).public_dict()


def _perps_wallet_environment(*, chain_id: str) -> dict[str, Any]:
    return KeyExecutionEnvironment(
        environment_id="perps-wallet-a-localtest-session-1",
        environment_kind=KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        chain_id=chain_id,
        policy_hash=LOCAL_FIXTURE_POLICY_HASH,
        challenge_hash=LOCAL_FIXTURE_CHALLENGE_HASH,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()


def _perps_wallet_environment_policy(*, chain_id: str) -> dict[str, Any]:
    return build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE],
        expected_chain_id=chain_id,
        expected_policy_hash=LOCAL_FIXTURE_POLICY_HASH,
        expected_challenge_hash=LOCAL_FIXTURE_CHALLENGE_HASH,
        require_user_presence=True,
        require_rollback_protection=True,
    )


def _perps_wallet_device_approval_exercise(*, chain_id: str) -> dict[str, Any]:
    base = build_perps_wallet_device_approval_exercise_v1(
        authority_id=LOCAL_PERPS_AUTHORITY_ID,
        chain_id=chain_id,
        key_id="perps-wallet-a",
        payload_kind="perps_wallet_prepare",
        purpose="sign",
        current_epoch=13,
        backend_descriptor=_perps_wallet_backend_descriptor(),
        use_policy=build_perps_wallet_device_approval_use_policy_v1(
            allowed_payload_kinds=["perps_wallet_prepare"],
            allowed_chain_ids=[chain_id],
            allowed_purposes=["sign"],
            valid_from_epoch=10,
            valid_until_epoch=20,
        ),
        environment=_perps_wallet_environment(chain_id=chain_id),
        environment_policy=_perps_wallet_environment_policy(chain_id=chain_id),
        payload={
            "domain": "zenodex.perps.stream8.device-approval.v1",
            "chain_id": chain_id,
            "nonce": 14,
            "action": "deposit_collateral",
            "stream_key": "8",
        },
        seen_nonces=[11, 12],
    )
    return base


def _perps_wallet_signer_payload(*, chain_id: str) -> dict[str, Any]:
    return {
        "domain": "zenodex.perps.stream8.signer-execution.v1",
        "chain_id": chain_id,
        "nonce": 15,
        "action": "deposit_collateral",
        "stream_key": "8",
    }


def _perps_wallet_signer_payload_hash(*, chain_id: str) -> str:
    return hash_v0("zeno_key_manager_runtime_payload_v0", _perps_wallet_signer_payload(chain_id=chain_id))


def _perps_wallet_signer_device_integration(*, chain_id: str) -> dict[str, Any]:
    base = build_perps_wallet_signer_device_integration_v1(
        authority_id=LOCAL_PERPS_AUTHORITY_ID,
        chain_id=chain_id,
        key_id="perps-wallet-a",
        current_epoch=13,
        backend_descriptor=_perps_wallet_backend_descriptor(),
        environment=_perps_wallet_environment(chain_id=chain_id),
        environment_policy=_perps_wallet_environment_policy(chain_id=chain_id),
        device_label="Local-Testnet Hardware Wallet A",
        approval_reference="local-testnet-prompt:wallet-a:epoch-13",
    )
    return base


def _perps_wallet_signer_prompt_capture(*, chain_id: str) -> dict[str, Any]:
    base = build_perps_wallet_signer_prompt_capture_v1(
        authority_id=LOCAL_PERPS_AUTHORITY_ID,
        chain_id=chain_id,
        key_id="perps-wallet-a",
        current_epoch=13,
        backend_descriptor=_perps_wallet_backend_descriptor(),
        environment=_perps_wallet_environment(chain_id=chain_id),
        environment_policy=_perps_wallet_environment_policy(chain_id=chain_id),
        device_label="Local-Testnet Hardware Wallet A",
        approval_reference="local-testnet-prompt:wallet-a:epoch-13",
        prompt_reference="local-testnet-prompt:wallet-a:epoch-13",
        prompt_source="local-testnet-fixture",
        prompt_presented_at_epoch=12,
        prompt_confirmed_at_epoch=13,
        prompt_message_hash=_perps_wallet_signer_payload_hash(chain_id=chain_id),
        capture_source="local-testnet-fixture-receipt",
        capture_evidence_hash="0x" + "ab" * 32,
    )
    return base


def _perps_wallet_signer_execution_exercise(*, chain_id: str) -> dict[str, Any]:
    payload = _perps_wallet_signer_payload(chain_id=chain_id)
    base = build_perps_wallet_signer_execution_exercise_v1(
        authority_id=LOCAL_PERPS_AUTHORITY_ID,
        chain_id=chain_id,
        key_id="perps-wallet-a",
        payload_kind="perps_wallet_submit",
        purpose="sign",
        current_epoch=13,
        backend_descriptor=_perps_wallet_backend_descriptor(),
        use_policy=build_perps_wallet_device_approval_use_policy_v1(
            allowed_payload_kinds=["perps_wallet_submit"],
            allowed_chain_ids=[chain_id],
            allowed_purposes=["sign"],
            valid_from_epoch=10,
            valid_until_epoch=20,
        ),
        environment=_perps_wallet_environment(chain_id=chain_id),
        environment_policy=_perps_wallet_environment_policy(chain_id=chain_id),
        device_label="Local-Testnet Hardware Wallet A",
        approval_reference="local-testnet-prompt:wallet-a:epoch-13",
        prompt_reference="local-testnet-prompt:wallet-a:epoch-13",
        prompt_presented_at_epoch=12,
        prompt_confirmed_at_epoch=13,
        payload=payload,
        seen_nonces=[11, 12, 14],
        execution_reference="local-testnet-submit:wallet-a:epoch-13",
        signed_payload_hash=_perps_wallet_signer_payload_hash(chain_id=chain_id),
    )
    return base
