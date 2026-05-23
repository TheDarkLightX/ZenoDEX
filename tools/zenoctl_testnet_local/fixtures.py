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
from pathlib import Path
from typing import Any, Mapping

from src.integration.autotrader_supervisor_profile import build_autotrader_supervisor_profile_v1
from src.integration.perps_wallet_authority import (
    PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    build_perps_wallet_authority_profile_v1,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.integration.zeno_key_manager import KeyRef, RecoveryGuardian, SocialRecoveryPolicy, ZenoKeyManager
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_oracle_authority import ORACLE_AUTHORITY_PAYLOAD_KIND, build_oracle_authority_profile_v1

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


SCHEMA_KEY_BUNDLE = "zenodex.local_testnet.key_bundle.v0"
SCHEMA_GUARDIAN_QUORUM = "zenodex.local_testnet.guardian_quorum.v0"
SCHEMA_ORACLE_HOME = "zenodex.local_testnet.oracle_home_seed.v0"


@dataclass(frozen=True)
class FixtureBundle:
    """Paths to the per-fixture artifacts persisted on disk."""

    key_bundle: Path
    oracle_authority_profile: Path
    perps_wallet_authority_profile: Path
    autotrader_supervisor_profile: Path
    guardian_quorum: Path

    def as_manifest_paths(self) -> dict[str, str]:
        return {
            "key_bundle": str(self.key_bundle),
            "oracle_authority_profile": str(self.oracle_authority_profile),
            "perps_wallet_authority_profile": str(self.perps_wallet_authority_profile),
            "autotrader_supervisor_profile": str(self.autotrader_supervisor_profile),
            "guardian_quorum": str(self.guardian_quorum),
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

    fixtures_dir = Path(out_dir).resolve() / "fixtures"
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

    perps_authority = _perps_wallet_authority_profile(
        chain_id=chain_id,
        account_a_pubkey=role_pubkeys["alice"],
        account_b_pubkey=role_pubkeys["bob"],
        guardian_a_pubkey=role_pubkeys["guardian_1"],
        guardian_b_pubkey=role_pubkeys["guardian_2"],
    )

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
        key_bundle=fixtures_dir / "keys.json",
        oracle_authority_profile=fixtures_dir / "oracle_authority_profile.json",
        perps_wallet_authority_profile=fixtures_dir / "perps_wallet_authority_profile.json",
        autotrader_supervisor_profile=fixtures_dir / "autotrader_supervisor_profile.json",
        guardian_quorum=fixtures_dir / "guardians.json",
    )

    _write_json(paths.key_bundle, key_bundle)
    _write_json(paths.oracle_authority_profile, oracle_authority)
    _write_json(paths.perps_wallet_authority_profile, perps_authority)
    _write_json(paths.autotrader_supervisor_profile, autotrader)
    _write_json(paths.guardian_quorum, guardian_quorum)

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


def _perps_wallet_authority_profile(
    *,
    chain_id: str,
    account_a_pubkey: str,
    account_b_pubkey: str,
    guardian_a_pubkey: str,
    guardian_b_pubkey: str,
) -> dict[str, Any]:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=account_a_pubkey, recovery_policy_id="recovery-perps-wallet-a"),
            KeyRef(key_id="perps-wallet-b", public_key=account_b_pubkey, recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-a",
                subject_key_id="perps-wallet-a",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
                ),
            ),
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
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
                "public_key": account_a_pubkey,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "wallet-b",
                "key_id": "perps-wallet-b",
                "public_key": account_b_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )
    return build_perps_wallet_authority_profile_v1(
        authority_id="perps-wallet-authority-v1",
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
