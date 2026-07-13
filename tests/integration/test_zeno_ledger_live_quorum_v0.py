from __future__ import annotations

import pytest

from src.integration import zeno_ledger_signature
from src.integration.zeno_ledger_live_quorum_v0 import (
    build_live_checkpoint_quorum_admission_v0,
    validate_live_checkpoint_quorum_admission_v0,
)
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0

ZERO_ROOT = "0x" + "00" * 32
TEST_BLS_PRIVATE_KEY_A = "0x" + "01" * 32
TEST_BLS_PRIVATE_KEY_B = "0x" + "02" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _header(*, height: int = 6, label: str = "a") -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-live-quorum-testnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("validator-set"),
        ingress_root=_root(f"ingress-{label}"),
        tx_root=_root(f"tx-{label}"),
        pre_state_root=_root(f"pre-{label}"),
        post_state_root=_root(f"post-{label}"),
        app_hash=_root(f"app-{label}"),
        evidence_root=_root(f"evidence-{label}"),
        body_root=_root(f"body-{label}"),
        data_availability_root=_root(f"da-{label}"),
        proof_journal_hash=_root(f"proof-{label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="live-checkpoint-quorum-testnet-v0",
        payload_kind="checkpoint",
        threshold=2,
        signers=[
            {
                "signer_id": "validator-a",
                "key_id": "bls-a",
                "public_key": bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_A),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "validator-b",
                "key_id": "bls-b",
                "public_key": bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_B),
                "weight": 1,
                "status": "active",
            },
        ],
    )


def _envelopes(header_hash: str) -> list[dict[str, object]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=header_hash,
            signer_id="validator-a",
            key_id="bls-a",
            private_key_hex=TEST_BLS_PRIVATE_KEY_A,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=header_hash,
            signer_id="validator-b",
            key_id="bls-b",
            private_key_hex=TEST_BLS_PRIVATE_KEY_B,
        ),
    ]


def test_bls_release_signature_rejects_inconsistent_dependency_state(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(zeno_ledger_signature, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(zeno_ledger_signature, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc\\.bls is required for BLS release signatures"):
        zeno_ledger_signature.bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_A)


def test_live_checkpoint_quorum_admission_accepts_threshold() -> None:
    header = _header()
    checkpoint = build_checkpoint_v0(header)
    registry = _registry()
    envelopes = _envelopes(str(checkpoint["header_hash"]))

    admission = build_live_checkpoint_quorum_admission_v0(
        header=header,
        checkpoint=checkpoint,
        registry=registry,
        envelopes=envelopes,
    )

    assert admission["ok"] is True
    assert admission["accepted_weight"] == 2
    assert admission["threshold"] == 2
    validate_live_checkpoint_quorum_admission_v0(
        admission=admission,
        header=header,
        checkpoint=checkpoint,
        registry=registry,
        envelopes=envelopes,
    )


def test_threshold_two_registry_rejects_two_identities_from_one_private_key() -> None:
    payload_hash = _root("single-private-key-witness")
    first_envelope = build_bls_signed_artifact_envelope_v0(
        payload_kind="checkpoint",
        payload_hash=payload_hash,
        signer_id="validator-a",
        key_id="bls-a",
        private_key_hex=TEST_BLS_PRIVATE_KEY_A,
    )
    alias_envelope = build_bls_signed_artifact_envelope_v0(
        payload_kind="checkpoint",
        payload_hash=payload_hash,
        signer_id="validator-a-alias",
        key_id="bls-a-alias",
        private_key_hex=TEST_BLS_PRIVATE_KEY_A,
    )
    assert first_envelope["public_key"] == alias_envelope["public_key"]

    with pytest.raises(ValueError, match="duplicate signer public_key"):
        build_signer_registry_v0(
            registry_id="single-key-alias-witness-v0",
            payload_kind="checkpoint",
            threshold=2,
            signers=[
                {
                    "signer_id": "validator-a",
                    "key_id": "bls-a",
                    "public_key": first_envelope["public_key"],
                    "weight": 1,
                    "status": "active",
                },
                {
                    "signer_id": "validator-a-alias",
                    "key_id": "bls-a-alias",
                    "public_key": alias_envelope["public_key"],
                    "weight": 1,
                    "status": "active",
                },
            ],
        )


def test_live_checkpoint_quorum_admission_rejects_insufficient_weight() -> None:
    header = _header()
    checkpoint = build_checkpoint_v0(header)

    with pytest.raises(ValueError, match="threshold not met"):
        build_live_checkpoint_quorum_admission_v0(
            header=header,
            checkpoint=checkpoint,
            registry=_registry(),
            envelopes=_envelopes(str(checkpoint["header_hash"]))[:1],
        )


def test_live_checkpoint_quorum_admission_rejects_header_checkpoint_mismatch() -> None:
    header = _header(label="a")
    checkpoint = build_checkpoint_v0(_header(label="b"))

    with pytest.raises(ValueError, match="checkpoint/header binding mismatch"):
        build_live_checkpoint_quorum_admission_v0(
            header=header,
            checkpoint=checkpoint,
            registry=_registry(),
            envelopes=_envelopes(str(checkpoint["header_hash"])),
        )
