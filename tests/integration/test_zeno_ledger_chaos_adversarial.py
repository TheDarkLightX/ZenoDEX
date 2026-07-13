"""Adversarial chaos tests for ZenoLedger signer registry and quorum.

These tests simulate an attacker trying to:
  - Subvert the signer registry (duplicate IDs, weight inflation, status
    spoofing, threshold underrun).
  - Slip non-conforming envelopes past quorum verification (wrong algorithm,
    forged signer ID, reused envelope).
  - Replay quorum reports across payloads, kinds, or registries.

The Tau Net validator set is exactly the kind of contract that *will* change
over time (rotating signers, threshold adjustments, key migrations). These
tests ensure each rotation requires a deliberate registry rev, not a silent
substitution.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
)
from src.integration.zeno_ledger_signer_registry import (
    SIGNER_REGISTRY_SCHEMA_V0,
    build_signer_registry_v0,
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0

_PK_A = "0x" + "a1" * 48
_PK_B = "0x" + "b2" * 48
_PK_C = "0x" + "c3" * 48
_PUBLIC_KEY_DEDUPE_VECTORS = (
    Path(__file__).resolve().parents[1] / "fixtures" / "zeno_bls_public_key_dedupe_v0.json"
)


def _signers(*specs: dict[str, Any]) -> list[dict[str, Any]]:
    return list(specs)


def _signer(*, signer_id: str, key_id: str, public_key: str, **kwargs: Any) -> dict[str, Any]:
    return {"signer_id": signer_id, "key_id": key_id, "public_key": public_key, **kwargs}


# -----------------------------------------------------------------------------
# A. Signer-registry construction — adversarial inputs.
# -----------------------------------------------------------------------------


class TestSignerRegistryConstructionChaos:
    def test_builds_valid_registry(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="release-2026Q2",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(_signer(signer_id="a", key_id="k1", public_key=_PK_A)),
        )
        assert reg["schema"] == SIGNER_REGISTRY_SCHEMA_V0
        assert reg["registry_hash"].startswith("0x")

    def test_rejects_empty_signers(self) -> None:
        with pytest.raises(ValueError, match="at least one"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=[],
            )

    def test_rejects_string_as_signers(self) -> None:
        with pytest.raises(TypeError, match="sequence"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers="abc",  # type: ignore[arg-type]
            )

    def test_rejects_zero_threshold(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=0,
                signers=_signers(_signer(signer_id="a", key_id="k", public_key=_PK_A)),
            )

    def test_rejects_threshold_exceeds_active_weight(self) -> None:
        # Single signer with weight 1; threshold 5 cannot be met.
        with pytest.raises(ValueError, match="threshold exceeds"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=5,
                signers=_signers(_signer(signer_id="a", key_id="k", public_key=_PK_A, weight=1)),
            )

    def test_rejects_unknown_payload_kind(self) -> None:
        with pytest.raises(ValueError, match="payload_kind"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="not_a_real_kind",
                threshold=1,
                signers=_signers(_signer(signer_id="a", key_id="k", public_key=_PK_A)),
            )

    def test_rejects_duplicate_signer_id_key_id(self) -> None:
        with pytest.raises(ValueError, match="duplicate"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=_signers(
                    _signer(signer_id="a", key_id="k1", public_key=_PK_A),
                    _signer(signer_id="a", key_id="k1", public_key=_PK_B),
                ),
            )

    def test_fixed_public_key_dedupe_vectors_match_registry_contract(self) -> None:
        vectors = json.loads(_PUBLIC_KEY_DEDUPE_VECTORS.read_text(encoding="utf-8"))
        assert vectors["schema"] == "zenodex/test/zeno_bls_public_key_dedupe_vectors/v0"

        for case in vectors["cases"]:
            if case["expected_registry_status"] == "rejected":
                with pytest.raises(ValueError, match=case["expected_error"]):
                    build_signer_registry_v0(
                        registry_id=case["registry_id"],
                        payload_kind="checkpoint",
                        threshold=case["threshold"],
                        signers=case["signers"],
                    )
            else:
                registry = build_signer_registry_v0(
                    registry_id=case["registry_id"],
                    payload_kind="checkpoint",
                    threshold=case["threshold"],
                    signers=case["signers"],
                )
                validate_signer_registry_v0(registry)

    def test_rejects_duplicate_public_key_across_active_and_revoked_signers(self) -> None:
        with pytest.raises(ValueError, match="duplicate signer public_key"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=_signers(
                    _signer(signer_id="a", key_id="active", public_key=_PK_A),
                    _signer(
                        signer_id="b",
                        key_id="revoked",
                        public_key=_PK_A,
                        status="revoked",
                    ),
                ),
            )

    def test_accepts_same_signer_id_different_key_id(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(
                _signer(signer_id="a", key_id="k1", public_key=_PK_A),
                _signer(signer_id="a", key_id="k2", public_key=_PK_B),
            ),
        )
        assert len(reg["signers"]) == 2

    def test_rejects_uppercase_pubkey(self) -> None:
        with pytest.raises(ValueError):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=_signers(
                    _signer(signer_id="a", key_id="k", public_key=_PK_A.upper()),
                ),
            )

    def test_rejects_unknown_status(self) -> None:
        with pytest.raises(ValueError, match="status must be active or revoked"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=_signers(
                    _signer(signer_id="a", key_id="k", public_key=_PK_A, status="pending"),
                ),
            )

    def test_rejects_negative_weight(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=_signers(
                    _signer(signer_id="a", key_id="k", public_key=_PK_A, weight=-1),
                ),
            )

    def test_rejects_zero_weight(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=_signers(
                    _signer(signer_id="a", key_id="k", public_key=_PK_A, weight=0),
                ),
            )

    def test_revoked_signers_excluded_from_active_weight(self) -> None:
        # Only the active signer counts toward threshold.
        with pytest.raises(ValueError, match="threshold exceeds"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=2,
                signers=_signers(
                    _signer(signer_id="a", key_id="k", public_key=_PK_A, weight=1),
                    _signer(signer_id="b", key_id="k", public_key=_PK_B, weight=10, status="revoked"),
                ),
            )

    def test_signers_sorted_canonically_in_output(self) -> None:
        # Order in → order out is canonical, not insertion order.
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(
                _signer(signer_id="z", key_id="k", public_key=_PK_C),
                _signer(signer_id="a", key_id="k", public_key=_PK_A),
                _signer(signer_id="m", key_id="k", public_key=_PK_B),
            ),
        )
        ids = [s["signer_id"] for s in reg["signers"]]
        assert ids == ["a", "m", "z"]

    def test_signer_hash_changes_with_field_mutation(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(_signer(signer_id="a", key_id="k1", public_key=_PK_A)),
        )
        original_hash = reg["signers"][0]["signer_hash"]

        reg2 = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(_signer(signer_id="a", key_id="k1", public_key=_PK_B)),
        )
        assert reg2["signers"][0]["signer_hash"] != original_hash

    def test_registry_hash_changes_with_threshold_mutation(self) -> None:
        a = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(
                _signer(signer_id="a", key_id="k", public_key=_PK_A),
                _signer(signer_id="b", key_id="k", public_key=_PK_B),
            ),
        )
        b = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=2,
            signers=_signers(
                _signer(signer_id="a", key_id="k", public_key=_PK_A),
                _signer(signer_id="b", key_id="k", public_key=_PK_B),
            ),
        )
        assert a["registry_hash"] != b["registry_hash"]

    def test_registry_hash_changes_with_registry_id_mutation(self) -> None:
        base_signers = _signers(_signer(signer_id="a", key_id="k", public_key=_PK_A))
        a = build_signer_registry_v0(
            registry_id="release-1",
            payload_kind="checkpoint",
            threshold=1,
            signers=base_signers,
        )
        b = build_signer_registry_v0(
            registry_id="release-2",
            payload_kind="checkpoint",
            threshold=1,
            signers=base_signers,
        )
        assert a["registry_hash"] != b["registry_hash"]


# -----------------------------------------------------------------------------
# B. Signer-registry validation — tampered binding detection.
# -----------------------------------------------------------------------------


class TestSignerRegistryTamperDetection:
    @staticmethod
    def _build_reg() -> dict[str, Any]:
        return build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(
                _signer(signer_id="a", key_id="k", public_key=_PK_A),
                _signer(signer_id="b", key_id="k", public_key=_PK_B),
            ),
        )

    def test_valid_registry_validates(self) -> None:
        validate_signer_registry_v0(self._build_reg())  # no raise

    def test_rejects_tampered_threshold(self) -> None:
        reg = self._build_reg()
        reg = dict(reg)
        reg["threshold"] = 999
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg)

    def test_rejects_added_phantom_signer(self) -> None:
        reg = self._build_reg()
        reg = dict(reg)
        reg["signers"] = list(reg["signers"]) + [
            {
                "signer_id": "z",
                "key_id": "k",
                "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                "public_key": _PK_C,
                "weight": 1,
                "status": "active",
                "signer_hash": "0x" + "00" * 32,
            }
        ]
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg)

    def test_rejects_hash_consistent_registry_with_duplicate_public_key(self) -> None:
        registry = self._build_reg()
        signers = [dict(signer) for signer in registry["signers"]]
        signers[1]["public_key"] = signers[0]["public_key"]
        second_body = {key: value for key, value in signers[1].items() if key != "signer_hash"}
        signers[1]["signer_hash"] = hash_v0("signer_registry_entry_v0", second_body)
        body = {
            "schema": registry["schema"],
            "registry_id": registry["registry_id"],
            "payload_kind": registry["payload_kind"],
            "threshold": registry["threshold"],
            "signers": signers,
        }
        malicious_registry = {
            **body,
            "registry_hash": hash_v0("signer_registry_v0", body),
        }

        with pytest.raises(ValueError, match="duplicate signer public_key"):
            validate_signer_registry_v0(malicious_registry)

    def test_rejects_removed_signer(self) -> None:
        reg = self._build_reg()
        reg = dict(reg)
        reg["signers"] = list(reg["signers"])[:1]
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg)

    def test_rejects_swapped_pubkey(self) -> None:
        reg = self._build_reg()
        reg = dict(reg)
        signers = [dict(s) for s in reg["signers"]]
        signers[0]["public_key"] = _PK_C
        reg["signers"] = signers
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg)

    def test_rejects_wrong_schema(self) -> None:
        reg = self._build_reg()
        reg = dict(reg)
        reg["schema"] = "zenodex/zeno_ledger/signer_registry/v999"
        with pytest.raises(ValueError, match="schema mismatch"):
            validate_signer_registry_v0(reg)

    def test_rejects_added_unknown_field(self) -> None:
        reg = self._build_reg()
        reg = dict(reg)
        reg["extra_field"] = "evil"
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg)

    def test_rejects_status_promotion_revoked_to_active(self) -> None:
        # Build a registry with one revoked signer.
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(
                _signer(signer_id="a", key_id="k", public_key=_PK_A, status="active"),
                _signer(signer_id="b", key_id="k", public_key=_PK_B, status="revoked"),
            ),
        )
        reg = dict(reg)
        signers = [dict(s) for s in reg["signers"]]
        # Find signer b and try to promote.
        for s in signers:
            if s["signer_id"] == "b":
                s["status"] = "active"
        reg["signers"] = signers
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg)


# -----------------------------------------------------------------------------
# C. Quorum verification — adversarial envelope shapes.
# -----------------------------------------------------------------------------


class TestQuorumVerificationChaos:
    """We can't actually verify BLS signatures here without py_ecc and real
    keys, but we can verify that the *envelope sanity checks* fail closed
    on every malformed shape Tau might send our way.
    """

    @staticmethod
    def _reg() -> dict[str, Any]:
        return build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(_signer(signer_id="a", key_id="k", public_key=_PK_A)),
        )

    def test_rejects_empty_envelopes(self) -> None:
        with pytest.raises(ValueError, match="at least one envelope"):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[],
            )

    def test_rejects_string_as_envelopes(self) -> None:
        with pytest.raises(TypeError, match="sequence"):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes="not-a-list",  # type: ignore[arg-type]
            )

    def test_rejects_bytes_as_envelopes(self) -> None:
        with pytest.raises(TypeError, match="sequence"):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=b"x",  # type: ignore[arg-type]
            )

    def test_rejects_payload_kind_mismatch_with_registry(self) -> None:
        with pytest.raises(ValueError, match="payload_kind does not match"):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="watcher_attestation",  # different valid kind
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "a",
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )

    def test_rejects_unknown_signer(self) -> None:
        with pytest.raises(ValueError, match="not active in registry"):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "phantom",
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )

    def test_rejects_unknown_algorithm(self) -> None:
        with pytest.raises(ValueError, match="algorithm is not allowed"):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "a",
                    "key_id": "k",
                    "algorithm": "ed25519",  # algorithm drift
                }],
            )

    def test_rejects_duplicate_envelopes(self) -> None:
        """Duplicate envelopes for the same signer must be rejected — either
        by the duplicate-detection logic or, earlier, by envelope-shape
        validation. Either path is fail-closed; we accept any ``ValueError``.
        """
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(_signer(signer_id="a", key_id="k", public_key=_PK_A)),
        )
        envelope = {
            "signer_id": "a",
            "key_id": "k",
            "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        }
        with pytest.raises(ValueError):
            verify_signature_quorum_v0(
                registry=reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[envelope, envelope],
            )

    def test_quorum_defense_rejects_duplicate_public_key_before_weight(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        registry = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=2,
            signers=_signers(
                _signer(signer_id="a", key_id="k-a", public_key=_PK_A),
                _signer(signer_id="b", key_id="k-b", public_key=_PK_B),
            ),
        )
        signers = [dict(signer) for signer in registry["signers"]]
        signers[1]["public_key"] = signers[0]["public_key"]
        registry = {**registry, "signers": signers}
        monkeypatch.setattr(
            "src.integration.zeno_ledger_signer_registry.validate_signer_registry_v0",
            lambda _registry: None,
        )
        monkeypatch.setattr(
            "src.integration.zeno_ledger_signer_registry.validate_bls_signed_artifact_envelope_v0",
            lambda **_kwargs: None,
        )
        envelopes = [
            {
                "signer_id": signer["signer_id"],
                "key_id": signer["key_id"],
                "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                "public_key": signer["public_key"],
                "envelope_hash": "0x" + f"{index + 1:064x}",
            }
            for index, signer in enumerate(signers)
        ]

        with pytest.raises(ValueError, match="duplicate envelope signer public_key"):
            verify_signature_quorum_v0(
                registry=registry,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=envelopes,
            )

    def test_rejects_invalid_registry_first(self) -> None:
        # Quorum verifier validates the registry first; bad registry must
        # be rejected even with a valid envelope.
        bad_reg = self._reg()
        bad_reg = dict(bad_reg)
        bad_reg["threshold"] = 999
        with pytest.raises(ValueError):
            verify_signature_quorum_v0(
                registry=bad_reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "a",
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )

    def test_rejects_envelope_with_revoked_signer(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(
                _signer(signer_id="a", key_id="k", public_key=_PK_A),
                _signer(signer_id="b", key_id="k", public_key=_PK_B, status="revoked"),
            ),
        )
        with pytest.raises(ValueError, match="not active in registry"):
            verify_signature_quorum_v0(
                registry=reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "b",
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )

    def test_rejects_envelope_missing_signer_id(self) -> None:
        with pytest.raises(ValueError):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )

    def test_rejects_envelope_missing_key_id(self) -> None:
        with pytest.raises(ValueError):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "a",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )

    def test_rejects_string_envelope(self) -> None:
        with pytest.raises(TypeError):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=["not an envelope"],  # type: ignore[list-item]
            )

    def test_rejects_payload_hash_non_canonical(self) -> None:
        # payload_hash is passed through to envelope validator; uppercase
        # will be rejected at the canonical hex check.
        with pytest.raises(ValueError):
            verify_signature_quorum_v0(
                registry=self._reg(),
                payload_kind="checkpoint",
                payload_hash="0X" + "11" * 32,  # uppercase 0X
                envelopes=[{
                    "signer_id": "a",
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )


# -----------------------------------------------------------------------------
# D. Registry stability under serialization round-trip.
# -----------------------------------------------------------------------------


class TestRegistryRoundTripStability:
    """A registry that was built once must validate after JSON round-trip.
    If it doesn't, an operator who stores the registry as JSON and reloads
    will see a different binding hash — exactly the silent drift we want to
    catch.
    """

    def test_registry_survives_json_round_trip(self) -> None:
        import json as _json

        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=2,
            signers=_signers(
                _signer(signer_id="a", key_id="k", public_key=_PK_A),
                _signer(signer_id="b", key_id="k", public_key=_PK_B),
            ),
        )
        round_tripped = _json.loads(_json.dumps(reg))
        validate_signer_registry_v0(round_tripped)  # no raise
        assert round_tripped["registry_hash"] == reg["registry_hash"]

    def test_registry_survives_sorted_keys_round_trip(self) -> None:
        import json as _json

        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=_signers(_signer(signer_id="a", key_id="k", public_key=_PK_A)),
        )
        round_tripped = _json.loads(_json.dumps(reg, sort_keys=True))
        validate_signer_registry_v0(round_tripped)
        assert round_tripped["registry_hash"] == reg["registry_hash"]
