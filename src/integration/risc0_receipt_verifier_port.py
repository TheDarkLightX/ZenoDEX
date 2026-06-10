"""Production ReceiptVerifierPort: real RISC0 receipt.verify via the blessed CLI.

This replaces the WS2 test stub with the real thing, closing the honesty gap named
in docs/WS2_TRUSTLESS_REFUSE_BY_DEFAULT.md ("the tests inject a fake that returns
VERIFIED by fiat"). Contract (ReceiptVerifierPort, client_admission_decision.py):

  (a) blessed-verifier identity FIRST: absolute path, no PATH lookup, regular file,
      sha256(binary) == the client-pinned expected_cmd_hash. An unpinned or
      tampered verifier binary is never executed.
  (b) REAL cryptographic verification: the binary runs
      `tau_state_proof_decode_journal`, which calls receipt.verify(GUEST_ID)
      BEFORE echoing any journal byte (zk/state_proof_risc0/cli/src/decode_journal.rs).
  (c) the CLIENT pin is enforced against the VERIFIER's identity: the emitted
      compiled-in `verifier_image_id_words` must equal `pinned_image_id`. A wrong
      or stale verifier (different guest) fails the pin even if its own receipt
      verifies. The journal's echoed image id is re-checked here and again at
      gate 5 (defense in depth, never a substitute).
  (d) UNKNOWN/TIMEOUT/ERROR are distinct and all fail closed; no host-asserted
      field (ok/production_security_claim/...) is ever read from the PROOF side —
      the only trusted JSON is the blessed binary's own stdout, parsed CLOSED-shape.

The journal parse is strict and closed per proof_type: unknown keys, missing keys,
wrong types, or malformed hex all return ERROR (a journal with unexpected shape
means a different guest version, which the pin should have caught — fail closed).
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path
from typing import Any, Mapping, Optional

from src.integration.client_admission_decision import (
    ReceiptVerifyResult,
    VerifierIdentity,
    VerifyStatus,
)

_DECODE_SCHEMA = "tau_state_proof_decode_journal"

_PROOF_TYPE_PERPS_NP = "risc0.zenodex_perps_np_transition.v1"
_PROOF_TYPE_ZUSD = "risc0.zenodex_zusd_transition.v1"
_PROOF_TYPE_CLOB = "risc0.zenodex_clob_transition.v1"

_HEX64_RE = re.compile(r"\A[0-9a-f]{64}\Z")
_INT_STR_RE = re.compile(r"\A-?[0-9]+\Z")
_U32_MAX = (1 << 32) - 1

# Field kind vocabulary: hex32 -> bytes(32); image -> tuple of 8 u32 ints;
# str / bool / uint passed through type-checked; int_str -> int from a strict
# decimal string (the CLI emits i128/u128 as strings to survive JSON).
_JOURNAL_SPECS: Mapping[str, Mapping[str, str]] = {
    _PROOF_TYPE_PERPS_NP: {
        "proof_type": "str",
        "risc0_image_id": "image",
        "state_hash": "hex32",
        "chain_id": "str",
        "pre_app_hash_present": "bool",
        "pre_app_hash": "hex32",
        "post_app_hash": "hex32",
        "operation_hash": "hex32",
        "state_delta_hash": "hex32",
        "oracle_binding_hash": "hex32",
        "collateral_binding_hash": "hex32",
        "participant_set_hash": "hex32",
        "receipt_root": "hex32",
        "participant_count": "uint",
        "net_position_base": "int_str",
        "total_collateral_e8": "int_str",
        "funding_residual_e8": "int_str",
        "matched_base_volume": "int_str",
    },
    _PROOF_TYPE_ZUSD: {
        "proof_type": "str",
        "risc0_image_id": "image",
        "state_hash": "hex32",
        "chain_id": "str",
        "pre_app_hash_present": "bool",
        "pre_app_hash": "hex32",
        "post_app_hash": "hex32",
        "operation_hash": "hex32",
        "state_delta_hash": "hex32",
        "oracle_binding_hash": "hex32",
        "zusd_balance_root_hash": "hex32",
        "zusd_vault_root_hash": "hex32",
        "participant_set_hash": "hex32",
        "minted_zusd_e8": "int_str",
        "collateral_value_e8": "int_str",
        "mcr_bps": "uint",
    },
    _PROOF_TYPE_CLOB: {
        "proof_type": "str",
        "risc0_image_id": "image",
        "state_hash": "hex32",
        "chain_id": "str",
        "pre_app_hash_present": "bool",
        "pre_app_hash": "hex32",
        "post_app_hash": "hex32",
        "pre_book_root": "hex32",
        "post_book_root": "hex32",
        "operation_hash": "hex32",
        "state_delta_hash": "hex32",
        "event_log_root": "hex32",
        "matching_rule_hash": "hex32",
        "fee_rule_hash": "hex32",
        "fee_total": "int_str",
        "resting_taker_qty": "uint",
        "fill_count": "uint",
    },
}

_TOP_LEVEL_OK_KEYS = frozenset({"ok", "verifier_image_id", "verifier_image_id_words", "journal"})


# Environment variables that change HOW the pinned binary verifies — the sha256
# pin proves WHICH binary runs, not under WHICH verification mode. RISC0_DEV_MODE
# makes receipt.verify accept un-proven dev receipts; RISC0_* / loader-injection
# (LD_*, DYLD_*) vars can otherwise subvert a correctly-pinned binary. They are
# stripped and dev mode is hard-pinned OFF for the production verify call.
_VERIFIER_ENV_STRIP_PREFIXES = ("RISC0_", "LD_", "DYLD_")


def _sanitized_env() -> dict[str, str]:
    env = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith(_VERIFIER_ENV_STRIP_PREFIXES)
    }
    env["RISC0_DEV_MODE"] = "0"
    return env


def _error(status: VerifyStatus, message: str) -> ReceiptVerifyResult:
    return ReceiptVerifyResult(status=status, journal=None, error=message)


def _sha256_file(path: Path) -> Optional[str]:
    try:
        h = hashlib.sha256()
        with path.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        return h.hexdigest()
    except OSError:
        return None


def _check_blessed_identity(blessed: VerifierIdentity) -> Optional[str]:
    """Returns an error string, or None if the binary is the pinned one."""
    if blessed.allow_path_lookup:
        return "blessed verifier must not allow PATH lookup"
    if type(blessed.binary_path) is not str or not blessed.binary_path.startswith("/"):
        return "blessed verifier binary path must be absolute"
    if type(blessed.expected_cmd_hash) is not str or not _HEX64_RE.match(
        blessed.expected_cmd_hash.lower()
    ):
        return "blessed verifier expected_cmd_hash must be 64 hex chars"
    path = Path(blessed.binary_path)
    if not path.is_file():
        return "blessed verifier binary missing or not a regular file"
    digest = _sha256_file(path)
    if digest is None:
        return "blessed verifier binary unreadable"
    if digest != blessed.expected_cmd_hash.lower():
        return "blessed verifier binary hash mismatch"
    return None


def _parse_image_words(value: Any) -> Optional[tuple[int, ...]]:
    if not isinstance(value, list) or len(value) != 8:
        return None
    words: list[int] = []
    for item in value:
        if type(item) is not int or not (0 <= item <= _U32_MAX):
            return None
        words.append(item)
    return tuple(words)


def _parse_journal(
    raw: Any, spec: Mapping[str, str]
) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    if not isinstance(raw, dict):
        return None, "journal must be an object"
    if set(raw.keys()) != set(spec.keys()):
        return None, "journal shape mismatch (closed set)"
    parsed: dict[str, Any] = {}
    for key, kind in spec.items():
        value = raw[key]
        if kind == "str":
            if type(value) is not str or not value:
                return None, f"journal.{key} must be a non-empty string"
            parsed[key] = value
        elif kind == "bool":
            if type(value) is not bool:
                return None, f"journal.{key} must be a bool"
            parsed[key] = value
        elif kind == "uint":
            if type(value) is not int or value < 0:
                return None, f"journal.{key} must be a non-negative integer"
            parsed[key] = value
        elif kind == "int_str":
            if type(value) is not str or not _INT_STR_RE.match(value):
                return None, f"journal.{key} must be a decimal string"
            parsed[key] = int(value)
        elif kind == "hex32":
            if type(value) is not str or not _HEX64_RE.match(value):
                return None, f"journal.{key} must be 64 lowercase hex chars"
            parsed[key] = bytes.fromhex(value)
        elif kind == "image":
            words = _parse_image_words(value)
            if words is None:
                return None, f"journal.{key} must be 8 u32 words"
            parsed[key] = words
        else:  # pragma: no cover - spec vocabulary is closed above
            return None, f"unknown spec kind for journal.{key}"
    return parsed, None


class Risc0CliReceiptVerifierPort:
    """The production ReceiptVerifierPort. One instance per pinned proof_type."""

    def __init__(self, proof_type: str, *, timeout_s: float = 120.0) -> None:
        if proof_type not in _JOURNAL_SPECS:
            raise ValueError(f"unsupported proof_type: {proof_type!r}")
        self._proof_type = proof_type
        self._timeout_s = float(timeout_s)

    def verify_receipt(
        self,
        proof_bytes: bytes,
        pinned_image_id: tuple[int, ...],
        *,
        blessed_verifier: VerifierIdentity,
    ) -> ReceiptVerifyResult:
        identity_error = _check_blessed_identity(blessed_verifier)
        if identity_error is not None:
            return _error(VerifyStatus.ERROR, identity_error)

        pinned = _parse_image_words(list(pinned_image_id))
        if pinned is None:
            return _error(VerifyStatus.ERROR, "pinned_image_id must be 8 u32 words")

        request = json.dumps(
            {
                "schema": _DECODE_SCHEMA,
                "schema_version": 1,
                "proof_type": self._proof_type,
                "proof": base64.b64encode(bytes(proof_bytes)).decode("ascii"),
            },
            separators=(",", ":"),
        )
        try:
            proc = subprocess.run(
                [blessed_verifier.binary_path],
                input=request,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=self._timeout_s,
                check=False,
                env=_sanitized_env(),
            )
        except subprocess.TimeoutExpired:
            return _error(VerifyStatus.TIMEOUT, "blessed verifier timed out")
        except OSError as exc:
            return _error(VerifyStatus.ERROR, f"blessed verifier failed to run: {exc}")

        if proc.returncode != 0:
            return _error(
                VerifyStatus.ERROR,
                f"blessed verifier exited {proc.returncode}: {proc.stderr.strip()[-200:]}",
            )
        try:
            out = json.loads(proc.stdout)
        except json.JSONDecodeError:
            return _error(VerifyStatus.ERROR, "blessed verifier returned invalid JSON")
        if not isinstance(out, dict):
            return _error(VerifyStatus.ERROR, "blessed verifier returned non-object JSON")

        if out.get("ok") is not True:
            err = out.get("error")
            message = err if type(err) is str and err else "receipt verification failed"
            return _error(VerifyStatus.FAILED, message)

        if set(out.keys()) != _TOP_LEVEL_OK_KEYS:
            return _error(VerifyStatus.ERROR, "blessed verifier output shape mismatch")

        verifier_words = _parse_image_words(out.get("verifier_image_id_words"))
        if verifier_words is None:
            return _error(VerifyStatus.ERROR, "verifier_image_id_words malformed")
        # The client pin governs WHICH guest may attest: enforce it against the
        # verifier's compiled-in identity, never the proof's claim.
        if verifier_words != pinned:
            return _error(VerifyStatus.FAILED, "verifier image id does not match client pin")

        journal, parse_error = _parse_journal(out.get("journal"), _JOURNAL_SPECS[self._proof_type])
        if journal is None:
            return _error(VerifyStatus.ERROR, f"journal parse: {parse_error}")
        if journal["risc0_image_id"] != pinned:
            return _error(VerifyStatus.FAILED, "journal image id does not match client pin")

        return ReceiptVerifyResult(status=VerifyStatus.VERIFIED, journal=journal, error=None)
