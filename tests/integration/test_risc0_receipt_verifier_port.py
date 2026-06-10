"""Fail-closed corpus for the production Risc0CliReceiptVerifierPort.

Strategy: the port's parsing/identity behavior is exercised against FAKE blessed
binaries (tiny generated scripts whose sha256 we pin, so the identity gate
passes and the stage under test is reached). The REAL cryptographic path is
covered by tests/integration/test_ws2_refuse_loop_e2e_risc0.py against a real
STARK; nothing here claims receipt-verification itself.

Every non-VERIFIED status must carry journal=None — the decision core treats the
journal as fabricated bytes until the port says VERIFIED.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from pathlib import Path
from typing import Any

import pytest

from src.integration.client_admission_decision import VerifierIdentity, VerifyStatus
from src.integration.risc0_receipt_verifier_port import Risc0CliReceiptVerifierPort

PERPS_PT = "risc0.zenodex_perps_np_transition.v1"
IMAGE_WORDS = [1, 2, 3, 4, 5, 6, 7, 8]
PIN = tuple(IMAGE_WORDS)


def _valid_journal() -> dict[str, Any]:
    return {
        "proof_type": PERPS_PT,
        "risc0_image_id": list(IMAGE_WORDS),
        "state_hash": "ab" * 32,
        "chain_id": "devnet",
        "pre_app_hash_present": True,
        "pre_app_hash": "11" * 32,
        "post_app_hash": "22" * 32,
        "operation_hash": "33" * 32,
        "state_delta_hash": "44" * 32,
        "oracle_binding_hash": "55" * 32,
        "collateral_binding_hash": "66" * 32,
        "participant_set_hash": "77" * 32,
        "receipt_root": "88" * 32,
        "participant_count": 4,
        "net_position_base": "0",
        "total_collateral_e8": "500040000",
        "funding_residual_e8": "-1",
        "matched_base_volume": "0",
    }


def _valid_output(journal: dict[str, Any] | None = None) -> dict[str, Any]:
    return {
        "ok": True,
        "verifier_image_id": "00" * 32,
        "verifier_image_id_words": list(IMAGE_WORDS),
        "journal": journal if journal is not None else _valid_journal(),
    }


def _make_fake_binary(tmp_path: Path, name: str, body: str) -> VerifierIdentity:
    """Write an executable python script and pin ITS sha256 (identity passes)."""
    path = tmp_path / name
    path.write_text(f"#!/usr/bin/env python3\n{body}\n")
    path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return VerifierIdentity(
        expected_cmd_hash=digest, binary_path=str(path), allow_path_lookup=False
    )


def _emitting_binary(tmp_path: Path, name: str, payload: Any) -> VerifierIdentity:
    body = f"import sys, json\nsys.stdin.read()\nprint(json.dumps({payload!r}))"
    return _make_fake_binary(tmp_path, name, body)


def _verify(blessed: VerifierIdentity, *, pin: tuple[int, ...] = PIN, timeout: float = 30.0):
    port = Risc0CliReceiptVerifierPort(PERPS_PT, timeout_s=timeout)
    return port.verify_receipt(b"receipt-bytes", pin, blessed_verifier=blessed)


def test_unsupported_proof_type_rejected_at_construction() -> None:
    with pytest.raises(ValueError):
        Risc0CliReceiptVerifierPort("risc0.zenodex_unknown.v1")


def test_dev_mode_and_loader_env_are_scrubbed(tmp_path: Path, monkeypatch) -> None:
    # The sha256 pin proves WHICH binary runs, not under WHICH mode. A client
    # started with RISC0_DEV_MODE=1 (un-proven dev receipts "verify") or a loader
    # override must NOT leak into the verifier process. The fake binary verifies
    # ok ONLY if its environment is clean.
    monkeypatch.setenv("RISC0_DEV_MODE", "1")
    monkeypatch.setenv("RISC0_SOMETHING", "x")
    monkeypatch.setenv("LD_PRELOAD", "/evil/lib.so")
    monkeypatch.setenv("DYLD_INSERT_LIBRARIES", "/evil/dylib")
    body = (
        "import os, sys, json\n"
        "sys.stdin.read()\n"
        "bad = (os.environ.get('RISC0_DEV_MODE') != '0'\n"
        "       or any(k.startswith(('RISC0_','LD_','DYLD_')) and k != 'RISC0_DEV_MODE'\n"
        "              for k in os.environ))\n"
        "print(json.dumps({'ok': False, 'error': 'dirty-env'} if bad else "
        f"{_valid_output()!r}))"
    )
    blessed = _make_fake_binary(tmp_path, "envcheck.py", body)
    result = _verify(blessed)
    assert result.status == VerifyStatus.VERIFIED, result.error
    assert result.journal is not None


# --------------------------------------------------------------------------- #
# (a) blessed identity: never run an unpinned binary
# --------------------------------------------------------------------------- #
def test_identity_refuses_path_lookup(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "v.py", _valid_output())
    relaxed = VerifierIdentity(
        expected_cmd_hash=blessed.expected_cmd_hash,
        binary_path=blessed.binary_path,
        allow_path_lookup=True,
    )
    result = _verify(relaxed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_identity_refuses_relative_path(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "v.py", _valid_output())
    relative = VerifierIdentity(
        expected_cmd_hash=blessed.expected_cmd_hash,
        binary_path=os.path.relpath(blessed.binary_path),
        allow_path_lookup=False,
    )
    result = _verify(relative)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_identity_refuses_missing_binary(tmp_path: Path) -> None:
    blessed = VerifierIdentity(
        expected_cmd_hash="ab" * 32, binary_path=str(tmp_path / "absent"), allow_path_lookup=False
    )
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_identity_refuses_hash_mismatch(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "v.py", _valid_output())
    wrong = VerifierIdentity(
        expected_cmd_hash="00" * 32, binary_path=blessed.binary_path, allow_path_lookup=False
    )
    result = _verify(wrong)
    assert result.status == VerifyStatus.ERROR and result.journal is None
    assert "hash mismatch" in (result.error or "")


def test_identity_refuses_malformed_pin_hash(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "v.py", _valid_output())
    malformed = VerifierIdentity(
        expected_cmd_hash="not-hex", binary_path=blessed.binary_path, allow_path_lookup=False
    )
    result = _verify(malformed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_tampered_binary_fails_identity(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "v.py", _valid_output())
    with open(blessed.binary_path, "a") as fh:
        fh.write("# tampered\n")
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


# --------------------------------------------------------------------------- #
# (b/c) process + output mapping
# --------------------------------------------------------------------------- #
def test_timeout_maps_to_timeout(tmp_path: Path) -> None:
    blessed = _make_fake_binary(tmp_path, "slow.py", "import time\ntime.sleep(5)")
    result = _verify(blessed, timeout=0.5)
    assert result.status == VerifyStatus.TIMEOUT and result.journal is None


def test_nonzero_exit_maps_to_error(tmp_path: Path) -> None:
    blessed = _make_fake_binary(tmp_path, "boom.py", "import sys\nsys.exit(2)")
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_invalid_json_maps_to_error(tmp_path: Path) -> None:
    blessed = _make_fake_binary(tmp_path, "garbage.py", "print('not-json')")
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_ok_false_maps_to_failed_with_error(tmp_path: Path) -> None:
    blessed = _emitting_binary(
        tmp_path, "rej.py", {"ok": False, "error": "receipt verification failed: bad seal"}
    )
    result = _verify(blessed)
    assert result.status == VerifyStatus.FAILED and result.journal is None
    assert "bad seal" in (result.error or "")


def test_host_style_fake_green_fields_do_not_accept(tmp_path: Path) -> None:
    # A compromised wrapper echoing success-flavoured fields without the contract
    # shape must NOT verify (closed top-level set).
    payload = {**_valid_output(), "production_security_claim": True, "is_final": True}
    blessed = _emitting_binary(tmp_path, "fake.py", payload)
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


# --------------------------------------------------------------------------- #
# (c) the client pin governs: verifier identity words must equal the pin
# --------------------------------------------------------------------------- #
def test_verifier_image_words_must_match_pin(tmp_path: Path) -> None:
    out = _valid_output()
    out["verifier_image_id_words"] = [9, 9, 9, 9, 9, 9, 9, 9]
    blessed = _emitting_binary(tmp_path, "wrongid.py", out)
    result = _verify(blessed)
    assert result.status == VerifyStatus.FAILED and result.journal is None
    assert "client pin" in (result.error or "")


def test_journal_image_words_must_match_pin(tmp_path: Path) -> None:
    journal = _valid_journal()
    journal["risc0_image_id"] = [9, 9, 9, 9, 9, 9, 9, 9]
    blessed = _emitting_binary(tmp_path, "wrongjid.py", _valid_output(journal))
    result = _verify(blessed)
    assert result.status == VerifyStatus.FAILED and result.journal is None


def test_malformed_pin_is_error(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "v.py", _valid_output())
    result = _verify(blessed, pin=(1, 2, 3))
    assert result.status == VerifyStatus.ERROR and result.journal is None


# --------------------------------------------------------------------------- #
# (d) strict closed-shape journal parse
# --------------------------------------------------------------------------- #
def test_valid_output_verifies_with_typed_journal(tmp_path: Path) -> None:
    blessed = _emitting_binary(tmp_path, "good.py", _valid_output())
    result = _verify(blessed)
    assert result.status == VerifyStatus.VERIFIED
    journal = result.journal
    assert journal is not None
    assert journal["pre_app_hash"] == bytes.fromhex("11" * 32)
    assert journal["post_app_hash"] == bytes.fromhex("22" * 32)
    assert journal["risc0_image_id"] == PIN
    assert journal["pre_app_hash_present"] is True
    assert journal["funding_residual_e8"] == -1
    assert journal["participant_count"] == 4


@pytest.mark.parametrize(
    "mutate",
    [
        lambda j: j.pop("operation_hash"),  # missing key
        lambda j: j.update(extra="x"),  # unknown key
        lambda j: j.update(operation_hash="33" * 31),  # short hex
        lambda j: j.update(operation_hash="ZZ" * 32),  # non-hex
        lambda j: j.update(operation_hash=b"33"),  # wrong type (not JSON-str)
        lambda j: j.update(pre_app_hash_present="true"),  # str-as-bool
        lambda j: j.update(pre_app_hash_present=1),  # int-as-bool
        lambda j: j.update(participant_count="4"),  # str-as-uint
        lambda j: j.update(participant_count=True),  # bool-as-uint
        lambda j: j.update(participant_count=-1),
        lambda j: j.update(net_position_base="0x0"),  # non-decimal int_str
        lambda j: j.update(net_position_base=0),  # number where string expected
        lambda j: j.update(chain_id=""),
        lambda j: j.update(proof_type=None),
        lambda j: j.update(risc0_image_id=[1, 2, 3]),
        lambda j: j.update(risc0_image_id=[True, 2, 3, 4, 5, 6, 7, 8]),
    ],
)
def test_journal_shape_violations_are_errors(tmp_path: Path, mutate) -> None:
    journal = _valid_journal()
    mutate(journal)
    blessed = _emitting_binary(tmp_path, "mut.py", _valid_output(journal))
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_top_level_shape_violations_are_errors(tmp_path: Path) -> None:
    out = _valid_output()
    del out["verifier_image_id"]
    blessed = _emitting_binary(tmp_path, "top.py", out)
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None


def test_ok_true_non_dict_journal_is_error(tmp_path: Path) -> None:
    out = _valid_output()
    out["journal"] = "[]"
    blessed = _emitting_binary(tmp_path, "nj.py", out)
    result = _verify(blessed)
    assert result.status == VerifyStatus.ERROR and result.journal is None
