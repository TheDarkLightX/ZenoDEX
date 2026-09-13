"""Opt-in actual guest execution correspondence; no cryptographic receipt claim.

Run against freshly built execute_margin_frame_v2 and a pinned r0vm. The evidence
record must retain their hashes. This suite does not replace receipt/publication
qualification and has no fallback emulator or protocol stub.
"""

import hashlib
import os
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.perps_margin_receipt_v2 import (
    encode_perps_margin_frame_v2,
    replay_perps_margin_frame_v2,
)
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration import global_receipt_verifier_v1 as receipt_bridge
from tests.core.test_perps_margin_global_v2 import (
    CLOSE,
    DEPOSIT,
    WITHDRAW,
    _command,
    _initial,
    _occurrence,
)
from tests.core.test_perps_margin_receipt_v2 import _frame_from_parts, _frame_parts


@pytest.fixture(scope="module")
def actual_margin_executor():
    binary = os.environ.get("ZENODEX_MARGIN_EXECUTOR")
    r0vm = os.environ.get("ZENODEX_MARGIN_R0VM")
    if binary is None and r0vm is None:
        pytest.skip("actual guest execution unqualified: configure executor and pinned r0vm")
    assert binary and r0vm, "both actual guest executor paths are required"
    for path in (binary, r0vm):
        assert Path(path).is_absolute() and Path(path).is_file(), path
    return [binary, r0vm]


def _execute(executor, frame):
    outer = len(frame).to_bytes(4, "little") + frame
    return subprocess.run(executor, input=outer, capture_output=True, timeout=60, check=False)


def test_actual_guest_connected_deposit_drain_refill_close(actual_margin_executor):
    inputs = _initial()
    for nonce, (kind, amount) in enumerate(((DEPOSIT, 40), (WITHDRAW, 10), (WITHDRAW, 30),
                                           (DEPOSIT, 20), (WITHDRAW, 20), (CLOSE, 0)), start=1):
        command = _command(kind, amount, nonce)
        request = PerpsMarginRequestV2(command, _occurrence(inputs[2], command, nonce))
        frame = encode_perps_margin_frame_v2(*inputs, request)
        expected = replay_perps_margin_frame_v2(frame)
        actual = _execute(actual_margin_executor, frame)
        assert actual.returncode == 0, actual.stderr
        assert actual.stdout == expected.statement
        assert actual.stderr.startswith(b"execution only; user cycles:")
        result = expected.result
        inputs = result.post_assets, result.post_margin, result.post_state
    assert inputs[1].economic_state.accounts[0].status.value == "CLOSED"
    assert not inputs[2].custody and not inputs[2].liabilities


@pytest.mark.parametrize("mutation", ("zero", "overspend", "unauthorized", "stale", "body", "canonical", "trailing"))
def test_actual_guest_rejects_without_committing_a_journal(actual_margin_executor, mutation):
    inputs = _initial()
    amount = {"zero": 0, "overspend": 101}.get(mutation, 1)
    command = _command(DEPOSIT, amount, 1)
    occurrence = _occurrence(inputs[2], command, 1)
    if mutation == "unauthorized":
        occurrence = replace(occurrence, subject_id="mallory")
    elif mutation in ("stale", "body"):
        field = "pre_state_root" if mutation == "stale" else "command_body_hash"
        occurrence = replace(occurrence, **{field: "0x" + "ab" * 32})
    frame = encode_perps_margin_frame_v2(*inputs, PerpsMarginRequestV2(command, occurrence))
    if mutation == "canonical":
        parts = _frame_parts(frame)
        frame = _frame_from_parts((*parts[:3], parts[3] + b" "))
    elif mutation == "trailing":
        frame += b"x"
    with pytest.raises(ValueError):
        replay_perps_margin_frame_v2(frame)
    actual = _execute(actual_margin_executor, frame)
    assert actual.returncode == 2 and not actual.stdout, actual
    assert b"guest execution rejected:" in actual.stderr


def test_actual_verifier_image_binding_and_measured_python_launch(actual_margin_executor):
    verifier_path = Path(actual_margin_executor[0]).parent.parent / "verify_margin_receipt_v2"
    assert verifier_path.is_file()
    # Independent of the verifier request: measured candidate pin retained by
    # the native image test. Correct-image rejection must reach receipt decoding.
    words = (2623568652, 651265610, 1043979988, 1361420132, 2865992097, 3697114616, 2674229025, 75673820)
    image = "0x" + b"".join(word.to_bytes(4, "little") for word in words).hex()
    for supplied, reason in ((image, b"ReceiptEncoding"), ("0x" + "ab" * 32, b"ImageBinding")):
        frame = receipt_bridge._encode_request_v1(b"{}", supplied, b"journal")
        result = subprocess.run([str(verifier_path)], input=frame, capture_output=True,
                                timeout=30, check=False)
        assert result.returncode == 2 and not result.stdout
        assert result.stderr == b"receipt verifier rejected: " + reason + b"\n"
    verifier = receipt_bridge.GlobalReceiptVerifierV1(
        str(verifier_path), hashlib.sha256(verifier_path.read_bytes()).hexdigest(), image, 30_000,
    )
    with pytest.raises(receipt_bridge.GlobalReceiptVerifierErrorV1) as caught:
        verifier.verify_succinct_receipt(b"{}", expected_image_id=image, expected_journal_bytes=b"journal")
    assert caught.value.reason is receipt_bridge.GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED
