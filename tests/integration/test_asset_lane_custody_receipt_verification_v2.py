"""Protocol-only coverage for the conditional V2 custody receipt transport.

The child process fixture checks request framing and response binding.  It is
ordinary Python process evidence, not a RISC0 proof or receipt qualification.
"""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
from typing import Callable

import pytest

import src.integration.asset_lane_custody_receipt_verification_v2 as receipt
from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from src.integration import global_receipt_verifier_v1 as bridge
from tests.core.test_asset_lane_coordinator_v2 import _context
from tests.core.test_asset_lane_custody_statement_parity_v2 import CASES, typed_inputs
from tests.integration.test_global_receipt_verifier_v1 import (
    IMAGE,
    OTHER_IMAGE,
    backend,
    install_protocol_process,
)

_RECEIPT = b"protocol-fixture-receipt-is-not-proof"


def _expected_statement(case: dict[str, object]) -> bytes:
    return canonical_global_bytes_v2(case["statement"])


def _exact_protocol(expected_image_id: str, expected_journal: bytes) -> str:
    """Return a process that accepts only one fully bound V1 request."""
    image = bytes.fromhex(expected_image_id[2:])
    return f"""
import hashlib
import struct
import sys

request = sys.stdin.buffer.read()
expected_image = {image!r}
expected_journal = {expected_journal!r}
journal_length, receipt_length = struct.unpack("<II", request[40:48])
if (
    request[:8] != b"ZDXRV1RQ"
    or request[8:40] != expected_image
    or journal_length != len(expected_journal)
    or receipt_length != {len(_RECEIPT)}
    or request[48 : 48 + journal_length] != expected_journal
    or request[48 + journal_length :] != {_RECEIPT!r}
):
    raise SystemExit(2)
sys.stdout.buffer.write(b"ZDXRV1OK" + hashlib.sha256(request).digest() + expected_image)
"""


def _call(
    case: dict[str, object], verifier: bridge.GlobalReceiptVerifierV1
) -> bytes | AssetLaneRejectedV2:
    return receipt.verify_asset_lane_custody_global_receipt_v2(
        *typed_inputs(case),
        receipt_bytes=_RECEIPT,
        verifier=verifier,
    )


def _forbid_launch(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*_: object, **__: object) -> None:
        pytest.fail("input reached the receipt verifier process")

    monkeypatch.setattr(bridge.subprocess, "Popen", forbidden)


@pytest.mark.parametrize("case", CASES, ids=lambda case: str(case["name"]))
def test_native_golden_cases_bind_exact_image_and_prepared_journal(
    monkeypatch: pytest.MonkeyPatch,
    case: dict[str, object],
) -> None:
    expected = _expected_statement(case)
    verifier = backend()
    launched = install_protocol_process(
        monkeypatch,
        _exact_protocol(verifier.expected_image_id, expected),
    )

    actual = _call(case, verifier)

    assert type(actual) is bytes
    assert actual == expected
    assert len(launched) == 1
    assert launched[0].returncode == 0


def test_unauthorized_leaf_noop_returns_verbatim_without_receipt_launch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, pre_state, command, _, _ = typed_inputs(CASES[0])
    rejected_context = _context(command, subject="mallory")
    _forbid_launch(monkeypatch)

    actual = receipt.verify_asset_lane_custody_global_receipt_v2(
        rejected_context,
        pre_state,
        command,
        object(),  # type: ignore[arg-type]
        object(),  # type: ignore[arg-type]
        receipt_bytes=_RECEIPT,
        verifier=backend(),
    )

    assert type(actual) is AssetLaneRejectedV2
    assert actual.code.value == "UNAUTHORIZED_SUBJECT"
    assert actual.pre_state_root == actual.post_state_root == pre_state.state_root
    assert actual.effects.is_empty


def test_wrong_context_and_global_semantic_failure_never_launch_receipt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context, pre_state, command, global_pre, global_post = typed_inputs(CASES[0])
    wrong_context = AssetLaneContextV2(
        context.writer_epoch,
        context.module_release_id,
        "0x" + "03" * 32,
        context.occurrence,
    )
    _forbid_launch(monkeypatch)

    rejected = receipt.verify_asset_lane_custody_global_receipt_v2(
        wrong_context,
        pre_state,
        command,
        global_pre,
        global_post,
        receipt_bytes=_RECEIPT,
        verifier=backend(),
    )
    assert type(rejected) is AssetLaneRejectedV2
    assert rejected.effects.is_empty

    with pytest.raises(ValueError, match="replay post-state mismatch"):
        receipt.verify_asset_lane_custody_global_receipt_v2(
            context,
            pre_state,
            command,
            global_pre,
            replace(global_post, replay_state=()),
            receipt_bytes=_RECEIPT,
            verifier=backend(),
        )


class _VerifierSubclass(bridge.GlobalReceiptVerifierV1):
    __slots__ = ()


@pytest.mark.parametrize(
    "make_verifier",
    (
        lambda: object(),
        lambda: _VerifierSubclass(
            backend().executable_path,
            backend().executable_sha256,
            backend().expected_image_id,
            backend().timeout_ms,
        ),
        lambda: _invalid_timeout_verifier(),
    ),
    ids=("nonexact", "subclass", "invalid_config"),
)
def test_invalid_verifier_precedes_statement_preparation(
    monkeypatch: pytest.MonkeyPatch,
    make_verifier: Callable[[], object],
) -> None:
    called: list[object] = []

    def forbidden_preparation(*_: object) -> bytes:
        called.append(object())
        return b"unexpected"

    monkeypatch.setattr(
        receipt, "prepare_asset_lane_custody_global_statement_v2", forbidden_preparation
    )
    with pytest.raises((TypeError, ValueError)):
        receipt.verify_asset_lane_custody_global_receipt_v2(
            *typed_inputs(CASES[0]),
            receipt_bytes=_RECEIPT,
            verifier=make_verifier(),  # type: ignore[arg-type]
        )
    assert called == []


def _invalid_timeout_verifier() -> bridge.GlobalReceiptVerifierV1:
    verifier = backend()
    object.__setattr__(verifier, "timeout_ms", 0)
    return verifier


def test_verifier_snapshot_blocks_alias_mutation_during_preparation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = CASES[0]
    expected = _expected_statement(case)
    verifier = backend()
    launched = install_protocol_process(
        monkeypatch,
        _exact_protocol(IMAGE, expected),
    )
    original_prepare = receipt.prepare_asset_lane_custody_global_statement_v2

    def mutate_then_prepare(*args: object) -> bytes | AssetLaneRejectedV2:
        object.__setattr__(verifier, "expected_image_id", OTHER_IMAGE)
        object.__setattr__(verifier, "timeout_ms", 1)
        return original_prepare(*args)  # type: ignore[arg-type]

    monkeypatch.setattr(
        receipt, "prepare_asset_lane_custody_global_statement_v2", mutate_then_prepare
    )
    actual = _call(case, verifier)

    assert actual == expected
    assert len(launched) == 1


@pytest.mark.parametrize(
    "kind",
    ("empty_receipt", "unavailable", "rejected", "wrong_response_image"),
)
def test_native_verifier_rejections_propagate_unchanged(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    kind: str,
) -> None:
    case = CASES[0]
    verifier = backend()
    if kind == "empty_receipt":
        _forbid_launch(monkeypatch)
        receipt_bytes = b""
        expected = bridge.GlobalReceiptVerifierRejectV1.INPUT_BOUNDS
    elif kind == "unavailable":
        verifier = backend(executable_path=str(tmp_path / "missing-verifier"))
        receipt_bytes = _RECEIPT
        expected = bridge.GlobalReceiptVerifierRejectV1.EXECUTABLE_UNAVAILABLE
    elif kind == "rejected":
        install_protocol_process(monkeypatch, "import sys; sys.stdin.buffer.read(); sys.exit(2)")
        receipt_bytes = _RECEIPT
        expected = bridge.GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED
    else:
        install_protocol_process(
            monkeypatch,
            """
import hashlib
import sys
request = sys.stdin.buffer.read()
sys.stdout.buffer.write(b"ZDXRV1OK" + hashlib.sha256(request).digest() + b"\\x02" * 32)
""",
        )
        receipt_bytes = _RECEIPT
        expected = bridge.GlobalReceiptVerifierRejectV1.RESPONSE_BINDING

    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        receipt.verify_asset_lane_custody_global_receipt_v2(
            *typed_inputs(case),
            receipt_bytes=receipt_bytes,
            verifier=verifier,
        )
    assert error.value.reason is expected


def test_verifier_request_error_from_prepared_bytes_is_unmapped(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _forbid_launch(monkeypatch)
    monkeypatch.setattr(receipt, "prepare_asset_lane_custody_global_statement_v2", lambda *_: b"")

    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        _call(CASES[0], backend())

    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.INPUT_BOUNDS


def test_retry_reverifies_the_same_statement_without_mutating_inputs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = CASES[0]
    expected = _expected_statement(case)
    verifier = backend()
    launched = install_protocol_process(
        monkeypatch,
        _exact_protocol(verifier.expected_image_id, expected),
    )
    inputs = typed_inputs(case)
    before = tuple(canonical_global_bytes_v2(value.to_canonical()) for value in inputs)

    first = receipt.verify_asset_lane_custody_global_receipt_v2(
        *inputs,
        receipt_bytes=_RECEIPT,
        verifier=verifier,
    )
    second = receipt.verify_asset_lane_custody_global_receipt_v2(
        *inputs,
        receipt_bytes=_RECEIPT,
        verifier=verifier,
    )

    assert first == second == expected
    assert len(launched) == 2
    assert tuple(canonical_global_bytes_v2(value.to_canonical()) for value in inputs) == before
