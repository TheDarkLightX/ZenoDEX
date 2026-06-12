"""Bounded covert-channel assurance gates for ZenoDEX runtime kernels.

These tests pin three narrow properties:

* selected authority kernels do not import common side-input or I/O modules;
* optional trace capture does not influence replay-guard decisions or roots;
* public trace events and confidential-lane reason codes do not echo raw private
  inputs used by the test fixtures.

They are regression gates, not a universal noninterference proof.
"""

from __future__ import annotations

import ast
from pathlib import Path
from typing import Any

from src.core.confidential_extension_receipts import (
    make_confidential_extension_receipt,
    verify_confidential_extension_receipt,
)
from src.core.replay_guard import AdmitAccepted, AdmitRejected, ReplayGuardState, admit
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[2]

AUTHORITY_KERNEL_PATHS = (
    "src/state/canonical.py",
    "src/state/state_root.py",
    "src/state/support_root.py",
    "src/core/replay_guard.py",
    "src/core/balance_kernel.py",
    "src/core/fee_router.py",
    "src/core/burn_receipts.py",
    "src/core/confidential_extension_receipts.py",
    "src/core/uniform_batch_admission.py",
    "src/core/uniform_batch_clearing.py",
    "src/core/uniform_batch_optimality.py",
)

SIDE_INPUT_IMPORT_ROOTS = {
    "asyncio",
    "datetime",
    "httpx",
    "logging",
    "multiprocessing",
    "os",
    "platform",
    "random",
    "requests",
    "secrets",
    "socket",
    "subprocess",
    "threading",
    "time",
    "urllib",
    "uuid",
}

SIDE_INPUT_ATTR_PREFIXES = (
    "datetime.datetime.now",
    "datetime.datetime.utcnow",
    "datetime.date.today",
    "logging.",
    "os.environ",
    "os.getenv",
    "platform.",
    "random.",
    "secrets.",
    "socket.",
    "subprocess.",
    "time.",
    "uuid.",
)

SIDE_EFFECT_CALL_NAMES = {"__import__", "eval", "exec", "input", "open", "print"}

DENIED_PUBLIC_TRACE_KEY_PARTS = (
    "authorization",
    "bearer",
    "header",
    "measurement",
    "nonce",
    "operation",
    "payload",
    "private",
    "request",
    "secret",
    "sender",
    "signature",
    "strategy",
    "token",
)

PRIVATE_SENTINELS = (
    "DO_NOT_LEAK",
    "private-alpha-request",
    "private-beta-request",
    "secret_strategy",
    "0x" + "a1" * 48,
    "0x" + "b2" * 48,
)

SENDER_A = "0x" + "a1" * 48
SENDER_B = "0x" + "b2" * 48

POLICY_DIGEST = "0x" + "11" * 32
CONFIDENTIAL_MEASUREMENT = "nitro:pcr0:" + "aa" * 48 + ":pcr8:" + "bb" * 48


def _attr_name(node: ast.AST) -> str | None:
    parts: list[str] = []
    cur = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        parts.append(cur.id)
        return ".".join(reversed(parts))
    return None


def test_authority_kernels_do_not_depend_on_common_side_inputs():
    violations: list[str] = []
    for rel in AUTHORITY_KERNEL_PATHS:
        path = ROOT / rel
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    root = alias.name.split(".", 1)[0]
                    if root in SIDE_INPUT_IMPORT_ROOTS:
                        violations.append(f"{rel}:{node.lineno} imports {alias.name}")
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    root = node.module.split(".", 1)[0]
                    if root in SIDE_INPUT_IMPORT_ROOTS:
                        violations.append(f"{rel}:{node.lineno} imports from {node.module}")
            elif isinstance(node, ast.Call):
                if isinstance(node.func, ast.Name) and node.func.id in SIDE_EFFECT_CALL_NAMES:
                    violations.append(f"{rel}:{node.lineno} calls {node.func.id}()")
                attr = _attr_name(node.func)
                if attr and any(
                    attr == prefix.rstrip(".") or attr.startswith(prefix)
                    for prefix in SIDE_INPUT_ATTR_PREFIXES
                ):
                    violations.append(f"{rel}:{node.lineno} calls {attr}()")

    assert not violations


def _public_digest(surface: str, private_input: Any) -> str:
    return sha256_hex(
        domain_sep_bytes(f"covert_channel_trace.{surface}")
        + canonical_json_bytes(private_input)
    )


def _public_replay_trace_event(
    *,
    step: int,
    pre_root: str,
    post_root: str,
    result: AdmitAccepted | AdmitRejected,
    private_input: dict[str, Any],
) -> dict[str, Any]:
    accepted = isinstance(result, AdmitAccepted)
    return {
        "version": 1,
        "surface": "replay_guard",
        "step": step,
        "decision": "accept" if accepted else "reject",
        "reason_code": None if accepted else result.reason,
        "input_digest": _public_digest("replay_guard", private_input),
        "pre_state_root": pre_root,
        "post_state_root": post_root,
    }


def _public_confidential_trace_event(*, ok: bool, reason: str) -> dict[str, Any]:
    return {
        "version": 1,
        "surface": "confidential_extension_receipt",
        "decision": "accept" if ok else "reject",
        "reason_code": reason,
    }


def _assert_public_trace_shape(value: Any, *, extra_denied_terms: tuple[str, ...] = ()) -> None:
    denied_terms = PRIVATE_SENTINELS + extra_denied_terms

    def visit(obj: Any) -> None:
        if isinstance(obj, dict):
            for key, item in obj.items():
                assert isinstance(key, str)
                lowered = key.lower()
                assert not any(part in lowered for part in DENIED_PUBLIC_TRACE_KEY_PARTS), key
                visit(item)
            return
        if isinstance(obj, (list, tuple)):
            for item in obj:
                visit(item)
            return
        if isinstance(obj, str):
            for term in denied_terms:
                assert term not in obj, (term, obj)

    visit(value)


def _run_replay_sequence(*, capture_trace: bool) -> tuple[str, list[tuple[bool, str | None]], list[dict[str, Any]]]:
    state = ReplayGuardState()
    decisions: list[tuple[bool, str | None]] = []
    traces: list[dict[str, Any]] = []
    calls = (
        (SENDER_A, 1),
        (SENDER_A, 1),
        (SENDER_A, 3),
        (SENDER_A, 2),
        (SENDER_B, 1),
        ("0xzz" + "33" * 47, 1),
        (SENDER_B, 0),
    )

    for step, (sender, nonce) in enumerate(calls):
        pre_root = state.state_root()
        result = admit(state=state, sender=sender, nonce=nonce)
        accepted = isinstance(result, AdmitAccepted)
        if accepted:
            state = result.state
        post_root = state.state_root()
        decisions.append((accepted, None if accepted else result.reason))
        if capture_trace:
            traces.append(
                _public_replay_trace_event(
                    step=step,
                    pre_root=pre_root,
                    post_root=post_root,
                    result=result,
                    private_input={
                        "sender": sender,
                        "nonce": nonce,
                        "secret_strategy": "DO_NOT_LEAK",
                    },
                )
            )

    return state.state_root(), decisions, traces


def test_trace_capture_does_not_change_replay_decisions_or_state_root():
    root_without_trace, decisions_without_trace, no_trace = _run_replay_sequence(capture_trace=False)
    root_with_trace, decisions_with_trace, traces = _run_replay_sequence(capture_trace=True)

    assert no_trace == []
    assert decisions_with_trace == decisions_without_trace
    assert root_with_trace == root_without_trace
    assert {reason for _ok, reason in decisions_with_trace} == {
        None,
        "duplicate_nonce",
        "nonce_gap",
        "invalid_sender",
        "invalid_nonce",
    }
    assert len(traces) == 7
    for event in traces:
        _assert_public_trace_shape(event)


def _confidential_receipt(request_id: str) -> dict[str, Any]:
    return make_confidential_extension_receipt(
        extension_id="sealed-bid-alpha",
        provider_id="tee-provider-1",
        request_id=request_id,
        policy_version="policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=CONFIDENTIAL_MEASUREMENT,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=9,
        max_attestation_age=5,
        fee_charged=3,
        receipt_fee=3,
        credit_before=10,
        credit_after=7,
        provider_balance_before=4,
        provider_balance_after=7,
    )


def test_confidential_receipt_reason_code_does_not_echo_private_request_or_measurement():
    receipt_a = _confidential_receipt("private-alpha-request-DO_NOT_LEAK")
    receipt_b = _confidential_receipt("private-beta-request-DO_NOT_LEAK")

    ok_a, reason_a = verify_confidential_extension_receipt(receipt_a, approved_measurements=set())
    ok_b, reason_b = verify_confidential_extension_receipt(receipt_b, approved_measurements=set())

    assert (ok_a, reason_a) == (False, "measurement_not_approved")
    assert (ok_b, reason_b) == (False, "measurement_not_approved")
    assert reason_a == reason_b

    approved_a = verify_confidential_extension_receipt(
        receipt_a,
        approved_measurements={CONFIDENTIAL_MEASUREMENT},
    )
    approved_b = verify_confidential_extension_receipt(
        receipt_b,
        approved_measurements={CONFIDENTIAL_MEASUREMENT},
    )
    assert approved_a == (True, "ok")
    assert approved_b == (True, "ok")

    private_terms = (
        CONFIDENTIAL_MEASUREMENT,
        receipt_a["body"]["request_id"],
        receipt_b["body"]["request_id"],
        receipt_a["receipt_hash"],
        receipt_b["receipt_hash"],
    )
    for ok, reason in ((ok_a, reason_a), (ok_b, reason_b), approved_a, approved_b):
        event = _public_confidential_trace_event(ok=ok, reason=reason)
        _assert_public_trace_shape(event, extra_denied_terms=private_terms)
