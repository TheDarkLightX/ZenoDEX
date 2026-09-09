"""Falsifiable vectors for the ZenoLacuna signed-command boundary."""

from __future__ import annotations

import base64
import json
from dataclasses import replace

import pytest
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.zenolacuna.authority import (
    MAX_PAYLOAD_BYTES,
    MAX_WIRE_BYTES,
    Action,
    Command,
    Delegation,
    SignedCommand,
    command_root,
    decode_delegation,
    decode_signed,
    encode_delegation,
    encode_signed,
    sign,
    verify,
)
from src.zenolacuna.model import LacunaError

OWNER_SEED = bytes.fromhex("11" * 32)
DELEGATE_SEED = bytes.fromhex("22" * 32)
OTHER_SEED = bytes.fromhex("33" * 32)
SCOPE_ROOT = "a" * 64
PARENT_ROOT = "b" * 64


def _public_key(seed: bytes) -> str:
    return Ed25519PrivateKey.from_private_bytes(seed).public_key().public_bytes_raw().hex()


OWNER_KEY = _public_key(OWNER_SEED)
DELEGATE_KEY = _public_key(DELEGATE_SEED)
OTHER_KEY = _public_key(OTHER_SEED)


def _payload(scope_root: str = SCOPE_ROOT, **extra: object) -> bytes:
    value: dict[str, object] = {"scope_root": scope_root, **extra}
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii") + b"\n"


def _command(action: Action = Action.ANSWER, *, parent: str | None = PARENT_ROOT, payload: bytes | None = None) -> Command:
    return Command("release-project", parent, action, _payload() if payload is None else payload)


def _delegation(*actions: Action, scope_root: str = SCOPE_ROOT) -> Delegation:
    return Delegation(DELEGATE_KEY, scope_root, tuple(actions))


def _code(callable_object: object, *args: object, **kwargs: object) -> str:
    with pytest.raises(LacunaError) as raised:
        callable_object(*args, **kwargs)  # type: ignore[operator]
    return raised.value.code


def test_given_owner_signed_command_when_encoded_and_decoded_then_exact_value_roundtrips() -> None:
    signed = sign(_command(Action.REVISE), OWNER_SEED)

    assert isinstance(signed, SignedCommand)
    assert decode_signed(encode_signed(signed)) == signed
    assert encode_signed(signed).endswith(b"\n")
    assert len(signed.public_key) == 64
    assert len(signed.signature) == 128


@pytest.mark.parametrize("action", tuple(Action))
def test_given_owner_key_when_any_action_is_signed_then_verification_accepts(action: Action) -> None:
    verify(sign(_command(action), OWNER_SEED), owner_key=OWNER_KEY, delegates=(), scope_root=SCOPE_ROOT)


@pytest.mark.parametrize("action", (Action.ANSWER, Action.ASSESS, Action.COMPLETE))
def test_given_exact_scoped_delegate_when_allowed_action_is_signed_then_verification_accepts(action: Action) -> None:
    signed = sign(_command(action), DELEGATE_SEED)

    verify(
        signed,
        owner_key=OWNER_KEY,
        delegates=(_delegation(action),),
        scope_root=SCOPE_ROOT,
    )


@pytest.mark.parametrize("action", (Action.INIT, Action.REVISE, Action.CANCEL, Action.RESUME))
def test_given_delegate_when_owner_only_action_is_signed_then_verification_rejects(action: Action) -> None:
    signed = sign(_command(action), DELEGATE_SEED)

    assert _code(
        verify,
        signed,
        owner_key=OWNER_KEY,
        delegates=(_delegation(action),),
        scope_root=SCOPE_ROOT,
    ) == "UNAUTHORIZED"


def test_given_delegate_when_scope_is_different_then_verification_rejects() -> None:
    signed = sign(_command(Action.ANSWER), DELEGATE_SEED)

    assert _code(
        verify,
        signed,
        owner_key=OWNER_KEY,
        delegates=(_delegation(Action.ANSWER, scope_root="c" * 64),),
        scope_root=SCOPE_ROOT,
    ) == "UNAUTHORIZED"


@pytest.mark.parametrize("field", ("project_id", "parent", "action", "payload"))
def test_tampering_each_signed_command_field_rejects_with_invalid_signature(field: str) -> None:
    signed = sign(_command(), OWNER_SEED)
    command = signed.command
    changed: Command
    if field == "project_id":
        changed = replace(command, project_id="other-project")
    elif field == "parent":
        changed = replace(command, parent="c" * 64)
    elif field == "action":
        changed = replace(command, action=Action.ASSESS)
    else:
        changed = replace(command, payload=_payload(answer="changed"))

    assert _code(verify, replace(signed, command=changed), owner_key=OWNER_KEY, delegates=(), scope_root=SCOPE_ROOT) == "INVALID_SIGNATURE"


def test_given_key_substitution_when_signature_is_unchanged_then_verification_rejects() -> None:
    signed = sign(_command(), OWNER_SEED)

    assert _code(
        verify,
        replace(signed, public_key=OTHER_KEY),
        owner_key=OWNER_KEY,
        delegates=(),
        scope_root=SCOPE_ROOT,
    ) == "INVALID_SIGNATURE"


def test_given_unknown_signer_with_valid_signature_when_verified_then_unauthorized() -> None:
    signed = sign(_command(), OTHER_SEED)

    assert _code(verify, signed, owner_key=OWNER_KEY, delegates=(), scope_root=SCOPE_ROOT) == "UNAUTHORIZED"


def test_given_delegation_when_action_order_is_not_canonical_or_repeated_then_rejects() -> None:
    assert _code(Delegation, DELEGATE_KEY, SCOPE_ROOT, (Action.COMPLETE, Action.ANSWER)) == "MALFORMED_APPROVAL"
    assert _code(Delegation, DELEGATE_KEY, SCOPE_ROOT, (Action.ANSWER, Action.ANSWER)) == "MALFORMED_APPROVAL"


def test_delegation_wire_roundtrip_is_canonical_and_closed() -> None:
    delegation = _delegation(Action.ANSWER, Action.COMPLETE)
    raw = encode_delegation(delegation)

    assert decode_delegation(raw) == delegation
    payload = json.loads(raw)
    payload["extra"] = 1
    assert _code(decode_delegation, json.dumps(payload).encode()) == "MALFORMED_APPROVAL"


@pytest.mark.parametrize(
    "raw",
    (
        b"",
        b"{}\n",
        b'{"version":1.0}\n',
        b'{"version":1,"version":1,"command":{},"public_key":"","signature":""}\n',
        b'{"version":1,"command":{},"public_key":"NaN","signature":""}\n',
    ),
)
def test_malformed_or_noncanonical_signed_wire_rejects(raw: bytes) -> None:
    assert _code(decode_signed, raw) == "MALFORMED_APPROVAL"


def test_payload_is_required_to_be_canonical_ascii_json_dictionary() -> None:
    for payload in (b"[]\n", b'{ "scope_root": "' + SCOPE_ROOT.encode() + b'"}\n', b'{"scope_root":1.0}\n'):
        assert _code(Command, "p", PARENT_ROOT, Action.ANSWER, payload) == "MALFORMED_APPROVAL"


def test_payload_duplicate_nan_and_float_values_are_rejected() -> None:
    for payload in (
        b'{"scope_root":"' + SCOPE_ROOT.encode() + b'","scope_root":"' + SCOPE_ROOT.encode() + b'"}\n',
        b'{"scope_root":NaN}\n',
        b'{"scope_root":1.5}\n',
    ):
        assert _code(Command, "p", PARENT_ROOT, Action.ANSWER, payload) == "MALFORMED_APPROVAL"


def test_payload_depth_and_size_bounds_fail_closed() -> None:
    deep = b'{"x":' * 33 + b"{}" + b"}" * 33 + b"\n"
    assert _code(Command, "p", PARENT_ROOT, Action.ANSWER, deep) == "MALFORMED_APPROVAL"
    oversized = b'{"x":"' + b"x" * (MAX_PAYLOAD_BYTES + 1) + b'"}\n'
    assert _code(Command, "p", PARENT_ROOT, Action.ANSWER, oversized) == "MALFORMED_APPROVAL"


def test_signed_wire_rejects_noncanonical_payload_base64_and_oversize_wire() -> None:
    signed = sign(_command(), OWNER_SEED)
    raw = encode_signed(signed)
    outer = json.loads(raw)
    outer["command"]["payload"] = base64.b64encode(b'{"scope_root": "' + SCOPE_ROOT.encode() + b'"}\n').decode()
    assert _code(decode_signed, json.dumps(outer).encode()) == "MALFORMED_APPROVAL"
    assert _code(decode_signed, b" " * (MAX_WIRE_BYTES + 1)) == "MALFORMED_APPROVAL"


def test_parent_project_and_scope_roots_are_strict_lowercase_hex() -> None:
    assert _code(Command, "", None, Action.INIT, _payload()) == "MALFORMED_APPROVAL"
    assert _code(Command, "unsafe/project", None, Action.INIT, _payload()) == "MALFORMED_APPROVAL"
    assert _code(Command, "p", "A" * 64, Action.ANSWER, _payload()) == "MALFORMED_APPROVAL"
    assert _code(Delegation, DELEGATE_KEY, "A" * 64, (Action.ANSWER,)) == "MALFORMED_APPROVAL"


def test_command_root_is_domain_separated_and_binds_every_command_field() -> None:
    command = _command()
    roots = {
        command_root(command),
        command_root(replace(command, project_id="other-project")),
        command_root(replace(command, parent="c" * 64)),
        command_root(replace(command, action=Action.ASSESS)),
        command_root(replace(command, payload=_payload(answer="changed"))),
    }

    assert len(roots) == 5
    assert all(len(root) == 64 and root == root.lower() for root in roots)
