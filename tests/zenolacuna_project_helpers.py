"""Test-only keys and independently readable finite project fixtures."""

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.zenolacuna.codec import encode
from src.zenolacuna.model import (
    Hypothesis,
    Outcome,
    OutcomeKind,
    Profile,
    Question,
    Requirement,
    Scope,
)

OWNER_SECRET = bytes(range(32))
AGENT_SECRET = bytes(reversed(range(32)))


def public_key(secret: bytes = OWNER_SECRET) -> str:
    return Ed25519PrivateKey.from_private_bytes(secret).public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw,
    ).hex()


def scope() -> Scope:
    return Scope(
        "owner-contract", ("positive", "choice"),
        (Outcome("allow", "allow", OutcomeKind.ACCEPT), Outcome("deny", "deny", OutcomeKind.REJECT)), (0, 1),
        ((0,), (0, 1)),
        (Requirement("positive", (0,), ((0,), (0, 1)), ((0,), ())),),
        (Hypothesis("h1", ((0,), (0,))), Hypothesis("h2", ((0,), (1,))),
         Hypothesis("h3", ((0,), (0,)))),
        (Question("choice", "Allow the optional operation?", 1, ("yes", "no", "yes")),),
        profile=Profile.REAL_OWNER,
    )


def payload(value: object) -> bytes:
    return encode(value)
