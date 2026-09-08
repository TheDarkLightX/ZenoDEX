"""Original bounded message-format implementation alternatives."""

from __future__ import annotations

from .models import Stage, Task
from .programs import Program


def program(name: str, expression: str) -> Program:
    return Program(name, f"def transform(x):\n    return {expression}\n".encode())


def message_task() -> Task:
    """Three owners share the end-to-end requirement of 64 exact round trips."""
    encoder = Stage("encoder", (
        program("raw_mask", "x & 63"), program("raw_mod", "x % 64"),
        program("tag_v1_or", "(x & 63) | 64"), program("tag_v1_add", "x % 64 + 64"),
        program("tag_v2_or", "(x & 63) | 128"), program("tag_v2_add", "x % 64 + 128"),
        program("tag_both_or", "(x & 63) | 192"), program("tag_both_add", "x % 64 + 192"),
    ))
    adapter = Stage("adapter", (
        program("identity", "x"), program("identity_xor", "x ^ 0"),
        program("strip_mask", "x & 63"), program("strip_mod", "x % 64"),
        program("keep_v1_mask", "x & 127"), program("keep_v1_mod", "x % 128"),
        program("v2_to_v1_or", "(x & 63) | ((x & 128) >> 1)"),
        program("v2_to_v1_add", "x % 64 + (x // 128) * 64"),
    ))
    decoder = Stage("decoder", (
        program("legacy_lt", "x if x < 64 else 0"),
        program("legacy_eq", "x if (x & 192) == 0 else 0"),
        program("v1_lt", "(x & 63) if x < 128 else 0"),
        program("v1_eq", "(x % 64) if (x & 128) == 0 else 0"),
        program("tolerant_mask", "x & 63"), program("tolerant_mod", "x % 64"),
        program("v2_mask", "(x & 63) if (x & 64) == 0 else 0"),
        program("v2_div", "(x % 64) if (x // 64) % 2 == 0 else 0"),
    ))
    return Task("message_roundtrip", 8, (encoder, adapter, decoder), tuple(range(64)),
                tuple(range(64)), ("raw_mask", "identity", "tolerant_mask"))
