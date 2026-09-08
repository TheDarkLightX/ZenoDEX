"""Small, immutable Boolean terms for Tau composition research."""

from .terms import (
    MAX_NATIVE_TERM_BYTES,
    MAX_NATIVE_TERM_DEPTH,
    MAX_NATIVE_TERM_NODES,
    Term,
    constant,
    join,
    meet,
    negate,
    parse_native_term,
    variable,
    xor,
)

__all__ = [
    "MAX_NATIVE_TERM_BYTES",
    "MAX_NATIVE_TERM_DEPTH",
    "MAX_NATIVE_TERM_NODES",
    "Term",
    "constant",
    "join",
    "meet",
    "negate",
    "parse_native_term",
    "variable",
    "xor",
]
