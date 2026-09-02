"""Explicit names for the non-ordinal M6 assurance gates.

The repository also uses an advisory numeric review score that may be mapped
to conventional A--F letters.  These gates are a separate binary assurance
vocabulary.  Their names carry their assurance meaning instead of reusing
ambiguous ordinal labels.

This module is a functional-core value surface: it contains no I/O, policy
lookup, clock, environment read, or mutable global state.
"""

from __future__ import annotations

from enum import Enum


class M6AssuranceGateV1(str, Enum):
    """Closed M6 assurance-gate registry.

    ``M6-R01`` through ``M6-R13`` remain separate requirement identifiers.
    The advisory A--F review score is also separate from this registry.
    """

    FORMAL = "FormalGate"
    RUNTIME_REFINEMENT = "RuntimeRefinementGate"
    MOUNTED_AUTHORITY = "MountedAuthorityGate"


__all__ = ["M6AssuranceGateV1"]
