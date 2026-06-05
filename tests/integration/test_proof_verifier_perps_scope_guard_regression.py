"""Regression: the projected-snapshot scope guard must reject unbound PERPS state,
mirroring its vault/oracle siblings.

Why this exists (D-CANON-002 residual): the spot state root (compute_state_root)
commits balances/pools/lp/nonces/fee_accumulator but OMITS vault/oracle/perps. On the
externally-supplied-pre_state paths (proof verification / light-client / state-sync) a
projected snapshot is bound to the chain only via pre_state_root, so any field the root
omits is unbound unless the scope guard rejects it as non-empty. `_projected_snapshot_
scope_error` already rejected non-None vault/oracle (and non-zero fee_accumulator dust)
but NOT perps — so an unbound perps could ride a projected snapshot undetected. The guard
now rejects non-None perps too. This test pins that fail-closed behavior in both the v3
and v4 proof verifiers.

Scope note: this closes the perps hole in the SNAPSHOT SCOPE GUARD. A later consensus
review chose the compatible enforce-empty design for the spot lane:
`dex_state_root_v0` now rejects non-None vault/oracle/perps before committing the v5
spot root. This test remains the proof-verifier sibling of that consensus guard.
"""

from __future__ import annotations

import types

import pytest

from tools.proof_verifiers.recompute_batch_v3 import (
    _projected_snapshot_scope_error as scope_error_v3,
)
from tools.proof_verifiers.recompute_batch_v4 import (
    _projected_snapshot_scope_error as scope_error_v4,
)

PERPS_ERROR = "projected pre_state_snapshot carries unbound perps state"


def _state(**overrides):
    """A minimal state whose vault/oracle are None and fee dust is 0, so the perps check
    is the first (and only) guard to fire. perps non-None returns BEFORE the guard touches
    pools/balances, so no further state is needed for the reject path."""
    base = dict(
        fee_accumulator=types.SimpleNamespace(dust=0),
        vault=None,
        oracle=None,
        perps=None,
    )
    base.update(overrides)
    return types.SimpleNamespace(**base)


@pytest.mark.parametrize("guard", [scope_error_v3, scope_error_v4])
def test_scope_guard_rejects_unbound_perps(guard) -> None:
    # any non-None perps payload must be rejected fail-closed
    assert guard(_state(perps=types.SimpleNamespace(positions={"acct": 1})), []) == PERPS_ERROR
    assert guard(_state(perps=object()), []) == PERPS_ERROR


@pytest.mark.parametrize("guard", [scope_error_v3, scope_error_v4])
def test_scope_guard_perps_is_checked_alongside_vault_oracle(guard) -> None:
    # the perps reject is a sibling of vault/oracle: each non-None support-lane field is
    # rejected with its own message (proves perps wasn't accidentally aliased to another).
    assert "vault" in guard(_state(vault=object()), [])
    assert "oracle" in guard(_state(oracle=object()), [])
    assert "perps" in guard(_state(perps=object()), [])
