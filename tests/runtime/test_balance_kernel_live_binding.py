"""Proven-refinement BINDING: ``src.core.balance_kernel`` ≡ the live ``BalanceTable``.

The CBC balances proof chain has three links:

1. **Kani-Rust**: ``rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs``
   carries 7 ``#[kani::proof]`` harnesses (totality, ``settle_transfer_conserves_and_moves_exact``
   = supply conservation, reject precedence, credit totality/mints-or-overflows, two
   reachability covers); CI-gated by ``.github/workflows/runtime-kani.yml`` (``kani --lib``).
2. **Python ``balance_kernel.py`` ≡ Rust**: the differential
   ``tests/runtime/test_balance_kernel_conformance.py`` (CI ``runtime-shadow.yml``).
3. **THIS test — the open link**: ``src.core.balance_kernel`` (the CBC-core
   credit/transfer the proof/differential chain reaches) vs.
   ``src.state.balances.BalanceTable`` — the balance store the **live authority path**
   actually uses (``state.balances`` throughout ``src/integration/dex_engine.py`` and
   ``src/state/state_root.py``).

Without link 3 the proof chain stops at ``balance_kernel.py`` and never reaches the
running store. This test closes link 3 by asserting observational equivalence on the
SHARED DOMAIN: the **live ``BalanceTable`` is the reference**, and ``balance_kernel``'s
credit/transfer must produce the IDENTICAL ``(pubkey, asset) -> amount`` mapping that
``BalanceTable.add`` / ``subtract`` produce (so a bug in either would diverge — this is a
genuine differential, not a property baked into a definition). Supply conservation
(the Kani-proven property) is then checked on the resulting live-store balances.

``balance_kernel`` is strictly MORE conservative than the raw ``BalanceTable`` on two
axes, which this test PINS rather than hides:
* OVERFLOW: ``balance_kernel`` rejects ``balance_overflow`` above ``MAX_BALANCE``
  (2**112-1, the Rust u128 shadow bound); ``BalanceTable`` is unbounded
  (arbitrary-precision int).
* FORMAT: ``balance_kernel`` rejects non-canonical pubkey/asset; ``BalanceTable`` does
  no format validation. (The live settlement path validates upstream; ``BalanceTable``
  itself is just the store.)
On the shared domain (canonical inputs, within ``MAX_BALANCE``, sufficient balance) the
two agree exactly. ``balance_kernel`` ``insufficient_balance`` corresponds to
``BalanceTable.subtract`` raising ``ValueError`` — both refuse and leave the store
unchanged (reject-is-no-op).
"""

from __future__ import annotations

import pytest

from src.core.balance_kernel import (
    BALANCE_SURFACE,
    MAX_BALANCE,
    BalanceAccepted,
    BalanceRejected,
    BalanceState,
    credit,
    transfer,
)
from src.runtime.authority import AuthorityMode, active_mode
from src.state.balances import BalanceTable

# Canonical, in-bounds identifiers (verified canonical fixed-points: balance_kernel's
# canonicalizer returns them unchanged, so its BalanceState keys equal BalanceTable's
# raw keys for these literals).
A = "0x" + "11" * 48
B = "0x" + "22" * 48
C = "0x" + "33" * 48
X = "0x" + "aa" * 32
Y = "0x" + "bb" * 32


def _bk_map(state: BalanceState) -> dict:
    return {(e.pubkey, e.asset): e.amount for e in state.entries}


def _bt_map(bt: BalanceTable) -> dict:
    return dict(bt.get_all_balances())


def _asset_total(m: dict, asset: str) -> int:
    return sum(amt for (pk, a), amt in m.items() if a == asset)


def test_authority_mode_pinned_to_python():
    # Hygiene: credit/transfer are authority-routed; this binding is meaningful only
    # against the Python core. Pin the ambient mode so a future Rust promotion can't
    # silently turn this into a Rust-binary comparison.
    assert active_mode(BALANCE_SURFACE) is AuthorityMode.PYTHON_AUTHORITY


def test_credit_matches_live_balancetable_add():
    bk = BalanceState()
    bt = BalanceTable()
    for recipient, asset, amount in [(A, X, 1000), (B, X, 500), (A, X, 1), (C, Y, 7)]:
        res = credit(state=bk, recipient=recipient, asset=asset, amount=amount)
        assert isinstance(res, BalanceAccepted)
        bk = res.state
        bt.add(recipient, asset, amount)
        assert _bk_map(bk) == _bt_map(bt)
    assert _bk_map(bk) == {(A, X): 1001, (B, X): 500, (C, Y): 7}


def test_transfer_matches_live_subtract_then_add():
    bk = BalanceState()
    bt = BalanceTable()
    for r, a, amt in [(A, X, 1000), (B, Y, 200)]:  # fund
        bk = credit(state=bk, recipient=r, asset=a, amount=amt).state
        bt.add(r, a, amt)
    for sender, recipient, asset, amount in [(A, B, X, 300), (A, C, X, 700), (B, A, Y, 50)]:
        res = transfer(state=bk, sender=sender, recipient=recipient, asset=asset, amount=amount)
        assert isinstance(res, BalanceAccepted), (sender, recipient, amount)
        bk = res.state
        bt.subtract(sender, asset, amount)
        bt.add(recipient, asset, amount)
        assert _bk_map(bk) == _bt_map(bt), (sender, recipient, asset, amount)
    # A fully drained X to B+C; balances match the live store exactly.
    assert _bk_map(bk) == _bt_map(bt)
    assert bk.balance_of(A, X) == bt.get(A, X) == 0


def test_transfer_conserves_supply_on_the_live_store():
    # The Kani-proven conservation (settle_transfer_conserves_and_moves_exact), shown
    # to hold for the LIVE BalanceTable operations: a transfer never changes the
    # per-asset total, in either implementation.
    bk = credit(state=BalanceState(), recipient=A, asset=X, amount=1000).state
    bt = BalanceTable()
    bt.add(A, X, 1000)
    before_bk = _asset_total(_bk_map(bk), X)
    before_bt = _asset_total(_bt_map(bt), X)
    assert before_bk == before_bt == 1000
    res = transfer(state=bk, sender=A, recipient=B, asset=X, amount=400)
    assert isinstance(res, BalanceAccepted)
    bk = res.state
    bt.subtract(A, X, 400)
    bt.add(B, X, 400)
    assert _asset_total(_bk_map(bk), X) == 1000  # conserved (kernel)
    assert _asset_total(_bt_map(bt), X) == 1000  # conserved (live store)
    assert _bk_map(bk) == _bt_map(bt)


def test_insufficient_balance_both_refuse_and_are_no_ops():
    bk = credit(state=BalanceState(), recipient=A, asset=X, amount=100).state
    bt = BalanceTable()
    bt.add(A, X, 100)
    before = _bt_map(bt)
    # kernel: rejects insufficient_balance, no state change.
    res = transfer(state=bk, sender=A, recipient=B, asset=X, amount=101)
    assert isinstance(res, BalanceRejected) and res.reason == "insufficient_balance"
    # live store: subtract raises (insufficient) BEFORE any mutation -> store unchanged.
    with pytest.raises(ValueError):
        bt.subtract(A, X, 101)
    assert _bt_map(bt) == before  # reject-is-no-op on the live store too
    assert _bk_map(bk) == _bt_map(bt)


def test_full_mixed_sequence_state_map_identical():
    bk = BalanceState()
    bt = BalanceTable()
    accepts = 0
    seq = [
        ("credit", A, X, 5),
        ("credit", B, X, 5),
        ("transfer", A, B, X, 2),
        ("transfer", A, C, X, 3),   # A now 0
        ("transfer", B, A, X, 7),
        ("credit", A, Y, 9),
        ("transfer", A, B, Y, 9),   # A Y -> 0 (sparse drop)
    ]
    for op in seq:
        if op[0] == "credit":
            _, r, a, amt = op
            res = credit(state=bk, recipient=r, asset=a, amount=amt)
            assert isinstance(res, BalanceAccepted)
            bk = res.state
            bt.add(r, a, amt)
        else:
            _, s, r, a, amt = op
            res = transfer(state=bk, sender=s, recipient=r, asset=a, amount=amt)
            assert isinstance(res, BalanceAccepted), op
            bk = res.state
            bt.subtract(s, a, amt)
            bt.add(r, a, amt)
        accepts += 1
        assert _bk_map(bk) == _bt_map(bt), op
    # Final state (identical in both): A.X=7 (B sent 7 back in step 5), C.X=3, B.Y=9.
    # Both drop zero balances (sparse): A.Y and B.X went to 0 and are gone.
    final = _bk_map(bk)
    assert final == _bt_map(bt) == {(A, X): 7, (C, X): 3, (B, Y): 9}
    assert (A, Y) not in final and (B, X) not in final  # sparse drop, in both
    assert accepts == len(seq)


# --- documented divergences: balance_kernel is strictly MORE conservative ----


def test_divergence_overflow_kernel_rejects_live_store_unbounded():
    bk = credit(state=BalanceState(), recipient=A, asset=X, amount=MAX_BALANCE).state
    bt = BalanceTable()
    bt.add(A, X, MAX_BALANCE)
    # kernel: a further credit overflows -> balance_overflow (no state change).
    res = credit(state=bk, recipient=A, asset=X, amount=1)
    assert isinstance(res, BalanceRejected) and res.reason == "balance_overflow"
    # live store: unbounded arbitrary-precision int -> accepts past MAX_BALANCE.
    bt.add(A, X, 1)
    assert bt.get(A, X) == MAX_BALANCE + 1
    # So on the OVERFLOW edge the two diverge; balance_kernel is the safer one.
    assert bk.balance_of(A, X) == MAX_BALANCE != bt.get(A, X)


def test_divergence_noncanonical_kernel_validates_live_store_does_not():
    bad_sender = "0xzz" + "11" * 47  # right width, non-hex
    bk = credit(state=BalanceState(), recipient=A, asset=X, amount=10).state
    # kernel: rejects non-canonical sender.
    res = transfer(state=bk, sender=bad_sender, recipient=A, asset=X, amount=1)
    assert isinstance(res, BalanceRejected) and res.reason == "invalid_sender"
    # live store: no format validation — it would happily store under the raw bad key.
    bt = BalanceTable()
    bt.add(bad_sender, X, 1)
    assert bt.get(bad_sender, X) == 1
    # Hence canonical-format safety is the kernel's (and the upstream validator's), not
    # the raw store's — pinned so the binding's shared-domain scoping is explicit.


def test_binding_corpus_is_non_vacuous():
    # The equivalence corpus must exercise both accepts and rejects, and a non-empty
    # resulting state — so a degenerate "everything rejects" regression cannot pass.
    bk = credit(state=BalanceState(), recipient=A, asset=X, amount=100).state
    assert _bk_map(bk) == {(A, X): 100}  # accept reached a non-trivial state
    assert isinstance(
        transfer(state=bk, sender=A, recipient=B, asset=X, amount=101), BalanceRejected
    )  # reject reachable
