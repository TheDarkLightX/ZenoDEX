"""Symbolic disaster-witness mine for the spot-DEX state-root v5 surface.

`compute_state_root` / `state_root_preimage` (``src/state/state_root.py``) is the
spot-DEX ledger state commitment: the header pre/post_state_root binds balances,
pools, LP balances + duration-risk metadata, nonces, and the v5 fee-accumulator
dust carry. A verifier admits a replayed snapshot iff the recomputed root equals
the committed root, so this hash must be:

    DETERMINISM + ORDER-INDEPENDENCE:  the same logical decoded state, built via
        ANY insertion order into the underlying tables / pool mapping, hashes to
        ONE root. A verifier must never see a root change on a mere
        re-serialization.

    FRAMING-INJECTIVITY (decoded content):  two states that differ in ANY
        committed decoded field (a balance amount, a pool reserve/fee/status/
        curve, an LP amount, a duration-risk timestamp/tier, a nonce, the fee
        dust) MUST hash to DIFFERENT roots. In particular there must be no
        concatenation / framing ambiguity where a value can be "moved" between
        adjacent fields or sections (e.g. a balance row vs the byte-identical LP
        row, a mint-vs-remove timestamp) while preserving the root.

A collision here is a state-commitment forgery: an operator could swap one
committed state for a materially different one under the same root, defeating
replay verification. A clean run over thousands of generated states is a bounded
NEGATIVE receipt for this disaster class on the decoded-content commitment path.

SCOPE / NON-CLAIMS:
  * Authority mode is PYTHON_AUTHORITY (the default), so this exercises the pure
    `_compute_state_root_python` path. No Rust subprocess and NO BLS/signature
    crypto is invoked by this surface, so `crypto_oracle_stubbed` is N/A here.
  * Pubkey and asset hex spellings are compared by decoded identity. Pool IDs
    are stricter: uppercase or otherwise noncanonical spellings are rejected,
    and every pool entry is bound to its assets, fee, and curve configuration.
  * Out of scope: cross-module sequencing (apply_ops), the Python<->Rust bridge
    (covered by tests/runtime/test_state_root_disaster_state.py), and SHA-256
    pre-image resistance (assumed).
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.state import state_root as m  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.canonical import sha256_hex  # noqa: E402
from src.state.lp import LPTable  # noqa: E402
from src.state.nonces import NonceTable  # noqa: E402
from src.state.pools import PoolState, PoolStatus, compute_pool_id  # noqa: E402


# Small, BOUNDED canonical (lowercase) hex domains so the build-time constraints
# (48-byte pubkeys, 32-byte assets/pools, distinct decoded keys, asset0<asset1,
# fee_bps<=10000, u32 nonces) are easily satisfiable -> we exercise the ADMIT
# path, not just the reject path.
def _pk(i: int) -> str:
    return "0x" + f"{i & 0xFF:02x}" * 48


def _asset(i: int) -> str:
    return "0x" + f"{i & 0xFF:02x}" * 32


_STATUSES = [PoolStatus.ACTIVE, PoolStatus.FROZEN, PoolStatus.DISABLED]


def _root(balances, pools, lp, nonces, fee=None) -> str:
    return m.compute_state_root(
        balances=balances, pools=pools, lp_balances=lp, nonces=nonces, fee_accumulator=fee
    )


# ---------------------------------------------------------------------------
# Logical state model: a small bag of decoded-content facts that a verifier
# commits. We build the SAME logical state in two independent (table, order)
# realizations to test determinism, and we mutate exactly ONE fact to test
# injectivity.
# ---------------------------------------------------------------------------

# A balance fact: (pubkey-index, asset-index, amount>0). amount>0 because the
# table drops zero balances (a zero balance is the absence of the entry).
_balance = st.tuples(
    st.integers(min_value=0, max_value=6),
    st.integers(min_value=0, max_value=4),
    st.integers(min_value=1, max_value=10_000),
)

# An LP fact: (pubkey-index, pool-index, lp_amount>0, mint?, remove?, tier, churn_ts?)
_lp = st.tuples(
    st.integers(min_value=0, max_value=6),
    st.integers(min_value=0, max_value=4),
    st.integers(min_value=1, max_value=10_000),
    st.one_of(st.none(), st.integers(min_value=0, max_value=500)),
    st.one_of(st.none(), st.integers(min_value=0, max_value=500)),
    st.integers(min_value=0, max_value=4),
    st.one_of(st.none(), st.integers(min_value=0, max_value=500)),
)

# A pool fact: (pool-index, a0-index, a1-index, r0, r1, fee_bps, lp_supply, status, created_at)
_pool = st.tuples(
    st.integers(min_value=0, max_value=6),
    st.integers(min_value=0, max_value=3),
    st.integers(min_value=0, max_value=3),
    st.integers(min_value=0, max_value=10_000),
    st.integers(min_value=0, max_value=10_000),
    st.integers(min_value=0, max_value=10_000),
    st.integers(min_value=0, max_value=10_000),
    st.sampled_from(_STATUSES),
    st.integers(min_value=0, max_value=10_000),
)

# A nonce fact: (pubkey-index, last_nonce in u32)
_nonce = st.tuples(
    st.integers(min_value=0, max_value=6),
    st.integers(min_value=0, max_value=0xFFFFFFFF),
)


def _build_balances(facts, order) -> BalanceTable:
    bt = BalanceTable()
    for idx in order:
        pk_i, a_i, amt = facts[idx]
        bt.set(_pk(pk_i), _asset(a_i), amt)
    return bt


def _build_lp(facts, order) -> LPTable:
    lp = LPTable()
    for idx in order:
        pk_i, pool_i, amt, mint, remove, tier, churn_ts = facts[idx]
        pk, pool = _pk(pk_i), _asset(pool_i)
        lp.set(pk, pool, amt)
        if mint is not None:
            lp.set_last_mint_timestamp(pk, pool, mint)
        if remove is not None:
            lp.set_last_remove_timestamp(pk, pool, remove)
        if tier:
            lp.set_churn_tier(pk, pool, tier)
        if churn_ts is not None:
            lp.set_last_churn_update_timestamp(pk, pool, churn_ts)
    return lp


def _build_pools(facts, order):
    pools = {}
    for idx in order:
        _pool_i, a0_i, a1_i, r0, r1, fee, sup, status, created = facts[idx]
        a0, a1 = _asset(a0_i), _asset(a1_i)
        if a0 == a1:  # self-pair rejected by normalize_pool_asset_pair
            continue
        if a0 > a1:
            a0, a1 = a1, a0
        pid = compute_pool_id(a0, a1, fee)
        pools[pid] = PoolState(
            pool_id=pid, asset0=a0, asset1=a1, reserve0=r0, reserve1=r1,
            fee_bps=fee, lp_supply=sup, status=status, created_at=created,
        )
    return pools


def _pool_identity_key(fact):
    _, a0_i, a1_i, _, _, fee, _, _, _ = fact
    return min(a0_i, a1_i), max(a0_i, a1_i), fee


def _build_nonces(facts, order) -> NonceTable:
    nt = NonceTable()
    for idx in order:
        pk_i, n = facts[idx]
        nt.set_last(_pk(pk_i), n)
    return nt


def _dedup_first(facts, key):
    """Keep only the first fact per decoded key — the underlying tables/maps are
    dicts, so a later same-key fact would silently overwrite an earlier one, and
    feeding two distinct facts with the same decoded key would (correctly) trip
    the encoder's duplicate-decoded guard. We commit ONE fact per key so the
    logical state is well-defined."""
    seen, out = set(), []
    for f in facts:
        k = key(f)
        if k in seen:
            continue
        seen.add(k)
        out.append(f)
    return out


# ===========================================================================
# Invariant helper (factored so the teeth tests reuse the EXACT checker).
# ===========================================================================

def _assert_no_root_collision(root_fn, build_a, build_b, *, label: str) -> None:
    """FRAMING-INJECTIVITY + DETERMINISM checker.

    `build_a` / `build_b` are zero-arg builders producing the two states to
    compare; `root_fn(state)` computes a root. The caller asserts the SEMANTIC
    relation it expects via `label`:

      - label == "same":  the two builders encode the SAME logical decoded
        state -> roots MUST be EQUAL (determinism / order-independence).
      - label == "diff":  the two builders differ in exactly one committed
        decoded field -> roots MUST DIFFER (framing-injectivity). A collision
        here is a state-commitment forgery.

    Raises AssertionError on a violation."""
    ra = root_fn(build_a())
    rb = root_fn(build_b())
    # Self-determinism guard: recomputation is stable (no nondeterminism).
    assert ra == root_fn(build_a()), f"{label}: root_fn not deterministic on A"
    if label == "same":
        assert ra == rb, f"DETERMINISM VIOLATION ({label}): same logical state -> {ra} != {rb}"
    elif label == "diff":
        assert ra != rb, (
            f"FRAMING-INJECTIVITY VIOLATION ({label}): distinct committed states "
            f"collide on root {ra}"
        )
    else:  # pragma: no cover - guard
        raise ValueError(f"unknown label {label!r}")


# ===========================================================================
# TEETH / NON-VACUITY. A passing property test with no teeth is a false
# receipt. We prove the checker RAISES on planted violations:
#   1. a totally broken (constant) root and a non-deterministic root, and
#   2. a REAL framing bug — a preimage that drops the section labels AND the
#      per-section length/count framing, so a balance row aliases the
#      byte-identical LP row across the section boundary.
# The injectivity helper must catch all of these.
# ===========================================================================

def _unframed_no_count_preimage(*, balances, lp_balances) -> bytes:
    """Deliberately BROKEN reference encoder: emit ONLY the raw (key,key,amount)
    rows of the balances and LP sections, back-to-back, with NO section label,
    NO section length prefix, and NO per-section entry count. This is the
    canonical framing bug: a balance row and a byte-identical LP row become
    indistinguishable because nothing delimits which section a row belongs to."""
    out = bytearray()
    for pk_b, asset_b, amount in m._sorted_balance_entries(balances):
        out += pk_b + asset_b + m.encode_uvarint(amount)
    for pk_b, pool_b, amount in m._sorted_lp_entries(lp_balances):
        out += pk_b + pool_b + m.encode_uvarint(amount)
    return bytes(out)


def _buggy_root(state) -> str:
    b, lp = state
    return sha256_hex(_unframed_no_count_preimage(balances=b, lp_balances=lp))


def test_teeth_constant_and_flaky_roots_are_caught():
    """A constant root (collides everywhere) and a non-deterministic root must
    both trip the checker. If they did not, the negative receipts below would be
    meaningless."""
    PK, A = _pk(1), _asset(0x10)
    bt1 = BalanceTable(); bt1.set(PK, A, 1)
    bt2 = BalanceTable(); bt2.set(PK, A, 2)  # DIFFERENT committed amount
    s1 = (bt1, {}, LPTable(), NonceTable(), None)
    s2 = (bt2, {}, LPTable(), NonceTable(), None)

    constant = lambda _s: "0x" + "00" * 32  # noqa: E731
    with pytest.raises(AssertionError, match="FRAMING-INJECTIVITY VIOLATION"):
        _assert_no_root_collision(constant, lambda: s1, lambda: s2, label="diff")

    box = {"n": 0}
    def _flaky(_s):
        box["n"] += 1
        return "0x" + f"{box['n']:064x}"
    with pytest.raises(AssertionError, match="not deterministic"):
        _assert_no_root_collision(_flaky, lambda: s1, lambda: s1, label="same")


def test_teeth_unframed_encoder_collides_real_encoder_does_not():
    """Plant a REAL framing collision and prove (a) the production framed encoder
    keeps the two states distinct (the safety property) and (b) the unframed
    reference collides, so the section label + length prefix is load-bearing.

    S1: balances = {(PK,A): 7}, lp = {}.
    S2: balances = {},          lp = {(PK,A): 7}.
    These are DIFFERENT logical states (an asset balance vs an LP-share balance).
    The unframed reference emits the same (PK|A|uvarint(7)) row for both with no
    section delimiter, so its two digests are byte-identical -> a collision the
    injectivity checker must reject."""
    PK, A = _pk(0x11), _asset(0x10)

    s1_bt = BalanceTable(); s1_bt.set(PK, A, 7)
    s1 = (s1_bt, LPTable())
    s2_lp = LPTable(); s2_lp.set(PK, A, 7)
    s2 = (BalanceTable(), s2_lp)

    # (a) Production framed encoder separates them (BAL vs LPB labels + lengths).
    r1 = sha256_hex(m.state_root_preimage(balances=s1[0], pools={}, lp_balances=s1[1], nonces=NonceTable()))
    r2 = sha256_hex(m.state_root_preimage(balances=s2[0], pools={}, lp_balances=s2[1], nonces=NonceTable()))
    assert r1 != r2, "production framed encoder must separate a BAL row from a byte-identical LPB row"

    # (b) Unframed reference collides.
    assert _buggy_root(s1) == _buggy_root(s2), "unframed reference must collide (teeth setup)"

    # (c) The injectivity checker, run over the unframed reference, RAISES.
    with pytest.raises(AssertionError, match="FRAMING-INJECTIVITY VIOLATION"):
        _assert_no_root_collision(_buggy_root, lambda: s1, lambda: s2, label="diff")


# ===========================================================================
# MINE 1: DETERMINISM / ORDER-INDEPENDENCE
# Build the SAME logical decoded state via two independent random insertion
# orders into the tables/pool map; the root MUST be identical.
# ===========================================================================

@settings(max_examples=900)
@given(
    bfacts=st.lists(_balance, max_size=8),
    lpfacts=st.lists(_lp, max_size=6),
    pfacts=st.lists(_pool, max_size=6),
    nfacts=st.lists(_nonce, max_size=6),
    dust=st.integers(min_value=0, max_value=1_000_000),
    perm=st.randoms(use_true_random=False),
)
def test_state_root_is_order_independent(bfacts, lpfacts, pfacts, nfacts, dust, perm):
    # One fact per decoded key (the tables are dicts; a second same-key fact
    # would overwrite, making "same logical state" ill-defined).
    bfacts = _dedup_first(bfacts, key=lambda f: (f[0], f[1]))
    lpfacts = _dedup_first(lpfacts, key=lambda f: (f[0], f[1]))
    pfacts = _dedup_first(pfacts, key=_pool_identity_key)
    nfacts = _dedup_first(nfacts, key=lambda f: f[0])

    class _Acc:
        dust = 0

    acc = _Acc(); acc.dust = dust

    def order(facts):
        idxs = list(range(len(facts)))
        perm.shuffle(idxs)
        return idxs

    def build():
        return (
            _build_balances(bfacts, order(bfacts)),
            _build_pools(pfacts, order(pfacts)),
            _build_lp(lpfacts, order(lpfacts)),
            _build_nonces(nfacts, order(nfacts)),
            acc,
        )

    def root_fn(state):
        b, p, lp, n, fee = state
        return _root(b, p, lp, n, fee)

    _assert_no_root_collision(root_fn, build, build, label="same")


# ===========================================================================
# MINE 2: FRAMING-INJECTIVITY
# Build a valid state, then mutate EXACTLY ONE committed decoded field; the root
# MUST change. This is the falsification target: a collision = state-commitment
# forgery (move a byte between fields / drop a field from the commitment).
# ===========================================================================

_MUTABLE_FIELDS = [
    "bal_amount", "bal_pubkey", "bal_asset",
    "pool_reserve0", "pool_reserve1", "pool_fee", "pool_lp_supply",
    "pool_status", "pool_created_at",
    "lp_amount", "lp_mint", "lp_remove", "lp_tier", "lp_churn_ts",
    "nonce", "fee_dust",
]


@settings(max_examples=1200)
@given(
    bfacts=st.lists(_balance, min_size=1, max_size=4),
    lpfacts=st.lists(_lp, min_size=1, max_size=3),
    pfacts=st.lists(_pool, min_size=1, max_size=3),
    nfacts=st.lists(_nonce, min_size=1, max_size=3),
    dust=st.integers(min_value=0, max_value=1_000_000),
    which=st.sampled_from(_MUTABLE_FIELDS),
    picker=st.data(),
)
def test_single_field_mutation_changes_root(bfacts, lpfacts, pfacts, nfacts, dust, which, picker):
    bfacts = _dedup_first(bfacts, key=lambda f: (f[0], f[1]))
    lpfacts = _dedup_first(lpfacts, key=lambda f: (f[0], f[1]))
    pfacts = _dedup_first(pfacts, key=_pool_identity_key)
    nfacts = _dedup_first(nfacts, key=lambda f: f[0])

    # Drop self-pair pools (rejected at build) so a pool genuinely exists.
    pfacts = [f for f in pfacts if _asset(f[1]) != _asset(f[2])]

    class _Acc:
        dust = 0

    def base_root(bf, lf, pf, nf, d):
        acc = _Acc(); acc.dust = d
        b = _build_balances(bf, range(len(bf)))
        p = _build_pools(pf, range(len(pf)))
        lp = _build_lp(lf, range(len(lf)))
        n = _build_nonces(nf, range(len(nf)))
        return _root(b, p, lp, n, acc)

    bf2, lf2, pf2, nf2, d2 = list(bfacts), list(lpfacts), list(pfacts), list(nfacts), dust

    if which in ("bal_amount", "bal_pubkey", "bal_asset"):
        i = picker.draw(st.integers(min_value=0, max_value=len(bf2) - 1))
        pk_i, a_i, amt = bf2[i]
        if which == "bal_amount":
            bf2[i] = (pk_i, a_i, amt + 1)
        elif which == "bal_pubkey":
            new_pk = picker.draw(st.integers(min_value=7, max_value=255))
            bf2[i] = (new_pk, a_i, amt)
            if any((new_pk, a_i) == (f[0], f[1]) for f in bf2[:i] + bf2[i + 1:]):
                return  # would collide with another key -> dedup territory; skip (harness limit)
        else:  # bal_asset
            new_a = picker.draw(st.integers(min_value=5, max_value=255))
            bf2[i] = (pk_i, new_a, amt)
            if any((pk_i, new_a) == (f[0], f[1]) for f in bf2[:i] + bf2[i + 1:]):
                return
    elif which.startswith("pool_"):
        if not pf2:
            return
        i = picker.draw(st.integers(min_value=0, max_value=len(pf2) - 1))
        pool_i, a0_i, a1_i, r0, r1, fee, sup, status, created = pf2[i]
        if which == "pool_reserve0":
            pf2[i] = (pool_i, a0_i, a1_i, r0 + 1, r1, fee, sup, status, created)
        elif which == "pool_reserve1":
            pf2[i] = (pool_i, a0_i, a1_i, r0, r1 + 1, fee, sup, status, created)
        elif which == "pool_fee":
            new_fee = (fee + 1) % 10_001
            if new_fee == fee:
                return
            pf2[i] = (pool_i, a0_i, a1_i, r0, r1, new_fee, sup, status, created)
        elif which == "pool_lp_supply":
            pf2[i] = (pool_i, a0_i, a1_i, r0, r1, fee, sup + 1, status, created)
        elif which == "pool_status":
            new_status = picker.draw(st.sampled_from([s for s in _STATUSES if s is not status]))
            pf2[i] = (pool_i, a0_i, a1_i, r0, r1, fee, sup, new_status, created)
        elif which == "pool_created_at":
            pf2[i] = (pool_i, a0_i, a1_i, r0, r1, fee, sup, status, created + 1)
    elif which.startswith("lp_"):
        if not lf2:
            return
        i = picker.draw(st.integers(min_value=0, max_value=len(lf2) - 1))
        pk_i, pool_i, amt, mint, remove, tier, churn_ts = lf2[i]
        if which == "lp_amount":
            lf2[i] = (pk_i, pool_i, amt + 1, mint, remove, tier, churn_ts)
        elif which == "lp_mint":
            new = 1 if mint in (None, 0) else None
            lf2[i] = (pk_i, pool_i, amt, new, remove, tier, churn_ts)
        elif which == "lp_remove":
            new = 1 if remove in (None, 0) else None
            lf2[i] = (pk_i, pool_i, amt, mint, new, tier, churn_ts)
        elif which == "lp_tier":
            lf2[i] = (pk_i, pool_i, amt, mint, remove, tier + 1, churn_ts)
        elif which == "lp_churn_ts":
            new = 1 if churn_ts in (None, 0) else None
            lf2[i] = (pk_i, pool_i, amt, mint, remove, tier, new)
    elif which == "nonce":
        if not nf2:
            return
        i = picker.draw(st.integers(min_value=0, max_value=len(nf2) - 1))
        pk_i, n = nf2[i]
        new_n = (n + 1) & 0xFFFFFFFF
        if new_n == n:
            return
        nf2[i] = (pk_i, new_n)
    elif which == "fee_dust":
        d2 = dust + 1

    def build_a():
        return (bfacts, lpfacts, pfacts, nfacts, dust)

    def build_b():
        return (bf2, lf2, pf2, nf2, d2)

    def root_of(state):
        bf, lf, pf, nf, d = state
        return base_root(bf, lf, pf, nf, d)

    _assert_no_root_collision(root_of, build_a, build_b, label="diff")
