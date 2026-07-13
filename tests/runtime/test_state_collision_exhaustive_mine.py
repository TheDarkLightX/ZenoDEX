"""Exhaustive-enumeration + adversarial-structural disaster mine for the
spot-DEX state-commitment encoders (STATE-ROOT / ENCODER COLLISION class).

Targets the REAL encoders (imported, never re-implemented except one clearly
marked BUGGY reference inside the teeth test):

  * ``src/state/state_root.py``     — ``state_root_preimage`` / ``compute_state_root``
  * ``src/state/canonical.py``      — ``encode_uvarint`` / ``encode_bytes`` / framing
  * ``src/state/support_root.py``   — ``compute_support_state_root`` (projected commitment)

DISASTER CLASS
--------------
A *state-root collision*: two DISTINCT logical states (or two distinct canonical
inputs) that produce the SAME root / canonical preimage bytes. A real collision
is a state-commitment forgery — an operator could swap one committed state for a
materially different one under the same root, defeating replay verification.
A real witness here is CRITICAL and must be REPORTED, not patched.

WHY THIS IS RUNG 2 (not "more random PBT")
------------------------------------------
The committed sibling ``test_state_root_witness_mine.py`` uses Hypothesis to
draw uniform-random single states (rung 1). It NEVER guarantees it visited every
boundary, and it cannot certify completeness — a clean Hypothesis run is a
*sampled* negative receipt.

This file is COMPLETE over its bound, not sampled. Two creative generators run
against the real encoders:

  GENERATOR A — EXHAUSTIVE BOUNDED ENUMERATION.  Three COMPLETE sweeps, each the
    FULL product over its own deliberately tiny but boundary-rich domain; logical
    states are canonicalized to a DECODED-byte normal form, DEDUPED, then EVERY
    unordered pair of distinct states is checked (distinct state => distinct root)
    via an O(N) injective root-map. Each sweep asserts its EXACT enumerated and
    deduped count and prints the EXACT C(N,2) pair count, so the negative receipt
    is a *complete* statement over its bound (not a sample):
      Sweep 1 (`test_exhaustive_balance_amount_boundaries_injective`): the empty
        state PLUS every single balance entry over the FULL 2 x 2 x 10 grid
        (pk in {PK_a,PK_b} x asset in {A_x,A_y} x amount in the 10-element
        carry/width boundary set {1,2,127,128,255,256,65535,65536,2^32-1,2^32}).
        Exact N=41, pairs=820.
      Sweep 2 (`test_exhaustive_two_section_le3_entries_injective`): the FULL
        cross-section product of 4 balance keys and 4 LP keys, each ABSENT or
        present with amount in a 4-value boundary sub-alphabet {1,128,256,2^32},
        crossed with dust in {0,1}, subject to (#bal + #lp) <= 3 total entries.
        Exact N=8130, pairs=33,044,385.
      Sweep 3 (`test_exhaustive_nonce_and_dust_boundaries_injective`): the empty
        state PLUS every single-nonce state over (pk x nonce in {1,2,255,256,
        2^32-1}) crossed with dust in {0,1,256}. Exact N=33, pairs=528.
      Sweep 4 (`test_exhaustive_single_pool_field_boundaries_injective`): one
        fixed asset pair with pool IDs derived from fee and curve identity
        fields, while reserves, LP supply, status, and created_at also vary over
        a boundary-rich field lattice.
        Exact N=1458, pairs=1,062,153.
      Sweep 5 (`test_exhaustive_lp_duration_risk_field_boundaries_injective`):
        one fixed LP key with a fixed positive LP balance and all duration-risk
        metadata fields varied over None/zero/carry-edge alphabets. Exact N=192,
        pairs=18,336.
    These are exhaustive over THESE bounds (sub-alphabets / single-nonce /
    <=3 entries), NOT over a hypothetical maximal domain — the claim is precisely
    the bound each sweep enumerates.

  GENERATOR B — ADVERSARIAL STRUCTURAL SEEDS.  Hand-crafted collision shapes a
    human auditor probes and that uniform sampling essentially never hits:
      (a) a balance row vs a byte-identical LP-share row (section aliasing);
      (b) FIELD-BOUNDARY SHIFT: two states that, WITHOUT the length/count
          framing, would let a byte migrate between adjacent fields to yield
          equal concatenation (proves the length-prefix/label is load-bearing);
      (c) pubkey/asset hex CASE variants 0xAA vs 0xaa (decode-equal => SAME
          logical state => MUST share a root — spelling independence, asserted
          as equality). Pool IDs use exact lowercase canonical form and are not
          case-equivalent inputs.
      (e) empty-string/absent vs explicit-zero (dust None vs dust 0 => SAME;
          amount-0 entry == absent entry => SAME);
      (f) "split aliasing": one key holding x+y  vs  two keys holding x and y;
      (g) reordering across DIFFERENT sections (a (pk,asset) in BAL vs the
          byte-identical (pk,pool) in LPB).
    For every adversarial pair we assert the REAL encoder's actual semantic
    relation (collide-as-same vs must-differ) — never a hand-waved "no collision".

TEETH / NON-VACUITY (mandatory, CLAUDE.md)
------------------------------------------
We plant REAL violations against an UNFRAMED reference encoder (labels + length
prefixes + entry counts stripped) and prove the injectivity checker RAISES on
them, while the production FRAMED encoder keeps the same states distinct. A
passing mine with no teeth is a false receipt.

SCOPE / NON-CLAIMS
------------------
  * Authority mode is the default PYTHON_AUTHORITY, so this exercises the pure
    ``_compute_state_root_python`` path. No Rust subprocess and no BLS/signature
    crypto is invoked by this surface.
  * Pubkey and asset identity is decoded content (``hex_to_bytes_fixed`` keys on
    48/32 raw bytes), so case-only variants share a root. Pool IDs are stricter:
    every occurrence uses exact lowercase canonical form, and pool entries bind
    that ID to assets, fee, and curve configuration.
  * Out of scope: cross-module sequencing (apply_ops), the Python<->Rust bridge,
    multi-pool enumeration beyond a couple of seeds (the balance/LP/nonce/fee
    sections and a single-pool field lattice are the exhaustive targets here),
    and SHA-256 pre-image resistance (assumed).
"""

from __future__ import annotations

import itertools

import pytest

from src.state import state_root as m
from src.state.balances import BalanceTable
from src.state.canonical import sha256_hex
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.support_root import BatchStateSupport, compute_support_state_root

# ---------------------------------------------------------------------------
# Boundary-rich, BOUNDED domain. Two distinct pubkeys/assets, and an amount
# alphabet that lands exactly on the LEB128 / fixed-width carry boundaries that
# a width/framing bug is most likely to confuse.
# ---------------------------------------------------------------------------
PK = ["0x" + f"{i:02x}" * 48 for i in (0xA1, 0xB2)]            # PK_a, PK_b (48-byte)
ASSET = ["0x" + f"{i:02x}" * 32 for i in (0x10, 0x20)]         # A_x, A_y (32-byte)

# Carry / width boundaries: 1-byte<->2-byte uvarint (127/128, 255/256),
# 2<->3 byte (65535/65536), and the u32 edge (2^32-1 / 2^32).
BOUNDARY_AMTS = (1, 2, 127, 128, 255, 256, 65535, 65536, 2**32 - 1, 2**32)


def _root(balances, pools, lp, nonces, fee=None) -> str:
    return m.compute_state_root(
        balances=balances, pools=pools, lp_balances=lp, nonces=nonces, fee_accumulator=fee
    )


class _Acc:
    """Minimal fee-accumulator stand-in: only the ``dust`` attribute is read by
    the encoder (see ``_fee_accumulator_dust``)."""

    def __init__(self, dust: int) -> None:
        self.dust = dust


# ===========================================================================
# Logical-state normal form + the injectivity checker (shared with teeth).
# A logical state is a tuple of FROZEN, canonicalized facts so that:
#   - it is hashable / dedup-able (logical equality, order-independent);
#   - building it into the real tables is unambiguous.
# Sections used: balances, lp (amount only, no duration metadata in Gen A),
# nonces, fee dust. (Pools are exercised by adversarial seeds in Gen B.)
# ===========================================================================

def _pk_bytes(pk: str) -> bytes:
    """Decoded 48-byte identity of a pubkey spelling (consensus key identity)."""
    return m.hex_to_bytes_fixed(pk, nbytes=48, name="pubkey")


def _asset_bytes(a: str) -> bytes:
    """Decoded 32-byte identity of an asset / pool_id spelling."""
    return m.hex_to_bytes_fixed(a, nbytes=32, name="asset")


def _normal_form(bal: dict, lp: dict, nonce: dict, dust: int) -> tuple:
    """Canonical, order-independent identity of a logical state, keyed ONLY on
    DECODED BYTES (the consensus identity ``hex_to_bytes_fixed`` commits — 48 raw
    bytes per pubkey, 32 per asset/pool), NOT on hex spelling. Two spellings that
    decode to the same bytes therefore map to the SAME normal form, matching the
    decoded-content identity the verifier relies on. (The canonical lowercase
    spelling is reconstructed from the bytes at build time, so the spelling is a
    pure function of the identity and never leaks into the tuple.)

    ``bal`` / ``lp`` map (pk, asset) -> amount>0; ``nonce`` maps pk -> n>0;
    ``dust`` is the fee-accumulator dust (0 == empty/None). Zero amounts are
    DROPPED because the tables drop them (a zero entry is the absence of the
    entry — that equivalence is itself one of the adversarial seeds, below)."""
    nf_bal = tuple(sorted(
        (_pk_bytes(pk), _asset_bytes(a), v) for (pk, a), v in bal.items() if v != 0
    ))
    nf_lp = tuple(sorted(
        (_pk_bytes(pk), _asset_bytes(a), v) for (pk, a), v in lp.items() if v != 0
    ))
    nf_n = tuple(sorted(
        (_pk_bytes(pk), v) for pk, v in nonce.items() if v != 0
    ))
    return (nf_bal, nf_lp, nf_n, int(dust))


def _build_from_normal_form(nf: tuple):
    """Reconstruct the real tables from the decoded-byte normal form. The
    build-time hex spelling is the canonical lowercase rendering of the decoded
    bytes, so it is a pure function of the logical identity (no spelling state)."""
    nf_bal, nf_lp, nf_n, dust = nf
    bt = BalanceTable()
    for pkb, ab, v in nf_bal:
        bt.set("0x" + pkb.hex(), "0x" + ab.hex(), v)
    lp = LPTable()
    for pkb, ab, v in nf_lp:
        lp.set("0x" + pkb.hex(), "0x" + ab.hex(), v)
    nt = NonceTable()
    for pkb, v in nf_n:
        nt.set_last("0x" + pkb.hex(), v)
    return bt, {}, lp, nt, _Acc(dust)


def _root_of_normal_form(nf: tuple) -> str:
    bt, pools, lp, nt, acc = _build_from_normal_form(nf)
    return _root(bt, pools, lp, nt, acc)


def _assert_injective_over(states, *, label: str, root_fn=_root_of_normal_form):
    """COMPLETE injectivity check over a set of logical states.

    `states` is an iterable of canonical normal-form tuples (already deduped by
    the caller's set construction). Computes each root once (via `root_fn`, the
    REAL encoder by default), then asserts the root map is INJECTIVE: distinct
    normal forms => distinct roots. On a collision raises AssertionError naming
    both colliding states (a real witness). The teeth tests pass a BUGGY
    `root_fn` to prove this exact helper raises on a planted collision.
    Returns (n_states, n_pairs_checked, root_by_state)."""
    states = list(states)
    root_by_state: dict[tuple, str] = {}
    state_by_root: dict[str, tuple] = {}
    for nf in states:
        r = root_fn(nf)
        # determinism guard: recompute is stable
        assert r == root_fn(nf), f"{label}: root not deterministic on {nf!r}"
        if r in state_by_root and state_by_root[r] != nf:
            raise AssertionError(
                f"STATE-ROOT COLLISION ({label}): distinct logical states "
                f"{state_by_root[r]!r} and {nf!r} share root {r}"
            )
        root_by_state[nf] = r
        state_by_root[r] = nf
    n = len(states)
    n_pairs = n * (n - 1) // 2
    return n, n_pairs, root_by_state


# ===========================================================================
# TEETH / NON-VACUITY. Plant real violations; the checker MUST raise.
# ===========================================================================

def _unframed_no_count_preimage(*, balances: BalanceTable, lp_balances: LPTable) -> bytes:
    """Deliberately BROKEN reference encoder (the ONLY re-implementation allowed):
    emit ONLY the raw (key,key,amount) rows of the balances then the LP section,
    back-to-back, with NO section label, NO section length prefix, NO entry
    count. A balance row and a byte-identical LP row become indistinguishable —
    the canonical framing bug."""
    out = bytearray()
    for pk_b, asset_b, amount in m._sorted_balance_entries(balances):
        out += pk_b + asset_b + m.encode_uvarint(amount)
    for pk_b, pool_b, amount in m._sorted_lp_entries(lp_balances):
        out += pk_b + pool_b + m.encode_uvarint(amount)
    return bytes(out)


def _buggy_root_of_normal_form(nf: tuple) -> str:
    bt, _pools, lp, _nt, _acc = _build_from_normal_form(nf)
    return sha256_hex(_unframed_no_count_preimage(balances=bt, lp_balances=lp))


def test_teeth_injectivity_checker_catches_a_constant_root():
    """A constant root collides everywhere; the ACTUAL checker `_assert_injective_over`
    must raise on the first pair of distinct states. Driven through the real
    helper (not a mirror) so the mandatory teeth exercise the same code path the
    sweeps use. Also asserts it does NOT raise when the planted bug is removed
    (a faithful per-state identity root => no collision)."""
    s1 = _normal_form({(PK[0], ASSET[0]): 1}, {}, {}, 0)
    s2 = _normal_form({(PK[0], ASSET[0]): 2}, {}, {}, 0)  # distinct amount
    assert s1 != s2

    constant = lambda _nf: "0x" + "00" * 32  # noqa: E731
    with pytest.raises(AssertionError, match="STATE-ROOT COLLISION"):
        _assert_injective_over([s1, s2], label="teeth-constant", root_fn=constant)

    # Bug removed => the same helper passes (proves the assertion is load-bearing,
    # not always-true): a faithful injective root yields no collision.
    faithful = lambda nf: sha256_hex(repr(nf).encode())  # noqa: E731
    n, pairs, _ = _assert_injective_over([s1, s2], label="teeth-faithful", root_fn=faithful)
    assert (n, pairs) == (2, 1)


def test_teeth_unframed_encoder_collides_real_encoder_does_not():
    """Plant a REAL framing collision and prove, THROUGH the actual checker:
      (a) the production FRAMED encoder keeps the two DIFFERENT logical states
          distinct (the safety property), and
      (b) the UNFRAMED reference COLLIDES, so the section label + length prefix
          is load-bearing, and
      (c) `_assert_injective_over` driven by the unframed reference RAISES, while
          driven by the real encoder it PASSES.

    S1: balances = {(PK,A): 7}, lp = {}.
    S2: balances = {},          lp = {(PK,A): 7}.
    These are DIFFERENT logical states (an asset balance vs an LP-share balance);
    the unframed reference emits the identical (PK|A|uvarint(7)) row for both."""
    s1 = _normal_form({(PK[0], ASSET[0]): 7}, {}, {}, 0)
    s2 = _normal_form({}, {(PK[0], ASSET[0]): 7}, {}, 0)
    assert s1 != s2

    # (a) framed encoder separates them.
    assert _root_of_normal_form(s1) != _root_of_normal_form(s2), (
        "production framed encoder must separate a BAL row from a byte-identical LPB row"
    )

    # (b) unframed reference collides.
    assert _buggy_root_of_normal_form(s1) == _buggy_root_of_normal_form(s2), (
        "unframed reference must collide (teeth setup)"
    )

    # (c) the ACTUAL checker, driven by the buggy root, RAISES ...
    with pytest.raises(AssertionError, match="STATE-ROOT COLLISION"):
        _assert_injective_over([s1, s2], label="teeth-unframed", root_fn=_buggy_root_of_normal_form)

    # ... while driven by the real (framed) encoder it PASSES (bug removed).
    n, pairs, _ = _assert_injective_over([s1, s2], label="teeth-framed-ok")
    assert (n, pairs) == (2, 1)


# ===========================================================================
# GENERATOR A — EXHAUSTIVE BOUNDED ENUMERATION (complete, not sampled).
# ===========================================================================

def test_exhaustive_balance_amount_boundaries_injective():
    """Sweep 1 (single-entry, full amount alphabet).

    Domain: exactly ONE balance entry, over EVERY (pk, asset, amount) with
    pk in {PK_a,PK_b}, asset in {A_x,A_y}, amount in the 10-element boundary set,
    PLUS the empty state. This is COMPLETE: every cell of the
    2 x 2 x 10 (+1 empty) grid is materialized and deduped, then ALL pairs are
    checked. It pins the LEB128 carry boundaries (127/128, 255/256, 65535/65536,
    2^32-1/2^32) against a width-confusion collision that random sampling would
    only hit by luck."""
    states = set()
    states.add(_normal_form({}, {}, {}, 0))  # empty
    for pk in PK:
        for a in ASSET:
            for amt in BOUNDARY_AMTS:
                states.add(_normal_form({(pk, a): amt}, {}, {}, 0))
    expected = 1 + len(PK) * len(ASSET) * len(BOUNDARY_AMTS)
    assert len(states) == expected, f"dedup changed domain size: {len(states)} != {expected}"
    n, pairs, _ = _assert_injective_over(states, label="bal-amount-boundaries")
    assert n == expected
    print(f"[exhaustive bal] enumerated N={n} states, checked C(N,2)={pairs} pairs")


def test_exhaustive_two_section_le3_entries_injective():
    """Sweep 2 (the core <=3-entry cross-section enumeration).

    Each of the 4 distinct balance keys and 4 distinct LP keys (pk x asset) is
    independently ABSENT or PRESENT-with-amount-in-{1,128,256,2^32} (a 4-value
    boundary sub-alphabet to keep the product complete-yet-bounded), the single
    fee dust is in {absent(0), 1}, subject to (#balance entries + #lp entries) <= 3.
    This is the EXHAUSTIVE product over that bound — every reachable small state
    is materialized, deduped to its normal form, and EVERY pair is checked.

    This is the region uniform-random PBT misses: it deterministically realizes
    the byte-identical (pk,asset) BAL row vs (pk,pool) LPB row living in the SAME
    state, every absent/zero equivalence, and every cross-section reordering, with
    a CERTIFICATE of completeness (the pair count), not a sample."""
    sub_amts = (1, 128, 256, 2**32)
    bal_keys = list(itertools.product(PK, ASSET))   # 4 keys
    lp_keys = list(itertools.product(PK, ASSET))    # 4 keys (pool space == asset space)
    # Per-key option: None (absent) or one of sub_amts.
    key_opts = (None,) + sub_amts

    states = set()
    enumerated = 0
    for bal_choice in itertools.product(key_opts, repeat=len(bal_keys)):
        n_bal = sum(1 for v in bal_choice if v is not None)
        if n_bal > 3:
            continue
        for lp_choice in itertools.product(key_opts, repeat=len(lp_keys)):
            n_lp = sum(1 for v in lp_choice if v is not None)
            if n_bal + n_lp > 3:
                continue
            for dust in (0, 1):
                enumerated += 1
                bal = {bal_keys[i]: v for i, v in enumerate(bal_choice) if v is not None}
                lp = {lp_keys[i]: v for i, v in enumerate(lp_choice) if v is not None}
                states.add(_normal_form(bal, lp, {}, dust))

    n, pairs, _ = _assert_injective_over(states, label="two-section-le3")
    assert n == len(states)
    # Honest reporting: raw enumerated cells vs deduped distinct logical states.
    print(
        f"[exhaustive 2-section] enumerated {enumerated} raw cells -> "
        f"N={n} distinct logical states, checked C(N,2)={pairs} pairs"
    )
    # EXACT completeness certificate: every enumerated cell is a distinct logical
    # state here (no two cells normalize equal), so N == raw cells, and the pair
    # count is fully determined by the bound.
    assert enumerated == 8130, f"enumeration size drifted: {enumerated}"
    assert n == 8130, f"deduped state count drifted: {n}"
    assert pairs == 8130 * 8129 // 2 == 33_044_385
    # Sanity: the empty state must survive (non-vacuity).
    assert _normal_form({}, {}, {}, 0) in states


def test_exhaustive_nonce_and_dust_boundaries_injective():
    """Sweep 3 (nonce x dust boundaries).

    EVERY (pk in {PK_a,PK_b}, nonce in {1,2,255,256,2^32-1}) single-nonce state,
    crossed with dust in {0,1,256}, plus the empty state. Pins the u32 nonce edge
    and the fee-dust section against a cross-section width-confusion collision,
    complete over the bound."""
    nonce_vals = (1, 2, 255, 256, 2**32 - 1)
    dusts = (0, 1, 256)
    states = set()
    for dust in dusts:
        states.add(_normal_form({}, {}, {}, dust))  # empty-nonce, varying dust
        for pk in PK:
            for nv in nonce_vals:
                states.add(_normal_form({}, {}, {pk: nv}, dust))
    # EXACT domain: 3 dusts x (1 empty + 2 pk x 5 nonce) = 3 x 11 = 33 distinct
    # logical states (the empty-nonce state still differs across the 3 dusts).
    expected = len(dusts) * (1 + len(PK) * len(nonce_vals))
    assert expected == 33
    assert len(states) == expected, f"nonce/dust dedup changed size: {len(states)} != {expected}"
    n, pairs, _ = _assert_injective_over(states, label="nonce-dust-boundaries")
    assert n == 33
    assert pairs == 33 * 32 // 2 == 528
    print(f"[exhaustive nonce/dust] N={n} states, checked C(N,2)={pairs} pairs")


def _pool_root_identity(pool: PoolState) -> tuple:
    """Decoded logical identity for the bounded single-pool enumeration."""
    return (
        _asset_bytes(pool.pool_id),
        _asset_bytes(pool.asset0),
        _asset_bytes(pool.asset1),
        int(pool.reserve0),
        int(pool.reserve1),
        int(pool.fee_bps),
        int(pool.lp_supply),
        pool.status,
        int(pool.created_at),
        str(pool.curve_tag),
        str(pool.curve_params),
    )


def test_exhaustive_single_pool_field_boundaries_injective():
    """Sweep 4 (single-pool field lattice).

    Domain: one canonical asset pair with the pool ID derived from fee and curve
    identity fields, while committed fields vary over boundary-rich alphabets:
      reserve0/reserve1 in {0, 1, 128}
      fee_bps in {0, 30, 10000}
      lp_supply in {0, 1, 2^32}
      status in {ACTIVE, FROZEN, DISABLED}
      created_at in {0, 1}
      curve config in {CPMM, CUBIC_SUM_V1(p=1,q=1), SUM_BOOST_V1(1/2)}

    This is complete over the declared single-pool bound. It upgrades the pool
    section from seed-covered to a small exact field lattice. Every distinct
    decoded pool identity must yield a distinct root."""
    a0, a1 = (ASSET[0], ASSET[1]) if ASSET[0] < ASSET[1] else (ASSET[1], ASSET[0])
    reserves = (0, 1, 128)
    fee_bps_values = (0, 30, 10_000)
    lp_supplies = (0, 1, 2**32)
    statuses = (PoolStatus.ACTIVE, PoolStatus.FROZEN, PoolStatus.DISABLED)
    created_at_values = (0, 1)
    curves = (
        ("CPMM", ""),
        ("CUBIC_SUM_V1", '{"p":1,"q":1}'),
        ("SUM_BOOST_V1", '{"mu_den":2,"mu_num":1}'),
    )

    root_by_identity: dict[tuple, str] = {}
    identity_by_root: dict[str, tuple] = {}
    for reserve0, reserve1, fee_bps, lp_supply, status, created_at, curve in itertools.product(
        reserves,
        reserves,
        fee_bps_values,
        lp_supplies,
        statuses,
        created_at_values,
        curves,
    ):
        pid = compute_pool_id(
            a0,
            a1,
            fee_bps,
            curve_tag=curve[0],
            curve_params=curve[1],
        )
        pool = PoolState(
            pool_id=pid,
            asset0=a0,
            asset1=a1,
            reserve0=reserve0,
            reserve1=reserve1,
            fee_bps=fee_bps,
            lp_supply=lp_supply,
            status=status,
            created_at=created_at,
            curve_tag=curve[0],
            curve_params=curve[1],
        )
        identity = _pool_root_identity(pool)
        assert identity not in root_by_identity, f"duplicate pool identity in enumeration: {identity}"
        root = _root(BalanceTable(), {pid: pool}, LPTable(), NonceTable())
        assert root == _root(BalanceTable(), {pid: pool}, LPTable(), NonceTable()), (
            f"pool root not deterministic for {identity!r}"
        )
        if root in identity_by_root and identity_by_root[root] != identity:
            raise AssertionError(
                f"POOL STATE-ROOT COLLISION: distinct pool identities "
                f"{identity_by_root[root]!r} and {identity!r} share root {root}"
            )
        root_by_identity[identity] = root
        identity_by_root[root] = identity

    n = len(root_by_identity)
    pairs = n * (n - 1) // 2
    expected = (
        len(reserves)
        * len(reserves)
        * len(fee_bps_values)
        * len(lp_supplies)
        * len(statuses)
        * len(created_at_values)
        * len(curves)
    )
    assert n == expected == 1458
    assert pairs == 1458 * 1457 // 2 == 1_062_153
    print(f"[exhaustive single-pool] N={n} states, checked C(N,2)={pairs} pairs")


def _lp_duration_risk_root_identity(
    *,
    pubkey: str,
    pool_id: str,
    amount: int,
    last_mint_timestamp: int | None,
    last_remove_timestamp: int | None,
    churn_tier: int,
    last_churn_update_timestamp: int | None,
) -> tuple:
    """Decoded logical identity for the bounded LP duration-risk enumeration."""
    return (
        _pk_bytes(pubkey),
        _asset_bytes(pool_id),
        int(amount),
        last_mint_timestamp,
        last_remove_timestamp,
        int(churn_tier),
        last_churn_update_timestamp,
    )


def _lp_duration_risk_table_from_identity(identity: tuple) -> LPTable:
    pk_b, pool_b, amount, last_mint, last_remove, churn_tier, last_churn_update = identity
    pubkey = "0x" + pk_b.hex()
    pool_id = "0x" + pool_b.hex()
    lp = LPTable()
    lp.set(pubkey, pool_id, amount)
    if last_mint is not None:
        lp.set_last_mint_timestamp(pubkey, pool_id, last_mint)
    if last_remove is not None:
        lp.set_last_remove_timestamp(pubkey, pool_id, last_remove)
    if churn_tier:
        lp.set_churn_tier(pubkey, pool_id, churn_tier)
    if last_churn_update is not None:
        lp.set_last_churn_update_timestamp(pubkey, pool_id, last_churn_update)
    return lp


def test_exhaustive_lp_duration_risk_field_boundaries_injective():
    """Sweep 5 (single-LP duration-risk field lattice).

    Domain: one fixed (pubkey, pool_id) LP key with a fixed positive LP balance,
    while every committed duration-risk metadata field varies over small
    boundary alphabets:
      last_mint_timestamp in {None, 0, 1, 128}
      last_remove_timestamp in {None, 0, 1, 128}
      churn_tier in {0, 1, 2}
      last_churn_update_timestamp in {None, 0, 1, 128}

    The LP amount is fixed at 1 so the sweep isolates LPA metadata framing. Every
    distinct decoded metadata identity must produce a distinct spot-DEX state
    root."""
    pubkey = PK[0]
    pool_id = "0x" + "42" * 32
    amount = 1
    timestamps = (None, 0, 1, 128)
    churn_tiers = (0, 1, 2)

    root_by_identity: dict[tuple, str] = {}
    identity_by_root: dict[str, tuple] = {}
    for last_mint, last_remove, churn_tier, last_churn_update in itertools.product(
        timestamps,
        timestamps,
        churn_tiers,
        timestamps,
    ):
        identity = _lp_duration_risk_root_identity(
            pubkey=pubkey,
            pool_id=pool_id,
            amount=amount,
            last_mint_timestamp=last_mint,
            last_remove_timestamp=last_remove,
            churn_tier=churn_tier,
            last_churn_update_timestamp=last_churn_update,
        )
        assert identity not in root_by_identity, f"duplicate LP metadata identity: {identity}"
        lp = _lp_duration_risk_table_from_identity(identity)
        root = _root(BalanceTable(), {}, lp, NonceTable())
        assert root == _root(BalanceTable(), {}, lp, NonceTable()), (
            f"LP duration-risk root not deterministic for {identity!r}"
        )
        if root in identity_by_root and identity_by_root[root] != identity:
            raise AssertionError(
                f"LP DURATION-RISK STATE-ROOT COLLISION: distinct identities "
                f"{identity_by_root[root]!r} and {identity!r} share root {root}"
            )
        root_by_identity[identity] = root
        identity_by_root[root] = identity

    n = len(root_by_identity)
    pairs = n * (n - 1) // 2
    expected = len(timestamps) * len(timestamps) * len(churn_tiers) * len(timestamps)
    assert n == expected == 192
    assert pairs == 192 * 191 // 2 == 18_336
    print(f"[exhaustive LP duration-risk] N={n} states, checked C(N,2)={pairs} pairs")


# ===========================================================================
# GENERATOR B — ADVERSARIAL STRUCTURAL SEEDS.
# Hand-crafted collision shapes; each asserts the encoder's ACTUAL relation.
# ===========================================================================

def test_adv_balance_row_vs_byte_identical_lp_row_differ():
    """(a) + (g): a balance row {(PK,A):x} vs the byte-identical LP-share row
    {(PK,A):x}. DIFFERENT logical states (asset vs LP-share); the framed encoder
    MUST separate them via the BAL/LPB labels + section lengths."""
    for x in BOUNDARY_AMTS:
        s_bal = _normal_form({(PK[0], ASSET[0]): x}, {}, {}, 0)
        s_lp = _normal_form({}, {(PK[0], ASSET[0]): x}, {}, 0)
        assert s_bal != s_lp
        assert _root_of_normal_form(s_bal) != _root_of_normal_form(s_lp), (
            f"BAL vs LPB row collide at amount {x}"
        )


def test_adv_field_boundary_shift_two_entries_differ():
    """(b) FIELD-BOUNDARY SHIFT.

    Within the balances section a row is pk(48) || asset(32) || uvarint(amount).
    Construct two DIFFERENT 2-entry balance states that share the SAME multiset
    of pubkeys/assets but pair them differently:
      S1: {(PK_a, A_x): v1, (PK_b, A_y): v2}
      S2: {(PK_a, A_y): v1, (PK_b, A_x): v2}
    If asset were not bound (length/position) to its pubkey, the concatenations
    could coincide. The fixed-width framing must keep them distinct."""
    v1, v2 = 128, 256
    s1 = _normal_form({(PK[0], ASSET[0]): v1, (PK[1], ASSET[1]): v2}, {}, {}, 0)
    s2 = _normal_form({(PK[0], ASSET[1]): v1, (PK[1], ASSET[0]): v2}, {}, {}, 0)
    assert s1 != s2
    assert _root_of_normal_form(s1) != _root_of_normal_form(s2), "field-boundary shift collides"

    # Stronger: equal amounts so ONLY the (pk<->asset) pairing differs.
    s3 = _normal_form({(PK[0], ASSET[0]): 200, (PK[1], ASSET[1]): 200}, {}, {}, 0)
    s4 = _normal_form({(PK[0], ASSET[1]): 200, (PK[1], ASSET[0]): 200}, {}, {}, 0)
    assert s3 != s4
    assert _root_of_normal_form(s3) != _root_of_normal_form(s4), "pairing-only shift collides"


def test_adv_hex_case_variants_are_same_logical_state():
    """(c): hex CASE (0xAB vs 0xAB upper) spellings that DECODE to the same bytes
    are the SAME logical state and MUST share a root. This is spelling-
    independence (a SAFETY property the verifier relies on), asserted as equality
    — NOT a collision.

    NOTE: the encoder requires EXACT fixed-width hex (``hex_to_bytes_fixed`` at
    canonical.py), so leading-zero / variable-width spellings of the same logical
    value are REJECTED inputs, not collision candidates. CASE is the only
    decode-equal spelling variant available here.

    We drive it through the real encoder by building tables keyed with the two
    spellings and confirming equal roots, AND confirming the encoder fails closed
    if both spellings of one key were ever fed into the SAME table."""
    pk_lower = "0x" + "ab" * 48
    pk_upper = "0x" + "AB" * 48
    a_lower = "0x" + "cd" * 32
    a_upper = "0x" + "CD" * 32

    bt1 = BalanceTable(); bt1.set(pk_lower, a_lower, 99)
    bt2 = BalanceTable(); bt2.set(pk_upper, a_upper, 99)
    r1 = sha256_hex(m.state_root_preimage(balances=bt1, pools={}, lp_balances=LPTable(), nonces=NonceTable()))
    r2 = sha256_hex(m.state_root_preimage(balances=bt2, pools={}, lp_balances=LPTable(), nonces=NonceTable()))
    assert r1 == r2, "decode-equal hex spellings must hash to the SAME root (spelling independence)"

    # Fail-closed: two distinct spellings of ONE decoded key in one table.
    bt_dup = BalanceTable()
    bt_dup.set(pk_lower, a_lower, 1)
    bt_dup.set(pk_upper, a_upper, 2)  # same decoded key, different stored string
    with pytest.raises(ValueError, match="duplicate decoded"):
        m.state_root_preimage(balances=bt_dup, pools={}, lp_balances=LPTable(), nonces=NonceTable())


def test_adv_absent_vs_explicit_zero_are_same():
    """(e) empty/absent vs explicit-zero.

    - A balance/LP entry set to 0 is dropped by the table => identical to absent.
    - fee dust None is identical to dust 0 (see ``_fee_accumulator_dust``).
    All three must hash to the SAME root as the empty state."""
    empty = _build_from_normal_form(_normal_form({}, {}, {}, 0))
    r_empty = _root(*empty)

    # Explicit-zero balance: set then it is dropped.
    bt = BalanceTable(); bt.set(PK[0], ASSET[0], 0)
    lp = LPTable(); lp.set(PK[0], ASSET[0], 0)
    r_zero = _root(bt, {}, lp, NonceTable(), _Acc(0))
    assert r_zero == r_empty, "explicit-zero entries must equal the empty state"

    # dust None vs dust 0.
    r_dust_none = _root(BalanceTable(), {}, LPTable(), NonceTable(), None)
    r_dust_zero = _root(BalanceTable(), {}, LPTable(), NonceTable(), _Acc(0))
    assert r_dust_none == r_dust_zero == r_empty, "dust None must equal dust 0 (and the empty state)"


def test_adv_split_aliasing_x_plus_y_vs_x_and_y_differ():
    """(f) SPLIT ALIASING.

    One key holding (x+y) vs two keys holding x and y must be DISTINCT states:
      S1: balances {(PK_a, A_x): x+y}
      S2: balances {(PK_a, A_x): x, (PK_b, A_x): y}
    A length/count framing bug (entry count not committed) is exactly what would
    let these collide. The framed encoder must separate them."""
    for x, y in ((1, 1), (127, 1), (128, 128), (1, 2**32 - 1)):
        s1 = _normal_form({(PK[0], ASSET[0]): x + y}, {}, {}, 0)
        s2 = _normal_form({(PK[0], ASSET[0]): x, (PK[1], ASSET[0]): y}, {}, {}, 0)
        assert s1 != s2
        assert _root_of_normal_form(s1) != _root_of_normal_form(s2), (
            f"split aliasing collides for x={x} y={y}"
        )

    # Same-key amount split across sections: bal x+y  vs  bal x + lp y on same key.
    s3 = _normal_form({(PK[0], ASSET[0]): 200}, {}, {}, 0)
    s4 = _normal_form({(PK[0], ASSET[0]): 100}, {(PK[0], ASSET[0]): 100}, {}, 0)
    assert s3 != s4
    assert _root_of_normal_form(s3) != _root_of_normal_form(s4), "cross-section split aliasing collides"


def test_adv_support_root_section_aliasing_differs():
    """Adversarial seed against the PROJECTED commitment (``support_root.py``),
    which uses the SAME b'BAL'/b'LPB' label + length framing.

    Same byte-identical (pk, A) appearing as a support BALANCE entry vs a support
    LP entry must yield DIFFERENT support roots. Also a balance amount split
    x+y vs x,y across two support keys must differ."""
    pk0, pk1, a0 = PK[0], PK[1], ASSET[0]

    # (g)/(a) for support: balance key vs lp key, byte-identical row.
    bt = BalanceTable(); bt.set(pk0, a0, 7)
    sup_b = BatchStateSupport(balance_keys=((pk0, a0),), pool_ids=(), lp_keys=(), nonce_keys=())
    r_b = compute_support_state_root(balances=bt, pools={}, lp_balances=LPTable(), support=sup_b)

    lp = LPTable(); lp.set(pk0, a0, 7)
    sup_l = BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=((pk0, a0),), nonce_keys=())
    r_l = compute_support_state_root(balances=BalanceTable(), pools={}, lp_balances=lp, support=sup_l)
    assert r_b != r_l, "support BAL row vs LPB row collide"

    # (f) split aliasing in support balances.
    bt1 = BalanceTable(); bt1.set(pk0, a0, 200)
    sup1 = BatchStateSupport(balance_keys=((pk0, a0),), pool_ids=(), lp_keys=(), nonce_keys=())
    r1 = compute_support_state_root(balances=bt1, pools={}, lp_balances=LPTable(), support=sup1)

    bt2 = BalanceTable(); bt2.set(pk0, a0, 100); bt2.set(pk1, a0, 100)
    sup2 = BatchStateSupport(balance_keys=((pk0, a0), (pk1, a0)), pool_ids=(), lp_keys=(), nonce_keys=())
    r2 = compute_support_state_root(balances=bt2, pools={}, lp_balances=LPTable(), support=sup2)
    assert r1 != r2, "support split aliasing collides"


def test_adv_pool_status_and_curve_seeds_differ():
    """Two adversarial POOL seeds (the one section Gen A leaves out):
      - same canonical pool, only ``status`` differs;
      - identity-bound curve config differs (CPMM vs CUBIC_SUM_V1), with each
        pool carrying its corresponding canonical ID.
    All must yield distinct roots — the status code and curve framing are
    committed."""
    a0, a1 = (ASSET[0], ASSET[1]) if ASSET[0] < ASSET[1] else (ASSET[1], ASSET[0])

    def pool_root(status, tag, params):
        pid = compute_pool_id(
            a0,
            a1,
            30,
            curve_tag=tag,
            curve_params=params,
        )
        p = PoolState(
            pool_id=pid, asset0=a0, asset1=a1, reserve0=10, reserve1=20,
            fee_bps=30, lp_supply=5, status=status, created_at=7,
            curve_tag=tag, curve_params=params,
        )
        return _root(BalanceTable(), {pid: p}, LPTable(), NonceTable())

    roots = {
        ("ACTIVE", "CPMM"): pool_root(PoolStatus.ACTIVE, "CPMM", ""),
        ("FROZEN", "CPMM"): pool_root(PoolStatus.FROZEN, "CPMM", ""),
        ("DISABLED", "CPMM"): pool_root(PoolStatus.DISABLED, "CPMM", ""),
        ("ACTIVE", "CUBIC"): pool_root(PoolStatus.ACTIVE, "CUBIC_SUM_V1", '{"p":1,"q":1}'),
    }
    distinct = set(roots.values())
    assert len(distinct) == len(roots), f"pool status/curve seeds collide: {roots}"
