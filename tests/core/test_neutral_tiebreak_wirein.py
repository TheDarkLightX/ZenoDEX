"""Wire-in tests for the grinding-resistant tie-break (src/core/neutral_tiebreak.py)
and its dormant, default-off seam in batch_clearing_ordering._ab_ordering_key.

Two guarantees:
  1. CHARACTERIZATION: with ``seed=None`` (the production default; no caller passes
     a seed) the canonical key is byte-identical to the pre-seam intent_id tuple.
  2. SEEDED: a non-None seed preserves (A, B) and replaces ONLY the tie-break
     component with a grinding-resistant token, so it can de-grind the tie winner.
"""

from __future__ import annotations

import hashlib

import pytest

from src.core.batch_clearing_ordering import (
    _ab_ordering_key,
    _is_better_ab_key,
    _order_swaps_greedy_ab,
    _order_swaps_limit_price,
    _order_swaps_mci_ab,
)
from src.core.batch_clearing import (
    _SWAP_ORDERING_COW_PAIR_NETTING_V1,
    clear_batch_single_pool,
)
from src.core.neutral_tiebreak import neutral_tiebreak_key, tiebreak_token
from src.core.settlement import FillAction
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

# A deterministic characterization corpus of (A, B, id-tuple) canonical keys.
CORPUS = [
    (100, 5, ("z-intent", "a-intent", "m-intent")),
    (0, 0, ()),
    (250, 9, ("only-one",)),
    (1_000_000, 1, ("0x" + "11" * 4, "0x" + "22" * 4)),
    (7, 7, ("dup", "dup")),  # repeated ids
]
SEED = b"per-batch-seed-fixed-before-ids"


# --- Promoted primitive -------------------------------------------------

def test_token_none_is_identity():
    assert tiebreak_token("intent-1", None) == "intent-1"


def test_seeded_key_is_deterministic_and_distinct():
    assert neutral_tiebreak_key(SEED, "a") == neutral_tiebreak_key(SEED, "a")
    assert neutral_tiebreak_key(SEED, "a") != neutral_tiebreak_key(SEED, "b")


def test_framing_is_collision_free():
    # canonical length-prefixed framing must not collide across the field boundary
    assert neutral_tiebreak_key(b"ab", "c") != neutral_tiebreak_key(b"a", "bc")


def test_seeded_token_is_fair_over_seeds():
    # No single identifier wins the min-token across random seeds more than ~1/k.
    ids = [f"intent-{i:03d}" for i in range(8)]
    rng = __import__("random").Random(99)
    seeds = [rng.randbytes(16) for _ in range(2000)]
    wins = {i: 0 for i in ids}
    for s in seeds:
        winner = min(ids, key=lambda i: neutral_tiebreak_key(s, i))
        wins[winner] += 1
    for i, c in wins.items():
        assert abs(c / len(seeds) - 1 / len(ids)) < 0.04


def test_rejects_bad_inputs():
    with pytest.raises(TypeError):
        neutral_tiebreak_key("not-bytes", "id")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        neutral_tiebreak_key(b"s", 123)  # type: ignore[arg-type]


# --- Characterization: seed=None is byte-identical ----------------------

def test_ab_key_seed_none_reproduces_intent_id_tuple():
    for a, b, ids in CORPUS:
        key = _ab_ordering_key(A_B_order=(a, b, ids))
        assert key == (a, b, ids)  # third component unchanged → grindable status quo


def test_ab_key_seed_none_matches_default_call():
    # The default (no seed kwarg) and explicit seed=None are identical.
    for a, b, ids in CORPUS:
        assert _ab_ordering_key(A_B_order=(a, b, ids)) == _ab_ordering_key(
            A_B_order=(a, b, ids), seed=None
        )


# --- Seeded: preserves (A, B), only the tie-break changes ----------------

def test_seeded_ab_key_preserves_ab_and_reseeds_tiebreak():
    for a, b, ids in CORPUS:
        plain = _ab_ordering_key(A_B_order=(a, b, ids))
        seeded = _ab_ordering_key(A_B_order=(a, b, ids), seed=SEED)
        assert seeded[0] == plain[0] == a  # A preserved
        assert seeded[1] == plain[1] == b  # B preserved
        assert seeded[2] == tuple(neutral_tiebreak_key(SEED, str(x)) for x in ids)
        if ids:
            assert seeded[2] != plain[2]  # tie-break component is reseeded


def test_seed_de_grinds_the_tie_winner():
    # Two orderings tied on (A, B) but different id tuples. Under intent_id the
    # lexicographically-smaller id tuple always wins (grindable). Under a seed the
    # winner is decided by the seeded tokens — find a seed where it flips, proving
    # a participant cannot guarantee a win by choosing a small intent_id.
    a, b = 100, 5
    x = (100, 5, ("aaaa", "zzzz"))
    y = (100, 5, ("zzzz", "aaaa"))  # same (A,B), reverse ids
    plain_x = _ab_ordering_key(A_B_order=x)
    plain_y = _ab_ordering_key(A_B_order=y)
    # intent_id: x (with "aaaa" first) is lexicographically smaller → x is "better".
    assert _is_better_ab_key(plain_x, plain_y) is True
    flipped = False
    for k in range(64):
        s = hashlib.sha256(bytes([k])).digest()
        sx = _ab_ordering_key(A_B_order=x, seed=s)
        sy = _ab_ordering_key(A_B_order=y, seed=s)
        if _is_better_ab_key(sx, sy) is False:  # seed makes y win instead
            flipped = True
            break
    assert flipped, "seeded tie-break never flipped the winner — unexpected"


# --- The DEFAULT (greedy) path and the other entries de-grind when seeded -----

def _pool() -> PoolState:
    return PoolState(
        pool_id="pool_ab", asset0="A", asset1="B",
        reserve0=1_000_000, reserve1=1_000_000, fee_bps=30,
        lp_supply=1_000_000, status=PoolStatus.ACTIVE, created_at=0,
    )


def _swap(label: str, amount_in: int = 1000) -> Intent:
    import hashlib as _h
    return Intent(
        module="TauSwap", version="0.1",
        intent_id="0x" + _h.sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey="0x" + "11" * 48,
        kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
        fields={"pool_id": "pool_ab", "asset_in": "A", "asset_out": "B",
                "amount_in": amount_in, "min_amount_out": 0},
    )


def _order_ids(fn, intents, *, seed):
    pool = _pool()
    return [it.intent_id for it in fn(intents, pool_state=pool, reserves=(pool.reserve0, pool.reserve1), seed=seed)]


def test_default_greedy_path_unchanged_and_de_grindable():
    # Two identical-size A->B swaps: same (A,B) contribution, so the order is
    # decided purely by the tie-break — this is the grindable default path.
    a, b = _swap("alpha"), _swap("omega")
    intents = [a, b]
    pool = _pool()
    res = (pool.reserve0, pool.reserve1)
    default = [it.intent_id for it in _order_swaps_greedy_ab(intents, pool_state=pool, reserves=res)]
    none_kw = _order_ids(_order_swaps_greedy_ab, intents, seed=None)
    assert default == none_kw                              # seed=None is byte-identical
    assert default[0] == min(a.intent_id, b.intent_id)     # default picks small id (grindable)
    flipped = any(
        _order_ids(_order_swaps_greedy_ab, intents, seed=hashlib.sha256(bytes([k])).digest()) != default
        for k in range(64)
    )
    assert flipped, "seeded greedy never reordered equal swaps — default path NOT de-grinded"


def test_limit_price_path_unchanged_and_de_grindable():
    a, b = _swap("alpha"), _swap("omega")
    intents = [a, b]
    default = [it.intent_id for it in _order_swaps_limit_price(intents)]
    assert default == [it.intent_id for it in _order_swaps_limit_price(intents, seed=None)]
    flipped = any(
        [it.intent_id for it in _order_swaps_limit_price(intents, seed=hashlib.sha256(bytes([k])).digest())] != default
        for k in range(64)
    )
    assert flipped


def test_all_entries_seed_none_is_byte_identical():
    intents = [_swap("alpha"), _swap("omega"), _swap("mike")]
    pool = _pool()
    res = (pool.reserve0, pool.reserve1)
    for fn in (_order_swaps_greedy_ab, _order_swaps_mci_ab):
        a = [it.intent_id for it in fn(intents, pool_state=pool, reserves=res)]
        b = [it.intent_id for it in fn(intents, pool_state=pool, reserves=res, seed=None)]
        assert a == b, f"{fn.__name__}: seed=None changed the order"


# --- End-to-end: the seed plumbs through the public settlement entry ----------

def _swap_from(label: str, sender: str, amount_in: int = 5000) -> Intent:
    import hashlib as _h
    return Intent(
        module="TauSwap", version="0.1",
        intent_id="0x" + _h.sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey=sender, kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
        fields={"pool_id": "pool_ab", "asset_in": "A", "asset_out": "B",
                "amount_in": amount_in, "min_amount_out": 0},
    )


def _fill_order(fills):
    return [f.intent_id for f in fills if f.action == FillAction.FILL]


def test_clear_batch_single_pool_seed_plumbs_end_to_end():
    # The public settlement entry now threads the default-off seed all the way to
    # the ordering. Two tied A->B swaps: their settled order is decided by the
    # tie-break, so the seed is observable in the final fills.
    pool = _pool()
    swaps = [_swap_from("alpha", "alice"), _swap_from("omega", "bob")]
    bal = BalanceTable()
    bal.set("alice", "A", 1_000_000)
    bal.set("bob", "A", 1_000_000)

    default = _fill_order(clear_batch_single_pool(swaps, pool, bal, LPTable()))
    none_kw = _fill_order(clear_batch_single_pool(swaps, pool, bal, LPTable(), swap_tiebreak_seed=None))
    assert default == none_kw and len(default) == 2  # seed=None is byte-identical

    # Some seed reorders the settled fills -> de-grinded through the public API.
    flipped = False
    for k in range(64):
        s = hashlib.sha256(bytes([k])).digest()
        if _fill_order(clear_batch_single_pool(swaps, pool, bal, LPTable(), swap_tiebreak_seed=s)) != default:
            flipped = True
            break
    assert flipped, "seed never changed the settled order through clear_batch_single_pool"

    # Replayable: identical seed -> identical settlement (consensus-safe determinism).
    s = hashlib.sha256(b"fixed-batch-seed").digest()
    r1 = _fill_order(clear_batch_single_pool(swaps, pool, bal, LPTable(), swap_tiebreak_seed=s))
    r2 = _fill_order(clear_batch_single_pool(swaps, pool, bal, LPTable(), swap_tiebreak_seed=s))
    assert r1 == r2 and sorted(r1) == sorted(default)  # same set, possibly different order


# --- CoW pair-netting path: tie-break also de-grinds when seeded --------------

def _swap_dir(label, sender, asset_in, asset_out, amount_in=1000, min_out=900):
    import hashlib as _h
    return Intent(
        module="TauSwap", version="0.1",
        intent_id="0x" + _h.sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey=sender, kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
        fields={"pool_id": "pool_ab", "asset_in": asset_in, "asset_out": asset_out,
                "amount_in": amount_in, "min_amount_out": min_out},
    )


def test_cow_netting_path_de_grinds_when_seeded():
    # alice & carol both A->B compete to net with bob's single B->A. Both candidate
    # match-sets have equal (volume, surplus), so WHICH one nets is decided purely
    # by the CoW pair-selection tie-break — grindable by intent_id today.
    pool = _pool()
    swaps = [
        _swap_dir("alpha", "alice", "A", "B"),
        _swap_dir("carol", "carol", "A", "B"),
        _swap_dir("bravo", "bob", "B", "A"),
    ]
    bal = BalanceTable()
    bal.set("alice", "A", 1_000_000)
    bal.set("carol", "A", 1_000_000)
    bal.set("bob", "B", 1_000_000)

    def netted(seed):
        fills = clear_batch_single_pool(
            swaps, pool, bal, LPTable(),
            swap_ordering=_SWAP_ORDERING_COW_PAIR_NETTING_V1, swap_tiebreak_seed=seed,
        )
        return frozenset(f.intent_id for f in fills if f.reason == "COW_NETTED")

    base = netted(None)
    assert base == netted(None)                       # deterministic
    assert len(base) == 2 and swaps[2].intent_id in base  # bob + one of alice/carol
    # a seed flips WHICH of alice/carol nets with bob -> CoW tie-break de-grinded
    flipped = any(netted(hashlib.sha256(bytes([k])).digest()) != base for k in range(64))
    assert flipped, "CoW netting tie-break was not de-grinded by the seed"
    # replayable: identical seed -> identical netting decision
    s = hashlib.sha256(b"cow-seed").digest()
    assert netted(s) == netted(s)


def test_cow_greedy_path_de_grinds_when_seeded():
    # >8 candidates routes to the GREEDY matcher (_select_cow_pairs_greedy), which
    # picks each counterparty via the best_y tie-break. 5 A->B vs 6 B->A: exactly
    # one B->A stays unmatched, and WHICH one is decided by the (now seeded) key.
    pool = _pool()
    swaps = []
    bal = BalanceTable()
    for i in range(5):
        s = f"ax{i}"
        swaps.append(_swap_dir(f"a{i}", s, "A", "B"))
        bal.set(s, "A", 1_000_000)
    for j in range(6):
        s = f"by{j}"
        swaps.append(_swap_dir(f"b{j}", s, "B", "A"))
        bal.set(s, "B", 1_000_000)
    assert len(swaps) == 11  # 5 + 6 > 8 -> greedy path

    def netted(seed):
        fills = clear_batch_single_pool(
            swaps, pool, bal, LPTable(),
            swap_ordering=_SWAP_ORDERING_COW_PAIR_NETTING_V1, swap_tiebreak_seed=seed,
        )
        return frozenset(f.intent_id for f in fills if f.reason == "COW_NETTED")

    base = netted(None)
    assert base == netted(None)  # deterministic
    flipped = any(netted(hashlib.sha256(bytes([k])).digest()) != base for k in range(96))
    assert flipped, "greedy CoW best_y tie-break was not de-grinded by the seed"
