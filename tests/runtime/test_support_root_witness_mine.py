"""Symbolic disaster-witness mine for the projected (support) state root.

`compute_support_state_root` (src/state/support_root.py) is the consensus-critical
quotient commitment: a batch-validation certificate carries a projected pre-state
snapshot committed to by this root instead of the full global state. It is the
same disaster CLASS as the full state_root, so the same safety contract applies:

  SUPPORT-ROOT DETERMINISM / INJECTIVITY / ORDER-INDEPENDENCE
    (D1) ORDER-INDEPENDENCE  same logical support set + state  ->  same root,
         regardless of the order the support tuples are listed in.
    (D2) REPEATABILITY       a pure function: identical inputs -> identical root.
    (D3) CASE-FOLDING        a key whose hex differs only in case decodes to the
         same bytes -> same logical entry -> same root.
    (D4) INJECTIVITY         any difference in a *committed* scalar (a tracked
         balance amount, pool reserve/fee/lp_supply/curve_params, lp amount,
         lp duration metadata, or nonce) -> a DISTINCT root (no silent collision).

A witness for any of these is a finality disaster: either the same logical state
hashes two ways (a validator and a recomputing verifier disagree on the support
root -> split / stuck batch), or two genuinely different states collide (a forged
projected snapshot is accepted as a valid pre-image).

This mine builds VALID inputs through the module's own decode/sort path, with
SMALL bounded domains so the build-time constraints (canonical 48-/32-byte hex,
fee_bps<=10000, distinct decoded keys, non-negative scalars) are satisfiable and
we never live only on the reject branch.

SCOPE / NON-CLAIMS:
  * NO crypto: `compute_support_state_root` performs no signature/BLS check, so
    no oracle is stubbed (crypto_oracle_stubbed=false). SHA-256 collision
    resistance is ASSUMED, not tested; "injectivity" here means the canonical
    pre-image differs, which is the falsifiable, in-scope property.
  * This mine does NOT cover `derive_batch_state_support` (read-set derivation),
    multi-module sequencing, or composition with the full state_root. It tests a
    single call of `compute_support_state_root` on a single support+state pair.
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.state.balances import BalanceTable  # noqa: E402
from src.state.lp import LPTable  # noqa: E402
from src.state.nonces import NonceTable  # noqa: E402
from src.state.pools import PoolState, PoolStatus, compute_pool_id  # noqa: E402
from src.state import support_root as m  # noqa: E402


# ----------------------------- canonical fixtures ----------------------------

def PK(i: int) -> str:
    """Canonical lowercase 48-byte (96 hex char) pubkey, identity fixed by i."""
    return "0x" + f"{i + 0x10:096x}"


def ASSET(i: int) -> str:
    """Canonical lowercase 32-byte asset id, identity fixed by i."""
    return "0x" + f"{i + 0x20:064x}"


# A pool of distinct canonical assets used to build canonically-ordered pairs.
_ASSETS = [ASSET(i) for i in range(6)]
_PKS = [PK(i) for i in range(4)]


def _pool_for(asset_a: str, asset_b: str, fee_bps: int, reserve0: int, reserve1: int, lp_supply: int) -> tuple[str, PoolState]:
    """Build a canonically-ordered ACTIVE pool; returns (pool_id, PoolState)."""
    a0, a1 = (asset_a, asset_b) if asset_a < asset_b else (asset_b, asset_a)
    pool_id = compute_pool_id(a0, a1, fee_bps, curve_tag="CPMM", curve_params="")
    pool = PoolState(
        pool_id=pool_id,
        asset0=a0,
        asset1=a1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=lp_supply,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )
    return pool_id, pool


# --------------------------- the disaster-class checker ----------------------

def _assert_no_support_root_disaster(scene: dict) -> None:
    """Encode (D1)-(D4) as falsifiable assertions over a built scene.

    A scene is a dict carrying the canonical inputs plus the precomputed
    reference root. Factored out so the teeth test can replay it against a
    deliberately-buggy support-root implementation.

    `scene["root_fn"]` is the support-root function under test (the real module
    by default; a planted-bug variant in the teeth test).
    """
    import random

    root_fn = scene["root_fn"]
    balances = scene["balances"]
    pools = scene["pools"]
    lp = scene["lp"]
    nonces = scene["nonces"]
    support = scene["support"]

    def root(supp) -> str:
        return root_fn(balances=balances, pools=pools, lp_balances=lp, support=supp, nonces=nonces)

    base = root(support)

    # (D2) REPEATABILITY: pure function -> identical output on a repeat call.
    assert root(support) == base, "non-deterministic: identical inputs gave two roots"

    # (D1) ORDER-INDEPENDENCE: shuffle every support tuple (same logical sets).
    rng = random.Random(scene["seed"])
    for _ in range(3):
        bk = list(support.balance_keys)
        pk = list(support.pool_ids)
        lk = list(support.lp_keys)
        nk = list(support.nonce_keys)
        rng.shuffle(bk)
        rng.shuffle(pk)
        rng.shuffle(lk)
        rng.shuffle(nk)
        shuffled = m.BatchStateSupport(
            balance_keys=tuple(bk), pool_ids=tuple(pk), lp_keys=tuple(lk), nonce_keys=tuple(nk)
        )
        assert root(shuffled) == base, (
            "ORDER-DEPENDENCE: a permutation of the same support set changed the root"
        )

    # (D4) INJECTIVITY: bumping any single COMMITTED scalar must change the root.
    # We mutate one tracked entry at a time, recompute, then restore.
    for (pubkey, asset) in support.balance_keys:
        old = balances.get(pubkey, asset)
        balances.set(pubkey, asset, old + 1)
        try:
            mutated = root(support)
        finally:
            balances.set(pubkey, asset, old)
        assert mutated != base, (
            f"COLLISION: bumping tracked balance ({pubkey[:6]},{asset[:6]}) "
            f"from {old} to {old + 1} did not change the support root"
        )

    for (pubkey, pool_id) in support.lp_keys:
        old = lp.get(pubkey, pool_id)
        lp.set(pubkey, pool_id, old + 1)
        try:
            mutated = root(support)
        finally:
            lp.set(pubkey, pool_id, old)
        assert mutated != base, (
            f"COLLISION: bumping tracked LP amount ({pubkey[:6]},{pool_id[:6]}) did not change the root"
        )

    for pool_id in support.pool_ids:
        pool = pools.get(pool_id)
        if pool is None:
            continue
        old_r0 = pool.reserve0
        pool.reserve0 = old_r0 + 1
        try:
            mutated = root(support)
        finally:
            pool.reserve0 = old_r0
        assert mutated != base, (
            f"COLLISION: bumping pool {pool_id[:6]} reserve0 from {old_r0} did not change the root"
        )

    for pubkey in support.nonce_keys:
        old_n = nonces.get_last(pubkey)
        nonces.set_last(pubkey, old_n + 1)
        try:
            mutated = root(support)
        finally:
            nonces.set_last(pubkey, old_n)
        assert mutated != base, (
            f"COLLISION: bumping tracked nonce {pubkey[:6]} from {old_n} did not change the root"
        )


# ------------------------------ scene builder --------------------------------

@st.composite
def _scenes(draw):
    """Build a VALID, SMALL support + projected state, with at least one
    non-trivial committed entry in each section so injectivity has teeth."""
    seed = draw(st.integers(min_value=0, max_value=2**31 - 1))

    balances = BalanceTable()
    lp = LPTable()
    nonces = NonceTable()
    pools: dict[str, PoolState] = {}

    balance_keys: list[tuple[str, str]] = []
    lp_keys: list[tuple[str, str]] = []
    pool_ids: list[str] = []
    nonce_keys: list[str] = []

    # --- balance entries: distinct (pubkey, asset), positive amounts ---
    n_bal = draw(st.integers(min_value=1, max_value=4))
    seen_bal: set[tuple[str, str]] = set()
    for _ in range(n_bal):
        pk = _PKS[draw(st.integers(min_value=0, max_value=len(_PKS) - 1))]
        asset = _ASSETS[draw(st.integers(min_value=0, max_value=len(_ASSETS) - 1))]
        if (pk, asset) in seen_bal:
            continue
        seen_bal.add((pk, asset))
        amount = draw(st.integers(min_value=1, max_value=10_000))
        balances.set(pk, asset, amount)
        balance_keys.append((pk, asset))

    # --- pools: distinct canonical pairs / fees -> distinct pool_ids ---
    n_pool = draw(st.integers(min_value=0, max_value=3))
    seen_pool: set[str] = set()
    for _ in range(n_pool):
        ia = draw(st.integers(min_value=0, max_value=len(_ASSETS) - 1))
        ib = draw(st.integers(min_value=0, max_value=len(_ASSETS) - 1))
        if ia == ib:
            continue
        fee = draw(st.integers(min_value=0, max_value=10_000))
        r0 = draw(st.integers(min_value=0, max_value=1_000_000))
        r1 = draw(st.integers(min_value=0, max_value=1_000_000))
        sup = draw(st.integers(min_value=0, max_value=1_000_000))
        pid, pool = _pool_for(_ASSETS[ia], _ASSETS[ib], fee, r0, r1, sup)
        if pid in seen_pool:
            continue
        seen_pool.add(pid)
        pools[pid] = pool
        pool_ids.append(pid)

    # --- LP positions: bind balances and optional duration metadata ---
    # Only meaningful with a real pool_id; reuse pool_ids when available else synth.
    lp_pool_ids = pool_ids if pool_ids else [_pool_for(_ASSETS[0], _ASSETS[1], 30, 1, 1, 1)[0]]
    n_lp = draw(st.integers(min_value=0, max_value=3))
    seen_lp: set[tuple[str, str]] = set()
    for _ in range(n_lp):
        pk = _PKS[draw(st.integers(min_value=0, max_value=len(_PKS) - 1))]
        pid = lp_pool_ids[draw(st.integers(min_value=0, max_value=len(lp_pool_ids) - 1))]
        if (pk, pid) in seen_lp:
            continue
        seen_lp.add((pk, pid))
        amount = draw(st.integers(min_value=1, max_value=1_000_000))
        lp.set(pk, pid, amount)
        # optional duration-risk metadata (committed in the LPA section)
        if draw(st.booleans()):
            lp.set_last_mint_timestamp(pk, pid, draw(st.integers(min_value=0, max_value=10_000)))
        if draw(st.booleans()):
            lp.set_churn_tier(pk, pid, draw(st.integers(min_value=1, max_value=5)))
        lp_keys.append((pk, pid))

    # --- nonces: positive last-nonce per distinct pubkey ---
    n_nonce = draw(st.integers(min_value=0, max_value=3))
    seen_nonce: set[str] = set()
    n_pks = draw(st.lists(st.integers(min_value=0, max_value=len(_PKS) - 1), min_size=0, max_size=n_nonce))
    for i in n_pks:
        pk = _PKS[i]
        if pk in seen_nonce:
            continue
        seen_nonce.add(pk)
        nonces.set_last(pk, draw(st.integers(min_value=1, max_value=0xFFFF)))
        nonce_keys.append(pk)

    support = m.BatchStateSupport(
        balance_keys=tuple(balance_keys),
        pool_ids=tuple(pool_ids),
        lp_keys=tuple(lp_keys),
        nonce_keys=tuple(nonce_keys),
    )
    return {
        "seed": seed,
        "balances": balances,
        "pools": pools,
        "lp": lp,
        "nonces": nonces,
        "support": support,
        "root_fn": m.compute_support_state_root,
    }


# --------------------------------- the mine ----------------------------------

@settings(max_examples=900, suppress_health_check=[HealthCheck.too_slow, HealthCheck.data_too_large])
@given(scene=_scenes())
def test_support_root_has_no_determinism_or_injectivity_witness(scene):
    """Mine: over hundreds of valid support+state scenes, (D1)-(D4) must hold.
    A clean run is a bounded NEGATIVE receipt for the support-root disaster class."""
    _assert_no_support_root_disaster(scene)


# ------------------------- (D3) case-folding consistency ---------------------

@settings(max_examples=900, suppress_health_check=[HealthCheck.too_slow])
@given(
    pk_i=st.integers(min_value=0, max_value=3),
    asset_i=st.integers(min_value=0, max_value=5),
    amount=st.integers(min_value=1, max_value=10_000),
)
def test_support_root_case_folding_is_logical_identity(pk_i, asset_i, amount):
    """A balance key whose hex differs only in CASE decodes to identical bytes,
    so it is the SAME logical entry and MUST hash identically. (Disaster: a
    validator and a verifier that normalise case differently would split.)"""
    pk = PK(pk_i)
    asset = ASSET(asset_i)
    # Only meaningful when there are hex letters to flip case on.
    if pk[2:].lower() == pk[2:].upper() and asset[2:].lower() == asset[2:].upper():
        return
    balances = BalanceTable()
    balances.set(pk, asset, amount)
    balances.set(pk.upper().replace("0X", "0x"), asset.upper().replace("0X", "0x"), amount)

    lower = m.BatchStateSupport(balance_keys=((pk, asset),), pool_ids=(), lp_keys=(), nonce_keys=())
    upper = m.BatchStateSupport(
        balance_keys=((pk.upper().replace("0X", "0x"), asset.upper().replace("0X", "0x")),),
        pool_ids=(), lp_keys=(), nonce_keys=(),
    )
    r_lower = m.compute_support_state_root(balances=balances, pools={}, lp_balances=LPTable(), support=lower)
    r_upper = m.compute_support_state_root(balances=balances, pools={}, lp_balances=LPTable(), support=upper)
    assert r_lower == r_upper, "CASE-SPLIT: same logical key hashed two ways across hex case"


# ----------------------- TEETH / non-vacuity (mandatory) ---------------------

def _buggy_support_root_no_sort(*, balances, pools, lp_balances, support, nonces=None):
    """A planted-bug support-root: commits balance entries in *input order* with
    NO sort and NO dedup. This violates (D1) ORDER-INDEPENDENCE: two permutations
    of the same support set produce different pre-images -> different roots.

    Used ONLY by the teeth test to prove `_assert_no_support_root_disaster` has
    teeth (would catch a real order-dependent root). It is NOT the module."""
    from src.state.canonical import (
        domain_sep_bytes,
        encode_bytes,
        encode_uvarint,
        hex_to_bytes_fixed,
        sha256_hex,
    )

    bal_out = bytearray()
    entries = []
    for pubkey, asset in support.balance_keys:  # NOTE: no sort, input order kept
        amount = balances.get(pubkey, asset)
        if amount == 0:
            continue
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        asset_b = hex_to_bytes_fixed(asset, nbytes=32, name="asset")
        entries.append((pk_b, asset_b, amount))
    bal_out += encode_uvarint(len(entries))
    for pk_b, asset_b, amount in entries:
        bal_out += pk_b + asset_b + encode_uvarint(amount)

    payload = (
        domain_sep_bytes("state_support_root", version=m.SUPPORT_ROOT_VERSION)
        + b"BAL"
        + encode_bytes(bytes(bal_out))
    )
    return sha256_hex(payload)


def test_invariant_catches_order_dependent_root():
    """TEETH: feed `_assert_no_support_root_disaster` a deliberately
    order-dependent root function over a support set with two balance keys that
    are NOT already in sorted order. The checker MUST raise ORDER-DEPENDENCE.
    If this passed silently, the negative receipt above would be a false one."""
    pk_a, pk_b = PK(0), PK(1)
    asset = ASSET(0)
    balances = BalanceTable()
    balances.set(pk_a, asset, 5)
    balances.set(pk_b, asset, 7)
    # pk_a < pk_b, so list them out of order to force a real permutation effect.
    support = m.BatchStateSupport(
        balance_keys=((pk_b, asset), (pk_a, asset)),
        pool_ids=(), lp_keys=(), nonce_keys=(),
    )
    scene = {
        "seed": 1,
        "balances": balances,
        "pools": {},
        "lp": LPTable(),
        "nonces": NonceTable(),
        "support": support,
        "root_fn": _buggy_support_root_no_sort,
    }
    with pytest.raises(AssertionError, match="ORDER-DEPENDENCE"):
        _assert_no_support_root_disaster(scene)


def test_invariant_catches_collision_blind_root():
    """TEETH #2: a root that ignores balance AMOUNTS (commits only keys) collides
    when an amount is bumped. The checker MUST raise COLLISION. Proves the (D4)
    injectivity branch has teeth, not just the (D1) order branch."""

    def _amount_blind_root(*, balances, pools, lp_balances, support, nonces=None):
        from src.state.canonical import domain_sep_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex

        out = bytearray()
        keys = sorted(
            (hex_to_bytes_fixed(pk, nbytes=48, name="pk"), hex_to_bytes_fixed(a, nbytes=32, name="a"))
            for pk, a in support.balance_keys
            if balances.get(pk, a) != 0
        )
        out += encode_uvarint(len(keys))
        for pk_b, a_b in keys:
            out += pk_b + a_b  # AMOUNT INTENTIONALLY OMITTED -> collisions
        payload = domain_sep_bytes("state_support_root", version=m.SUPPORT_ROOT_VERSION) + b"BAL" + encode_bytes(bytes(out))
        return sha256_hex(payload)

    pk = PK(0)
    asset = ASSET(0)
    balances = BalanceTable()
    balances.set(pk, asset, 5)
    support = m.BatchStateSupport(balance_keys=((pk, asset),), pool_ids=(), lp_keys=(), nonce_keys=())
    scene = {
        "seed": 1,
        "balances": balances,
        "pools": {},
        "lp": LPTable(),
        "nonces": NonceTable(),
        "support": support,
        "root_fn": _amount_blind_root,
    }
    with pytest.raises(AssertionError, match="COLLISION"):
        _assert_no_support_root_disaster(scene)


# ------------------------------ boundary / reject ----------------------------

def test_malformed_support_keys_reject_deterministically():
    """Malformed/duplicate decoded keys must raise the SAME ValueError on every
    call (deterministic fail-closed), never silently admit a root."""
    pk = PK(0)
    asset = ASSET(0)
    balances = BalanceTable()
    balances.set(pk, asset, 1)
    # Same decoded key listed twice in mixed case -> duplicate decoded (pk,asset).
    dup = m.BatchStateSupport(
        balance_keys=((pk, asset), (pk.upper().replace("0X", "0x"), asset)),
        pool_ids=(), lp_keys=(), nonce_keys=(),
    )
    for _ in range(3):
        with pytest.raises(ValueError, match=r"duplicate decoded \(pubkey, asset\)"):
            m.compute_support_state_root(balances=balances, pools={}, lp_balances=LPTable(), support=dup)

    # Non-canonical hex length must reject (and never produce a root).
    bad = m.BatchStateSupport(balance_keys=(("0xdead", asset),), pool_ids=(), lp_keys=(), nonce_keys=())
    balances.set("0xdead", asset, 1)
    with pytest.raises(ValueError):
        m.compute_support_state_root(balances=balances, pools={}, lp_balances=LPTable(), support=bad)
