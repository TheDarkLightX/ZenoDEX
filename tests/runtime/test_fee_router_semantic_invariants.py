"""Independent **semantic invariants** for the fee router.

These tests do NOT compare Python against Rust. They assert properties derived
from the *intended economics* of the fee router, against the Python authority
alone. Their job is to catch a bug that is present *identically* in both
runtimes — the class of defect that cross-language differential testing cannot
see, because two implementations of the same flawed model agree with each other.

Motivating example (the asset-scoped accounting bug fixed in 7312551): a single
global accumulator let a zUSD rounding remainder bleed into an AGRS receipt, and
a DEX remainder get re-split under the redemption table. Python and Rust agreed,
so the differential stayed green. The invariants below fail on that model and
pass on the fixed, `(source, asset)`-scoped model.

See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import random
from collections import defaultdict

from src.core.fee_router import (
    BORROW,
    DEX,
    PERPS,
    REDEMPTION,
    FeeAccumulator,
    RouteAccepted,
    canonical_split_table,
    route_fee,
)

ASSETS = ["zUSD", "zDEX", "AGRS", "BTC"]
DOMAINS = [DEX, PERPS, BORROW, REDEMPTION]
BUCKETS = ["cum_buyburn", "cum_stakers", "cum_reserve", "cum_hosts"]


def _route(acc, source, asset, amount):
    return route_fee(
        source=source,
        asset=asset,
        amount=amount,
        split_table=canonical_split_table(source),
        accumulator=acc,
    )


def _receipt_tuple(rc):
    return (rc.buyburn, rc.stakers, rc.reserve, rc.hosts, rc.dust)


def _run(calls):
    """Apply ``calls`` (list of (source, asset, amount)); return (acc, receipts_by_stream)."""
    acc = FeeAccumulator()
    receipts: dict[tuple[str, str], list[tuple]] = {}
    for source, asset, amount in calls:
        result = _route(acc, source, asset, amount)
        assert isinstance(result, RouteAccepted), (source, asset, amount, result)
        # I1: per-call conservation, scoped to (source, asset).
        dust_in = acc.dust_for(source, asset)
        r = result.receipt
        assert amount + dust_in == r.buyburn + r.stakers + r.reserve + r.hosts + r.dust
        acc = result.accumulator
        receipts.setdefault((source, asset), []).append(_receipt_tuple(r))
    return acc, receipts


def _mixed_calls(seed: int, n: int = 250):
    rng = random.Random(seed)
    return [
        (rng.choice(DOMAINS), rng.choice(ASSETS), rng.randint(0, 50_000)) for _ in range(n)
    ]


# --- I1: per-stream conservation (checked inside _run on every step) ----------


def test_per_stream_conservation_holds_over_random_sequences():
    for seed in range(8):
        _run(_mixed_calls(seed))  # asserts conservation on every step


# --- I2: NO cross-stream interference (the property that catches the bug) ------


def test_no_cross_stream_interference():
    """A stream's receipts depend ONLY on that stream's own sub-sequence.

    Routing other (source, asset) streams in between must not change a stream's
    receipts. This is exactly the property the global-accumulator bug violated.
    """
    calls = _mixed_calls(seed=1234)
    _, mixed = _run(calls)

    sub_sequences: dict[tuple[str, str], list] = defaultdict(list)
    for source, asset, amount in calls:
        sub_sequences[(source, asset)].append((source, asset, amount))

    for key, sub in sub_sequences.items():
        _, alone = _run(sub)
        assert alone[key] == mixed[key], (
            f"stream {key} was perturbed by interleaved unrelated streams"
        )


def test_interleaving_specific_adversarial_case():
    """The exact shapes that broke the global accumulator must now be inert."""
    # (a) DEX dust must not be re-split under the redemption table.
    alone = _run([(DEX, "zUSD", 3), (DEX, "zUSD", 7)])[1][(DEX, "zUSD")]
    interleaved = _run([(DEX, "zUSD", 3), (REDEMPTION, "zUSD", 5), (DEX, "zUSD", 7)])[1][
        (DEX, "zUSD")
    ]
    assert alone == interleaved

    # (b) A zUSD remainder must not bleed into an AGRS receipt.
    acc = FeeAccumulator()
    acc = _route(acc, DEX, "zUSD", 1).accumulator  # leaves zUSD dust
    agrs = _route(acc, DEX, "AGRS", 9_999).receipt
    fresh = _route(FeeAccumulator(), DEX, "AGRS", 9_999).receipt
    assert _receipt_tuple(agrs) == _receipt_tuple(fresh)


# --- I3: asset / unit coherence ----------------------------------------------


def test_routing_one_asset_never_touches_another_assets_state():
    acc = FeeAccumulator()
    acc = _route(acc, DEX, "zUSD", 12_347).accumulator
    # No AGRS state may have appeared from zUSD activity.
    assert acc.dust_for(DEX, "AGRS") == 0
    for bucket in BUCKETS:
        assert acc.bucket_total(bucket, "AGRS") == 0


def test_dust_is_scoped_per_source_within_an_asset():
    acc = FeeAccumulator()
    acc = _route(acc, DEX, "zUSD", 1).accumulator  # dex/zUSD dust
    # A redemption/zUSD route must see zero carried dust from the dex stream.
    assert acc.dust_for(REDEMPTION, "zUSD") == 0
    routed = _route(acc, REDEMPTION, "zUSD", 9_999).receipt
    fresh = _route(FeeAccumulator(), REDEMPTION, "zUSD", 9_999).receipt
    assert _receipt_tuple(routed) == _receipt_tuple(fresh)


# --- I4: per-domain routing holds for ALL routed value (incl. carried dust) ---


def test_redemption_never_routes_to_buyburn_or_hosts():
    acc = FeeAccumulator()
    for amount in [1, 1, 1, 3, 7, 9_999, 1_000_000]:
        r = _route(acc, REDEMPTION, "zUSD", amount)
        assert isinstance(r, RouteAccepted)
        assert r.receipt.buyburn == 0 and r.receipt.hosts == 0
        acc = r.accumulator


def test_borrow_never_routes_to_buyburn_and_dex_never_to_stakers():
    acc = FeeAccumulator()
    for amount in [1, 7, 9_999, 1_000_000]:
        rb = _route(acc, BORROW, "zUSD", amount)
        assert rb.receipt.buyburn == 0
        rd = _route(acc, DEX, "zUSD", amount)
        assert rd.receipt.stakers == 0
        rp = _route(acc, PERPS, "zUSD", amount)
        assert rp.receipt.stakers == 0


# --- I5: cumulative buckets are exactly the sum of routed receipts per asset ---


def test_cumulative_buckets_equal_sum_of_receipts_per_asset():
    calls = _mixed_calls(seed=99)
    acc, receipts = _run(calls)

    expected: dict[str, list[int]] = defaultdict(lambda: [0, 0, 0, 0])
    for (_source, asset), rlist in receipts.items():
        for buyburn, stakers, reserve, hosts, _dust in rlist:
            agg = expected[asset]
            agg[0] += buyburn
            agg[1] += stakers
            agg[2] += reserve
            agg[3] += hosts

    for asset, (bb, st, rs, ho) in expected.items():
        assert acc.bucket_total("cum_buyburn", asset) == bb
        assert acc.bucket_total("cum_stakers", asset) == st
        assert acc.bucket_total("cum_reserve", asset) == rs
        assert acc.bucket_total("cum_hosts", asset) == ho


# --- I6: total conservation across the whole accumulator ----------------------


def test_global_conservation_inflow_equals_buckets_plus_dust():
    calls = _mixed_calls(seed=2026)
    acc, receipts = _run(calls)

    inflow_by_asset: dict[str, int] = defaultdict(int)
    for (_source, asset, amount) in calls:
        inflow_by_asset[asset] += amount

    for asset, inflow in inflow_by_asset.items():
        routed = sum(acc.bucket_total(b, asset) for b in BUCKETS)
        dust = sum(
            acc.dust_for(domain, asset) for domain in DOMAINS
        )
        assert inflow == routed + dust, f"value not conserved for asset {asset}"
