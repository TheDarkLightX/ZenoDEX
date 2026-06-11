"""Wave 2 sealed-bid deviation evidence.

These tests cover the sealed-bid obligations in
`docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md` (O-SB-01..06) against the
implemented mechanism: `settle_uniform_price_sealed_bids` in
`src/core/sealed_bid_auction.py` (sort `(-limit_price, commitment,
bidder_id)`, clearing price = last filled bid's limit price, every fill pays
it) and `settle_sealed_bid_non_reveal_bonds` in
`src/core/sealed_bid_bonds.py` (refund iff revealed, else slash).

Model conventions, shared by every test here:

- A bidder's *value* is a private model parameter (units of the quote asset
  per inventory unit). Payoffs are exact integers:
  ``filled_quantity * (value - paid_price)`` summed over fills, minus any
  slashed bond. No floats anywhere.
- Every settlement outcome that a payoff depends on is computed by the real
  implementation, never re-derived by hand.
- Commitments are real `sealed_bid_reveal_hash` digests over the revealed
  (quantity, limit_price, nonce), so tie-break behavior matches production
  hashing exactly.

They are research evidence only. They do not change auction behavior.
"""

from __future__ import annotations

from src.core.sealed_bid_auction import (
    MAX_PRICE,
    MAX_UNITS,
    RevealedSealedBid,
    SealedBidSettlement,
    sealed_bid_reveal_hash,
    settle_uniform_price_sealed_bids,
)
from src.core.sealed_bid_bonds import (
    MAX_BOND,
    BondedSealedBidCommit,
    SealedBidRevealRef,
    settle_sealed_bid_non_reveal_bonds,
)


def _bid(
    bidder_id: str, quantity: int, limit_price: int, nonce: str
) -> RevealedSealedBid:
    return RevealedSealedBid(
        bidder_id=bidder_id,
        commitment=sealed_bid_reveal_hash(
            quantity=quantity, limit_price=limit_price, nonce=nonce
        ),
        quantity=quantity,
        limit_price=limit_price,
    )


def _surplus(
    settlement: SealedBidSettlement, bidder_id: str, value_per_unit: int
) -> int:
    """Integer surplus for one bidder: sum of fill_qty * (value - paid)."""
    total = 0
    for fill in settlement.fills:
        if fill.bidder_id == bidder_id:
            total += fill.filled_quantity * (value_per_unit - fill.paid_price)
    return total


def _filled_quantity(settlement: SealedBidSettlement, bidder_id: str) -> int:
    return sum(
        f.filled_quantity for f in settlement.fills if f.bidder_id == bidder_id
    )


# ---------------------------------------------------------------------------
# H-MD-SB-001 / O-SB-01: demand reduction exists.
# ---------------------------------------------------------------------------


def test_h_md_sb_001_demand_reduction_strictly_profits() -> None:
    """Reducing reported quantity strictly raises surplus: 2 bidders, 2 units.

    Bidder A has 2-unit demand at value 100/unit. Rival B bids 1 unit at a
    lower price r. Truthful A (quantity=2, limit=100) fills both units but is
    itself the last accepted bid, so the clearing price equals A's own limit
    and A's surplus is exactly 0. Reducing to quantity=1 lets B's bid set the
    clearing price r, earning A a strict surplus of 100 - r.
    """

    value = 100

    # Minimal witness from the charter row: rival at 60.
    truthful = settle_uniform_price_sealed_bids(
        units_for_sale=2,
        bids=[
            _bid("alice", 2, value, "a-truthful"),
            _bid("bob", 1, 60, "b-witness"),
        ],
    )
    assert truthful.clearing_price == value  # A's own bid is pivotal
    assert _filled_quantity(truthful, "alice") == 2
    assert _surplus(truthful, "alice", value) == 0

    reduced = settle_uniform_price_sealed_bids(
        units_for_sale=2,
        bids=[
            _bid("alice", 1, value, "a-reduced"),
            _bid("bob", 1, 60, "b-witness"),
        ],
    )
    assert reduced.clearing_price == 60  # B's bid now sets the price
    assert _filled_quantity(reduced, "alice") == 1
    assert _surplus(reduced, "alice", value) == 40  # exact integer gain

    # Witness family: the gain is strict for every rival price below value.
    for rival_price in range(1, value):
        truthful_r = settle_uniform_price_sealed_bids(
            units_for_sale=2,
            bids=[
                _bid("alice", 2, value, "a-truthful"),
                _bid("bob", 1, rival_price, "b-sweep"),
            ],
        )
        reduced_r = settle_uniform_price_sealed_bids(
            units_for_sale=2,
            bids=[
                _bid("alice", 1, value, "a-reduced"),
                _bid("bob", 1, rival_price, "b-sweep"),
            ],
        )
        assert _surplus(truthful_r, "alice", value) == 0
        assert _surplus(reduced_r, "alice", value) == value - rival_price
        assert value - rival_price > 0


# ---------------------------------------------------------------------------
# H-MD-SB-002 / O-SB-02: single-unit bidding is not truthful either.
# ---------------------------------------------------------------------------


def test_h_md_sb_002_pivotal_winner_shades_to_runner_up_plus_one() -> None:
    """A pivotal single-unit winner pays its own bid, so shading profits.

    One unit for sale, A values it at 100, rival B bids 60. Truthful A pays
    its own 100 (surplus 0). Any report s in (60, 100] still wins and pays s,
    so surplus is 100 - s, maximized at s = runner_up + 1 = 61 with strict
    gain 39.
    """

    value = 100
    runner_up = 60

    truthful = settle_uniform_price_sealed_bids(
        units_for_sale=1,
        bids=[
            _bid("alice", 1, value, "a-true"),
            _bid("bob", 1, runner_up, "b-true"),
        ],
    )
    assert truthful.clearing_price == value
    assert _surplus(truthful, "alice", value) == 0

    best_shade = None
    best_surplus = -1
    for shade in range(runner_up + 1, value + 1):
        outcome = settle_uniform_price_sealed_bids(
            units_for_sale=1,
            bids=[
                _bid("alice", 1, shade, "a-shade"),
                _bid("bob", 1, runner_up, "b-true"),
            ],
        )
        # A strictly outbids B, wins the unit, and pays its own report.
        assert _filled_quantity(outcome, "alice") == 1
        assert outcome.clearing_price == shade
        surplus = _surplus(outcome, "alice", value)
        assert surplus == value - shade
        if surplus > best_surplus:
            best_surplus = surplus
            best_shade = shade

    assert best_shade == runner_up + 1
    assert best_surplus == value - (runner_up + 1) == 39
    assert best_surplus > 0  # strictly beats truthful reporting


# ---------------------------------------------------------------------------
# H-MD-SB-003 / O-SB-03: price ties are grindable via the commitment hash.
# ---------------------------------------------------------------------------


def test_h_md_sb_003_tie_value_is_positive_and_nonce_grinding_flips_it() -> None:
    """At equal prices the smaller commitment wins, and nonces are free.

    Two bids at price 80 compete for one unit (value 100): the winner takes
    integer surplus 20, the loser takes 0. Which bid wins is decided by the
    lexicographic order of the commitment hex digests, and the commitment is
    a hash over a bidder-chosen nonce, so the losing side can grind nonces
    until its digest sorts first.
    """

    value = 100
    price = 80

    bid_a = _bid("alice", 1, price, "tie-a")
    bid_b = _bid("bob", 1, price, "tie-b")
    baseline = settle_uniform_price_sealed_bids(
        units_for_sale=1, bids=[bid_a, bid_b]
    )
    assert baseline.clearing_price == price
    winner_id = (
        "alice" if bid_a.commitment < bid_b.commitment else "bob"
    )
    loser_id = "bob" if winner_id == "alice" else "alice"
    assert _surplus(baseline, winner_id, value) == value - price == 20
    assert _surplus(baseline, loser_id, value) == 0

    # The loser grinds deterministic nonces until its commitment beats the
    # winner's. By the exchangeability law, 64 trials beat one rival with
    # probability 64/65; this fixed nonce sequence is verified to succeed
    # (no expected-trials claim — the trial-count distribution is heavy-
    # tailed, see the win-rate test below).
    target = bid_a.commitment if winner_id == "alice" else bid_b.commitment
    ground = None
    trials = 0
    for i in range(64):
        trials = i + 1
        candidate = _bid(loser_id, 1, price, f"grind-{i}")
        if candidate.commitment < target:
            ground = candidate
            break
    assert ground is not None

    keeper = bid_a if winner_id == "alice" else bid_b
    flipped = settle_uniform_price_sealed_bids(
        units_for_sale=1, bids=[keeper, ground]
    )
    assert _surplus(flipped, loser_id, value) == 20  # tie now won by grinding
    assert _surplus(flipped, winner_id, value) == 0
    assert trials <= 64  # cost: a handful of sha256 calls for a value-20 tie


def test_h_md_sb_003_grinding_win_rate_matches_exchangeability_law() -> None:
    """Best-of-T own digests beats min-of-m rivals with probability T/(T+m).

    All T + m digests are sha256 outputs of distinct inputs, so the smallest
    is uniform among them. With T = m grinding trials the win probability is
    exactly 1/2 regardless of m: ties are not 'rare and neutral', they are
    cheaply contestable. Inputs are fixed strings, so this measurement is
    deterministic.
    """

    configs = 240
    for m in (1, 3, 7):
        trials_per_config = m
        wins = 0
        for c in range(configs):
            rival_min = min(
                sealed_bid_reveal_hash(
                    quantity=1, limit_price=80, nonce=f"rival-{m}-{c}-{j}"
                )
                for j in range(m)
            )
            own_best = min(
                sealed_bid_reveal_hash(
                    quantity=1, limit_price=80, nonce=f"own-{m}-{c}-{t}"
                )
                for t in range(trials_per_config)
            )
            if own_best < rival_min:
                wins += 1
        expected = configs * trials_per_config // (trials_per_config + m)
        # T/(T+m) = 1/2 here; allow +-9 percentage points of sampling noise
        # around the exact exchangeability law (fixed inputs, no flakiness).
        assert abs(wins - expected) <= int(round(configs * 0.09)), (
            f"m={m}: wins={wins}, expected~{expected}"
        )


# ---------------------------------------------------------------------------
# H-MD-SB-004 / O-SB-04: the maximum bond is below multi-unit option value.
# ---------------------------------------------------------------------------


def test_h_md_sb_004_max_bond_cannot_force_reveal_for_multi_unit_bids() -> None:
    """For every q >= 2 an in-domain adverse move makes slashing cheaper.

    A bidder committed to (q, p) and the market moved against it: its value
    is now v = p - delta. Revealing fills q units at clearing price p (the
    bid is pivotal), losing q * delta; not revealing loses exactly the bond.
    With the maximum admissible bond (MAX_BOND) and delta = MAX_BOND//q + 1,
    q * delta > MAX_BOND, so silent abandonment strictly dominates. One delta
    lower, revealing is weakly better: the threshold is exact.

    Coverage is two-layered: the threshold arithmetic is checked exhaustively
    for every quantity 2..MAX_UNITS (the inequality that makes the q >= 2
    claim universal), and the full strategy payoffs are bound to the real
    settlement + bond implementations for q in 2..16.
    """

    # Layer 1: exhaustive threshold arithmetic over the whole bid domain.
    for q in range(2, MAX_UNITS + 1):
        delta = MAX_BOND // q + 1
        assert delta <= MAX_PRICE - 1  # adverse move stays in-domain
        assert q * delta > MAX_BOND  # slashing strictly cheaper at delta
        assert q * (delta - 1) <= MAX_BOND  # reveal weakly better one lower

    # Layer 2: real-function payoff binding on a representative prefix.
    price = MAX_PRICE
    for quantity in range(2, 17):
        delta_min = MAX_BOND // quantity + 1
        assert 1 <= price - delta_min  # value stays in-domain

        reveal = settle_uniform_price_sealed_bids(
            units_for_sale=quantity,
            bids=[_bid("carol", quantity, price, f"opt-{quantity}")],
        )
        assert reveal.clearing_price == price
        assert _filled_quantity(reveal, "carol") == quantity

        commitment = reveal.fills[0].commitment
        commit = BondedSealedBidCommit(
            bidder_id="carol", commitment=commitment, bond_amount=MAX_BOND
        )
        revealed_bonds = settle_sealed_bid_non_reveal_bonds(
            commits=[commit],
            reveals=[SealedBidRevealRef(bidder_id="carol", commitment=commitment)],
        )
        assert revealed_bonds.total_slashed == 0  # reveal: bond comes back
        slashed_bonds = settle_sealed_bid_non_reveal_bonds(
            commits=[commit], reveals=[]
        )
        assert slashed_bonds.total_slashed == MAX_BOND

        # Adverse value v = p - delta_min: integer payoffs of each strategy.
        value = price - delta_min
        reveal_payoff = _surplus(reveal, "carol", value)  # = -q * delta_min
        abandon_payoff = -slashed_bonds.total_slashed  # = -MAX_BOND
        assert reveal_payoff == -quantity * delta_min
        assert abandon_payoff > reveal_payoff  # abandoning strictly wins

        # Tightness: one unit less adverse and revealing is weakly better.
        value_edge = price - (delta_min - 1)
        assert _surplus(reveal, "carol", value_edge) >= abandon_payoff


def test_h_md_sb_004_max_bond_does_force_reveal_for_single_unit_bids() -> None:
    """Boundary refinement: at q = 1 the maximum bond is always sufficient.

    The worst in-domain adverse move is delta = MAX_PRICE - 1 (value 1
    against a price-MAX_PRICE fill), losing MAX_PRICE - 1 = 65534 on reveal,
    strictly less than the slashed MAX_BOND = 65535. So the documented bond
    design works exactly for single-unit commitments and fails from q = 2 up.
    """

    reveal = settle_uniform_price_sealed_bids(
        units_for_sale=1, bids=[_bid("dave", 1, MAX_PRICE, "q1-worst")]
    )
    assert reveal.clearing_price == MAX_PRICE
    worst_value = 1
    reveal_payoff = _surplus(reveal, "dave", worst_value)
    assert reveal_payoff == -(MAX_PRICE - 1)

    commitment = reveal.fills[0].commitment
    slashed = settle_sealed_bid_non_reveal_bonds(
        commits=[
            BondedSealedBidCommit(
                bidder_id="dave", commitment=commitment, bond_amount=MAX_BOND
            )
        ],
        reveals=[],
    )
    assert -slashed.total_slashed < reveal_payoff  # reveal strictly better

    # No larger bond is admissible, so MAX_BOND is the binding ceiling.
    try:
        settle_sealed_bid_non_reveal_bonds(
            commits=[
                BondedSealedBidCommit(
                    bidder_id="dave",
                    commitment=commitment,
                    bond_amount=MAX_BOND + 1,
                )
            ],
            reveals=[],
        )
    except ValueError:
        pass
    else:
        raise AssertionError("bond above MAX_BOND must be rejected")


# ---------------------------------------------------------------------------
# H-MD-SB-005 / O-SB-05: conditional reveal beats always-reveal past q*w > b.
# ---------------------------------------------------------------------------


def test_h_md_sb_005_conditional_reveal_threshold_is_exact() -> None:
    """Reveal-iff-favorable beats always-reveal exactly when q*w > bond.

    A bidder commits to (q=2, p=1000). The realized value is v_high = p + w
    or v_low = p - w (two-point support of width w around the commit price).
    In the high state both strategies reveal and earn q*w. In the low state
    always-reveal loses q*w while conditional reveal forfeits the bond b.
    Summing both states, conditional - always = q*w - b exactly, for every
    (w, b) on the grid: the commit becomes a free option whenever the
    support is wider than the bond.
    """

    quantity = 2
    price = 1_000

    for width in range(1, 41):
        v_high = price + width
        v_low = price - width
        assert 1 <= v_low and v_high <= MAX_PRICE

        reveal = settle_uniform_price_sealed_bids(
            units_for_sale=quantity,
            bids=[_bid("erin", quantity, price, f"straddle-{width}")],
        )
        assert reveal.clearing_price == price
        commitment = reveal.fills[0].commitment
        commit_payoff_high = _surplus(reveal, "erin", v_high)
        commit_payoff_low = _surplus(reveal, "erin", v_low)
        assert commit_payoff_high == quantity * width
        assert commit_payoff_low == -quantity * width

        for bond in range(1, 81):
            commit = BondedSealedBidCommit(
                bidder_id="erin", commitment=commitment, bond_amount=bond
            )
            refund = settle_sealed_bid_non_reveal_bonds(
                commits=[commit],
                reveals=[
                    SealedBidRevealRef(bidder_id="erin", commitment=commitment)
                ],
            )
            slash = settle_sealed_bid_non_reveal_bonds(
                commits=[commit], reveals=[]
            )
            assert refund.total_slashed == 0
            assert slash.total_slashed == bond

            always = commit_payoff_high + commit_payoff_low
            conditional = commit_payoff_high - slash.total_slashed
            gap = conditional - always
            assert gap == quantity * width - bond
            if quantity * width > bond:
                assert conditional > always
            elif quantity * width == bond:
                assert conditional == always
            else:
                assert conditional < always


# ---------------------------------------------------------------------------
# H-MD-SB-006 / O-SB-06: a decoy bid pins the clearing price for its owner.
# ---------------------------------------------------------------------------


def test_h_md_sb_006_self_decoy_bid_lowers_own_average_paid_price() -> None:
    """One bidder, two commitments: the decoy sets the price everyone pays.

    Four units for sale, honest demand only three: A wants 2 units at value
    100, rival B bids 1 at 90. With a single commitment, B's bid is the last
    accepted and A pays 90 per unit (surplus 20). Adding a worthless decoy
    bid (1 unit at price d < 90) under the same bidder_id fills the leftover
    unit, so the clearing price drops to d. Counting the decoy unit at value
    0, A's payoff is 200 - 3d: strictly better for d < 60, indifferent at
    d = 60, worse above. The mechanism admits the repeated bidder_id without
    complaint.
    """

    value = 100

    honest = settle_uniform_price_sealed_bids(
        units_for_sale=4,
        bids=[
            _bid("alice", 2, value, "real"),
            _bid("bob", 1, 90, "rival"),
        ],
    )
    assert honest.clearing_price == 90
    assert _filled_quantity(honest, "alice") == 2
    honest_payoff = _surplus(honest, "alice", value)
    assert honest_payoff == 20

    for decoy_price in range(1, 90):
        decoyed = settle_uniform_price_sealed_bids(
            units_for_sale=4,
            bids=[
                _bid("alice", 2, value, "real"),
                _bid("alice", 1, decoy_price, "decoy"),
                _bid("bob", 1, 90, "rival"),
            ],
        )
        # Same bidder_id twice is admitted; the decoy is the last fill.
        assert decoyed.clearing_price == decoy_price
        assert _filled_quantity(decoyed, "alice") == 3

        # All three filled units pay decoy_price; the decoy unit's true value
        # is 0, so subtract the one unit of value the raw surplus over-counts.
        assert _surplus(decoyed, "alice", value) == 3 * (value - decoy_price)
        decoy_payoff = _surplus(decoyed, "alice", value) - value
        assert decoy_payoff == 200 - 3 * decoy_price

        if decoy_price < 60:
            assert decoy_payoff > honest_payoff
        elif decoy_price == 60:
            assert decoy_payoff == honest_payoff
        else:
            assert decoy_payoff < honest_payoff

    # Minimal sharp witness: d = 1 collapses the price A pays from 90 to 1.
    best = settle_uniform_price_sealed_bids(
        units_for_sale=4,
        bids=[
            _bid("alice", 2, value, "real"),
            _bid("alice", 1, 1, "decoy"),
            _bid("bob", 1, 90, "rival"),
        ],
    )
    assert best.clearing_price == 1
    assert 2 * (value - 1) + (0 - 1) == 197 > honest_payoff


# ---------------------------------------------------------------------------
# Domain guard: the witnesses above stay inside documented bounds.
# ---------------------------------------------------------------------------


def test_wave2_witnesses_respect_documented_domains() -> None:
    """All witness parameters are inside the implemented validation bounds."""

    assert MAX_UNITS == 0xFFFF
    assert MAX_PRICE == 0xFFFF
    assert MAX_BOND == 0xFFFF
    # Bounds are enforced (not just documented): out-of-range bids reject.
    for bad_quantity in (0, MAX_UNITS + 1):
        try:
            settle_uniform_price_sealed_bids(
                units_for_sale=1,
                bids=[
                    RevealedSealedBid(
                        bidder_id="x",
                        commitment="c",
                        quantity=bad_quantity,
                        limit_price=1,
                    )
                ],
            )
        except ValueError:
            continue
        raise AssertionError("out-of-range quantity must be rejected")
