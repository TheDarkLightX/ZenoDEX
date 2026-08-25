# Perps Margin GlobalSettlement SHADOW V1

Date: 2026-08-24

Status: `IMPLEMENTED_SHADOW`, `UNMOUNTED`, `production_authority=NONE`

## Selected semantic boundary

This bounded core implements subject-bound margin accounting shared by the
repository's selected peer-to-peer perps family. It uses one collateral asset
per market, quote-e8 integer accounting, isolated margin, exact
owner/subject equality, immutable closed account tombstones, and at most 64
canonically ordered accounts. Every valid market state has exact peer-to-peer
position balance:

```text
sum(positive position_base) = sum(abs(negative position_base))
```

```text
deposit:
  account balance -= amount
  perps accounting location += amount
  owner liability += amount

withdraw:
  account balance += amount
  perps accounting location -= amount
  owner liability -= amount

close:
  require position = 0 and collateral = 0
  OPEN terminal obligation -> DRAINED
  account ID cannot reopen
```

Market lifecycle is an explicit closed typestate:

```text
ACTIVE:     deposit, withdraw, and close are eligible for policy checks
DRAIN_ONLY: deposit rejects; authenticated withdraw and close remain eligible
HALTED:     every command rejects with an exact no-op
```

`DRAIN_ONLY` preserves a path for claimants to recover collateral and drain
terminal obligations during a release retirement. A boolean enable flag cannot
represent this distinction and is absent from the V1 state.

A deposit that creates the 64th account is accepted. A deposit that would
create a 65th account returns typed `ACCOUNT_LIMIT` with identical pre/post
roots and no effects. A decoded 65-account state is structurally invalid.

Withdrawal from an open position requires:

```text
remaining_collateral >=
  ceil(abs(position_base) * index_price_e8
       * (maintenance_margin_bps + depeg_buffer_bps) / 10_000)
```

Every accepted output owns a typed private port bound into the module journal.
The port commits the command body, occurrence, market, account, effect plan,
terminal obligations, and the complete Oracle dependency triple. Every
withdrawal from a position-carrying account has a nonzero Oracle authority
root, Oracle occurrence root, and quote-e8 Oracle price. The committed price
must equal the market state's index price. A flat-account withdrawal has no
price-dependent maintenance decision, requires an absent Oracle triple, and
therefore remains available in `DRAIN_ONLY` during an Oracle outage. Deposit,
flat-account withdrawal, and close reject surplus Oracle bindings. The context
rejects partially populated Oracle triples.

All multiplication is bounded to unsigned 128-bit arithmetic. Candidate effect
deltas are bounded to signed 128-bit arithmetic. Rejections preserve the exact
pre-state root and carry an empty effect plan. Rust validates decoded rejection
objects before they can be accepted as exact no-op evidence.

Terminal-obligation IDs commit the lane, creating module release, market, and
account. Hash-derived obligations are sorted by obligation ID before their root
is computed, so canonical ordering does not depend on incidental hash order.

## Authority boundary

The leaf module emits candidate `ACCOUNT_MOVEMENT`, `CUSTODY`, and `LIABILITY`
rows, one `PERPS_MARKET` lane write, occurrence consumption, and the complete
post-state terminal-obligation root. Its owned input wrapper snapshots and
recomputes the transition before release binding or receipt verification.

The release binder now requires the authenticated command occurrence, the
governed active route selected from a synthetic test profile, and the exact
typed Oracle price authority when the margin transition depends on a price.
That price authority commits the Oracle ID, market, base asset, quote asset,
price-e8, observed height, finalized occurrence root, route, policy, pre-state,
and command occurrence. Only a `SUCCINCT` receipt under the release-selected
image and exact canonical module journal can create the opaque module receipt
witness. The verifier remains an injected port in this research slice.

The structural perps lane coordinator takes complete pre/post projections of
account balances, accounting locations, claimant liabilities, supplies,
terminal obligations, and the perps state. It checks exact module/port/context
bindings, derives projected deltas, rejects hidden movement, and replaces the
module lane write with projection roots while adding the complete per-asset
conservation row. Every typed rejection has identical pre/post roots and empty
effects.

The remaining fail-closed boundary is receipt-backed lane composition and
route/global refinement. The current coordinator output has no verified
coordinator receipt, route-composition witness, epoch proof, or durable
publisher authority.

No caller can use this module or structural coordinator output as a verified
epoch or durable commit witness. The active releases used in tests are
synthetic fixtures only. No perps module release, route release, RISC0 image,
verifier deployment, API, UI, or writer is mounted.

The formal ABI term `CUSTODY` means a committed accounting location. It does
not identify a third-party key holder or make a claim about legal custodianship.

## Evidence

```bash
python3 -m pytest -q tests/core/test_perps_margin_module_v1.py
python3 -m pytest -q \
  tests/core/test_global_oracle_occurrence_authority_v1.py \
  tests/core/test_global_oracle_price_occurrence_v1.py \
  tests/core/test_perps_margin_release_receipt_binding_v1.py \
  tests/core/test_perps_margin_lane_coordinator_v1.py

CARGO_TARGET_DIR=/tmp/zenodex-perps-margin-target \
  cargo test --manifest-path zk/global_settlement_abi_v1/Cargo.toml \
  --test perps_margin \
  --test global_oracle_occurrence_authority \
  --test lane_module_release_route_binding \
  --locked --offline
```

The tests cover deposit creation, exact candidate effects, maintenance BVA at
one atom below/equal/above the boundary, deposit-withdraw-close history,
terminal non-reopen, `ACTIVE`/`DRAIN_ONLY`/`HALTED` behavior, exact zero net
position, the 64/65 account boundary, release/market/account terminal-ID
namespacing, fixed rejection precedence, exact no-op rejection, overflow,
nonce exhaustion, canonical ordering, unknown fields, hostile Python
subclasses, absent/partial/mismatched/surplus Oracle bindings, private-port and
statement substitution, decoded Rust rejection validation, and frozen
Rust/Python accepted-transition roots. Shared fixed vectors also bind the typed
Oracle payload, governed perps input statement, module journal, complete
pre/post lane projections, normalized effect plan, and lane journal across
Python and Rust. Negative coordinator evidence covers hidden accounting
movement, profile substitution, unsupported effect kinds, incomplete claimant
liabilities, and incomplete terminal obligations.

## Nonclaims and remaining semantic decisions

- No intent matching, position opening, or epoch settlement.
- No funding rule or funding source.
- No deployed Oracle module receipt or cross-lane Oracle composition proof.
- No real RISC0 perps guest image or cryptographic receipt replay. Tests use an
  injected verifier port and synthetic release/profile data.
- No liquidation, insurance, ADL, or bankruptcy policy.
- No cross-market or portfolio margin.
- No complete whole-market terminal closeout.
- No coordinator receipt verifier, receipt-backed lane composition, route
  composer, epoch proof, migration, mount, writer, or publication authority.
- No governed registry that binds a perps market ID to its expected base asset;
  the typed price payload commits the base asset, while this bounded route
  currently binds market ID and quote asset only.
- No shared data-driven Rust/Python rejection-vector corpus; rejection parity is
  covered by implementation-specific negative tests in this slice.
- No change to the M6 `PERPS_MARKET` disposition `REQUIRED_UNRESOLVED`.

The repository currently contains incompatible wider perps choices around
insurance and ADL. Those policies need an explicit protocol decision before a
full M6 perps release can be specified.
