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

The module emits candidate `ACCOUNT_MOVEMENT`, `CUSTODY`, and `LIABILITY` rows,
one `PERPS_MARKET` lane write, occurrence consumption, and the complete
post-state terminal-obligation root. It does not emit a global conservation row.

This omission is a fail-closed boundary. A future perps lane coordinator and
route composer must derive global owned-and-custodied totals and supply from the
authenticated complete pre/post ZenoLedger states, bind account availability,
bind terminal-table refinement, verify the command authentication and grant
behind the committed subject and grant root, verify that the committed Oracle
authority root was produced by `GlobalOracleOccurrenceAuthorityV1`, pair the
committed price with the authenticated Oracle module output, and add the exact
conservation row. The current global state/effect refiner rejects the candidate
effect plan as route-incomplete.

No caller can use this module output as a verified epoch or durable commit
witness. No module release, route release, RISC0 image, verifier, API, UI, or
writer is mounted.

The formal ABI term `CUSTODY` means a committed accounting location. It does
not identify a third-party key holder or make a claim about legal custodianship.

## Evidence

```bash
python3 -m pytest -q tests/core/test_perps_margin_module_v1.py

CARGO_TARGET_DIR=/tmp/zenodex-perps-margin-target \
  cargo test --manifest-path zk/global_settlement_abi_v1/Cargo.toml \
  --test perps_margin --locked --offline
```

The tests cover deposit creation, exact candidate effects, maintenance BVA at
one atom below/equal/above the boundary, deposit-withdraw-close history,
terminal non-reopen, `ACTIVE`/`DRAIN_ONLY`/`HALTED` behavior, exact zero net
position, the 64/65 account boundary, release/market/account terminal-ID
namespacing, fixed rejection precedence, exact no-op rejection, overflow,
nonce exhaustion, canonical ordering, unknown fields, hostile Python
subclasses, absent/partial/mismatched/surplus Oracle bindings, private-port and
statement substitution, decoded Rust rejection validation, and frozen
Rust/Python accepted-transition roots.

## Nonclaims and remaining semantic decisions

- No intent matching, position opening, or epoch settlement.
- No funding rule or funding source.
- No objective Oracle witness or price-port verification inside this module;
  its committed Oracle fields gain authority only through a future governed
  route composition proof.
- No objective command authentication or grant verification inside this
  module; owner/subject equality alone grants no authority.
- No liquidation, insurance, ADL, or bankruptcy policy.
- No cross-market or portfolio margin.
- No complete whole-market terminal closeout.
- No lane coordinator, route composer, proof guest, receipt verification, or
  publication authority.
- No shared data-driven Rust/Python rejection-vector corpus; rejection parity is
  covered by implementation-specific negative tests in this slice.
- No change to the M6 `PERPS_MARKET` disposition `REQUIRED_UNRESOLVED`.

The repository currently contains incompatible wider perps choices around
insurance and ADL. Those policies need an explicit protocol decision before a
full M6 perps release can be specified.
