# ZenoDEX O-008 Formal Cycle V1

Date: 2026-09-01

Status: `FORMAL_CYCLE_COMPLETE_O008_OPEN`

Supported claim:
`O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`

O-008 status: `OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`

Formal core complete: `false`

Whole value movement safe: `false`

Value-movement gates: `0/12`

Production, settlement, release, verifier, and value-moving authority: `NONE`

The formal cycle is complete at a bounded research claim. It produced the
necessary runtime guards, a solver-checked exact target relation, Lean proofs,
minimized counterexamples, a V1 information-loss theorem, an all-lane
feasibility audit, and the minimum sidecar contract. Exact all-lane
reconciliation remains an implementation and proof obligation.

The machine-readable source of truth is
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`. Replay its fail-closed
admission with:

```bash
python3 tools/check_o008_formal_cycle_v1.py
```

## Established results

The Python and Rust V1 refinements now enforce two state-visible necessary
conditions for every checked pre-state and post-state:

```text
sum liabilities(asset, domain) <= sum custody(asset, domain)

sum OPEN terminals(asset, claimant) <= sum liabilities(asset, claimant)
```

Balances and reserves are excluded as claimant-backing sources. Checked
aggregation rejects unsigned 128-bit overflow. These conditions reject
aggregate-only, cross-domain, reserve-masking, claimant-total, and overflow
families visible in V1 global state.

The exact bounded certificate target is stronger. For one asset, two domains,
and two claimants, it records claimant/domain allocation cells, requires exact
custody partition and exact claimant/domain liabilities, binds OPEN terminal
amounts to the exact cell, requires zero unclassified custody in the current
profile, and preserves named reserves as a separate class:

```text
custody(domain) + named_reserve(domain)
  = claimant_liabilities(domain) + named_reserve(domain)
```

Lean proves that named reserves cancel from this equality. A reserve atom
therefore cannot cover a missing claimant-liability atom. Exact deposit and
drain updates preserve the full bounded relation under their arithmetic
premises.

ESSO verifies initialization and one-step inductiveness for `open_claim` and
`drain_claim` with Z3 4.15.4 and CVC5 1.1.2. Eight per-invariant projections
also verify. Five named semantic mutants produce cross-solver
counterexamples. The model is finite, with cells bounded to at most eight
atoms.

Lean 4.27 checks 18 theorems with warnings as errors, zero placeholders, and
only the recorded standard axioms. The counterexamples cover aggregate-only
backing, claimant substitution, cross-domain substitution, and reserve
masking.

## Proved V1 boundary

`TerminalObligationV1` records obligation identity, lane, claimant, asset,
amount, and status. It omits liability domain and custody principal. Two
domain-bound source records can therefore project to identical V1 terminal
bytes. Lean proves that this projection is non-injective and that no
deterministic function of the V1 projection can recover every source domain.

Other current loss points compound this boundary:

- lane state roots do not disclose their private accounting projections;
- global economic rows do not retain lane provenance;
- external outbox rows omit asset and amount;
- verified lane and route values retain roots and discard allocation
  preimages;
- the epoch proof path does not currently receive the full allocation
  certificate.

The executable V1 regressions preserve two accepted known gaps: a claimant
projection substitution behind the same opaque lane root, and one domainless
terminal with two distinct hidden domain preimages. These are checker
incompleteness witnesses. They do not establish a mounted exploit or
production reachability.

## All-lane feasibility result

| Lane | Exact source-data status |
| --- | --- |
| Asset transfer | Partial; claimant and reserve classification absent |
| Spot liquidity | Partial; LP ownership and terminal detail remain behind opaque roots |
| Farm incentives | V1 projection and receipt producer missing |
| ZDEX tokenomics | Partial; several allocation preimages remain opaque |
| zUSD monetary | Matching Python/Rust V1 projection and receipt path missing |
| Perps market | Narrow margin deposit, withdrawal, and close fragment only |
| Oracle market | Reporter bond, reward, and claim projection missing |
| Sealed auction | Matching V1 Rust and proof projection missing |
| Strategy escrow | V1 accounting projection missing |
| Proof rewards | Empty state exists; global lane-root binding is missing |
| External custody | Disabled empty state exists; global lane-root binding is missing |
| Governance migration | Lane-specific accounting projection and receipt missing |

Current V1 projections, journals, and receipts cannot produce exact all-lane
claimant and reserve reconciliation. Eleven lanes require broader or new
producer work; the narrow perps fragment alone has sufficient local typed
source data.

## Minimum wire-compatible sidecar

V1 global-state bytes can remain unchanged if a sibling
`GlobalAccountingAllocationCertificateV1` is introduced. It must bind:

- global state, profile, chain context, and writer epoch;
- exactly 12 ordered lane fragments and their state/projection roots;
- receipt or journal bindings for every fragment;
- canonical source, claimant, reserve, external, and terminal allocation rows;
- field-ownership, terminal-binding, and allocation roots.

Its checker must require exact source-atom classification, exact claimant and
reserve equations, complete external asset and amount data, terminal domain
and principal binding, lane/global aggregate equality, canonical order, and
checked unsigned 128-bit arithmetic.

A detached host-generated sidecar has `EVIDENCE_ONLY` authority because it can
be substituted independently of the accepted epoch receipt. Verifier authority
requires all lane producers, receipt binding, route and epoch proof
propagation, a versioned journal, and commit-port enforcement.

## Evidence replay

```bash
ZENO_ESSO_PYTHON=/path/to/clean/ESSO/.venv/bin/python \
  python3 -m pytest -q \
  tests/formal/test_esso_global_claimant_custody_certificate_v1.py

cd lean-mathlib
lake env lean -DwarningAsError=true \
  Proofs/GlobalClaimantCustodyRelationV1.lean
cd ..

python3 -m pytest -q \
  tests/formal/test_lean_global_claimant_custody_relation_v1.py \
  tests/test_check_o008_formal_cycle_v1.py
```

## Nonclaims

- O-008 is open.
- The exact all-lane certificate is neither implemented nor mounted.
- The ESSO model does not refine current runtime or proof execution.
- The Lean theorems do not prove cryptographic binding, finite-width runtime
  parity, settlement authority, or whole-program value safety.
- No production, release, settlement, verifier, migration, publication, or
  value-moving authority is granted.
