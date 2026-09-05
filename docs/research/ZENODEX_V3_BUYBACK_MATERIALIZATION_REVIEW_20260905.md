# V3 buyback materialization: parent acceptance

Base: `08905c720c`, on the V3 integration branch. This is a bounded W08/W09
advance. It does not complete either task, the formal core, or production
value safety. The runtime coordinator and composer are unchanged.

## Result and invariant

`Proofs/ZDEXBuybackMaterializationV2.lean` checks 29 theorems with Lean
`leanprover/lean4:v4.27.0`, warnings treated as errors. Its effect key retains
kind, principal, asset and custody domain. It proves:

- coalescing, zero removal and permutation preserve every keyed signed sum;
- fee allocation remains distinct from its physical custody mirror;
- normalization produces unique keys and nonzero rows;
- a zero keyed sum in that normalized plan implies actual row absence;
- the modeled buyback route has only the selected pool custody debit and the
  matching supply burn on ZDEX, with no foreign ZDEX row;
- accepted model terminal bindings retain one occurrence and equal acquired
  and burned amounts. A positive witness and independent guard failures are
  checked.

The last result obtains amount equality from the terminal admission guard.
The earlier `ZDEXAcquisitionBurnOccurrenceV2` conservation derivation remains
a separate result. Neither establishes authenticated runtime receipt fields.
The unpublished draft's fee theorem was renamed from
`materialized_fee_liability_is_separate` to
`materialized_fee_allocation_is_separate` to match its actual kind.

## Runtime correspondence and negative evidence

The formal harness freshly compiles its dependency from source, checks exact
consumer types for the central conclusions, and inspects every theorem's
axioms. Only `propext`, `Quot.sound`, and `Classical.choice` are permitted.
No proof holes, custom axioms, `unsafe`, or `native_decide` are accepted.

Full-row permutation checks compare the integer model with actual Python
materializers, a 14-case arithmetic/key corpus, and the existing accepted
SHADOW fixture. A 56-row fixture checks injective coordinate translation.
Runtime `REWARD` and `SLASH`, absent from this Lean model, reject explicitly.
A separate ZDEX-only comparison uses the fixture's real terminal IDs, pool,
amounts and occurrence to instantiate `boundRoute`. Foreign principals and
domains retain distinct representations. Quote accounting is excluded from
that last comparison.

The retained runtime tests cover ownership, kind/asset/domain distinctions,
zero cancellation, exact signed-i128 neighbors, Spot shape rejection,
occurrence/lane/outbox guards, and independent recursive no-mutation snapshots.
The staged overflow witness is tokenomics custody `1` plus allocation
`MAX_I128`, followed by Spot custody `-1`: the eventual mathematical custody
sum fits, while fee materialization rejects before composition.

Four Lean definition mutations break preservation proofs: subtraction during
merge, erased domain identity, negated custody mirror, and doubled occurrence.
Five in-memory Python mutations are killed by retained invariant tests: omitted
fee mirror, erased principal key, wrong Spot kind, bypassed outbox rejection,
and corrupted duplicate occurrence output. The principal mutation initially
survived a single-claimant fee fixture. Adding a second fee claimant with the
same asset/domain made the distinction observable; that regression is retained.
These are executed local mutation checks, not deployed adversarial histories.

## Reviewed subject

| Artifact | SHA-256 |
| --- | --- |
| Lean materialization proof | `dcdeeffbee0b6a936fe87c74500bb78702166db0ab40f4f05ca2c2485d6f1780` |
| Formal harness | `71e85276e95172dd7c81c552458b4cb8fd1ce5014223d5a12b346874c98d65e0` |
| Runtime invariant tests | `e5b4818929d8d831e39a55aa36570385e8e38ea6150c8e96463bdea903971472` |
| Runtime mutation tests | `f533da5caa3dd299b29ce6a57d98038097675a552e961c6bd4c8ce2036389216` |
| Unchanged lane coordinator | `bc8dd3adcdce73d1fc2cefdc4d7e2d705f3d53a91836cb9d7f49b74a29268511` |
| Unchanged route composer | `c5590e3722be8e431e0473d3217e29e172ba0753186f05b48698d972299eb16d` |

Astra independently reviewed the mathematical statements and harness. Parent
review added the exact central theorem consumers and distinguished route-key
mapping requested by that review. Terra supplied the runtime tests; parent
review corrected aliased no-effect observations and used the surviving
principal mutation to strengthen the oracle.

## Replay and limits

From the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_zdex_buyback_materialization_v2.py \
  tests/core/test_zdex_buyback_materialization_semantics_v2.py \
  tests/core/test_zdex_buyback_materialization_mutants_v2.py \
  tests/core/test_zdex_atomic_buyback_route_composition_v2.py
```

These four files contributed 29 passing cases to the parent integration run.
Ruff passed on the added Python files. The production-boundary checker passed
its 14 existing checks while continuing to report M6 as unmounted with open
release coverage. That checker is not a whole-program release qualification.

The proof uses mathematical integers and a right fold. Runtime stage/order
checks can reject earlier. Finite comparisons do not discharge universal
finite-width, decoding, Python/Rust, guest-image, journal, or implementation
refinement. The accepted route fixture uses a mock cryptographic verifier and
an unmounted SHADOW composer. Initialization, trace reachability, real receipt
qualification, authenticated store snapshots, publication, recovery and
deployment-complete mediation remain separate obligations.

No full Lake/Mathlib, Rust/RISC0 guest, Kani, remote solver, or production
promotion run was performed for this slice. The next mathematical step is
checked-runtime transition refinement under the pinned row and terminal ABI;
the next operational dependency remains real receipt/store authority and the
complete publication path. Source/test counts do not close those gaps.
