# Boundary and Authority Review Worksheet

Complete this worksheet before changing critical ZenoDEX code. The point is to
prevent a local improvement from changing the wrong semantic layer.

## A. Domain relation

- Adopted scenario/invariant IDs:
- Exact relation being implemented or repaired:
- Units and integer domains:
- Rounding rule and remainder owner:
- Legal states currently missing from the representation:
- Illegal states currently representable:
- Independent obligations that must survive together on rejection:

## B. Authority level

Mark the strongest authority this artifact currently has:

- [ ] arithmetic helper only
- [ ] pure transition candidate
- [ ] authenticated-fact constructor
- [ ] profile-specific projection or certificate
- [ ] proof/verifier result
- [ ] commit authority
- [ ] observation only

Then answer:

- Is the helper's input language broader than the consuming profile?
- What exact checks narrow helper output to profile authority?
- Can any public constructor, deserializer, Boolean, or same-payload expected hash
  mint the authority-bearing value?
- Does a proof result bind every value-moving observable?
- Can a candidate be mistaken for committed state?

## C. Functional boundary

### Shell input acquisition

- External sources read:
- Clock/epoch/finality source:
- Policy/configuration source:
- Authentication source:
- Snapshot/root source:
- Which reads must be atomic with one another:

### Values passed to the core

For every value, record:

| Value | Exact type | Subject/root binding | Chain/profile/version | Freshness | Trusted constructor |
|---|---|---|---|---|---|
| | | | | | |

### Core output

- Accepted post-state type:
- Typed rejection type:
- Complete effect-plan type:
- Certificate/proof projection type:
- Which outputs are immutable and canonical:

### Shell execution

- CAS predicate:
- State writes:
- Custody/effect writes:
- Nonce/replay/nullifier writes:
- Receipt/outbox writes:
- Retry identity and conflict rule:
- Crash points tested:

## D. Ownership and aliasing

- Constructors:
- Mutation sites:
- Retained aliases:
- Shallow copies:
- Nested mutable values:
- Values that escape, persist, hash, sign, cache, or cross tasks:
- Local builders discarded on rejection:

Any escaping value with a retained mutable alias is a blocking finding.

## E. Canonical representation

- Schema/version:
- Field order:
- Integer widths and endianness:
- String normalization:
- Collection order:
- Duplicate policy:
- Empty/zero omission rule:
- Unknown-field policy:
- Golden vectors:
- Cross-language codec tests:

## F. Arithmetic

- Persisted field domain:
- Intermediate multiplication/addition domain:
- Checked overflow sites:
- Zero and denominator rules:
- Max and max-plus-one tests:
- Python/Rust domain parity:
- Dust/carry/residue invariant:

## G. Failure semantics

For each failure:

| Failure | Protocol reject | Operational error | Programmer error | No-op evidence | Public code |
|---|---:|---:|---:|---:|---|
| | | | | | |

- Are independent violations returned in canonical order?
- Are dependent checks blocked without invented defaults?
- Does any broad exception handler erase defect identity?

## H. Formal and executable correspondence

- Abstract relation:
- Executable Python model:
- Rust implementation:
- Tau/ESSO/SMT model:
- Lean theorem:
- RISC0 journal/guest:
- Mounted runtime transition:
- Differential vectors:
- Mutation controls:
- Which arrows are proved, checked, assumed, or absent:

```text
spec relation
  -> executable model
  -> implementation
  -> proof projection
  -> mounted commit
```

Do not summarize this chain with one unqualified word such as "verified."

## I. Evidence invalidation

A semantic or compiler-visible change may invalidate:

- [ ] state/schema versions
- [ ] canonical roots
- [ ] signatures
- [ ] Rust/Python vectors
- [ ] ESSO evidence
- [ ] Lean theorem imports/build
- [ ] RISC0 image IDs
- [ ] retained receipts
- [ ] verifier/source inventories
- [ ] claims registry entries
- [ ] release manifests

List exact artifacts to rebuild rather than rebinding hashes.

## J. Required counterexamples

- Minimal pre-repair witness:
- Mutation that old code accepted:
- Why local conservation or type checking did not catch it:
- New exact reject code/violation:
- Prestate/effects unchanged assertion:
- Positive legal state that remains representable:
- Nonbaseline/helper behavior that remains intentionally supported:

## K. PR claim

Complete these sentences:

> This PR proves/checks/implements ...

> This PR does not prove/check/implement ...

> The strongest remaining authority blocker is ...
