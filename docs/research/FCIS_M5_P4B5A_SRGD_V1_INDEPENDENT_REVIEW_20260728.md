# FCIS M5-P4B5A SRGD-v1 independent review

**Verdict:** `ARCHITECTURE_ACCEPTED_FRESH_UNMOUNTED_IMPLEMENTATION_AUTHORIZED`

**Implementation:** fresh unmounted Python/Rust checkpoint authorized

**Authority mount:** blocked

**Context source head:** `6771bff2d55ba08421b586e2db75441deb87f582`

**Reviewed amendment SHA-256:**
`c8fc946d916923fed8282112a5b4722fae774c67147e37a76b6099701f3f17e8`

**Supplied research bundle SHA-256:**
`28fef9d562d66cc6d6329c037604c393b93b555badeca1dea47fc96772e5bdf2`

## Result

Support-Respecting Greedy Deficit apportionment is a viable three-role
allocator architecture. Independent review found no counterexample against
the exact rule:

```text
score_i = deficit_i + current_fractional_numerator_i
eligible_i = current_fractional_numerator_i > 0
```

The review accepts SRGD-v1 as the allocator selected for the proposed P4B5A
amendment.

The exact amendment passed a focused architecture re-review after closing the
configuration-root, snapshot-namespace, selector-totality, and executable
relation gaps. It may now govern a fresh unmounted Python/Rust implementation
checkpoint. The supplied research result does not promote the existing
cursor/dust experiments, runtime authority, or release claims.

## Exact reduction to the primary source

For the paper's current residual vote `v_i` and accumulated surplus
`sigma_i`, use:

```text
v_i = fraction_i / D
sigma_i = -deficit_i / D
```

The paper minimizes:

```text
sigma_i - v_i
```

SRGD maximizes:

```text
deficit_i + fraction_i
```

These rankings are identical. The support restriction is also identical:
`fraction_i > 0`.

Primary sources:

- [Online Proportional Apportionment, SODA 2026](https://epubs.siam.org/doi/10.1137/1.9781611978971.174)
- [arXiv full text](https://arxiv.org/abs/2510.14752)

The paper permits future inputs to depend on previous allocations, matching
the adaptive policy threat model.

## Required claim corrections

### Ranking wording

“Greatest accumulated deficit” is ambiguous and unsafe.

The minimized mutation witness is:

```text
D = 3
d = (0,0,0)

w = (1,1,1), n = 1
deficit-only fixed tie chooses buyback
d = (-2,1,1)

w = (0,1,2), n = 1

deficit-only ranking chooses treasury
d' = (-2,-1,3)
```

The mutation reaches the forbidden boundary. Exact SRGD uses `d+f`, chooses
rewards, and returns `(-2,2,0)`.

### Fixed-grid optimality

The paper's lower bound uses unrestricted real residual inputs. It does not
prove optimality for the fixed `D=10_000` grid.

The paper's three-recipient impossibility boundary is scoped the same way. A
fourth fixed-grid role still requires a new architecture review, while
fixed-grid impossibility remains `UNKNOWN`.

## Replayed evidence

The supplied executable evidence was independently replayed:

| Gate | Result |
| --- | ---: |
| One-step invariant cases, `D=2..12` | 2,350,975 passed |
| Independent subset oracle, `D=2..8` | 251,615 passed |
| Tie-cutoff cases | 74,872 passed |
| Zero-support assertions | 1,139,754 passed |
| Two-way fragmentation cases | 8,458,860 passed |
| Schedule-dependent fragmentation cases | 1,038,141 |
| Maximum fixed-policy fragmentation difference | 1 atom per role |
| U256 boundary vectors | 144 passed |
| Adaptive `D=10_000` steps | 100,000 passed |
| Alias assignments | 243 arithmetic cases |

Python compilation and Ruff lint passed. Ruff format check reported formatting
drift in the supplied script.

## Formal evidence added during review

### Lean

File:

```text
lean-mathlib/Proofs/FCISFeeApportionmentSRGD.lean
```

SHA-256:

```text
a7104b2abca37e9ababbe121db34c91bf4fa973a3042f9ed30f165b37bfc92b0
```

The theorem `srgd_bonus_exists_unique` is parameterized by every positive
denominator. For every valid three-role residual quota and arbitrary integer
scores, it constructs exactly one bonus tuple satisfying the support,
seat-count, `deficit + fraction` ranking, and fixed semantic tie clauses.

The theorem `step_preserves_strict_deficit` consumes that same factored
relation. It proves zero-sum preservation and:

```text
-D < deficit_post_i < D
```

for the exact support-respecting top-`k` relation and fixed semantic tie-break.
The file compiles under Lean `4.27.0` without `sorry`, `axiom`, `admit`, or
`unsafe`. Replacing one symbolic finite-bit search with an explicit 64-case
helper reduced the focused compile to `5.06` seconds and `788912` KiB maximum
resident memory under the default heartbeat limit. The theorem statement and
proof obligations did not change.

These are allocator-kernel theorems. Quota extraction, state provenance,
Python/Rust executable-selector equality, U256 runtime refinement, codecs, and
commit semantics remain separate obligations.

The deterministic D=4 companion checker:

```text
docs/research/FCIS_M5_P4B5A_SRGD_SELECTOR_TOTALITY_20260728.py
```

found one unique intended selector for all `37 * 16 = 592` invariant-state and
valid-residual pairs. Relaxing semantic tie precedence produced 57
nondeterministic pairs. Strengthening the count guard from `4` to `100`
eliminated all 555 nonzero residual pairs. These are mutation witnesses for the
architecture-level theorem and later executable-refinement tests.

### ESSO

File:

```text
docs/research/FCIS_M5_P4B5A_SRGD_D4.esso.yaml
```

Source SHA-256:

```text
1e2b02801601298c0bcd8510d7fda6960cb38f92828acab0416497ca69b4c831
```

ESSO IR hash:

```text
sha256:db7187de5d3d595a25a0de092b3a93101cb469e47db153897c495f74af61d7ff
```

Z3 `4.15.4` and cvc5 `1.1.2` agreed that initialization and every enabled
allocation transition preserve the declared invariant. The deterministic
outcome fingerprint repeated:

```text
49a0de73628807e351c75143995ffa1becfd2cf6f3318517c7442504d100428c
```

The model ranges over all invariant-valid D=4 deficit states and checks every
transition enabled by its guard. ESSO alone does not prove that the guard
admits the required transition, selector totality, selector uniqueness, or
U256 runtime refinement. The separate Lean theorem and bounded checker close
the architecture-level existence and uniqueness question.

Two independent semantic mutants exposed the difference:

- replacing the count equation's denominator `4` with `100` removed all
  nonzero residual transitions, yet the inductiveness queries still verified;
- deleting the positive-support guard clauses also verified because the
  remaining relation was still safe on its enabled transitions.

Both mutants produced the same outcome fingerprint. The fingerprint therefore
binds solver outcomes, not model semantics. A promotable receipt must bind the
model source SHA, normalized IR hash, ESSO code hash, exact command, solver
versions, and results. Implementation approval additionally requires a
non-vacuity/availability query and selector existence, uniqueness, and
executable-refinement evidence.

The analogous relaxed-tie Lean mutant also compiles. This is expected for the
current theorem: it proves scaled-deficit safety conditional on a selected
relation and does not prove deterministic tie-order necessity.

## Evidence defects

### Receipt regeneration

The supplied Python script does not regenerate the supplied JSON exactly:

- the JSON adds `evidence_labels` outside the recorded builder;
- the `research_kernel` value differs;
- no canonical `--check` mode exists.

The gate values are consistent. The receipt is not promotable until one
canonical builder reproduces it byte-for-byte.

### Composition gate

The supplied composition gate checks scalar equations and set sizes. It does
not execute:

- closed witness admission;
- expected/admitted/consumed occurrence equality;
- domain-registry transitions;
- complete `(account, asset)` grouping;
- canonical balance and pool patch construction;
- receipt and root recomputation;
- atomic publication;
- shell double-application rejection.

The `243` alias assignments establish arithmetic conservation for the toy
delta model. They do not establish canonical patch refinement.

### Oracle scope

The subset oracle is independent of the optimized selector implementation. It
shares the same deficit objective and tie specification. Describe it as an
independent selector oracle, rather than an independent semantic
specification.

### Source provenance

Commit `6771bff2...` contains the research context packet. It does not contain
the supplied SRGD report, script, JSON, or manifest. Call it the
`context_source_head` until the reviewed artifacts are committed.

## Prior integration no-go findings and architecture closure

1. Pool reserve writes and account balance writes require distinct canonical
   patch namespaces.
2. Removing the legacy protocol-recipient credit requires the selected
   `OwnedSettlementV2` ABI and complete consumer migration.
3. The distribution-domain identifier needs authenticated committed
   authority.
4. Direct destination credits are a versioned economic switch.
5. A nonzero protocol fee share requires an active authenticated policy.
6. Provisional lineage needs expected/admitted/consumed occurrence-set
   equality.
7. Distribution records cannot be executable effects.
8. State roots, support roots, receipts, commit bundles, replay, and codecs
   still understand the V1 scalar accumulator.

The reviewed amendment closes these architecture choices normatively and also
specifies canonical zero-state encoding, an authenticated configuration value,
snapshot version 5, support profile 6, mixed-version rejection, and a
selector-totality gate. The focused re-review found no remaining normative
architecture blocker. Runtime and full refinement evidence remain absent.

## Research Kernel

Run:

```text
zenodex-fcis-p4b5a-srgd-v1-20260728
```

The run records:

- the exact kernel claim;
- the primary-source reduction;
- the score-substitution counterexample;
- the fixed-grid claim-scope risk;
- replay evidence;
- the Lean receipt;
- the two-solver ESSO receipt;
- the remaining protocol-refinement dependency;
- an open falsification plan.

Research Kernel `SUPPORTED` is a local promotion state, not a production
authority statement.

## Disposition

```text
SELECT_SRGD_V1_AS_RESEARCH_ARCHITECTURE
PACKET_AMENDMENT_ACCEPTED_AFTER_INDEPENDENT_REVIEW
FRESH_UNMOUNTED_PYTHON_RUST_IMPLEMENTATION_AUTHORIZED
EXISTING_CURSOR_AND_DUST_WIP_REJECTED
RUNTIME_UNCHANGED
AUTHORITY_MOUNT_PROHIBITED
```

The next action is a fresh unmounted Python/Rust implementation checkpoint
against the exact amendment. It must provide executable-selector refinement,
exact-byte parity, state/receipt/root bindings, settlement-lineage refinement,
and the required mutation evidence before another promotion review. The
existing contiguous-cursor and monetary-dust WIP remains excluded.
