# PR #477 Mounted Authority Migration

Status: **normative execution plan; all promotion claims remain blocked**

This file closes the gap between the exact committed-value substrate and the
mounted `DexState` authority path. It must be read after `ERRATA.md`,
`DECISIONS.md`, and `PR477_STATE_SCHEMA.md`.

## 1. Semantic hierarchy

```text
Formal Methods Philosophy FCIS tutorial
  defines the aggregate core/shell meaning

FCIS authority snapshot packet
  specializes ownership, admission, patches, and migration

mounted ZenoDEX runtime
  must refine both at every authority-bearing caller
```

The executable core is an implementation of the denotation. It is not itself
the independent specification that makes the denotation true.

The aggregate command relation is:

```text
Decision
  = Accept(NewDexState, CommitPlan, Receipt)
  | Reject(RejectReason, RejectionReceipt)
  | CommittedFailure(FailureReason, NewDexState, CommitPlan, FailureReceipt)
```

An internal state-patch leaf may use the narrower relation:

```text
LeafStep(CommittedValue, TypedDelta, ExplicitContext)
  -> LeafReject(StableReason)
   | LeafOk(NewCommittedValue, CanonicalPatch)
```

Leaf patches do not independently issue the aggregate receipt or authorize
shell effects.

## 2. Atomic mounting rule

The eight `DexState` fields form one ownership boundary:

```text
balances
pools
lp_balances
nonces
vault
oracle
fee_accumulator
perps
```

Do not change a subset of these fields to exact committed types while mounted
authority readers still expect legacy mutable classes. A partial switch creates
two meanings of `DexState`, encourages compatibility mutators or projections,
and makes roots, snapshots, effects, and rejection behavior depend on which
caller observed the state.

The final field switch occurs in one reviewed change only after every row in
section 5 has an exact implementation and parity evidence. `DexState` remains
the sole public committed aggregate. Do not add a second public
`CommittedDexStateV1`.

## 3. Allowed temporary coexistence

Before the atomic switch, exact values may exist beside the mounted legacy
state only as:

- one-way admission outputs;
- exact root and snapshot parity oracles;
- exact leaf transition outputs;
- read-only differential evidence.

They must not be converted back into a mutable whole-domain representation for
authority evaluation. A legacy implementation may remain temporarily as the
pinned comparison oracle. It cannot decide acceptance after the exact path is
promoted.

Proposal generation and authority validation are distinct:

```text
untrusted/advisory settlement proposer
  may use isolated implementation-specific work structures

exact strong validator
  replays the proposal over exact committed state and decides acceptance
```

The proposer never receives authority merely because it is deterministic or
because its result matches a happy-path fixture.

## 4. Migration phases and hard gates

### M0. Freeze the contract

Required before source migration:

- packet checker passes;
- packet receipt binds every normative file;
- source head and merge base are recorded;
- all `FCIS-477-*` statuses remain `OPEN` until mounted evidence exists;
- no implementation silently answers a design question.

### M1. Complete exact readers

Each exact committed value exposes only invariant-preserving reads needed by
mounted code. Readers return exact scalars, exact committed children, or
canonical tuples. They do not expose internal indexes, mutable dictionaries,
legacy domain objects, or structural protocols accepted by legacy builders.

Required readers include:

```text
balance lookup and canonical entries
LP balance and duration metadata lookup plus canonical entries
nonce lookup and canonical entries
pool lookup and canonical pool entries
optional-module exact scalar fields
perps exact market/account traversal
```

### M2. Complete exact leaf transitions

Implement and differentially bind these return-new operations:

```text
balance deltas
nonce advances
LP position and metadata deltas
pool reserve and supply deltas
pool creation
optional-module transitions used by mounted DEX paths
perps transitions used by mounted DEX paths
```

Pool supply changes are derived from canonical LP deltas inside the aggregate
spot candidate. An input cannot independently choose an LP balance delta and a
contradictory pool-supply delta.

Pool creation constructs `CommittedPoolStateV1` directly from exact trusted
kernel outputs and a profile-owned status value. It must not construct a
mutable `PoolState` and re-admit it. Creation plus its reserve, LP, balance, and
event consequences either produce one complete candidate or reject with no
candidate.

### M3. Replace mutable strong-validator replay

The promoted strong settlement validator consumes exact committed pre-state.
It may receive legacy settlement and intent inputs only until PR #478 supplies
the exact owned authority types. That temporary input compatibility does not
permit a legacy mutable state projection.

For each included intent, replay must:

1. validate the same shape and binding preconditions in the declared order;
2. evaluate the same exact integer kernel;
3. construct typed balance, reserve, LP, and creation deltas;
4. apply them through exact return-new leaf transitions;
5. carry the new exact candidate to the next intent;
6. accumulate expected canonical settlement data;
7. compare every supplied fill, delta, and event with that expected data;
8. run conservation and post-state invariants over the exact candidate.

The validator must not allocate `BalanceTable`, `LPTable`, `PoolState`, or a
mutable whole-state clone. If a math kernel currently requires a mutable domain
record, extract a scalar or exact-value pure kernel and prove parity before
using it.

Preserve current public rejection ordering and strings during PR #477 unless a
separate decision explicitly authorizes a change. The old validator remains a
differential oracle until the exact corpus, stateful sequences, and malformed
cases agree.

### M4. Migrate every authoritative consumer

Change signatures and implementations together. Do not add compatibility
mutators or committed-to-legacy projections. Each changed consumer receives a
focused exact-type negative test and a valid-corpus parity test.

### M5. Switch `DexState` atomically

`DexState.__post_init__` admits all eight field candidates in the fixed order
from `PR477_STATE_SCHEMA.md`, checks aggregate invariants and canonical size,
then assigns every candidate. Failure exposes no partially initialized state.

At this point:

- exact state/root/snapshot readers become the mounted readers;
- exact nonce and settlement transitions become the mounted transitions;
- `step` derives state, effects, and receipt from one candidate;
- aggregate `Reject` retains only its canonical rejection receipt;
- any protocol-defined committed failure uses the third decision branch.

### M6. Remove the obsolete authority representation

Only after M5 evidence passes, remove mounted use of:

```text
FrozenBalanceTable
FrozenLPTable
FrozenNonceTable
FrozenPoolState
deep_freeze compatibility paths
copy-based pure settlement application on the authority path
legacy mutable strong-validator replay
```

Legacy mutable source classes may remain at decode or compatibility ingress if
the exact admission facade owns them immediately and no committed state retains
their graph.

## 5. Mounted consumer matrix

| Surface | Current authority dependency | Required exact replacement | Promotion evidence |
| --- | --- | --- | --- |
| `src/core/dex.py::DexState.__post_init__` | `freeze_*` legacy subclasses and optional catch-all | eight exact field facades, all-candidate assignment, aggregate size check | invalid-last-field no-escape; retained-alias mutation; exact field-type audit |
| `src/core/dex.py::_validate_and_apply_settlement` | legacy strong validator and `apply_settlement_pure` | exact strong replay returns the same exact candidate used for effects | acceptance/rejection, post-bytes, roots, and effects parity |
| `src/core/dex.py::step*` | legacy nonce and settlement application | exact nonce advance plus exact evaluated candidate; three-way aggregate result | reject receipt only; committed-failure scenarios; same-candidate property |
| `src/core/settlement_strong_validator.py` | cloned mutable balances, pools, and LP table | exact candidate replay through typed leaf deltas | full validator suite differential; stateful route/CoW/create/liquidity sequences |
| `src/core/batch_clearing.py::compute_settlement` | mutable proposal scratch | remain explicitly proposal-only, then pass exact strong validation | negative test proving proposer output is never self-authorizing |
| `src/core/batch_clearing.py::apply_settlement_pure` | whole-domain legacy copies | removed from mounted authority; exact aggregate spot application | canonical delta and full-state parity |
| state and support root modules | legacy table/pool traversal | exact committed root preimages | golden preimage and digest parity |
| `src/integration/dex_snapshot.py::snapshot_from_state` | legacy getters and enum values | exact committed traversal with the same canonical snapshot schema | byte-identical full snapshot fixture |
| `src/integration/dex_snapshot.py::state_from_snapshot` | constructs legacy source graph | may remain outer decode ingress; `DexState` immediately owns all fields | malformed, bound, round-trip, and retained-source mutation tests |
| nonce batch validation/application | mutable `NonceTable` | exact nonce reads and one return-new canonical nonce patch | replay/no-op/error precedence parity |
| quote, route, and settlement binding readers | legacy pool and balance objects | exact committed pool/balance inputs or scalar pure kernels | fingerprint, quote, route, and rejection parity |
| perps integration | legacy perps aggregate and records | exact committed readers and return-new perps transitions | all variant lifecycle and root parity |
| zUSD, testnet, and monetary bridges | direct legacy `DexState` field assumptions | exact reads or explicit outer adapter with no authority projection | mounted scenario tests and terminal-path nonclaims |
| API/UI/debug projections | ad hoc dictionaries | non-authoritative typed projection followed by canonical codec | cannot flow back into core authority entry; round-trip tests |

## 6. Exact aggregate spot application

The spot candidate is constructed in one pure operation from:

```text
exact committed balances
exact committed pool map
exact committed LP table
canonical balance deltas
canonical reserve deltas
canonical LP deltas
canonical pool-creation values
explicit transition context
```

Evaluation order is fixed:

1. validate all delta representations and resource budgets;
2. validate unique pool creations against the pre-state;
3. derive LP supply deltas from LP position deltas;
4. build the full set of balance, pool, and LP patches;
5. apply every patch to exact pre-state values without publishing;
6. check reserve, supply, LP, conservation, and aggregate invariants;
7. return all three successor values plus their canonical patches.

Any rejection returns no successor component. The operation does not return a
new balance table while omitting a failed pool or LP candidate.

## 7. Same-candidate aggregate law

For every accepted or committed-failure aggregate result, all observable
outputs derive from one evaluated candidate:

```text
candidate.next_state
candidate.commit_plan
candidate.receipt
candidate.next_root
candidate.effect/order hashes
candidate.replay updates
candidate.outbox records
```

No output is recomputed from mutable source input after validation. The shell
publishes the resulting `CommitBundle` under expected-pre-root compare-and-swap.
Outbox delivery occurs later and is keyed by receipt-derived idempotency IDs.

## 8. Required final evidence

The atomic field switch is blocked until all of these pass at the exact head:

- packet and authority contract checkers;
- recursive exact-type and source-alias mutation audit;
- canonical snapshot, state-root, and support-root parity;
- strong-validator valid, malformed, route, CoW, create-pool, LP, and fee
  differential suites;
- stateful quote, settle, nonce, retry, and reject sequences;
- Python type checking and critical quality gate;
- production-boundary status with explicit remaining nonclaims;
- independent diff-aware review of mounted callers and consumers.

Persistent tree/HAMT adoption, deterministic parallel execution, datastore
linearizability, external delivery, and cross-language refinement remain
separate blocked contracts.
