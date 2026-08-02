# E04 completion report: total stored-state classifier

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

Functional target: the E04 files in this isolated worktree, dependent on the
clean E03 packet head `f0c260400afccd561d35345886f7c17dc4711944`.

Functional commit: `c601cba60d5b7e234b61bc920fec945c51151b0f`

Functional tree: `09973a4133d3f3725e2b2b2c84aa30770840b379`

## Result

E04 now has a typed, pure classifier over a verifier-owned attempt, a
structurally validated stored-state view, and a matching fresh-reopen receipt.
It returns one of the four retry classes required by the taskbook and carries
client knowledge separately:

```text
ALREADY_COMMITTED
ABSENT_RETRYABLE
STALE_STATE
DEFINITE_REJECTION

CONFIRMED | INDETERMINATE
```

The complete durable enum also retains `NEWLY_COMMITTED`, which is reserved
for the E05 linearizing publication operation.

The attempt root binds the E01 request identity, complete E03 identity,
expected pre-state, writer profile, authority root, verifier profile, and a
typed relation between request-context sequence and publication-history
sequence. The two coordinates are domain-separated and checked against their
respective E01/E03 sources. The state root binds the complete stored commit
chain, state head, authority context, allowed writers, and configuration
profile.

The reopen receipt binds that snapshot and subject context to a datastore
profile, read version, and freshness epoch. This is an explicit model port for
an external canonical-reopen verifier. The local private registry does not
prove that a real datastore supplied the receipt.

## Evidence

```text
20 focused E04 tests passed
260 existing M6 core regression tests passed
E04 source vector regeneration passed
E04 independent checker passed
Ruff passed
Ruff format passed on the touched Python files
strict mypy passed on the five E04 Python targets
Python compilation passed
```

The tests include constructor forgery, object mutation, nested-state
mutation, exact duplicate replay, changed fingerprint, nullifier collision,
stale head, authority/sequence/profile mismatch, reopen receipt forgery and
subject mismatch, bounded rejection paths, wrong enum/type, and
confirmed/indeterminate parity.

The Lean source artifact contains an abstract total Boolean-flag partition and
knowledge-separation theorem. It does not formalize E04's partial reopen
`value | reject` boundary or the Python refinement. The direct Lean 4.27
compilation passed against the existing local Mathlib build, with the output
written to a temporary directory. The ordinary Lake package command remains
blocked in this isolated copy because the shared Mathlib build cannot create
its lock file from this sandbox:

```text
cd lean-mathlib && lake env lean Proofs/FCISM6E04RetryClassifier.lean
error: read-only file system while opening
/home/trevormoc/deps/mathlib4/.lake/config/mathlib/lakefile.olean.lock

direct Lean 4.27 compilation: exit 0
```

## Nonclaims

E04 does not prove a production database read, canonical-reopen verifier,
freshness/authenticity of a datastore receipt, write, CAS, transaction
isolation, crash recovery, filesystem durability, runtime caller reachability,
destination authentication/idempotency, migration authority, accounting,
backing, zUSD safety, or value movement. The private registries and receipt
mint are model provenance guards rather than production authentication. M6
remains research-only, unmounted, and non-promotable.

## Next dependency

E05 must consume this classifier inside one transaction that compares the
current state root and authority epoch while inserting the complete
publication aggregate. E04 alone does not authorize a new commit.
