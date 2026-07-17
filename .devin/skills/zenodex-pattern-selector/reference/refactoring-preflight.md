# Refactoring Preflight Checklist

Before editing existing value-moving or state-carrying code, record every item
below. This prevents mechanical refactors that break canonical encoding,
silently drop effects, or create value-loss migration traps.

## 1. Identify the exact artifact

- File path and line range being changed.
- Type name, function name, or method name.
- Is this a type definition, a transition function, a shell handler, or a
  builder?

## 2. Authority and commit boundaries

- What does this code decide or bind? (amounts, fees, ordering, freshness,
  replay, roots, effect plans)
- Is this code in `src/core/**`, `src/state/**`, `src/integration/**`, or
  `src/kernels/**`?
- What is the commit boundary? Where does the pre-state become the post-state?
- What evidence layer covers this code? (tests, property tests, proofs,
  replay receipts, claim registry entries)

## 3. Constructors, mutation sites, and retained aliases

- Who constructs this type?
- Who mutates it? (list every mutation site)
- Who holds a reference to it after construction?
- Is there any shallow copy that aliases nested mutable values?
- Does the type escape to a context where someone else holds a reference?

## 4. Public APIs and callers

- List every public API method on this type.
- List every call site for each method.
- What breaks if the method name changes?
- What breaks if the return type changes?
- Are there Python/Rust parity consumers?

## 5. Snapshot/wire serialization

- Is this type serialized to disk, to wire, or to a hash?
- What is the canonical encoding? (field order, widths, version tags)
- Does changing the representation break canonical encoding?
- Is there a schema version or migration path?
- Are there golden vectors that verify the encoding?

## 6. State-root, hash, signature, and proof consumers

- Does this type feed a state root?
- Does this type feed a hash or signature?
- Does this type feed a proof witness or receipt?
- What happens if the representation changes but the canonical encoding is
  preserved? What if it is not preserved?

## 7. Existing semantics that must be preserved

- Ordering: what order are entries iterated? Is it protocol-defined or
  implementation-defined?
- Duplicates: what happens with duplicate keys?
- Rounding: what rounding mode is used? What happens at dust thresholds?
- Rejection: what rejection codes are returned? Are they part of the ABI?
- Zero/empty: are zero balances removed? Are empty entries omitted?
- Negative: are negative values rejected? At what layer?

## 8. Complexity and performance budget

- What is the current Big-O for lookup, insertion, iteration?
- Does the refactor change the Big-O?
- For large hot state (e.g., balance tables with 100k+ entries), benchmark
  before replacing maps with linear-scan tuples.
- What is the memory overhead of the new representation?

## 9. Representation-only or intentionally semantic?

- Is this patch changing only the in-memory representation, preserving all
  observable behavior?
- Or is this patch changing semantics (ordering, rounding, rejection)?
- Representation and semantic changes should be separate patches.
- No opportunistic neighboring refactors. Touch only what the task requires.

## 10. Migration plan

- If the API changes, what is the migration path for call sites?
- Are there call sites that ignore the return value? (silent value-loss trap)
- Is a new method name needed to prevent silent breakage? (e.g.,
  `with_delta()` instead of `add()`)
- Are there golden vectors or replay tests that verify the migration?
- Is a schema version bump required?
- Are there Python/Rust parity tests that need updating?

## 11. Test plan

- What tests cover this code?
- What property tests verify invariants?
- What negative tests verify rejection codes?
- What replay tests verify determinism?
- What parity tests verify Python/Rust equivalence?
- Will the existing tests catch a silent value-loss bug?

## 12. CAS/concurrency

- What happens on concurrent commits to the same pre-root?
- Is there a compare-and-swap on the expected pre-root and version?
- Does the commit return `CommitOk` or `CommitConflict`?
- Can two transactions read the same snapshot and both try to commit?

## 13. Crash points

- What happens if the process crashes between persisting state and delivering
  external effects?
- Is there a write-ahead log or transactional outbox?
- What is the recovery procedure for each crash point?

## 14. Outbox/idempotence

- Are external effects delivered exactly-once?
- What is the replay key? (effect-plan hash, nonce, tx-id)
- Can a crashed delivery be safely retried?
- Is the outbox persisted in the same atomic commit as the state?

## 15. Conservation postconditions

- Does the transition verify that `sum(post) == sum(pre) + sum(external_in)
  - sum(external_out)`?
- Is conservation checked across the complete effect plan, not per-delta?
- Are there property tests that verify conservation over random sequences?

## 16. Retained-alias tests

- Is there a test that verifies no mutable alias from the pre-state survives
  into the post-state?
- Is there a test that mutating the pre-state after the transition does not
  affect the post-state?

## 17. Deterministic activation/versioning

- Does the commit record the exact code version and activation epoch?
- Can the transition be replayed with the same code version and produce the
  same result?

## 18. Forward recovery

- If new consensus state was committed and the process crashed, what is the
- recovery procedure?
- "Rollback" is unsafe once new state is committed — the committed state is
  now the pre-state for the next transaction.
- Is there a forward-recovery procedure that replays the outbox from the
  last committed state?
