# Primary-Agent Review Checklist

Use this after the implementation agent returns each PR. Review #477 and #478
separately.

## 1. Source identity and ancestry

- [ ] Local head equals the supplied exact head.
- [ ] GitHub PR head equals the supplied exact head.
- [ ] Worktree is clean except explicitly listed artifacts.
- [ ] Base and merge base are correct.
- [ ] #478's parent is the reviewed final #477 head.
- [ ] Design-packet receipt is present and matches current packet files.
- [ ] Evidence artifacts name the same exact source head.

## 2. Closed accepted language

- [ ] Every authority entry point names an exact source schema.
- [ ] Every primitive rejects subclasses and bool-as-int.
- [ ] Every record, enum, intent kind, event policy, and perps variant appears in
      an exhaustive drift-checked registry.
- [ ] Exact Python enum members are copied to `OwnedEnumV1`; no member or
      mutable `.value` alias survives admission, including in map keys.
- [ ] Unknown tags, fields, and variants have one stable reject.
- [ ] The mounted `admit` facade has exactly four arguments and binds one
      nonempty module-owned registry plus exhaustive construction/encoding
      resolvers; no caller-selected fifth input exists.
- [ ] No generic copy, thaw, reflection, coercion, or compatibility fallback
      enlarges the language.
- [ ] Limits cover depth, active cycles, nodes, items, bytes, strings, and
      collection cardinality.
- [ ] Rejection order is independent of insertion order, hash seed, worker
      timing, and exception text.

## 3. Ownership and construction

- [ ] Source, committed, and scratch representations are distinct.
- [ ] Committed collections and records have no mutable base.
- [ ] No `object.__new__` or skipped invariant construction exists.
- [ ] Reinitialization and base-initializer regressions pass.
- [ ] Already-owned-looking values are revalidated.
- [ ] Every getter/projection returns immutable data or a fresh scratch value.
- [ ] No mutable source or scratch child reaches committed state.
- [ ] The CPython trusted-code nonclaim remains explicit.

## 4. Authority phases for #478

- [ ] Raw bytes, canonical bytes, parsed, authenticated, authorized, evaluated,
      and committed values are distinct.
- [ ] Full input consumption and duplicate-key rejection happen before
      authentication.
- [ ] Owned intent does not masquerade as authentication or authorization
      evidence.
- [ ] Signature bytes come from the exact owned canonical intent.
- [ ] Intent batches are bounded tuples with canonical order.
- [ ] State, effect, receipt, nonce updates, and hashes use one evaluated
      candidate.
- [ ] Generic bounded event JSON is documented as the open
      `EVENT-TYPING-001` compatibility boundary.

## 5. Static structural review

Search changed modules and mounted consumers for:

```text
Any
copy
deepcopy
pickle
__copy__
__deepcopy__
__reduce__
is_dataclass
fields(
isinstance(
Mapping
Sequence
Iterable
set
frozenset
object.__new__
__dict__
dataclasses.replace
mutable setter calls
environment, clock, random, filesystem, network, or global reads
```

Each hit is classified. The contract checker must reject forbidden authority
hits and its own mutation tests must prove every rule is live.

## 6. Executable evidence

- [ ] Every scoped audit ID maps to one or more retained test nodes.
- [ ] Pre-repair witnesses were observed or structurally justified.
- [ ] Shared combinator adversarial tests pass.
- [ ] Domain tests for the PR pass.
- [ ] Static checker and mutation tests pass.
- [ ] Canonical bytes and state/support/effect roots match valid baselines.
- [ ] Stateful reject/retry/replay sequences pass.
- [ ] Mounted DEX/perps consumers pass.
- [ ] Ruff, formatting, mypy, compilation, and critical gate results are
      recorded.
- [ ] GitHub checks apply to the exact reviewed head.
- [ ] Infrastructure or unrelated failures are classified, never converted to
      passes.

## 7. Claim audit

- [ ] PR claims only the contracts it actually closes.
- [ ] Parser ownership is not presented as cross-language refinement.
- [ ] Snapshot ownership is not presented as datastore atomicity.
- [ ] Bounded ESSO evidence is not presented as production linearizability.
- [ ] Lean abstract theorems are not presented as runtime refinement without a
      checked binding.
- [ ] Footprint and parallel execution remain advisory/disabled unless their
      separate contract closes.
- [ ] Economic lifecycle, consensus time, typed events, Rust ownership,
      persistent collections, outbox delivery, and production readiness remain
      open where applicable.

## 8. Decision

Return one of:

```text
PASS FOR STACK PROGRESSION
  all PR-scoped requirements SATISFIED;
  wider production profile still blocked

CHANGES REQUIRED
  one or more exact violations with witnesses

UNVERIFIED
  evidence or source identity insufficient
```

Do not return a merge recommendation from GitHub mergeability alone. For the
final Qwen or other peer-review packet, provide the exact commit, complete diff,
this specification folder, changed source files, changed tests, checker output,
and canonical/root parity artifacts.
