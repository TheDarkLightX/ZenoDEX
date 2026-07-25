# FCIS Active Pull Request Chain Review

**Review date:** 2026-07-25

**Scope:** ZenoDEX PRs #476, #477, #478, #479, and #484

**Decision:** no open FCIS PR in this set is currently ready to merge

## Executive result

The review separates source quality from GitHub merge readiness.

| PR | Exact remote head | Source verdict | GitHub verdict | Merge now |
| --- | --- | --- | --- | --- |
| #476 | `7261e38a28d8edc99eac2995d61335a6a9f8da49` | Conditional pass for its demotion and inventory scope | Draft, unstable, no review approval, dependency checks failing | No |
| #477 | `576c7bb8a61012858db14d7d1092244ed4e9f2b3` | Conditional pass as an unmounted stack base | Draft, unstable, no exact-head approval, broad checks failing | No |
| #478 | `6dbb9b36237d982515777caae04a296d0ebac040` | Blocking no-go | Conflicting, no approval, checks failing | No |
| #479 | `b0420dbc359a506cf1f410182e101803bc32babf` | Documentation accepted as proposed architecture guidance | Merged | Already merged; no runtime closure |
| #484 | `5d5366582633e96bcfa0b40a9226d4293c83283a` | Remote head is stale; reviewed local M4 source is a conditional pass for stack progression only | Draft, unstable, no approval, checks failing | No |

The repaired local #484 branch is at:

```text
source checkpoint: a6e20097d74641784402fb2af5a9939beaf11a9d
review and M5 handoff: fd0345bc76860e2bd6e2c48bdb2b830625a5cbb1
```

Those commits were not on GitHub when this review was recorded. GitHub must
test the pushed exact head before #484 can receive a remote verdict.

## PR #476: Rust FCIS inventory and authority gate

### Verdict

Conditional source pass for the stated containment scope. Do not treat this PR
as Python/Rust FCIS equivalence or as a Rust-authority promotion.

The relevant authority diff makes the public-testnet policy more conservative:
partial-CBC surfaces are removed from the required Rust-authority set, attempts
to re-promote those surfaces fail closed, and production-strict remains Python
authority. This is consistent with the verifier-authority doctrine.

### Evidence and limitations

- Exact head: `7261e38a28d8edc99eac2995d61335a6a9f8da49`.
- The dedicated structural-closure and runtime-reproducibility checks passed.
- Python/Rust shadow differential and Rust test/clippy/fmt checks passed.
- The PR is still a draft with no approving review.
- Python, UI, and RISC0 dependency-audit checks failed.
- The baseline explicitly accepts existing panic and raw-wire findings. Those
  entries are debt inventory, not closure evidence.
- `AuthorityPolicy.per_surface` remains a mutable mapping inside a frozen outer
  record in the surrounding implementation. PR #476 did not introduce that
  representation, but later authority-policy work must replace it with an
  exact owned value before claiming transitive authority immutability.

### Required disposition

Keep #476 as a containment/inventory PR. Merge only after its required GitHub
checks and review policy pass. Carry its accepted findings into the M5/M6
closure ledger rather than interpreting the baseline as acceptance for release.

## PR #477: closed state admission and exact transition substrate

### Verdict

Conditional pass as the M2/M3 stack base. It is not merge-ready and it does not
authorize a mounted FCIS transition.

The current head contains the closed schema algebra, owned values, exact state
admission profile, exact transition leaves, parity fixtures, and unmounted
shadow evaluator used by the later M4 repair. The reviewed descendant at
`a6e20097` passed the structural and semantic gates listed in the M4 completion
receipt, which supplies useful integration evidence for this ancestor.

### Evidence and limitations

- Exact remote head: `576c7bb8a61012858db14d7d1092244ed4e9f2b3`.
- The head is an ancestor of the independently reviewed M4 source checkpoint.
- The rerun state-alias critical-quality and mounted-state-consumer checks
  passed at this head.
- Runtime shadow, Python/Rust differential, Rust, CodeQL, Oracle, and ZRPF
  checks passed.
- The only GitHub Codex review targets older commit `7c51b360f1`; it is not an
  exact-head approval for `576c7bb8`.
- The PR remains draft and unstable. Dependency assurance and the closed-
  disaster receipt check failed.
- The diff is very large and contains legacy compatibility representations as
  well as the closed algebra. The final-mount gate remains the authority test;
  passing substrate tests cannot make legacy paths authoritative.

### Required disposition

Use this exact head only as the reviewed stack ancestor already consumed by
M4. Do not merge it as a production-authority change until required checks,
exact-head review, and the final mounted-consumer profile pass.

## PR #478: authenticated intent and settlement/effect snapshots

### Verdict

Blocking no-go. The implementation uses mechanisms explicitly prohibited by
the frozen FCIS authority-snapshot contract.

### Blocking findings

#### FCIS-478-001: open-ended recursive freezing at authority boundaries

`src/state/immutable_collections.py` defines:

```text
deep_freeze(value: Any) -> Any
```

It dispatches with open `isinstance` checks, invokes `deepcopy`, recursively
walks arbitrary dataclasses, and returns `deepcopy(value)` for unknown values.
That permits caller-controlled behavior and creates a second validation system
outside the closed admission algebra.

#### FCIS-478-002: mutable-domain inheritance for committed values

The exact head defines:

```text
class FrozenIntent(Intent)
class FrozenSettlement(_SealedSettlementValue, Settlement)
class FrozenFill(_SealedSettlementValue, Fill)
```

Read compatibility through inheritance does not establish an exact owned
normal form. It preserves parent behavior and makes the accepted authority
surface depend on mutable-domain classes.

#### FCIS-478-003: seal flags instead of immutability by construction

The implementation toggles `_snapshot_sealed` during construction and guards
later `__setattr__` calls. This is temporal mutation with an escape-prone flag,
not a closed immutable value produced by one total admission operation.

#### FCIS-478-004: focused checks prove outcomes, not the required mechanism

The tests demonstrate alias detachment and rejected writes. `deepcopy` plus
seal flags can satisfy those observations while bypassing the sole-admission
contract, stable error precedence, budget accounting, and closed registries.
The focused workflow did not enforce the frozen contract checker at this head.

### GitHub state

- Exact head: `6dbb9b36237d982515777caae04a296d0ebac040`.
- The PR is non-draft but conflicting.
- It has no approving review.
- Dependency-assurance and closed-disaster checks failed.
- The automated comment saying no major issue was a false negative. It reviewed
  behavior without the later frozen construction contract.

### Required disposition

Do not merge or repair this implementation in place. Supersede it with the
closed-algebra authority representation already present in the later stack.
Preserve its alias witnesses as negative tests against future regressions.

## PR #479: FCIS patterns report

### Verdict

Merged documentation with useful architectural guidance. It carries no runtime
authority and closes no implementation milestone.

Use the Formal Methods Philosophy FCIS tutorial as the semantic baseline and
the report as a specialized implementation companion. Keep claims such as
persistent-map adoption, typestate pilots, deterministic parallel execution,
and authenticated-state structures at proposed or experimental status until
their individual refinement gates pass.

## PR #484: exact authoritative consumers

### Verdict

The remote PR cannot be approved because its GitHub head predates the
implementation and review repairs. The repaired local source is a conditional
pass for M4 stack progression and remains deliberately unmounted.

### Reviewed local source

The repaired source checkpoint at `a6e20097` establishes:

1. one exact command admission;
2. the same admitted object graph reaches nonce, settlement, fee, and support
   consumers;
3. private already-admitted sinks are capability-restricted;
4. raw companion, ignored-result, second-admission, and reflective-import
   variants are checker-rejected;
5. support-root v5 is derived from the admitted pre-state;
6. mounted support-root v4 bytes remain unchanged;
7. v5 remains a separate unmounted profile.

Independent drift review rejected 11 bounded provenance and private-capability
mutations. The local source also passed the focused semantic suite, structural
checker suite, critical quality gate, production-boundary checker, Ruff, and
mypy as recorded in `FCIS_M4_COMPLETION_RECEIPT_V1.json`.

### GitHub state

- Remote exact head: `5d5366582633e96bcfa0b40a9226d4293c83283a`.
- Local reviewed head: `fd0345bc76860e2bd6e2c48bdb2b830625a5cbb1`.
- The remote head therefore lacks the reviewed M4 implementation and handoff.
- The remote PR is draft and unstable with no approving review.
- Its existing mounted-state-consumer, dependency, and closed-disaster
  failures apply to the stale head and cannot certify the local repairs.

### Required disposition

Push the reviewed local head, wait for exact-head CI, and obtain an independent
review against that SHA. Even after those checks pass, M4 is approved only as
an unmounted stack checkpoint. M5 owns the authority switch and must stop with
`M5_BLOCKED_NO_AUTHORITY_SWITCH` if any commit-bundle, support-root, datastore,
or Python/Rust refinement obligation remains open.

## Merge order

No merge order is currently authorized. The safe progression is:

```text
#478 stays blocked and is superseded
-> push and certify repaired #484 exact head
-> complete M5 on that reviewed ancestor
-> obtain exact-head review and required GitHub checks
-> decide how to collapse or rebase the oversized #477/#484 stack
-> merge only the clean reviewed lineage
```

PR #476 can proceed independently as containment after its own required checks
pass. PR #479 is already merged and remains documentation evidence only.
