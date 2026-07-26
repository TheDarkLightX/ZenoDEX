# FCIS M5 P0 Consolidation Preflight

Status: implementation design lock

Start head: `1989761cd7f7546ed10f63413c12b29186d25f2a`

Required corrected M4 checkpoint:
`1989761cd7f7546ed10f63413c12b29186d25f2a`

Normative packet SHA-256:
`4a5bac1ebc07165bd2d1c0cb56a81092ce9df66abcdbcc168fda743d7a2f719f`

## Authority invariant

One admitted command, one admitted context, and one admitted eight-field
pre-state produce at most one evaluated candidate. Every authority-bearing M5 value is
derived from that exact evaluation result. Decoded claims remain non-authoritative. No later constructor accepts a
replacement settlement, intent batch, context, pre-state, successor, patch,
effect, replay update, receipt, or outbox plan.

```text
OwnedSettlementV1
+ tuple[OwnedIntentV1, ...]
+ FCISStepExecutionContextV1
+ FCISCommittedStateV1
  -> FCISStepEvaluationOkV1(material, candidate, evidence)
  -> derive_decision_v1(evaluation)
  -> AcceptV1 | RejectV1 | CommittedFailureV1
  -> CommitBundleV1
```

## M4 correction

`FCISStepEvaluationOkV1` currently discards the exact admitted command and
pre-state. That omission enabled a caller to supply a different settlement to
the rejected M5 implementations. M4 will retain one immutable evaluated
material value containing:

1. the exact admitted eight-field pre-state;
2. the exact admitted settlement;
3. the exact admitted intent tuple in protocol order;
4. the exact admitted execution context.

The successor candidate will retain one exact eight-field successor aggregate
plus its already-computed canonical spot and nonce patches. Existing raw inputs
will not be retained.

## M5 P0 authority graph

The unmounted P0 graph separates decoded claims from derived authority. Closed
admission reconstructs exact claim data for replay and verification. It does
not mint an authority witness.

```text
untrusted source
  -> closed admission
  -> exact DecisionClaimV1 | CommitBundleClaimV1
  -> recompute from the exact M4 input lineage
  -> equality and binding checks
  -> controlled DecisionV1 | CommitBundleV1
  -> shell commit port
```

The commit port rejects every plain admitted claim even when its fields are
well-formed. Controlled constructors are restricted to the derivation modules
and structurally checked. This prevents a caller from selecting a successor
root, receipt root, budget hash, outbox identity, or committed-failure variant
and obtaining authority merely through successful decoding.

The unmounted P0 graph will define exact frozen, slotted, final claim values for:

- transition budget;
- owned balance, pool, LP-position, and optional-module patch atoms;
- canonical DEX patch;
- owned effects;
- replay/nullifier updates;
- commit plan;
- acceptance, rejection, and committed-failure receipts;
- outbox records and plan;
- exhaustive three-way decision;
- immutable commit bundle.

Every source carrier is an exact frozen, slotted, final dataclass distinct from
its exact claim output. Every record is registered in the existing closed
admission algebra. Canonical encoders use explicit field projections.
Reflection, generic object traversal, `str()` fallback, caller-supplied
canonical-byte witnesses, and treating caller-supplied roots as derived
authority are forbidden.

`CanonicalAuthorityClaimBytesV1` is evidence only that the closed encoder
produced the bytes. Its constructor is controlled and its call sites are
structurally restricted. Plain `bytes` and caller-created lookalikes carry no
canonicality evidence.

The normative `DecisionV1` and `CommitBundleV1` names are reserved for
controlled values produced by pure derivation. Their decoded counterparts use
the explicit `*ClaimV1` suffix.

## Patch law

The M5 patch grammar describes typed compare-and-replace data. The controlled
M5 patch is derived from the pre-state, successor, and reviewed M4 patch values.
An admitted patch claim alone authorizes no write.

```text
DeclaredChangedCells(pre, successor)
  = EncodedPatchCells(derived_patch)
```

The derivation rejects:

- a declared write whose expected value differs from the exact pre-state;
- a declared write whose replacement differs from the exact successor;
- a changed state cell absent from the patch;
- a patch cell whose value did not change;
- duplicate or non-canonical write order;
- a nonce successor not exactly reproduced by the replay update.

## Decision and bundle law

`AcceptV1` and `CommittedFailureV1` contain only one successor, one commit plan,
and one receipt. Effects and replay updates live only inside the commit plan.
The authoritative outbox plan lives only inside the controlled commit bundle and
is derived from the receipt identity plus the ordered external effect identity.
A decoded outbox plan is replay data only.

`RejectV1` contains only one rejection receipt. It has no successor, plan,
effects, replay update, outbox plan, or bundle.

The current spot profile has no intentional committed-failure rule. The
variant remains in the closed grammar and its production constructor is
unreachable until a separately versioned rule declares the fields it may
change.

An admitted `CommittedFailureClaimV1` is therefore replay data only. It cannot
be converted into a current-profile `DecisionV1` or `CommitBundleV1`.

## Supersession map

The following branches are evidence sources only and are not implementation
ancestors:

- PR #488 head `a2b570a8e5da043380ec1b3e43aab9932a42692f`;
- local PBT head `d2cc011b`.

Their mechanisms are superseded as follows:

| Rejected mechanism | Replacement |
| --- | --- |
| replacement settlement argument after evaluation | settlement retained in evaluated material |
| reflective dataclass patch encoder | explicit closed patch schema and codec |
| arbitrary canonical bytes/root fields | root derived from exact canonical encoder |
| duplicated effects on decision and plan | effects live once in `CommitPlanV1` |
| duplicated replay update on plan and bundle | replay lives once in `CommitPlanV1` |
| caller-supplied outbox plan | outbox derived inside bundle construction |
| stringly independent reject reason | reason exists only inside rejection receipt |
| one-way replay inclusion check | exact replay application equals successor nonce state |
| source files omitted from checker | M5 profile plus final-mount coverage assertion |

## Checker and evidence lock

Before broad tests:

```text
changed_authority_files subset_of checker.checked_paths
```

The M5 structural profile and its mutation tests must reject:

- omitted M5 authority path;
- generic byte binder;
- reflection or generic dataclass traversal;
- hand-written public admission outside the profile;
- raw-value read after admission;
- successor or settlement substitution;
- undeclared replay mutation;
- duplicate rejection reason;
- a fourth decision variant not registered in schema and codec.
- direct construction of canonical-byte evidence;
- claim values passed to the commit port;
- successor-root, receipt-root, budget-hash, effect, replay, or outbox
  substitution after evaluation;
- a current-profile committed-failure production path;
- schema, constructor, or projector branch omission for any registered
  variant.

The useful PR #488 and PBT counterexamples will be minimized into semantic
tests. Passing behavioral alias tests alone is insufficient.

## P0 nonclaims

P0 is unmounted. It does not claim:

- complete support-root v5 coverage;
- production datastore linearizability;
- crash-safe external delivery;
- Python/Rust byte parity;
- proof-guest or Tau refinement;
- mounted FCIS authority;
- M5 completion.
