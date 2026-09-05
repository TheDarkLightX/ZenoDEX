# Committed publication source acquisition review

Date: 2026-09-04. Advisory bounded source and local-test review. Authority: `NONE`.
Baseline: `9e1531539a5a25a7e1a55c70db014bc18dc1dd62`.

Verdict: no blocking behavioral defect found in the reviewed source acquisition
and publisher substitution. **The retained canonical source-closure gate still
rejects the changed subject.** This review does not qualify W06, W11, production
publication, authenticated historical receipt ancestry, or whole-program safety.

The reviewer implemented the shared state decoder dependency. This is an
independent review of the parent's journal/publisher packet, not independent
review of every dependency. No implementation, test or manifest was edited during
this review. Only this report was added.

## Exact subject

| File | SHA-256 |
|---|---|
| `src/integration/global_economic_epoch_journal_v1.py` | `7c52b02dae0fe2ab9650543a82b96d3761cef698f278e4107a36938173faa08a` |
| `src/integration/global_economic_durable_publisher_v1.py` | `e45ffb3b2851fbaba9de869f9af6c5a03da64fa8b71ade2d8d3f59aea57c1780` |
| `tests/integration/test_global_economic_publication_source_v1.py` | `bf5bee17635273a8b0cf033382d8a87a64dcad01c2550d99f8367e70517f8c49` |
| Shared decoder dependency, `src/core/global_economic_state_decoder_v1.py` | `6ba710f308f73cdd58ecd8dadd167c4b5087eab6eb6d795fcdc22b594cc84eca` |

The journal changed during the first replay from
`3dd606dec5666d6c1b2dfcc4190b347aa2985ecbe6e214523c354b12111538ef`.
Deleting its sole added function-local annotation,
`result: DurableEconomicPublicationHeadV1 | None`, reproduced those earlier
bytes and hash exactly. That annotation repairs an inherited typing issue; it
does not execute at runtime. The other three hashes stayed fixed. The four new
tests were rerun against the final journal hash above.

## Contract assessment

`_publication_source_for_verified_publisher_v1` checks an exact, registered
writer capability bound to that journal instance before acquiring its lock or
issuing SQL. A same-type capability from another journal refuses. The handle's
open-state check precedes `BEGIN`.

One read transaction validates the complete existing journal schema and lineage,
reads the activation and requested source bundle, validates the attached current
authority history, and decodes the complete source state. The source can be a
historical activation or epoch; the current tip is retained separately. The
decoder reconstructs all ten tables under their existing individual limits.
State root, chain, deployment, profile, writer epoch and height must match the
source head. The additional 8,192-row SHADOW ceiling is not imposed on this
publication decoder.

On success, the transaction commits before the CAS token is minted and before
receipt verification starts. The token binds the captured current tip and
authority coordinates in the existing journal-local registry. Unknown sources
return `None` without minting a token. Decode or validation exceptions roll the
transaction back. Captured bundles contain immutable bytes and owned typed
values; advancing the store afterward leaves the captured source unchanged.

The publisher still owns the candidate and body before admission. It retains
the existing candidate/source/profile/root checks, additionally requires exact
equality between the caller's pre-state disclosure and the acquired state, then
replaces the disclosure with the acquired object before calling the pure epoch
verifier. The caller receives no new snapshot-acceptance parameter. The ordinary
`_CommittedEconomicSourceV1` aggregate confers no authority through construction.

The following function ASTs are identical to baseline, as independently compared:

- `_require_write_capability_v1`
- `_validate_store_v1`
- `_commit_under_lock_v1`
- `_authority_is_current_v1`
- `_exact_retry_v1`

The economic linearization point therefore remains the existing
`BEGIN IMMEDIATE` commit transaction. It checks exact committed retry before
fresh authority admission, then current authority, source/head CAS and capacity
before inserting the complete epoch and updating the head. A captured old source
supports exact committed retry; it cannot authorize a new successor after a
competing writer or revocation. Lost-response retry retains one history entry.

## SAR-01: canonical source closure requires deliberate refresh

The expanded replay returned **111 passed, 1 failed**. Its sole failure was
`tests/test_check_global_settlement_canonical_manifest_v1.py::test_repository_canonical_manifest_source_closure_passes`:

```text
observed during replay:
587a82226fc3f6bd7694fb2209bbe5d69f5b00b84926f4aa868aac258a2d936f
expected at baseline:
e4cb0e935d5996b1e7b0978bd898673add91fc1f2f68a051b819440661366dbd
```

After the journal's annotation-only change, the final current closure is:

```text
9643388a6da6ffbc42c909b49c4d9699d83cdacc8b710c06dd7823b83dcbf8d1
```

A read-only counterfactual calculation identified exactly two changed members
of the existing 95-file closure: the reviewed journal and publisher. Replacing
their bytes with baseline bytes during that calculation reproduces the expected
digest exactly. All other closure members match baseline. The counts remain
104 serializer classes, 35 enum classes and 93 canonical-helper call files;
canonical helper call counts remain `1 / 48 / 4 / 219` for command-body bytes,
global bytes, command-body hash and global hash respectively. No serializer or
wire format was added by this packet.

The checker's recorded policy requires a fresh audit and explicit checker update
after digest changes; it has no automatic regeneration command. The read-only
replay command is:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/check_global_settlement_canonical_manifest_v1.py --json
```

The integration owner must explicitly refresh the current reviewed closure and
rerun its retained tests. This report preserves the pin and historical evidence.
The shared decoder has no direct canonical-helper call and is not included in
this static closure; its exact dependency hash is recorded above. The static
closure is not a complete transitive implementation proof.

## Executed evidence

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/integration/test_global_economic_publication_source_v1.py \
  tests/integration/test_global_economic_epoch_journal_v1.py \
  tests/integration/test_global_economic_durable_publisher_v1.py \
  tests/test_check_global_settlement_canonical_manifest_v1.py
```

Result: **111 passed, 1 failed**, with only SAR-01 failing. This includes retained
competing-writer, verifier-in-flight head change, in-flight authority revocation,
exact retry after revocation, restart and lost-acknowledgement cases. These tests
use recording receipt backends; they do not verify real cryptography.

The new four source tests passed again after the final annotation-only change:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/integration/test_global_economic_publication_source_v1.py
```

Those cases cover historical source preservation after a competing commit,
foreign capability refusal before source validation, unknown-source and failed
decode no-effect behavior with transaction release, and acquired-state object
identity at the actual pure-verifier entry.

Additional independent, temporary fault-injection checks used the existing
isolated fixtures and `unittest.mock.patch` without editing source or tests:

- Replaced the source decoder result with separately altered chain, deployment,
  profile, writer epoch, height or history root. All six cases raised
  `publication source state does not match its committed head`.
- Replaced the acquisition result with an inconsistent state while retaining its
  authentic source head. The publisher raised
  `durable publisher disclosed source differs from committed state` before any
  additional receipt-backend call. The epoch file bytes and logical head stayed
  unchanged. This models a controlled internal boundary fault, not an observed
  caller-accessible attack or cryptographic collision.

Ruff passed for both source files and the new test. Style routing selected typed
port/effect adapters. Red-flag scanning reported only two existing broad exception
handlers in the publisher's monotonic-anchor recovery; neither changed here.
Scanner output supplies review triage, not evidence of safety on its own.

## Remaining premises and work

Stored bundle validation checks canonical integrity, roots and lineage. It does
not cryptographically replay historical receipts. Trusted verified creation and
publication, the process/module namespace, and untampered store/authority
integrity remain ancestry premises. Low-level journal and test adapters remain
unmounted and callable; this packet establishes no deployment-complete
publication mediation or compromised-process protection.

The read transaction performs existing bounded history/schema validation and
source decoding while locks are held. DELETE-mode readers can delay other
writers. No mounted timing, throughput, lock-contention or resource-isolation
qualification was performed. Existing history limits remain 4,096 epochs and
512 MiB of epoch bundle bytes; their adequacy is outside this review.

The allocation checker is not made a publication prerequisite by this packet.
Real image-set receipt verification, predecessor allocation ancestry, complete
lane lifecycles, runtime/formal refinement and mounted no-bypass obligations
remain separate work. No heavy proof build, remote run, live activation or
balance migration was performed for this review.
