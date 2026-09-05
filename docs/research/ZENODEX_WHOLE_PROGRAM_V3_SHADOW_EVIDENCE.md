# Whole-program V3 allocation observation evidence

Research-only W04/W05 implementation evidence, 2026-09-04. Base subject:
`c6a9fd028ded9224427a645c1217d0ce576f78af`, plus the V3 integration patch.
The read-only consumer is implemented and tested on isolated SQLite journals.
Full W05 qualification remains open. No production profile, balance, publisher,
receipt image, journal schema, activation decision or live service was changed.

## Exact source and contract

| Artifact | SHA-256 at this review |
| --- | --- |
| `src/integration/global_allocation_shadow_v1.py` | `fe1f63399bcf64d5d4d28b1c989455f022b49ada3dda6db7ec900015e0c45719` |
| `tests/integration/test_global_allocation_shadow_v1.py` | `53c783d3e6a20e22b8c7680e590f421928694698e775830a1d46dabfd1a09f40` |

`ReadOnlyAllocationSourceV1` contains a normalized path. Each read opens a new
SQLite connection with `mode=ro`, enables `query_only`, disables trusted schema,
and installs an authorizer that refuses data writes, schema writes, attachments
and pragma reconfiguration. It deliberately omits `immutable=1`: the journal may
be changing. No connection, write capability, CAS token, authority-store handle
or publisher is returned to the observer.

The reader reuses the ordinary journal's exact schema, bundle and history
validators under one read transaction. It decodes every current and predecessor
state table into the exact V1 types, then binds state root, chain, deployment,
profile, writer epoch and height to the corresponding publication head. Complete
history linkage is validated by the existing journal validator. The direct
predecessor's publication and state roots are checked again against the current
epoch record. Transactions are rolled back on failure and connections always
close.

Observation ceilings are 64 ordinary epochs, 32 MiB for the database file and
combined bundle bytes, and 8,192 total decoded rows per state, in addition to the
existing per-table V1 limits. These are observational resource ceilings, not
economic policy choices. A limit produces `RESOURCE_LIMIT`; it never truncates a
state or history into a successful observation. Bundle byte/count limits are
checked before history bundle fetch and decode. Schema/integrity inspection is
bounded by the database-file ceiling.

`GlobalAllocationShadowObserverV1` invokes the existing projection and checker
only after the read returns. It retains at most 128 small diagnostics in memory.
The diagnostic states distinguish projection, caller-root agreement/disagreement,
projection rejection, missing witnesses, unavailable/invalid source, resource
limits and observation failure. A supplied expected allocation root is a caller
comparison value; it is not an allocation commitment in the ordinary epoch
journal. Diagnostics never modify profile roots or enter a commit decision.

Successful source reads report
`LOCAL_JOURNAL_CONSISTENCY_RECEIPTS_UNVERIFIED`. Unavailable, invalid or
over-budget reads report `SOURCE_NOT_OBSERVED`. Every diagnostic declares
`authority=NONE`.

## Executable evidence

The isolated integration run passed 218 tests across the Python allocation
admission and projection suites, their parity suites, the receipt bridge suite
and the SHADOW suite. The SHADOW suite contributes 14 cases at the source hashes
above. The allocation binding review records the complete replay command.
Ruff and the narrow mypy check passed. The security scanner found zero red flags
on the new observer source; scanner silence is not proof. The design-metrics
scanner flagged only the SQLite authorizer's five parameters, which follow the
SQLite callback API.

Focused replay:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/integration/test_global_allocation_shadow_v1.py
python3 -m ruff check \
  src/integration/global_allocation_shadow_v1.py \
  tests/integration/test_global_allocation_shadow_v1.py
python3 -m mypy --follow-imports=silent \
  src/integration/global_allocation_shadow_v1.py
```

| Obligation and named mutant | Retained observation |
| --- | --- |
| Observer writes through its SQLite connection, attaches a database, or disables query-only mode | Direct attempts through the actual observation connection reject; the source file family is unchanged. |
| Observation changes economic data, history, replay, effect material or profile | Complete SQLite metadata/history/head rows and all isolated database-family file hashes remain equal around observation. |
| Comparison equality inverted or one branch omitted | Both a committed empty activation and an ordinary single-transfer epoch yield `AGREES` and `DIFFERS` for independently assembled expected and foreign roots. |
| Required receipt witness silently omitted | A committed ordinary epoch reports `MISSING_WITNESS`; supplied test witnesses expose the additional multiple-enabled-lane refusal. |
| Invalid head pointer or unknown schema object accepted | The corrupted source reports `SOURCE_INVALID` without any further physical or logical change. |
| History bounds checked after decoding, or rows truncated | The over-budget observation rejects before a sentinel activation decoder can run; table overflow produces a resource failure. |
| Failed read retains a lock | A forced decode-limit failure is followed by a successful authorized ordinary epoch commit. |
| Observer exception contaminates later work | A deliberate diagnostic exception yields `OBSERVATION_FAILED`; the next snapshot read succeeds and source files remain unchanged. |
| Head or predecessor coordinate ignored | Changed chain, deployment, profile, epoch, height or root rejects, as does binding predecessor state to the current head. |

These tests provide fixed scenario/oracle evidence and named mutation-killing
obligations. A mutation campaign was not run on the observer. This packet claims
no theorem, cryptographic qualification or exhaustive interleaving coverage.

## Observed integration gaps

The original agreement/disagreement control uses a committed empty activation
with a disabled synthetic profile and supplies no economic lane coverage. A
second positive control now commits an ordinary single-transfer epoch under a
restricted profile prepared before mock signing, acquires complete predecessor
and current snapshots, and reaches `PROJECTED`, `AGREES`, `DIFFERS` and visible
`MISSING_WITNESS`. Disabled features do not count as completed product features. The ordinary-epoch fixture is separately persisted through the
existing test writer and supplies nonempty publication history, replay and
effect material for source-isolation checks. Its current multiple-enabled-lane
state correctly fails the restricted projection. All receipt/verifier fixtures
in these tests are mocks or structural evidence.

An additional W04 binding gap was checked independently on the exact baseline:
the admitted asset-transfer allocation fragment uses the module-state root,
while the global ordinary epoch lane commits the asset-lane projection root.
For the same fixture economic poststate:

```text
module journal post root = module poststate root
  = 0xf6b85b20f1751b63b8d60b0a3ba3cf212e3e691239f31e98cbf1b652268de1a1

asset lane projection post root = global epoch lane root
  = 0x66669af90c305309acae21de0d9c9a4fc852e3f9150af8a32e3c9e5f7d27824c
```

The source pointers are `AssetTransferLaneModuleAcceptedV1.module_journal`,
`accepted.post_state`, `accepted.private_port.post_state`, and the ordinary epoch
fixture's `body_and_state.post_state.lane_roots[0]`. The comparison used
`_admission_fixture()` in the retained receipt-admission tests and `_fixture_v1()`
in the retained ordinary-epoch journal tests. A module receipt witness therefore
cannot simply be relabeled as a coordinator/global-lane allocation witness.
The observer preserves the stored roots. The separately named global allocation
admission now derives the relation from the receipt-bound module private port,
exact occurrence and complete adjacent snapshots. The allocation binding review
records this restricted repair and its Python/Rust negative controls.

The retained `test_module_and_coordinator_roots_expose_unresolved_allocation_bridge`
checks this distinction. The certificate checker already compares each fragment's
`lane_state_root` with the supplied global state's corresponding lane root and
rejects `LANE_STATE_ROOT_DRIFT`. The separate `binding_root` is the module
journal's receipt commitment. These three commitments have distinct contracts;
their difference alone is not a missing comparison or a reason to rewrite a root.
The restricted module-to-global relation is now implemented and tested.
Authenticated store acquisition, real receipt composition and formal refinement
remain separate W04/W06 obligations.

## Residual limits and next step

- The source establishes local byte/lineage consistency. It does not authenticate
  publication authorization, receipts, the active authority journal, or OS/process
  integrity. A compromised publisher remains outside the claimed boundary.
- SQLite DELETE-mode readers can delay or cause timeout of a concurrent writer.
  Failed-read lock release is tested; mounted timing/resource isolation remains
  unqualified. Capturing bounded immutable blobs under a shorter read transaction
  and validating them after releasing the lock is a possible follow-up.
- Reuse of private journal validators creates explicit implementation coupling.
  A schema or validator change requires requalification of this consumer.
- No production publisher invokes this observer, no observation scheduler is
  mounted, and no economic decision depends on the diagnostics. Diagnostics are
  process-local and disappear on restart.
- Multi-lane field ownership, authentic predecessor continuity, formal/runtime
  refinement and real receipt-backed observation remain open. Coordinator-bound
  admission is implemented for the restricted single-transfer relation only.
  W04 and W05 are incomplete.

The next integration step is to connect the implemented coordinator/global-lane
allocation relation to real receipt witnesses and publisher-owned committed
snapshots. The isolated ordinary-transfer observation currently uses mock
cryptographic verification and supplies no publication authority.
