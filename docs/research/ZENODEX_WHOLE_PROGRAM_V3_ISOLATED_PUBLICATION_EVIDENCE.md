# V3 isolated publication implementation evidence

Status: **IMPLEMENTED SUBCONTRACTS; W06 OPEN**. The integration branch starts
at `c6a9fd028ded9224427a645c1217d0ce576f78af`. Its reviewed allocation relation
is frozen at `b5e983008826d213375ffe93906e592910153a74`. This record grants no
production, migration, writer activation or complete publication mediation claim.

## Measured root factory and explicit isolated purpose

The shell's `bind_isolated_economic_root_verifier_v1` acquires a bounded regular
ELF file, computes its implementation commitment, constructs the concrete sealed
subprocess bridge from those same bytes, and binds the selected profile/image
and verifier release. It accepts neither a caller backend nor separately claimed
measured bytes. Replacement after binding is rejected by the bridge before
launch. Artifact approval provenance and process/OS integrity remain premises.

`ISOLATED_QUALIFICATION` selects an exact SHADOW verifier release and ACTIVE
profile semantics. The isolated publisher requires that purpose for both create
and open. `RESEARCH_SHADOW` cannot construct it. Production selection remains
closed. This changes process-local selection identity without changing profile,
receipt, journal or historical decoding formats. A purpose value alone establishes
neither physical store isolation nor deployed writer exclusion.

The independent review is
`ZENODEX_WHOLE_PROGRAM_V3_ISOLATED_VERIFIER_REVIEW.md`. Its exact five-file subject
and bridge docstring-only drift are retained there. Its replay passed 124 tests
and failed the canonical source-closure pin. The failure was expected evidence
staleness caused by the two reviewed existing source changes: verifier registry
and publisher. Substituting their exact baseline bytes reproduces the retained
old digest. Serializer types, enum types and canonical helper call counts are
unchanged. No serializer was added or broadened.

After this audit, the parent explicitly updated the checker's source constant
from `e577e288f05985d7b64fc8c2606f2b119229db7f0f6175c0f938dc3913a0cc23`
to `e4cb0e935d5996b1e7b0978bd898673add91fc1f2f68a051b819440661366dbd`.
The checker has no automatic regeneration option. Its reproducible computation
is `python3 tools/check_global_settlement_canonical_manifest_v1.py --json`.
This is an explicit reviewed source-closure update, with the historical failed
review preserved. It changes no economic acceptance guard.

Replay:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/integration/test_isolated_economic_receipt_verifier_v1.py \
  tests/core/test_economic_receipt_verifier_release_v1.py \
  tests/integration/test_global_economic_durable_publisher_v1.py \
  tests/integration/test_global_receipt_verifier_v1.py \
  tests/test_check_global_settlement_canonical_manifest_v1.py
python3 tools/check_global_settlement_canonical_manifest_v1.py --json
```

After the explicit pin update, the replay above passed **125 tests**. The
canonical checker reports `ok=true`, 95 source-closure files, 104 serializer
types, 35 enum types and unchanged helper call counts. Ruff and narrow mypy
passed.

The factory tests use synthetic ELF-shaped data and recording receipt backends.
They establish construction, refusal and replacement behavior. Genuine structural
receipt qualification is recorded separately in the remote receipt job evidence.
Leaf image ports, the unified root, source acquisition, allocation publication
admission and genuine economic publication remain separate obligations.

No Lean, ESSO, Kani or whole-release proof claim follows from this patch. The
low-level binder and other unmounted test adapters remain callable; deployment
complete no-bypass remains open.

## Publisher-owned committed source

`GlobalEconomicEpochJournalV1._publication_source_for_verified_publisher_v1`
requires the exact journal's registered write capability before IO. A single
read transaction validates lineage, acquires the requested complete source
bundle and activation, decodes its exact state, binds all head coordinates,
and captures current tip and authority. Only after the successful read does the
journal mint a CAS token for those captured coordinates. Unknown sources return
no snapshot; failed reads release their transaction and grant no token.

The publisher checks the candidate's disclosed pre-state against that acquired
value, then passes the acquired state itself into the pure verifier. Complete
state acquisition no longer depends on a caller supplying the preimage of a
stored head. The existing canonical state format, journal bundles and single
economic commit transaction are unchanged.

Historical sources remain readable so an exact committed retry can be recognized
after another writer wins or writer authority changes. The unchanged commit path
recognizes exact retries before fresh admission and revalidates current authority
and source CAS for a new transition. Acquiring a snapshot does not authorize a
stale transition. Another winner may change physical files during a rejected
attempt; logical rejection contributes no economic change.

The independent `ZENODEX_WHOLE_PROGRAM_V3_SOURCE_ACQUISITION_REVIEW.md` records
the exact final source hashes, competing-writer and revoked-authority replay,
capability refusal before IO, historical PRE/current POST separation, decode
failure lock release, six source faults and acquired-state mismatch refusal.
Its expanded replay passed 111 tests and failed only the stale canonical pin.
The final annotation-only typing correction was checked separately; all four
new acquisition tests passed. Existing commit, CAS, authority and retry code
retains its prior AST.

After that independent audit, the explicit checker constant was updated from
`e4cb0e935d5996b1e7b0978bd898673add91fc1f2f68a051b819440661366dbd`
to `9643388a6da6ffbc42c909b49c4d9699d83cdacc8b710c06dd7823b83dcbf8d1`.
Only the existing publisher and journal changed in the 95-file source closure;
substituting their exact `9e1531539` bytes reproduces the prior digest. Counts
and canonical serializers remain unchanged. The historical failed review stays
intact. The final focused replay passed **233 tests**, including the canonical checker,
107 decoder cases, retained observer cases and complete publisher/journal suites.
Ruff and narrow mypy over the four touched implementation modules passed.

The journal validates canonical bytes and committed ancestry under trusted
publisher/process/store integrity. It does not reverify every stored receipt on
each read, establish independent disk authenticity or restore writer authority
on restart. Those remain explicit W11/release obligations. These tests use
recording receipt backends. Allocation admission is still a separate publication
prerequisite under development; W06 is open.
