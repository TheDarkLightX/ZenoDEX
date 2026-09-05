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
