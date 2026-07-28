# FCIS M5-P4B3 Implementor Review

## Result

Outcome: `M5_P4B3_COMPLETE_UNMOUNTED`

This checkpoint closes the exact route-binding substrate and migrates the
FCIS-only route readers. It does not switch mounted DEX authority.

Exact start head:

```text
9c7da554480f26c0466b1dae3757ff5fa2ba243a
```

Implementor heads reviewed:

```text
e5409114d  P4B3-A closed route child schemas
b0c917e98  P4B3-B controlled route values, derivation, and replay
```

The exact final P4B3-C commit is the commit containing this report. Git records
that identifier externally because a file cannot contain the hash of the
commit that contains the file without changing that commit.

Branch and worktree:

```text
agent/codex-fcis-m5-p4b3-complete-20260727
/home/trevormoc/Downloads/Autonomous Tau DEX/.worktrees/fcis-m5-p4b3-complete
```

## Review grade

The received Kimi checkpoint earns **C+ (74/100)**.

- P4B3-A was strong and close to the frozen schema design.
- P4B3-B implemented most of the route algebra and parity corpus.
- P4B3-C was absent when the implementor quota ended.
- Four authority-level defects remained: a derived binding was substitutable
  across commands, read-order parity was weakened by normalization in a test,
  hostile nested corruption could escape derivation, and FCIS support readers
  retained duplicated route validation.

The reviewer-corrected checkpoint is suitable as unmounted M5 evidence. It is
not a production-mount approval.

## Frozen-design correction

The P4B3 prompt described semantic leg scratch access as another committed
pool read. The established legacy trace and the actual FCIS read model perform
one canonical committed preflight read per unique fingerprint pool. Later
route legs use private threaded scratch reserves. Recording scratch access as a
second state read would overstate the read footprint and break direct parity.

The reviewed rule is:

```text
ObservedStateReads
  = canonical unique committed pool preflight reads

LocalScratchReads
  = internal replay evaluation
  = excluded from the committed-state read trace
```

The exact and legacy tests compare those tuples directly. No
`sorted(set(...))` projection is allowed at the parity assertion or exact
trace-consumer boundary.

## Changed

### Exact route derivation and replay

- `src/core/fcis_route_binding.py`
  - Requires the original `OwnedIntentV1` together with
    `RouteBindingV1` at pin and replay boundaries.
  - Recursively revalidates the binding and rederives it from the command
    before any pool read.
  - Rejects same-shape binding substitution from another command with
    `BINDING_INVALID` and an empty observed-read tuple.
  - Validates `OwnedMapV1` tuple storage, immutable index storage, entry
    identity, exact keys, exact values, canonical order, and schema identity.
  - Returns a stable structural rejection for hostile exact-object corruption.
  - Preserves ordered legs and repeated-pool reserve threading.
  - Returns canonical unique committed preflight reads without counting local
    scratch lookup as a state read.

### Exact route schemas and consumers

- `src/state/fcis_route_binding_schema.py`
  - Uses stable semantic schema identifiers independent of milestone names.
  - Retains the frozen 256-leg and 256-fingerprint bounds.
- `src/state/fcis_route_support_v5.py`
  - Delegates route validation to exact binding derivation.
  - Removes the parallel hand-written route validator.
  - Retains only a compatibility projection needed by legacy differential
    evidence.
- `src/core/fcis_support_profile_v5.py`
  - Derives route support cells from the exact command-bound binding.
- `src/core/fcis_traced_reads_v5.py`
  - Exact wrappers receive and forward intent, binding, and committed pools.
  - Extends the trace with the exact observed tuple directly.

### Tests and checker

- `tests/core/test_fcis_route_binding.py`
  - Adds command-substitution, hostile nested graph, schema/index corruption,
    exact boundary, rejection precedence, deterministic derivation, and wrapper
    projection evidence.
- `tests/core/test_fcis_route_binding_parity.py`
  - Compares exact and legacy outcomes and observed reads directly.
  - Covers repeated-pool scratch reuse, binding substitution, missing,
    inactive, drifted, orientation, quote mismatch, exact-in, and exact-out.
- `tests/core/test_support_root.py`
  - Binds corrupt-route support rejection to the exact derivation code/path.
- `tools/check_fcis_authority_snapshot_contract.py`
  - Registers the P4B3 authority modules.
  - Verifies exact API shapes, command-to-binding flow, recursive
    revalidation, stable schema identifiers, bounds, consumer forwarding, and
    the absence of parallel route validation or observed-read renormalization.
- `tests/tools/test_check_fcis_authority_snapshot_contract.py`
  - Adds semantic mutations for binding substitutability, open signatures,
    swapped command/binding flow, read-trace drift, schema and bound drift,
    route-support bypass, legacy reader reintroduction, traced argument swap,
    and set/sort normalization.

## Invariant and authority impact

The checkpoint establishes:

```text
Replay(intent, binding, pools) reads pools
  only if
binding = Derive(intent)
and binding is recursively exact
and pools are exact committed values
```

It also establishes:

```text
invalid or corrupted binding
  -> RouteReplayReject(BINDING_INVALID)
  -> observed_reads = ()
  -> no partial replay value
```

The following mounted files are byte-identical to the P4B2 start:

```text
src/core/dex.py
src/integration/dex_engine.py
src/core/settlement_strong_validator.py
src/core/route_settlement.py
```

No authority switch, Rust parity, proof-guest parity, production datastore
commit, crash-recovery proof, or external delivery claim is made.

## Evidence

Focused source gates:

```text
python3 -m py_compile <10 changed Python paths>
  PASS

python3 -m ruff check <10 changed Python paths>
  PASS

python3 -m ruff format --check <10 changed Python paths>
  PASS, 10 files already formatted

python3 -m mypy <5 changed source modules>
  PASS, no issues
```

Semantic and checker gates:

```text
pytest route/schema/parity/support corpus
  98 passed

pytest tests/tools/test_check_fcis_authority_snapshot_contract.py
  288 passed
```

Structural profiles:

```text
state-substrate  ok=true, violations=0
authority-graph  ok=true, violations=0
exact-replay     ok=true, violations=0
exact-consumers  ok=true, violations=0

final-mount      ok=false, violations=64
  OPEN_AUTHORITY_TYPE          5
  BROAD_ADMISSION             35
  COERCIVE_CONTAINER_COPY      1
  GENERIC_DEEP_FREEZE          3
  MUTABLE_BASE                 4
  SNAPSHOT_SEAL_FLAG          12
  FORBIDDEN_RECONSTRUCTION     4
```

Packet and repository boundary:

```text
docs/specs/fcis_authority_snapshot_v1/check_packet.py
  ok=true
  requirements=39
  declared tests=103
  bound tests=103

git diff --check
  PASS

protected mounted-file diff from 9c7da554...
  PASS, byte-identical

check_production_boundary.py --json
  ok=true
```

Broad critical gate:

```text
ruff, shell syntax, full mypy, four FCIS profiles, packet checker
  PASS

authority checker tests
  288 passed

acceptance-TCB suite
  556 passed

acceptance-TCB coverage floor
  BLOCKED
  src/core/settlement_strong_validator.py branch coverage:
  77.1% observed, 78.0% required
```

`settlement_strong_validator.py` is a protected immutable input in P4B3 and
is byte-identical to the start SHA. The broad script stopped at that inherited
floor, so its later aggregate critical coverage command did not run.

Local review tools:

```text
security red flags
  0 findings across the six source/checker paths

design metrics
  fcis_route_binding.py: 648 LOC
  check_fcis_authority_snapshot_contract.py: 5,628 LOC
  _check_p4b3_binding_v1: 173 LOC
```

## Commands not run

- Full release gate.
- Rust byte-level route refinement.
- Tau, Lean, ESSO, RISC0, and proof-guest lanes.
- Production datastore concurrency, crash-recovery, and external-outbox
  delivery lanes.
- The final aggregate critical coverage command after the inherited
  acceptance-TCB floor stopped the script.

## Residual risk

1. The mixed mounted strong validator and legacy route module remain reachable.
2. Final mount has 64 explicit structural violations.
3. Python/Rust/verifier exact-byte parity remains missing.
4. The production compare-and-swap and transactional outbox still require a
   real datastore adapter and fault evidence.
5. The checker is large. Its P4B3 functions have strong mutation evidence, and
   its size remains a reviewability cost for later decomposition.
6. The exact route module is 648 lines. Splitting it before the mounted
   specialization could improve reviewability, provided the split preserves
   controlled construction and rejection order.

## Next safest step

Return this unmounted checkpoint for review. The next M5 work is exact
strong-validator specialization and the single mounted P4 switch. P5 must then
make the final-mount profile pass. M6 removes the disconnected legacy authority
representations in that same reviewed mount unit.
