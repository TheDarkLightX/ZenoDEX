# WholeEconomyDisasterCoverageV1 Contract (research-only)

Status: `RESEARCH_ONLY_DENOMINATOR_INCOMPLETE`. Claim ceiling:
`RESEARCH_ONLY_NO_AUTHORITY`. `whole_economy_claim_allowed` is constant
`false` in V1.

This note explains the executable schemas owned by the typed functional core
(`tools/runtime_disaster_discovery.py` facade over the cohesive modules
`runtime_disaster_discovery_{primitives,vocabulary,sources,registry,inventory,subject,evidence,packet}_v1.py`),
the effect ports (`tools/runtime_disaster_discovery_ports_v1.py`), the
fixed-registry shell (`tools/run_runtime_disaster_discovery.py`), the
separately invoked replay verifier (`tools/check_runtime_disaster_discovery_receipt.py`),
and the closed registry (`tools/runtime_disaster_discovery_registry_v1.json`).
The code decides; this document cannot override it.

## Claim scope

The gate closes exactly two things for one exact subject:

1. denominator integrity: the manifest-derived applicability grid is derived
   from pinned source bytes and counted exactly for one subject; hard
   V1 floors prevent admission below 103 capabilities, 4 routes, 4 exclusions,
   and 11,988 cells, without claiming cross-version monotonicity;
2. evidence-association integrity: every evidence row binds one registered
   obligation, one registered runner and oracle, exact source pins, an exact
   subject, and committed artifacts, and its status is recomputed rather than
   trusted.

It grants no economic safety, proof, release, mount, settlement, writer,
migration, finality, or production authority. Accounting locations and
control domains never imply legal custody, title, possession, or key control.

## Subject

`c52c71d01a3edf3e298a840d41345abdc2d6d26d` (tree
`7978c0df78428e806e5f19281df537fe1cfc7451`) is the implementation base under
diagnosis and remains historical baseline metadata. Each packet binds the
current commit and tree captured by the shell; the eventual commit that adds
this checker is the assurance subject when replayed from that commit.
The historical whole-program baseline
`0_OF_967_MANIFEST_DERIVED_MINIMUM_EVIDENCE_CELLS` stays immutable; this gate
adds a finer denominator and never rewrites it.

`ExactSubjectV1` binds commit, tree, profile/release root, M6 manifest root,
whole-program requirement root, ShapeForge input root, obligation/runner/oracle
registry roots, checker source root, toolchain manifest root, source-pins root,
and the registry SHA-256. Every source pin binds path, Git mode, blob OID,
SHA-256, and byte size. The shell captures commit and tree once, probes every
path with `git ls-tree -z <captured tree> -- <path>`, reads each path exactly
once through an openat-style no-follow walk with byte ceilings checked before
allocation, and rejects `HEAD_MOVED` if the commit or tree changes across the
read or execution boundary. Mutable-worktree execution is recorded as
`EXTERNAL_PREMISE_MUTABLE_WORKTREE` and caps every runtime result at
`EXTERNAL_PREMISE`.

## Denominator

```text
targets = 103 capabilities (lane-qualified) + 4 required routes + 4 exclusions
cells   = targets x 9 lifecycle phases x 12 invariant families = 11,988
```

The four floor numbers are hard-coded in the core and enforced again by the
verifier; a registry may raise the floor and can never lower it. Every cell is
classified `REQUIRED`, `BLOCKED_SEMANTICS`, `APPLICABILITY_UNKNOWN`, or
`NOT_APPLICABLE_PROVED`. A `NOT_APPLICABLE_PROVED` cell remains in the exact
classification vector and obligation inventory. Its classification requires a
certificate bound to the current commit and tree and to a committed artifact;
a stale certificate counts as `APPLICABILITY_UNKNOWN`. In V1
every cell is `APPLICABILITY_UNKNOWN`, so `denominator_state` is
`DENOMINATOR_INCOMPLETE` and `coverage_ratio` is `WITHHELD`. Only exact count
vectors are reported; percentages are rejected in packets.

Source-derived universes (dangerous surfaces, writer entrypoints and coverage
rows, Pokayoke scenarios, stateful-bridge expansion axes extracted by `ast`
without importing or executing the bridge, ShapeForge cross-slice invariants
and scenario transforms, and the eight aggregate families) are composition
inputs. They are counted, rooted, and omission-checked, and they stay
`composition_pending` until an explicit composition registry maps them.

## Obligation identity

```text
ObligationKeyV1 = (semantic_requirement_root, target_kind, target_id,
                   ordered_participants, lifecycle_phase, invariant_family,
                   attack_family, bad_predicate_id, bounds_profile_id,
                   closure_mode)
obligation_id   = "WEDC1-" + SHA-256(domain_sep("wedc1-obligation-key") || canonical_json(key))
```

A cell without a registered predicate yields one row with `UNSPECIFIED`
coordinates and status `UNSPECIFIED_SEMANTICS`. A registered predicate refines
a `REQUIRED` cell into its own row. IDs are recomputed, never trusted;
duplicates, aliases (case, Unicode, separator, whitespace variants), floats,
bool-as-int, duplicate JSON keys, NaN, and Infinity reject.

## Evidence lattice

```text
UNSPECIFIED_SEMANTICS < UNKNOWN_REACHABILITY < SEARCH_PENDING < EXTERNAL_PREMISE
  < STALE_EVIDENCE < INCONCLUSIVE < NOT_WITNESSED_IN_TESTS
  < {MODEL_PROVED_UNREACHABLE, UNREACHABLE_BY_CONSTRUCTION,
     RUNTIME_REFINEMENT_CLOSED, DISABLED_PROVED_NO_WRITER}
WITNESSED_REACHABLE dominates every other status.
```

Exit zero or passing tests yield at most `NOT_WITNESSED_IN_TESTS`; stdout is
hashed, never read. Formal success yields `MODEL_PROVED_UNREACHABLE` only for a
registered formal obligation with exact theorem id, oracle, toolchain root, and
committed artifact. `RUNTIME_REFINEMENT_CLOSED` additionally requires a
refinement certificate. `DISABLED_PROVED_NO_WRITER` applies to explicit
exclusions only. Any bound bad-trace witness yields `WITNESSED_REACHABLE`.

Flags are `integrity_ok`, `execution_complete`, `bounded_discovery_complete`,
`formal_closure_complete`, and `whole_economy_claim_allowed` (always false).

## Receipts

A packet is `{schema, canonical_core, receipt_root, telemetry}`.
`receipt_root = 0x || SHA-256(domain_sep("wedc1-receipt-root") || canonical_json(canonical_core))`.
Timestamps, duration, and previews live in `telemetry`, outside the root.
Each result binds obligation id and key, predicate and schema roots, bounds
profile and cells, runner and oracle ids, registered argv hash, source-pins
root, subject root, execution premise, hashed observation, oracle verdict and
report hash, witness or replay hash, no-effect observations (`UNOBSERVED` when
the shell did not observe them), required and killed mutant ids, formal
certificates, `vm_gate_effect = CONTRIBUTES_TO`, computed status, and claim
ceiling. Reordered, duplicate, missing, unexpected, stale, or caller-promoted
rows reject with an exact code. Replay uses the same deterministic core from an
independent shell invocation, so it is recomputation and not an independent
implementation. The replay shell re-executes each referenced registered runner
from its own captured bytes and exact-compares the full observation before it
recomputes verdict or status. Legacy stateful-bridge receipts reject with
`LEGACY_BRIDGE_RECEIPT_REJECTED`. A runner entry that carries a command string,
`python -c`, `-m`, an unregistered module path, or an unknown field rejects
before any executor call. A registered module must also be a source-pinned
`CHECKER_SOURCE` whose bytes match the captured HEAD tree. The executor copies
the complete captured source set and registry into a private read-only tree,
executes the runner path from that tree, maps the logical `python3` token to the
running interpreter, adds `-s -P`, sets `PYTHONPATH` to exactly that private
tree, supplies a minimal environment, starts a new process group, streams and
measures raw output under a 1 MiB combined ceiling, replaces only the
executor-created random workspace prefix with a distinct typed frame before
hashing, and terminates the group on timeout, excess, or post-spawn setup
failure. Literal bytes and workspace frames have injective pre-hash encodings.
Timeout and output excess use fixed, stream-separated, domain-separated hashes
of the typed incomplete outcome instead of scheduler-dependent partial bytes;
they remain inconclusive.

## Commands

```bash
python3 tools/run_runtime_disaster_discovery.py --out /path/to/packet.json
python3 tools/check_runtime_disaster_discovery_receipt.py --receipt /path/to/packet.json
python3 -m pytest -q tests/test_runtime_disaster_discovery.py
```

Source-pin regeneration is manual and uses exactly one recorded command:

```bash
python3 tools/run_runtime_disaster_discovery.py --render-source-pins
```

Replace `source_pins` in `tools/runtime_disaster_discovery_registry_v1.json`
with that output verbatim (sorted by path). Every checker module, the two
shells, and the ports module are pinned as `CHECKER_SOURCE`, so any code change
drifts the pins and both shells reject until the pins are regenerated.

## Nonclaims and residual risks

- No cell is `REQUIRED` in V1; no predicate, runner, oracle, proof, or
  closure is fabricated, so no real runner executes and no obligation moves
  above `UNSPECIFIED_SEMANTICS`.
- The enumerations of nine phases and twelve families are closed vocabulary
  for the grid, not applicability claims.
- Git, the Python interpreter, and the operating system are trusted external
  premises; the toolchain root pins files, not executed binaries.
- A clean-worktree premise still trusts ignored files, the operating system,
  the exact interpreter binary, and system-level Python installation state.
  Runner execution drops inherited Python paths, pytest options and plugins,
  user HOME, and caller PATH. V1 caps runtime evidence at `EXTERNAL_PREMISE`
  whenever the worktree is dirty, the registry is not the captured HEAD blob,
  or any pinned source is not HEAD-bound.
- Process cleanup covers the created POSIX process group. A descendant that
  deliberately creates a new session or group can escape this containment;
  sandbox or container isolation is an external deployment requirement.
- Next frontier: an applicability registry with source-cited `REQUIRED`
  decisions, then bounds profiles, predicates, and registered runners for one
  lane while preserving the exact V1 floor and subject-bound count vector.
