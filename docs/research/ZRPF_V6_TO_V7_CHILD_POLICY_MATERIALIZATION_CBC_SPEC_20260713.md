# ZRPF V6-to-V7 child-policy materialization CBC specification

Date: 2026-07-13

Status: implemented authority-neutral candidate transition

## Scope

This lane converts one independently recomposed Spot V6 identity-rebuild
candidate into one exact indexed edit of:

```text
zk/spot_settlement_v7_risc0/child_policy/src/lib.rs
```

It replaces only
`FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1`, starting from the exact
`[0; 8]` placeholder, with the eight little-endian `u32` words that encode the
candidate report's single `v6_settlement` image ID.

The lane does not verify or generate a proof or receipt. It does not grant
release, settlement, or production authority.

## Inputs

The checker accepts:

```text
clean repository checkout at explicit C1
canonical V6 rebuild plan
canonical V6 rebuild observations
canonical V6 candidate report
```

All three JSON objects pass the existing bounded canonical JSON reader. The
report must equal a fresh call to `check_observations(plan, observations)`.

The plan names C0. The supplied C1 must satisfy:

```text
parents(C1) = [C0]
HEAD = C1
worktree and index are clean
diff_paths(C0, C1) = the eight V6 materialization paths
```

For every one of those eight paths, the checker independently reconstructs the
expected C1 bytes from the C0 Git blob plus the accepted observation repins or
candidate document. The C0 and C1 blobs must both be regular `100644` blobs,
and the committed C1 bytes must exactly equal the reconstruction.

This prevents an unrelated or coherently altered C1 commit from becoming the
source of the V7 child identity.

## Authority progression

```text
canonical plan, observations, report
    -> independent report recomposition
    -> exact C0 to C1 reconstruction
    -> exactly one V6 settlement program
    -> nonzero image words encode the reported image ID
    -> exact all-zero V7 placeholder
    -> deterministic one-file patch
    -> Git indexed check or apply
    -> authority-neutral external manifest
```

Neither JSON metadata nor a caller-provided Boolean can create a verified
program identity. The image ID comes from the accepted candidate report, whose
program row and little-endian word encoding were already checked by the V6
planner and are checked again at the selection boundary.

## Commands

Non-mutating check:

```bash
python3 tools/materialize_zrpf_v6_settlement_child_into_v7.py check \
  --c1-commit "$C1" \
  --plan "$PLAN" \
  --observations "$OBSERVATIONS" \
  --report "$REPORT"
```

Indexed candidate apply:

```bash
python3 tools/materialize_zrpf_v6_settlement_child_into_v7.py apply \
  --c1-commit "$C1" \
  --plan "$PLAN" \
  --observations "$OBSERVATIONS" \
  --report "$REPORT" \
  --manifest-out "$PRIVATE_EXTERNAL_DIRECTORY/v6-to-v7-manifest.json"
```

The manifest path must begin absent, be outside the repository, and have a
canonical parent directory private to the current UID.

## Apply and rollback contract

The apply mode:

1. opens the absent external output as a bounded directory capability;
2. reconstructs and checks the candidate transition;
3. validates the patch with `git apply --check --index`;
4. applies the patch with `git apply --index`;
5. requires the staged-path set to contain exactly the V7 child-policy file;
6. requires no unstaged or untracked path;
7. verifies exact index and worktree bytes and the resulting index tree;
8. writes and synchronizes the canonical external manifest.

Any failure after patch application and before the synchronized external
manifest invokes the shared exact reverse-patch rollback. The synchronized
manifest is the explicit candidate-transaction commit point. Descriptor close
is best-effort cleanup after that point; a close error does not turn a durable
manifest plus indexed candidate into a reported rejection. Mixed governed
state or unrelated checkout mutation before the commit point becomes a typed
partial-state error requiring operator inspection.

## Manifest binding

The manifest commits to:

- C0 and C1 commit IDs;
- canonical plan, observations, and candidate-report SHA-256 values;
- the final reconstructed V6 source root recorded by the report;
- the V6 settlement image ID and its exact eight words;
- the generated patch length and SHA-256;
- the path, Git mode, before and after lengths, and before and after SHA-256;
- the applied index tree, when apply mode succeeds;
- exact validated facts and explicit false authority fields.

Unknown authority is never represented as true. Every authority field in this
lane remains false.

### Implemented post-pin governance binding

The materializer still emits its canonical manifest outside the repository so
that a failed materialization cannot partially write governed evidence. The
separate post-pin checker now accepts one exact committed chain:

```text
C0 = rebuild-plan source commit
C1 = exact reconstructed V6 identity materialization
C2 = C1 plus only the exact V7 child-policy pin
G  = C2 plus only the four fixed canonical evidence objects
```

The four evidence objects are the plan, observations, candidate report, and
materialization manifest under the fixed
`evidence/zrpf_v6_to_v7_post_pin_v1/` directory. They must be new `100644`
blobs in G. G, C2, and C1 must each have exactly one literal parent, Git grafts
and replace refs reject, and the checkout must be clean at the exact G commit.

The checker independently recomposes the report and C0-to-C1 transition. It
then derives the expected nonzero settlement image words, renders the exact V7
source from C1, reconstructs the materializer patch and tree, and requires the
committed C2 source, C2 tree, and manifest to match exactly. Unknown manifest
fields, promoted authority fields, noncanonical JSON, an extra transition
path, or any manual post-pin source edit reject.

Run at the exact governance commit:

```bash
python3 tools/check_zrpf_v6_v7_post_pin_governance.py
```

Success establishes a committed, authority-neutral post-pin binding. It does
not convert the candidate into release evidence or program-binary provenance.

The materializer itself cannot start from a manually selected nonzero value:
it requires the exact zero placeholder and derives the only accepted nonzero
value from the independently recomposed report. After the indexed candidate is
created, ordinary same-UID code can still alter the staged source. Such an edit
does not inherit this manifest: the governance checker rejects its C2 bytes and
tree. Same-UID race resistance during checking remains explicitly unclaimed.

## Failure detector

The focused test suite covers:

- CLI invocation without `PYTHONPATH`;
- non-mutating checking;
- exact one-path indexed application;
- C1/HEAD mismatch rejection;
- noncanonical repository-root rejection;
- direct-child C1 with an extra committed path rejection;
- local Git graft ancestry rejection;
- exact eight-path C1 with one wrong committed byte rejection;
- duplicate settlement-row rejection;
- all-zero settlement-image rejection, including the end-to-end C1 path;
- nonzero-placeholder rejection;
- rollback after external-manifest failure;
- stable success after a post-commit descriptor-close error.

The post-pin governance suite additionally covers:

- an exact C0-to-C1-to-C2-to-G accepted chain;
- committed manual post-pin source mutation rejection;
- extra C2 and governance path rejection;
- manifest authority-promotion rejection;
- image-word/report mismatch and all-zero identity rejection;
- noncanonical committed-manifest rejection;
- Git-graft rejection;
- dirty governance-checkout rejection.

Run:

```bash
python3 -m pytest -q \
  tests/test_materialize_zrpf_v6_settlement_child_into_v7.py \
  tests/test_check_zrpf_v6_v7_post_pin_governance.py
```

## Explicit non-claims

This materializer does not establish:

- a complete build-input closure;
- cross-host reproducibility;
- source-to-program-binary provenance authority;
- proof generation or verification;
- receipt authority;
- release authority;
- settlement authority;
- production authority.

The resulting pin is one required source transition. Fresh V7 source build,
image derivation, receipt generation, negative controls, replay, release, data
availability, finality, and atomic settlement gates remain separate.

The real final-build source closure, fresh V7 image and receipt evidence,
release-policy promotion, independently replayed negative controls, and any
production authority remain separate pending obligations. The implemented
governance checker deliberately emits false for every authority field.
