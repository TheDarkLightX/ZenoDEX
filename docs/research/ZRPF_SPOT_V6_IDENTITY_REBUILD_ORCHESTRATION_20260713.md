# ZRPF Spot V6 Identity Rebuild Orchestration

Date: 2026-07-13

Status: deterministic plan, fail-closed executor, and candidate-observation
checker implemented

Authority: none

## Purpose

The source-opened ordinary Spot chain contains compiler-visible child program
identities. Changes to the source Spot guest, including the PR #426 snapshot
pool-identity and domain-bound work, invalidate every downstream identity.

The deterministic rebuild order is:

```text
source Spot guest and CLI
  -> source policy
  -> V2 adapter
  -> leaf expected-adapter pin
  -> V6 leaf
  -> L1 child pin
  -> V6 L1
  -> L2 child pin
  -> V6 L2
  -> settlement child pin
  -> V6 settlement
  -> settlement self-image host-only pin
  -> host verifier
```

`tools/plan_zrpf_source_opened_spot_v6_identity_rebuild.py` emits this plan and
checks a completed observation bundle.

`tools/execute_zrpf_source_opened_spot_v6_identity_rebuild.py` captures a
private, bounded source snapshot from the plan's exact Git commit and executes
the plan through a pinned no-network Docker runner. It performs the declared
repins inside that private snapshot, generates only the versioned V2 governance
candidates, records exact binary observations, enforces the settlement
two-pass control, and runs the final clean rebuild comparison. It never edits
the checkout. It performs no proof generation, receipt verification, evidence
promotion, or authority update.

The executor maintains an exact expected source-state machine after Git
materialization. Before and after every build, declared repin, and candidate
document write, it enumerates the complete live snapshot tree and requires the
exact governed directory set, file set, file modes, bytes, and source root.
Unknown files or directories, symlinks, special files, unsafe hardlinks, and
persistent changes outside the one declared transition reject the run.

## Build contract

Every planned pass uses:

- canonical in-sandbox source path `/src/zenodex`;
- the pinned Rust/RISC0 1.94.1 Cargo and rustc executables;
- the same pinned Cargo executable for outer and nested Cargo;
- RISC0 3.0.5 `r0vm` and `cargo-risczero` identities;
- `--locked`, `--offline`, and a network-disabled runtime;
- two build jobs, two CPUs, and a 6 GiB memory ceiling;
- a fresh 3 GiB executable in-container target tmpfs and 160 MiB non-executable
  output tmpfs; Docker defaults tmpfs mounts to `noexec`, so the target contract
  requires an explicit `exec` override while every auxiliary/output tmpfs keeps
  an explicit `noexec` policy;
- canonical bounded-base64 transport into fresh host output files;
- exact R0BF program byte length, SHA-256, image ID, and little-endian image-ID
  words;
- an absent run root beneath a current-user-owned, non-sticky parent with no
  group or world write permission; root and report creation use stable
  directory descriptors and relative creation.

The runner requires the deterministic container name to begin absent and passes
Docker a fresh private `--cidfile` beneath the per-pass target directory. Cleanup
removes only the exact 64-hex container ID read from that file, then verifies
both the ID and governed name are absent. If Docker creates a named container
without producing the private ID file, the runner reports an ownership failure
and leaves that container untouched rather than deleting by name.

The plan pins the existing no-network build image and its Ubuntu parent. The
executor directly applies these controls to its local candidate run. The
result still lacks a complete build-input closure, independent execution
attestation, and cross-host rebuild. The observation report therefore says
`locked_offline_builds_reported` and leaves complete build provenance false.

Before the first build, the executor requires one exact
`zenodex/zrpf_v6_identity_runner_security_posture/v1` object. The observation and
candidate report bind the four pinned tool byte lengths and SHA-256 values, a
bounded deterministic Cargo-registry root, exact CPU/job/tmpfs policy, and the
governed nested-Cargo wrapper digest. The checker rejects unknown fields,
changed tool digests, resource-policy drift, and any attempt to set
`same_uid_resistance` or `complete_build_input_closure_verified` to true.

## Acyclic repin rules

Each stage may update only the next edge:

| Built stage | Compiler-visible successor pin |
| --- | --- |
| source Spot | source image ID, R0BF SHA-256, and source-tree root in the adapter source policy |
| V2 adapter | adapter image ID in V6 leaf policy |
| V6 leaf | leaf image ID in L1 policy |
| V6 L1 | L1 image ID in L2 policy |
| V6 L2 | L2 image ID in settlement guest policy |
| V6 settlement | settlement image ID in the host-only verifier policy |

The settlement self-image policy is outside the settlement guest dependency
graph. The required two-pass control is:

1. build settlement before updating the host-only settlement identity;
2. update only the host-only identity;
3. rebuild settlement from a fresh target;
4. require exact equality of byte length, SHA-256, image ID, and image words.

A final clean rebuild under the fully repinned source must reproduce all six
primary program identities. Any difference rejects the candidate because it
indicates an undeclared downstream-to-upstream dependency, mutable build input,
or non-reproducible same-environment build.

## Source inventory coverage

The plan hashes every tracked regular file under:

```text
zk/state_proof_risc0
zk/zrpf_protocol
zk/zrpf_risc0
```

This is intentionally broader than the derived guest dependency graph. It
prevents a newly added compiler-visible tracked file from disappearing from the
candidate snapshot. The audit also requires the tracked
`parallel_shard_epoch_v1` Rust files to be present. The inventory is a
repository-local source superset. Compiler, linker, registry content, runtime
image, kernel, and other external inputs remain outside a complete build-input
closure.

The broad inventory root commits each path, Git file mode, byte length, and
SHA-256 and remains a repository-level build observation. A separate acyclic
source-guest inventory applies the same construction only to
`zk/state_proof_risc0`. The source-stage observation and future V2 source
policy must use that source-guest inventory root. This prevents the source
guest from committing a digest that includes the downstream policy which
stores the digest. An independently reported source-tree digest cannot satisfy
the checker.

The execution-time live inventory is stricter than the frozen entry-list hash.
It rejects an added compiler-visible file such as `.cargo/config.toml`, even
when that file was absent from the Git entry list used to compute the planned
root. Every allowed regular file must be owned by the executor UID and have a
link count of one. Persistent replacement with the same bytes through a
hardlink therefore also rejects.

The prior exact V6 retained inventory predates the parallel-shard files. It must
be regenerated for a future candidate and cannot support the new source tree.

## Historical anchor protection

These artifacts remain historical and are never repin targets:

```text
config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json
config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json
```

The current source requires new versioned successors:

```text
config/proof_profiles/zrpf_current_source_anchor_v2.json
config/proof_profiles/zrpf_v2_leaf_adapter_source_policy_v2.json
```

The checked-in pending anchor retains the bootstrap V1 plan-schema marker only
while every observed identity remains absent. A materialized
`observed_unpromoted_candidate` must bind the planner's current V2 schema. The
current-source adapter checker rejects a V1-labeled observed candidate and a
V2-labeled pending sentinel, preventing the bootstrap compatibility marker from
being reused as observed evidence.

The checker rejects any static topology that places a protected historical
artifact in the repin set.

## Commands

Choose an absent external run root and absent plan path. The first command only
emits a plan. Create a dedicated private parent first. Shared scratch parents,
including sticky directories and group-writable project scratch directories,
are intentionally rejected.

```bash
install -d -m 0700 /absolute/external/private-zrpf-runs

python3 tools/plan_zrpf_source_opened_spot_v6_identity_rebuild.py plan \
  --source-commit "$(git rev-parse HEAD)" \
  --run-root /absolute/external/private-zrpf-runs/zrpf-v6-identity-run \
  --output /absolute/external/absent/rebuild-plan.json
```

Run the exact plan with the locally pinned RISC0 toolchain, Cargo registry, and
Docker image. Both the run root and every executor output must begin absent.

```bash
python3 tools/execute_zrpf_source_opened_spot_v6_identity_rebuild.py \
  --plan /absolute/external/rebuild-plan.json \
  --risc0-home /home/trevormoc/.risc0 \
  --cargo-registry-dir /home/trevormoc/.cargo/registry
```

On success, the executor writes these exact canonical documents beneath the
governed run root:

```text
rebuild-observations.json
rebuild-candidate-report.json
```

Their current schemas are the versioned V2 observation and candidate-report
schemas. The embedded runner posture remains V1 and authority-neutral.

The executor invokes the checker before committing either document. An
independent consumer can repeat the check:

```bash
python3 tools/plan_zrpf_source_opened_spot_v6_identity_rebuild.py check \
  --plan /absolute/external/rebuild-plan.json \
  --observations /absolute/external/absent/zrpf-v6-identity-run/rebuild-observations.json \
  --output /absolute/external/absent/independent-rebuild-candidate-report.json
```

Both input JSON documents must be exact canonical JSON with unique keys,
bounded depth, bounded node count, no floats, and no unknown fields.

## Host mutation boundary

The exact state checks detect persistent changes and narrow same-process races
through stable descriptor reads and before/after identity checks. They do not
make the snapshot immutable. Hostile code with the executor's UID can still
mutate and restore a source, directory, toolchain, registry, target, or output
entirely between observations. The source snapshot is path-mounted into the
builder, so complete same-UID resistance remains false until a stronger
root-owned immutable staging or isolated execution boundary is demonstrated.
The private container-ID file prevents accidental name-only cleanup from
claiming ownership. It does not protect against hostile same-UID code that can
rewrite the private run directory while the runner is active.

## Candidate report boundary

A successful check establishes only that the supplied observations are
internally consistent with the deterministic acyclic plan. Every authority
flag remains false:

```text
complete_build_input_closure_verified
cross_host_reproducible_build
evidence_promoted
proofs_generated
receipts_verified
release_authority
settlement_authority
source_to_program_binary_provenance_verified
production_authority
```

The candidate report commits the complete canonical observation document by
SHA-256 so that omitted stage roots or execution facts cannot be substituted
after checking.

Promotion still requires fresh source and adapter proofs, V6 leaf/L1/L2 and
settlement proofs, external verifier replay, negative mutations, a governed
release manifest, CBC review, and the separate durable-admission gates.
