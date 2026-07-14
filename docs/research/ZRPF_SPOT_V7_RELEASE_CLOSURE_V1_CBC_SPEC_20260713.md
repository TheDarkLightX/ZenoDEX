# ZRPF Spot V7 Release Closure V1 CBC Specification

Date: 2026-07-13

Status: authority-neutral planner and checker implemented; post-G execution pending

Authority: none

## Purpose

This lane prepares the first reproducible-release gate after the governed
identity chain exists:

```text
C0 -> C1 -> C2 -> G
                  |
                  +-> committed V7 source closure
                  +-> Cargo path-dependency and lockfile closure
                  +-> toolchain, container, registry, and runtime identities
                  +-> canonical authority-neutral plan and check evidence
```

The planner executes the existing post-pin governance checker and then
independently reads the raw Git commit parents. A caller-provided success flag
cannot replace either check. The checkout must be clean, canonical, and exactly
at `G`. Git replace refs and grafts reject.

## Source inventory contract

The root is `zk/spot_settlement_v7_risc0/Cargo.toml`. The planner parses its
explicit workspace members and recursively follows local `path` dependencies
from normal, development, build, target-specific, and inherited workspace
dependency tables. It also follows local paths in every reached workspace
root's `[patch.<source>]` and `[replace]` tables. Patch source names are data,
so registry aliases and arbitrary source URLs receive the same traversal.

For every reached package it records:

- package name and manifest path;
- owning Cargo workspace root;
- every local dependency edge and dependency class;
- the workspace `Cargo.lock` bytes, mode, length, and SHA-256;
- every tracked regular file under every reached workspace;
- tracked `.cargo/config` or `.cargo/config.toml` files from every reached
  workspace through its repository ancestors;
- literal `include!`, `include_str!`, `include_bytes!`, and `#[path]` inputs
  that resolve outside those workspaces;
- the bounded literal compiler-input edge graph, including compiler-source
  inputs recursively reached from external Rust sources;
- source paths that consume generated `OUT_DIR` include files.

Literal compiler-source discovery runs to a bounded fixed point. Every source
reached by `include!` or `#[path]` is scanned for another literal input. Cycles,
source-count overflow, edge-count overflow, supplemental-input overflow, and
unrecognized include/path forms reject. `include_str!` and `include_bytes!`
targets are bound as bytes and are not reinterpreted as Rust source.

Cargo config selection also fails closed. If both `.cargo/config` and
`.cargo/config.toml` exist in one applicable ancestor, the closure rejects the
ambiguous precedence surface.

At the current pre-G source shape, the expected workspace family is:

```text
zk/spot_settlement_v7_risc0
zk/spot_settlement_v7_effect_binding_shared
zk/spot_state_root_v5_bridge_shared
zk/spot_state_root_v7_semantic_shared
zk/zrpf_risc0
zk/zrpf_protocol
zk/state_proof_risc0
```

The set is derived from committed manifests at `G`; it is not accepted from
this prose list. Missing manifests, globbed V7 members, path escapes, missing
workspace lockfiles, malformed or untracked local override targets, ambiguous
Cargo configs, non-regular tracked entries, absent literal includes,
compiler-source cycles, and resource-bound overflow reject.

The inventory is a conservative repository-source superset. Unknown include
forms reject instead of being omitted. It does not claim that arbitrary
build-script filesystem reads, procedural-macro behavior, host Cargo
configuration, or other runtime inputs have been statically discovered.

## Child and ancestry binding

The planner requires:

```text
literal_parent(C1) = C0
literal_parent(C2) = C1
literal_parent(G)  = C2
HEAD               = G
```

It reads the V7 child-policy source independently from C2 and G, requires exact
byte equality, parses the single governed `[u32; 8]` declaration, rejects the
all-zero value, and checks that its little-endian image ID equals the settlement
identity established by the post-pin governance record.

## Build-identity contract

The plan binds the existing fixed RISC0 toolchain hashes, build-container image
and parent digests, canonical in-container source path, nested Cargo wrapper,
and locked/offline/network-disabled build posture.

The runtime record has an exact schema and binds:

- Docker client executable SHA-256 and byte length;
- client, server, API, OCI-runtime, architecture, kernel, and cgroup identities;
- exact build image and parent digests;
- complete bounded Cargo registry root and inventory limits;
- clean-target, locked, offline, and pre-build network-disabled observations.

The checker binds this supplied runtime record by canonical SHA-256. It does
not live-attest the Docker daemon or host. A future governed runner must create
the record and the release evidence must bind that execution.

## Canonical commands

Run from a checkout containing the tools while `--repository` names a separate
clean worktree at exact `G`:

```bash
python3 tools/plan_zrpf_spot_v7_release_closure.py \
  --repository /absolute/path/to/exact-g-worktree \
  --runtime-identity /absolute/path/runtime-identity.json \
  > /private/output/spot-v7-release-plan.json
```

Anchor the printed file digest externally, then independently recompose it:

```bash
python3 tools/check_zrpf_spot_v7_release_closure.py \
  --repository /absolute/path/to/exact-g-worktree \
  --plan /private/output/spot-v7-release-plan.json \
  --runtime-identity /absolute/path/runtime-identity.json \
  --expected-plan-sha256 <64-lowercase-hex> \
  > /private/output/spot-v7-release-closure-evidence.json
```

Focused tests:

```bash
python3 -m pytest -q tests/test_zrpf_spot_v7_release_closure.py
```

## Positive claim

A successful check establishes one exact relation among:

- the governed literal C0/C1/C2/G chain;
- the nonzero V7 child pin;
- the committed recursive Cargo path-dependency graph;
- local Cargo patch and replacement override targets;
- every reached workspace lockfile;
- applicable tracked Cargo configs;
- the tracked workspace-source superset and fixed-point literal external
  compiler inputs;
- the declared toolchain, build container, Cargo registry, and runtime record;
- one canonical plan digest and authority-neutral check result.

## Required non-claims

Both plan and evidence keep every authority field exactly false. In particular,
this lane does not establish:

- complete build-input closure or unobserved build-script inputs;
- live runtime attestation;
- source-to-binary provenance;
- cross-host reproducibility;
- a V7 ELF, image ID, proof, receipt, or mutation rejection;
- data availability or checkpoint finality;
- release, settlement, or production authority.

Those claims require two clean builds, fresh targets and outputs, different
outer host paths, equal guest ELF bytes and recomputed image IDs, source-built
verifier replay, exact seal-mutation rejection, and independent release
governance. This checker records those future obligations without promoting
them.
