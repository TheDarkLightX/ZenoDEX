# ZKPF Reproof Planner V1

Date: 2026-07-14

Status: deterministic planning and delegation tool; no proof or release authority

## Purpose

A change near the bottom of the ZRPF proof chain can invalidate several program
identities, receipts, verifier binaries, replay records, runtime bindings, and
release artifacts. Manually reconstructing that dependency closure is slow and
error-prone, especially when work is delegated across multiple agents.

`tools/plan_zkpf_reproof.py` converts either an explicit changed-path set or an
exact Git base/head range into a canonical plan over the governed graph in
`config/proof_profiles/zkpf_reproof_graph_v1.json`.

The planner performs four operations:

1. identify stages whose declared source globs directly match a changed path;
2. propagate invalidation through the complete dependency graph;
3. divide the resulting DAG into deterministic execution waves;
4. emit content-addressed task packets with commands, success predicates,
   resource requirements, agent and review classes, dependencies, and outputs.

A stage marked `planned` remains in the graph, but its task is explicitly marked
`blocked_by_missing_implementation=true`. The planner never converts a design
target into a claim that code or evidence exists.

## Architecture lessons incorporated

The graph makes proof stages explicit rather than treating recursion as one
opaque operation. This follows the same broad discipline visible in mature
proof systems:

- RISC Zero separates segment, composite, succinct, and wrapped receipts and
  verifies intermediate constructions before returning them.
- SP1 represents normalization, composition, deferred verification, and shrink
  stages as distinct recursion shapes and schedules proving work through
  bounded worker pipelines.
- Stwo keeps the verifier small and separates generic proof-system code from
  application-specific AIR and prover code.
- Plonky3 exposes interchangeable primitives and treats benchmark methodology
  and verifier failure containment as integration responsibilities.

ZRPF does not copy those implementations. V1 adopts the reusable engineering
principles: explicit stages, typed dependencies, minimal authority-bearing
boundaries, deterministic scheduling, and reviewable single-purpose tasks.

## Task classes

Each stage declares:

- `resource_class`: `light`, `heavy`, or `privileged`;
- `minimum_agent_class`: `routine`, `strong`, `frontier`, or
  `privileged_operator`;
- `review_class`: `ordinary`, `security`, `math`, `release`, or `operations`;
- `implementation_status`: `implemented` or `planned`.

These fields are scheduling guidance, not proof that an assigned agent is
competent. Math, authority-boundary, release, and privileged-runtime changes
still require the relevant independent review.

## Examples

Plan from explicit paths:

```bash
python3 tools/plan_zkpf_reproof.py \
  --changed-path zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs \
  --pretty
```

Plan an exact branch range:

```bash
python3 tools/plan_zkpf_reproof.py \
  --repository . \
  --base <base-commit> \
  --head <head-commit> \
  --pretty
```

Emit one immutable task file per invalidated stage:

```bash
python3 tools/plan_zkpf_reproof.py \
  --changed-paths-file /private/changed-paths.txt \
  --tasks-directory /private/zkpf-tasks \
  > /private/zkpf-reproof-plan.json
```

The task directory must begin absent. The planner writes through a private
staging directory and publishes it with one rename. Re-running into an existing
directory rejects instead of overwriting prior task identities.

## Determinism and validation

The graph is canonical ASCII JSON with duplicate-key, float, non-finite number,
depth, size, path, field-set, enum, uniqueness, ordering, unknown-dependency,
and cycle rejection.

Changed paths are normalized, sorted, and deduplicated. The changed-path root is
SHA-256 over the ordered `path + newline` sequence. Each task ID additionally
commits to the graph digest, stage ID, and dependency task IDs. Equivalent path
sets therefore produce byte-identical plans regardless of caller ordering.

## Updating the graph

A new stage should be added only when it has a distinct identity, evidence, or
operational boundary. Do not use the graph to hide several unrelated changes
inside one task.

For each stage:

1. use conservative source globs;
2. declare every immediate dependency;
3. provide commands that exercise the narrow boundary;
4. state success predicates in observable terms;
5. mark future code as `planned`;
6. keep outputs semantic and stable rather than naming temporary files;
7. assign the strongest required agent and review class, not the cheapest one.

The graph is a planning contract. Source-closure and release checkers remain the
final authority for the exact bytes used in a build or proof.

## Explicit nonclaims

A successful plan does not establish:

- source-to-binary provenance;
- program or image identity;
- proof generation or receipt validity;
- data availability or external finality;
- successful Firecracker execution;
- release, settlement, or production authority;
- correctness of the declared dependency graph beyond its tested and reviewed
  scope.

Every emitted plan and task packet fixes all authority fields to false.
