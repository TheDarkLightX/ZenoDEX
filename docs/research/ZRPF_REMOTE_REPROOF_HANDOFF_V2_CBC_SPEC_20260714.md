# ZRPF remote reproof handoff V2 CBC specification

Status: implemented planner, per-stage exact-input packet builder, return
checker, and bounded authority-neutral worker for thirteen packet-expressible
stages. The identity rebuild, worker prover-build, source/V7 execution-profile,
and exact mutation adapters are implemented. The bundle-aware release checker
command template remains planned.

## Compute-profile protocol ratchet

The implementation filenames retain `v2` so the focused worker stack remains
one reviewable incremental change. Governed compute selection originally
ratcheted the wire family to V3. Adding the source execution-profile stage and
making it an exact predecessor of source proving changes the task topology and
acceptance-relevant artifacts. The handoff, task, execution-packet,
task-capture, and return schemas and identity domains are therefore V4. The
worker-capture schema remains V3 because its own field set and identity
construction are unchanged; it content-binds the V4 execution packet.

All earlier V2 and V3 handoffs, packets, task captures, and return bundles are
revoked. They must be regenerated. V4 checkers reject those objects by schema
before treating any content as current evidence.

The closed task/artifact catalog lives in
`tools/zrpf_remote_reproof_handoff_v2_catalog.py`. Parsing, content addressing,
Git ancestry, capture, and return validation live in
`tools/plan_zrpf_remote_reproof_handoff_v2.py`. This keeps declarative workflow
changes separate from the authority-bound checker.
Worker contract validation lives in
`tools/zrpf_remote_reproof_worker_v2_contract.py`; one-stage execution lives in
`tools/run_zrpf_remote_reproof_worker_v2.py`.

Scope: one fresh current-source, singleton Spot proof chain from the source
receipt through the V2 adapter, V6 leaf/L1/L2/settlement receipts, and the V7
settlement receipt. This object coordinates expensive work on another machine.
It does not generate or verify a proof by itself.

## Claim boundary

A successfully checked return establishes only these metadata facts:

1. The handoff contract is derived from one exact C0 commit, Git tree, tracked
   workspace inventory, source-guest inventory, toolchain identity, and build
   image identity.
2. Every task and artifact contract has a domain-separated content identity.
3. The returned artifact inventory is complete, unique, bounded, regular-file
   only, and byte-bound by SHA-256 and size.
4. Each execution packet commits to the declared exact G commit/tree, proof
   profile, exact current input artifact IDs, and task ID before the task's
   output is captured.
5. Each task-capture record commits to the execution packet, identity binding,
   output artifact IDs, and task ID without claiming that the command ran.
6. C1, C2, and G each have exactly one literal parent and form the exact chain
   `C0 -> C1 -> C2 -> G`. Replacement refs and grafts reject.
   G must equal the exact worker commit and tree fixed by the handoff.
7. The source-derived identity plan, observations, and candidate report pass
   the existing governed recomposition checker. Source-through-V6 program and
   source-CLI artifact bytes match that report.
8. The mutation stage is bound to the exact five programs, five positive
   receipts, two retained mutations, and three generated mutations in its
   packet. Its fixed Rust verifier authenticates every positive receipt under
   the expected image and Succinct profile before requiring exactly seal word
   1, bit 0 to differ and requiring each mutation to fail cryptographic receipt
   verification at the governed boundary.
9. The worker-build report binds one canonically validated, authority-false G
   governance object, all nine built worker artifacts, and an externally fixed
   candidate V7 image ID. The return checker additionally binds C0/C1/C2/G and
   the V6 settlement image to the validated handoff evidence. Complete
   build-input closure and same-UID resistance remain false.
10. Every authority field remains false.

The checker does not establish:

```text
proof validity
historical execution provenance
operator authorization or task-packet freshness
pre-packet substitution of external input bytes
same-handoff same-byte stale replay detection
coherent checker, catalog, and expected-policy redefinition
program image-ID recomputation
complete build-input closure
cross-host reproducible builds
data availability or retrievability
finality
ledger admission
release authority
settlement authority
production authority
```

Program image IDs in a return bundle are candidate exact identities. The
source-through-V6 IDs must equal the governed identity-rebuild report. The V7
ID must equal the source-bound worker-build report and the external candidate
expectation. Its construction path computes that candidate through the
packet/runtime-equal pinned r0vm; the reusable return checker does not repeat
that computation. The return remains authority-neutral. A separately governed
release-closure check must recompute every final identity before promotion.
Content IDs detect drift relative to an independently fixed expected identity.
This authority-neutral bundle does not authenticate a coherently replaced
artifact, report, and external image expectation. Checker, catalog, and policy
changes require independent review plus a separately governed release anchor.

## Authority progression

```text
exact C0 source identity
  -> content-addressed task contracts
  -> bounded external artifacts
  -> literal C0/C1/C2/G ancestry
  -> content-addressed exact-input execution packets
  -> content-addressed task captures
  -> authority-neutral return bundle
  -> separate proof and release verification
  -> no ledger authority
```

The task packet, worker, artifact paths, reports, commit messages, and supplied
program image IDs can propose facts. None can grant proof or settlement
authority.

The default single-artifact ceiling is 64 MiB. The separately declared
identity and proving `r0vm` executables each allow at most 512 MiB because the
official RISC Zero 3.0.5 release binary is 108,998,816 bytes and a CUDA build
may be larger. Collection and return checking retain a 1 GiB aggregate ceiling.
The real final bundle must be measured before dispatch; fitting the individual
contracts does not imply that the aggregate cap is satisfied.

## Bounded task DAG

The task order is fixed:

```text
identity_rebuild
  -> ancestry_materialization
  -> worker_prover_build
  -> source_execution_profile
  -> source_spot_proof
  -> v2_adapter_receipt
  -> v6_leaf_receipt
  -> v6_l1_receipt
  -> v6_l2_receipt
  -> v6_settlement_receipt
  -> v7_execution_profile
  -> v7_receipt
  -> mutation_verification
  -> release_checks
```

This ordering closes the previous Mac handoff dependency gap. A source proof
and V2 adapter receipt are explicit prerequisites. Source proving additionally
requires an execution-only profile over the exact source program, exact
materialized guest input, exact expected journal, and exact packet-pinned
`r0vm`. V7 proving has the corresponding exact profile predecessor. Each
profile records ordered segment/cycle facts and generates no receipt. The V6
leaf cannot become ready when the adapter receipt is absent. After an execution
packet has been created, its downstream task capture binds the exact packet
input artifact IDs.

The source-proof task also binds exact CUDA-build and H100-preflight artifacts.
Its first command evaluates one authority-false paid-calibration attempt over a
worker-private copy of the source-proof packet. The integer budget document is
provided after packet construction because it commits to the packet ID. The
qualification output commits to those exact budget bytes. No continuation or
additional-spend task exists.
The packet is an unkeyed deterministic commitment. It does not authenticate an
operator, prove freshness, detect external-input substitution that happened
before packet creation, or distinguish a same-handoff replay of the same bytes.
A future trusted-controller signature or external anchor and initial expected
digests are required for those claims.

`mutation_verification` is implemented by the fixed
`verify-spot-v7-remote-mutations` Rust executable from the dedicated
`mutation_verifier` workspace package. Mutation-only V6 method and aggregation
dependencies do not enter the production V7 verifier or Firecracker dependency
closure. The packet binds the five program ELFs, five positive receipts, exact
leaf and settlement inputs, and two retained prover mutations. After verifying
the L2 receipt, the verifier decodes the exact settlement envelope and requires
its proposal bytes to equal that verified L2 journal before settlement receipt
verification. The verifier derives the V6 leaf, L1, and L2
mutations only after all positive receipts verify, rejects any representation
change outside seal word 1 bit 0, requires all five mutations to fail at the
cryptographic receipt boundary, persists the three generated mutations, and
emits one canonical fixed-schema report. The report binds program, image,
receipt, journal, mutation, profile, and report digests. It carries no proof,
release, settlement, or production authority.

The schema, status, common profile, positive and negative counts, all-false
authority map, settlement-to-L2 link fact, and non-claim list are construction
invariants. They cannot be provided by a packet or receipt. Their exact bytes
still enter the report ID.
The report finalizer rejects a wrong stage position, profile, digest shape,
mutation relation, reject boundary, or reject code. An active-witness matrix
changes every other input-derived report scalar at each of the five positions
and requires the report ID to change. The same matrix proves the fixed
construction invariants are committed while excluding only the
self-referential report-ID field.

`release_checks` remains `template_planned`: the existing release checker
operates on repository paths and does not yet consume this returned
proof/mutation bundle. Manually supplied bytes can still be captured as
authority-neutral metadata; capture does not prove they were produced by the
declared task.

The catalog marks these packet-expressible stages as implemented:

```text
identity_rebuild
ancestry_materialization
worker_prover_build
source_execution_profile
source_spot_proof
v2_adapter_receipt
v6_leaf_receipt
v6_l1_receipt
v6_l2_receipt
v6_settlement_receipt
v7_execution_profile
v7_receipt
mutation_verification
```

The bounded worker resolves typed declared-artifact placeholders, the exact C0
commit, and a closed runtime-binding set. It executes argv directly without a
shell, stages exact outputs into a fresh private root, and emits an all-false
authority capture. It does not provide a mount, network, container, VM, or
hardware sandbox. `identity_rebuild` executes the existing pinned no-network
Docker identity builder, verifies the packet r0vm equals the governed runtime
r0vm, validates the candidate report against all produced bytes, exports the
ten declared artifacts, and removes the completed staging root. Runtime path
values enter the resolved-argv digest; the identity report separately binds
the compiler tools and Cargo-registry inventory. Complete build-input closure
and same-UID resistance remain false. The worker host must create the canonical
private parent `/external/zrpf-remote-reproof-handoff-v2/identity` before the
stage begins; the fixed child `run` must begin absent. The adapter rejects a
missing, noncanonical, repository-contained, or already-existing run root.
`worker_prover_build` uses the same pinned no-network runner to create one
deterministic V6 host bundle and one deterministic V7 bundle. Its adapter
requires an exact ordered archive-member inventory, extracts nine outputs,
computes the candidate V7 image ID through the packet-pinned r0vm, and emits a
canonical build report that binds canonically validated G governance and all
extracted bytes. The return checker binds that governance to the handoff
ancestry and validated V6 identity. Ephemeral archive hashes are excluded from
the reusable report. The release stage remains planned.

## Artifact contract

Every artifact contract fixes:

```text
role
relative path
kind
producer stage
maximum bytes
contract ID
```

The contract ID is:

```text
SHA256(
  "zenodex/zrpf_remote_reproof_artifact_contract_id/v2\0"
  || canonical_json(contract_with_zero_id)
)
```

Every returned artifact record fixes:

```text
contract ID
role
relative path
SHA-256
size
producer stage
artifact ID
```

Artifact reads use a descriptor-relative, `O_NOFOLLOW` walk beneath the opened
artifact root. They reject missing or empty files, special files, hard links,
symlinks, path escape, mutation during read, excess per-file size, and excess
aggregate inventory. The return inventory must match the handoff inventory in
the same canonical order. Missing, duplicate, surplus, or substituted records
reject.

## Task contract

Every task fixes:

```text
stage and ordinal
dependency stages
source-binding ID
proof-profile ID
prover-compute-profile ID
input artifact-contract IDs
output artifact-contract IDs
ordered command invocations
stdin and stdout artifact roles
success predicates
resource class
command-template status
execution-adapter status
false authority map
non-claims
task ID
```

The handoff fixes either `risc0_ipc_cpu_v1` or
`risc0_ipc_cuda_single_visible_device_build_request_v1` for its RISC0 compute
stages. Every such stage also consumes the exact, separately content-addressed
`prover_r0vm` input. The default CPU handoff is a partial execution and testing
plan: `source_spot_proof` is explicitly marked
`blocked_cpu_source_proof_disqualified`, so it cannot complete the proof chain.
The CUDA plan marks that adapter implemented only after an explicit non-CPU
`prover_r0vm` identity is supplied. The identity-rebuild r0vm remains
separately pinned. This prevents an
operator environment from silently selecting an in-process prover, another
`r0vm`, Bonsai, or another visible GPU. Compute selection
changes the handoff and task IDs. It does not change proof semantics or grant
performance, proof, release, settlement, or production authority.

The CUDA selection records intent and exact environment only. It is not
accelerator evidence. A paid H100 run additionally requires a governed CUDA
`r0vm` build record and a bounded live GPU-use preflight. Until those exist,
CPU execution under the CUDA request remains possible and the performance
claim remains false.

The handoff also commits one exact `prover_r0vm` SHA-256 and byte length. The
CPU profile defaults to the reviewed official RISC Zero 3.0.5 CPU binary. The
CUDA profile requires both values explicitly and rejects that known CPU-binary
identity. Task preparation and worker validation rehash the actual input bytes
and require them to equal the handoff expectation. This closes accidental
binary substitution. A different digest does not prove that the binary was
built from the governed CUDA source or that it used a GPU, so both provenance
and accelerator-use claims remain false until their separate evidence gates
pass.

The command records are execution templates. `@name` values are typed
substitutions interpreted only by the bounded worker for a stage whose
execution adapter is explicitly implemented. They are never interpreted by a
shell. The worker constructs an argv vector directly and maps each artifact
role to its validated private input snapshot or declared output path. Template
availability alone does not make a task executable.

The per-stage execution packet adds facts that are unavailable when the initial
handoff is planned:

```text
handoff and task IDs
exact G commit and tree
proof-profile ID
ordered input artifact IDs
```

The task-capture identity later commits the execution-packet ID, the validated
identity-binding ID, and ordered output artifact IDs. It is named a capture
because these records do not prove historical command execution.
The capture also does not prove who created or preserved the packet, operator
intent, or packet freshness.

## Literal ancestry

The ancestry checker reads raw commit objects with:

```text
/usr/bin/git cat-file commit <commit>
```

It requires exactly one `parent` header for C1, C2, and G and exact equality to
the preceding governed commit. G must also equal the handoff's worker commit
and tree. It does not use reachability as a substitute for direct parentage.
Git replacement refs and nonempty graft files under the Git common directory
reject, including from linked worktrees. The V2 ancestry reads use bounded
streaming capture, disable lazy fetching and terminal prompts, forbid transport
protocols, and kill the complete command process group during cleanup. Missing
objects therefore reject locally instead of consulting a promisor remote.

The inherited identity-rebuild planner still uses post-hoc bounded Git capture
for its repository inventory. The handoff calls that planner during build and
validation, so the complete path does not yet claim pre-allocation bounds or
no-lazy-fetch behavior for a hostile C0 object graph. All authority remains
false until that inherited boundary is hardened or executed only over an
independently trusted local source snapshot.

The intended interpretation is:

```text
C0: final source before V6 identity materialization
C1: exact V6 identity materialization
C2: exact V7 child-policy pin
G:  fixed governance/evidence commit
```

The existing post-pin governance and release-closure checkers remain the
semantic authority for these transitions. This handoff independently enforces
the literal graph shape and binds their returned bytes.

## Commands

Generate a handoff only after choosing exact C0 and worker commits:

```bash
python3 tools/plan_zrpf_remote_reproof_handoff_v2.py plan \
  --repository "$PWD" \
  --c0-commit "$C0" \
  --worker-commit "$WORKER" \
  --output /private/handoff.json
```

The output path must begin absent. The generated handoff is canonical ASCII
JSON with a trailing newline.

Before each task, after its exact inputs exist, create its canonical execution
packet. For example:

```bash
python3 tools/plan_zrpf_remote_reproof_handoff_v2.py prepare-task \
  --repository "$PWD" \
  --handoff /private/handoff.json \
  --artifact-root /private/zrpf-return \
  --stage v2_adapter_receipt \
  --c0-commit "$C0" --c1-commit "$C1" --c2-commit "$C2" \
  --governance-commit "$G" \
  --output /private/execution-packets/05-v2_adapter_receipt.json
```

The governed filename is `<two-digit ordinal>-<stage ID>.json`. The final
capture requires exactly one packet for every task. A packet proves input-byte
binding only. It does not prove when or whether execution occurred.

Run one implemented stage into a fresh private root and a fresh capture path:

```bash
python3 tools/run_zrpf_remote_reproof_worker_v2.py run-stage \
  --repository "$PWD" \
  --handoff /private/handoff.json \
  --packet /private/execution-packets/07-v6_l1_receipt.json \
  --artifact-root /private/zrpf-return \
  --run-root /private/worker-runs/07-v6_l1_receipt \
  --capture-output /private/worker-captures/07-v6_l1_receipt.json
```

Recheck that local capture against its packet, checkout, input snapshots, and
output bytes:

```bash
python3 tools/run_zrpf_remote_reproof_worker_v2.py check-capture \
  --repository "$PWD" \
  --handoff /private/handoff.json \
  --packet /private/execution-packets/07-v6_l1_receipt.json \
  --artifact-root /private/zrpf-return \
  --run-root /private/worker-runs/07-v6_l1_receipt \
  --capture-output /private/worker-captures/07-v6_l1_receipt.json
```

The source-proof stage additionally requires:

```text
--attempt-budget-and-price <canonical absolute budget record>
--trusted-current-epoch-seconds <explicit positive integer>
```

Those arguments are required for both `run-stage` and `check-capture` when the
selected packet is `04-source_spot_proof.json`.

The worker capture is an unkeyed local process observation with all authority
false. Cryptographic proof and release verification remain separate gates.

After all artifacts exist, prepare canonical program-image input bytes:

```json
{"source_program":"<64 hex>","v2_adapter_program":"<64 hex>","v6_l1_program":"<64 hex>","v6_l2_program":"<64 hex>","v6_leaf_program":"<64 hex>","v6_settlement_program":"<64 hex>","v7_program":"<64 hex>"}
```

Capture the returned inventory:

```bash
python3 tools/plan_zrpf_remote_reproof_handoff_v2.py capture-return \
  --repository "$PWD" \
  --handoff /private/handoff.json \
  --artifact-root /private/zrpf-return \
  --execution-packet-directory /private/execution-packets \
  --program-image-ids /private/program-image-ids.json \
  --c0-commit "$C0" \
  --c1-commit "$C1" \
  --c2-commit "$C2" \
  --governance-commit "$G" \
  --output /private/return-bundle.json
```

Check it independently:

```bash
python3 tools/plan_zrpf_remote_reproof_handoff_v2.py check-return \
  --repository "$PWD" \
  --handoff /private/handoff.json \
  --bundle /private/return-bundle.json \
  --artifact-root /private/zrpf-return
```

An accepted checker response still carries an all-false authority map.

## Required failure detectors

The focused tests require rejection or blocking for:

```text
missing source-proof task
missing source proof before V2 adapter
missing V2 adapter receipt before V6 leaf
stale handoff ID
substituted task ID
governance commit/tree different from the handoff worker
identity-plan hash substitution
identity observations or candidate-report recomposition failure
execution input changed after packet creation
missing or surplus execution packet
wrong literal parent
merge commit in the governed direct-parent chain
missing returned artifact
duplicate returned artifact
artifact-byte substitution
duplicate or noncanonical JSON
integer-for-Boolean and Boolean-for-integer substitution
oversized Git commit object
lazy-fetch attempt from a partial clone
descendant process retaining Git output pipes
aggregate artifact bytes above the governed cap
```

## Promotion sequence

1. Merge this planner/checker only after focused Python checks and independent
   review.
2. Merge the bounded worker only after its command, packet, content, path,
   output-inventory, resource, timeout, and capture negative controls pass.
3. Validate identity and worker-build source/output distinguishing witnesses.
4. Validate the bounded unified V6/V7 mutation worker.
5. Implement a bundle-aware release checker that consumes the exact returned
   identity, proof, mutation, and runtime artifacts.
6. Generate a handoff from the final integration C0 and worker G commit.
7. Run the expensive tasks on the Mac or a remote host.
8. Check the returned bundle independently.
9. Run exact cryptographic replay, program identity recomputation, release
   closure, production-boundary, DA, finality, and atomic-admission gates.

No step in this specification changes the current false production, release,
or settlement claims.
