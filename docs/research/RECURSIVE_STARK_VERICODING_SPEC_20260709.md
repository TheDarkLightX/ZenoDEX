# Recursive STARK Vericoding Spec

Date: 2026-07-09
Status: post-composition-repair current-image local recursive proofs and one
current-source exact retained V3 host-verifier replay verified; release and
production pending

Related artifacts:

- `docs/research/RECURSIVE_STARK_FABLE_BACKEND_IMPLEMENTATION_SPEC_20260709.md`
- `docs/research/RECURSIVE_STARK_CBC_MATRIX_20260709.json`
- `docs/research/RECURSIVE_STARK_V2_CURRENT_EVIDENCE_20260710.json`
- `docs/research/RECURSIVE_STARK_V2_TWO_LEAF_EXPERIMENT_20260710.json`
- `docs/research/RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json`
- `docs/research/RECURSIVE_STARK_V2_BOUNDED_FANOUT_GUIDE_20260710.md`
- `docs/research/RECURSIVE_STARK_REBUILD_PATH_EXPERIMENT_20260709.json`
- `docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md`
- `docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260711.json`
- `docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260710.json`
  (historical)
- `config/proof_profiles/risc0_recursive_rebuild_reference.json`
- `src/integration/recursive_stark_release_binding.py`
- `tools/check_risc0_recursive_rebuild_evidence.py`
- `tools/check_risc0_recursive_v2_two_leaf_source_pinned_evidence.py`
- `tools/check_recursive_stark_cbc_spec.py`
- `tools/check_zrpf_v3_replay_verifier_evidence.py`

## Claim Scope

This document specifies the stronger verification techniques required before
recursive STARK aggregation can move from local hardening evidence toward
production readiness.

This document is not evidence by itself. A vericoding item is complete only
when the corresponding code, test, proof, replay, or checker exists and is
referenced from the CBC matrix.

Current status:

- On 2026-07-10, adversarial fanout tests found and repaired receipt-ID merge
  ordering, host verified-facts ordering, repeated-verifier-set construction,
  and v2 partition-bound parity. These changes touched guest-linked source.
  Current-source v1 leaf/root receipts and a fixed-height v2 inner/root pair
  were subsequently rebuilt, generated, verified, and pinned atomically. The
  explicitly labeled pre-repair values below remain historical evidence.

- The current aggregate-v2 image ID is
  `fe131b0ec697a9bd703218f3733e44b84c8e347eb8ebfc8776be2200958fbe53`.
  Its local pair verifier accepted the one-leaf inner/root pair and rejected
  swapped levels, wrong outer image metadata, authenticated journal mutation,
  and noncanonical outer JSON in the recorded local negative-evidence run.
  Missing child-assumption execution also rejected. This supplies the pinned
  one-leaf part of the current-image, fixed-height, local
  computational-integrity evidence for `RS-CBC-014`.

- A separate unpromoted same-host experiment used the same aggregate-v2 image
  to prove a current spot leaf and a current zUSD leaf as two immediate children
  of one closed subtree, then proved an epoch root over that subtree. The
  authenticated inner shape is `2` immediate children, `2` flat leaves, height
  `1`, and `3` nodes. The authenticated root shape is `1` immediate child, `2`
  flat leaves, height `2`, and `4` nodes. A separate host process verified all
  four receipts, recomputed the exact leaf claim and journal roots, and checked
  the inner-to-root binding. The experiment manifest is pinned by SHA-256
  `c225841cff999b30d0b076845a76b6c0a1ee95127a62504dc2d7c0f49280b73d`.
  The temporary harness has absolute local paths and no governed statement,
  source-to-binary attestation, release authority, or settlement authority.
  The leaves use different verifier IDs and empty receipt-ID partitions, so
  this run does not cryptographically exercise either repaired regression.

- The bounded fanout constructor was then ported into the repository harness
  without the prototype's absolute paths. A target-absent clean build froze the
  20-file source closure at
  `20e5587e3ed7b8f6c561295a04f2cc2de92b90fd38c070de08a33d55b5f7572a`
  and reproduced the aggregate program, raw ELF, image ID, and both host pair
  verifiers. Its release harness regenerated the fanout-two inner and root
  receipts and verified their exact authenticated journals. The source-pinned
  evidence record is SHA-256
  `9a98b947f76a599109f5238861d010fd3dbb8a8299ef6e3f03685b3cac51ad74`.
  The historical and regenerated receipts have different byte hashes and equal
  authenticated journal hashes. General fanout promotion, nonempty receipt
  partitions, proof-byte determinism, and production authority remain open.
  The bounded live replay checker hash-checks every supplied artifact and
  executable, verifies the pinned `r0vm`, replays both leaf orders, checks the
  repository-pinned specialized verifier outputs, rejects a duplicate leaf and
  swapped node levels, and requires the one-leaf policy and missing-assumption
  controls. Its success status retains all release and production non-claims.

- A second source-pinned fixed-height run proves two spot leaves with one
  current image/profile and two distinct authenticated statement/source IDs.
  The specialized verifier recomputes source and scoped lane-assignment roots,
  rejects an exact duplicate lane and a same-statement lane alias, and verifies
  a one-word Succinct seal mutation fails cryptographically. The evidence record
  is SHA-256
  `18141ffae7279b1a717edb41674b4fae101a489e2d7870b920c45c8d6810512a`.
  This is bounded fanout-two same-profile evidence. It does not establish
  general fanout, value-moving batch throughput, independent implementation,
  release authority, or production readiness.

- A target-absent recursive-v2 rebuild froze and rechecked the 20-file source
  closure, rebuilt with the pinned outer and observed nested Cargo executable,
  independently recomputed the image ID, matched the pinned program, raw ELF,
  and both host pair verifiers, verified the pinned proof pair, and returned
  `same_host_clean_recursive_v2_rebuild_match`. The evidence report SHA-256 is
  `a366d6e0d00f963c061cd7c9be9bbc531d6502f49950834f4297b773db05aeb1`;
  its build-log SHA-256 is
  `ad482414d0e20970da320f0254b76a19d673b7eeb8458d18afe84552beb76ce9`.
  The path-redacted evidence record is pinned by file SHA-256
  `6063b2def168c59d0f187a46e8384979441f4bad8ef1a795f2163c86a7849ea1`.
  This is constrained same-host rebuild evidence. The report keeps
  cross-environment reproducibility, production readiness, public-claim
  permission, settlement authorization, source and builder authentication,
  proof-byte regeneration determinism, and whole-build network isolation false.

- CBC obligation matrix exists.
- P0/P1 verifier-boundary hardening has local Rust, Python, bounded SMT, and
  checker evidence.
- The prior RISC0 1.2.6 spot and aggregate receipts are revoked as assurance
  evidence because that SDK is affected by GHSA-jqq4-c7wq-36h7. Their image
  IDs, proof hashes, and verification reports must not authorize admission or
  claim promotion.
- The workspace dependency graph is migrated to exact RISC0 3.0.5 and guarded
  by offline advisory-baseline and toolchain-lock checkers.
- Two clean builds from distinct source and target roots on the same host, with
  unchanged compiler-visible dependency and home paths, matched all six combined
  guest program bytes, their image IDs, the artifact report, and the static host
  verifier. A third build kept those paths fixed and forced nested Cargo offline
  from a source-root config; it reproduced the same bytes, image IDs, verifier,
  and authenticated proof transcript. This is constrained manual same-host
  rebuild evidence.
- The committed v1 checker reports only `pinned_rebuild_artifact_match`. It
  keeps `same_host_clean_rebuild`, command/environment authentication,
  clean-target verification, independent rebuild, production, settlement, and
  reproducible-release flags false because copied bytes cannot attest how they
  were built. The recursive-v2 checker has a separate target-absent build mode.
  That mode matched the pinned local toolchain artifact hashes and observed
  nested Cargo for the successful run above, while retaining the narrower
  non-claims stated there.

- The ZRPF V3 structural lane now has a separate current-source, same-host
  retained-byte replay verifier anchored at commit `b37b7415`. Its selected dependency
  graph excludes methods, guests, the harness, Bonsai, client, and
  `risc0-build`. It binds eight exact receipt artifacts, cryptographically
  verifies seven Succinct receipts under the expected images, recomposes both
  level-one journals and the level-two journal, pins root journal
  `2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768`,
  and rejects the exact one-word root-seal mutation. Normal execution and
  `RISC0_DEV_MODE=1` execution produced byte-identical output. The evidence
  record SHA-256 is
  `9c6d80bdebb9bd7eb8ddfe49bd9797e4ad30de0022d59cd8b7e42f60d2d906dd`.
  Its live build uses a private detached worktree at the pinned commit, checks
  the exact 43-file source closure before and after compilation, disables
  automatic Cargo target discovery and checkout hooks, rejects unpinned
  ancestor Cargo config, remaps compiler-visible paths, and allowlists the
  `execve` environment. It executes exact freshly built verifier bytes from a
  fully sealed Linux memfd and scans the governed public artifacts for bounded
  leakage patterns.
  This is retained proof verification evidence. Proof generation, guest
  source-to-image binding, complete build inputs, compiler, linker,
  dependency-cache and runtime-rootfs identity,
  cross-host reproducibility, release authority, semantic aggregation, ledger
  or settlement admission, privacy, transaction counts, throughput, and
  production readiness remain unestablished.

- The v1 reference schema now pins its positive verifier request and a
  one-bit Succinct seal mutation. The checker validates that only the selected
  seal word changed, that the mutated verifier request changed only its proof
  artifact, and that the recorded response is a cryptographic proof rejection.
  The real candidate passed with `malformed_proof_reject_verified=true`. A
  handled verifier rejection exits zero, so acceptance must come from the
  canonical response object rather than process status. This artifact-mode
  checker validates pinned bytes and semantics; it does not attest verifier
  execution provenance.
- The promoted v1 and v2 source closures enumerate every bounded regular file
  under their declared source scopes. Those source scopes must be target-absent;
  any `target` directory rejects, and evidence builds place targets outside the
  source tree. This includes `include_bytes!` payloads and other non-Rust
  compiler inputs. Adding or mutating such a file reopens the current-image
  claim; focused tests cover binary-payload mutation and excluded-target
  attempts in both workspaces.
- A stricter same-host build relocated `HOME` and the Cargo dependency path and
  forced nested Cargo offline with `[net] offline = true`. It completed, while
  all six combined-program hashes and the static verifier hash differed from the
  reference. Independent `r0vm --id` checks also produced six different image
  IDs. Guest strings identify the relocated Cargo dependency paths in the image.
  This is guest image-identity drift and a counterexample to path-independent
  reproducibility. That historical proof remains bound to the pre-repair
  reference images and does not verify against the relocated images or current
  repaired source. Exact results are recorded in
  `docs/research/RECURSIVE_STARK_REBUILD_PATH_EXPERIMENT_20260709.json`.
- Before the 2026-07-10 composition repair, a force-built 3.0.5 spot leaf and
  one-child aggregate Succinct proof were generated and verified. The
  aggregate image ID matched that historical embedded program and an
  independent `r0vm --id` result.
- The experimental sibling workspace `zk/recursive_stark_v2_risc0` now keeps
  the fixed-height recursive-v2 guest, shared ABI, harness, lockfile, and target
  graph outside the byte-pinned v1 workspace. Before the composition repair, a
  real Succinct inner receipt was verified as the assumption of a real Succinct
  epoch-root receipt. Those historical receipts use
  aggregate-v2 image ID
  `8cd39919e79085bb357f1aa316175809c461c648c5b86481879a12e5c3c826ae`.
  The combined program is 445,696 bytes with SHA-256
  `71ee72cd87ed164e22941630c40fa221ad769f9fea88c9d6eda9985cd409cfd9`.
  A separate pair verifier accepted the two receipts and rejected wrong
  image metadata, journal substitution, swapped levels, and non-canonical JSON.
- The v2 build exposed a compiler-provenance requirement: `risc0-build` 3.0.5
  removes `RUSTUP_TOOLCHAIN` and every `CARGO*` variable before invoking bare
  `cargo` for guests. `cargo +risc0` therefore pinned only the outer process in
  this checkout. Cargo 1.87 changed every v1 program image; placing the pinned
  RISC0 Cargo 1.94 binary first on `PATH` restored exact equality for all six
  v1 programs. Future evidence must record and verify the outer and nested
  Cargo executable, version, compiler, dependency path, and offline config.
- The aggregate proof passed the sealed static-verifier adapter and exact-once
  admission. Replaying the same authenticated root returned
  `recursive_stark.duplicate_root_journal` with unchanged state.
- A bounded transcript-bound replay bundle passed with status
  `local_artifact_pinned_replay` and manifest SHA-256
  `9b50fb6eec7c7220556ac570b817ba6187439938fae67fe00cf9c200796e0ea2`.
  The bundle inventory includes the exact static verifier binary with SHA-256
  `54e80622715976049c2c02232d5e361b140626592875939a6c98eccb06627141`
  and the canonical local authority manifest with SHA-256
  `ef9d2c732f2bd79d1b617a266566d9f9b566516c95248220d5b6198c1538754d`.
  The adapter derives the executable digest and all trusted expectations from
  those manifest bytes after matching that digest. The manifest still needs a
  separately governed ledger or release anchor before it carries authority.
- A canonical release-binding loader now binds the authority-manifest digest,
  replay-manifest digest, chain, epoch, and proof profile to a domain-separated
  config digest supplied by the future authority. The Python nominal type is
  not an authorization capability; every consuming boundary must invoke the
  loader with independently trusted expectations. Governed digest sourcing and
  runtime admission remain pending under `RS-CBC-015`.
- Receipt envelopes now use a versioned depth-limited JSON codec, bind the
  verified Succinct hash function, verifier-parameter digest, and control ID,
  and use RISC0's canonical image-ID digest text.
- Promoted general fanout, mutation and malformed grammar fuzzing,
  arbitrary-depth recursion, durable ledger
  admission, public replay, independently provisioned cross-host rebuild
  equality, reproducible-release evidence, and separately governed
  authority-manifest binding remain open.
- Canonical compiler-visible dependency paths, pinned nested Cargo resolution,
  and guest path remapping remain required before another clean-build equality
  claim can advance.
- The constrained same-host comparison does not establish dependency-path
  independence, an independent rebuild, source or builder authenticity, public
  replay, production readiness, settlement authorization, or a reproducible
  release.
- Production recursive STARKs remain a non-claim.
- Full zk execution for all value-moving surfaces remains a non-claim.
- RISC0 receipts provide computational integrity here. No zero-knowledge or
  witness-privacy property is claimed.

V1 outer JSON remains a parser boundary rather than a canonical statement
encoding. The current CLI accepts duplicate JSON keys with last-key semantics,
and recursive V1 typed structs ignore unknown nested fields. Receipts bind the
resulting typed value, so this does not invalidate the pinned proofs. It does
preclude any claim that the complete outer JSON envelope is canonical or that
unknown fields fail closed. The next ABI must reject duplicate keys and unknown
critical fields before typed construction; production and public claims remain
false until that boundary is closed. `RS-CBC-021` records this as a pending
critical promotion obligation.

## Vericoding Goal

Every critical recursive aggregation claim must have at least one executable
failure detector and, where the invariant is mathematical, a formal or
semi-formal model.

```text
CriticalClaimMayAdvance :=
  CBCObligationExists
  && NegativeTestFailsOnOldBug
  && MutationIsKilled
  && ExternalCommandIsReplayable
  && PublicClaimMatchesEvidence
```

For mathematical invariants:

```text
MathClaimMayAdvance :=
  RuntimeInvariant
  && BoundedModelOrFormalProof
  && CounterexampleSearchDidNotFindGap
  && RuntimeTestMirrorsTheFormalStatement
```

## Technique Routing

| Technique | Use For | Do Not Use For | Required Output |
| --- | --- | --- | --- |
| Mutation tests | Verifier-boundary regressions, reject strings, fail-closed checks | Proving mathematical completeness | Mutant list, killed/survived report, command |
| Stateful BDD tests | Ledger admission, duplicate root, duplicate child, cross-epoch replay, reject-is-no-op | Pure hash ABI checks | Given/When/Then pytest scenarios |
| Property tests | Root determinism, sorted uniqueness, omission/substitution rejection, bounded inputs, conservation over represented rows | Real RISC0 receipt authority | Seeded corpus or deterministic generator |
| Grammar/concolic fuzz | Malformed recursive requests, malformed proof metadata, unknown critical fields | Long-running production proof generation | Minimized counterexamples and regression tests |
| ESSO/SMT | Exact-once admission, conservation row algebra, replay-state closure | CLI parsing and receipt serialization details | Bounded model, assumptions, SAT/UNSAT report |
| Lean | Stable conservation, framing/injectivity, exact-once theorem shape after ABI freezes | Early row design or unstable receipt plumbing | Checked theorem or explicit failed proof note |
| Real RISC0 proof smoke | Root proof production, verify path, malformed-proof reject | Replacing unit/property tests | Source-pinned proof artifact and replay command |
| External model review | Final claim language and design gaps after local evidence exists | Substituting for local evidence | Review packet, findings, disposition matrix |

## Verification Phases

### Phase V0: Patched Dependency And Receipt ABI

Purpose: prevent proof evidence produced by an unsound SDK or ambiguous receipt
ABI from entering a stronger evidence lane.

Required checks:

- every direct `risc0-zkvm` and `risc0-build` dependency is exactly `3.0.5`;
- the host enables `disable-dev-mode` and guest dependencies disable defaults;
- the lockfile resolves one reviewed RISC0 version and checksum set;
- affected 1.2.6 receipts and image IDs are rejected as assurance evidence;
- untrusted receipts use `risc0_receipt_canonical_serde_json_depth128_v1`;
- proof metadata equals the verified receipt's hash function, verifier
  parameters, and control ID;
- image IDs use canonical RISC0 digest bytes and match the embedded program.

Acceptance:

```bash
python3 tools/check_risc0_dependency_advisory_baseline.py --json
cd zk/state_proof_risc0
RISC0_SKIP_BUILD=1 cargo +risc0 test --locked --offline \
  -p tau-state-proof-risc0-cli --bin tau-state-proof-risc0-cli
```

This offline advisory snapshot is a minimum baseline. A current advisory audit
is still required for release promotion.

### Phase V1: Mutation-Killed Verifier Boundary

Purpose: prove the tests catch the Fable-class bugs.

Required mutants:

- Move child journal decode before `env::verify`.
- Remove child summary image-id equality check.
- Allow missing `recursive_expectations`.
- Allow mismatched `verifier_set_root`.
- Treat enabled `RISC0_DEV_MODE` as acceptable.
- Remove `InnerReceipt::Fake` rejection.
- Remove zUSD chain-id equality check.
- Remove perps chain-id equality check.

Acceptance:

- Each mutant is killed by a named test.
- Surviving mutants are recorded as gaps in the CBC matrix.
- Mutation tool output is deterministic and checked into a generated report only
  when the regeneration command is documented.

Candidate commands:

```bash
python3 tools/mutate_recursive_stark_boundary.py --list
python3 tools/mutate_recursive_stark_boundary.py --run --json
python3 -m pytest -q tests/test_recursive_stark_boundary_mutations.py
```

### Phase V2: Stateful Admission And Replay

Purpose: prove recursive roots cannot be replayed across admission boundaries.

Required scenarios:

- duplicate root for same `(chain_id, epoch_id, proof_profile)`;
- same child leaf admitted through two roots;
- same message ID admitted through two roots;
- chain relabel attempt at root admission;
- replay state created for one chain reused for another chain;
- stale verifier set root after governance update;
- wrong public policy hash after policy update;
- rejected admission leaves state unchanged.

Acceptance:

- Tests assert exact reject reason and reject-is-no-op.
- Tests use deterministic state fixtures, no wall clock, no network, no random
  seed without explicit commitment.
- CBC matrix references the test files before any exact-once claim advances.

Implemented command:

```bash
python3 -m pytest -q \
  tests/core/test_recursive_stark_exact_once_admission.py \
  tests/integration/test_recursive_stark_verifier_adapter.py
```

### Phase V3: Property And Fuzz Coverage

Purpose: widen malformed-input and invariant coverage around the deterministic
composition kernel.

Required properties:

- root journal is deterministic for the same typed statement and child set;
- child order canonicalization rejects unsorted or duplicate lanes;
- omitted child changes root or rejects;
- substituted child changes root or rejects;
- aggregate input bounds reject before allocation;
- represented asset deltas satisfy conservation;
- unrepresented value surfaces remain explicit non-claims.

Required fuzz lanes:

- malformed `recursive_expectations`;
- unknown critical metadata fields;
- overlarge child journal lengths;
- duplicate receipt IDs;
- duplicate message IDs;
- invalid chain/epoch/profile encodings.

Acceptance:

- Counterexamples are minimized into regression tests.
- Fuzz runs have bounded iteration counts and deterministic seeds.
- Property tests do not weaken existing unit tests.

Implemented bounded commands:

```bash
cd zk/state_proof_risc0 && cargo test -q -p tau-state-proof-risc0-shared recursive_prop --offline
python3 -m pytest -q tests/zk/test_recursive_stark_request_fuzz.py
```

### Phase V4: ESSO/SMT Models

Purpose: model the finite disaster states that are easier to prove outside
RISC0 execution.

Required models:

- exact-once root admission over bounded epochs;
- duplicate child admission over bounded root sets;
- duplicate message admission over bounded root sets;
- asset conservation over represented recursive rows;
- counterexample model for current perps self-balancing rows showing why they
  do not prove global source finality;
- zUSD lifecycle coverage model showing mint-only coverage is incomplete.

Acceptance:

- `UNKNOWN`, timeout, or missing model output is treated as failure.
- Each model states variables, bounds, assumptions, exclusions, and result.
- Runtime tests mirror the accepted model statements.

Candidate commands:

```bash
python3 docs/research/recursive_stark_exact_once_smt.py
python3 docs/research/recursive_stark_conservation_smt.py
```

Current evidence proves finite models only: two sequential admissions for four
namespaced ID classes, plus two assets with two rows each. The reports include
SAT witnesses for every removed modeled guard. Concurrency, crash recovery,
unbounded traces, cryptographic soundness, and runtime equivalence remain
outside those models.

### Phase V5: Lean Proofs For Stable Invariants

Purpose: promote stable mathematical invariants after the runtime shape stops
changing.

Completed first theorem lane:

- `lean-mathlib/Proofs/RecursiveCanonicalSetComposition.lean` proves the
  list-level accepted/rejected receipt-ID composition model with no `sorry`.
  Full-concatenation sorting preserves every occurrence, is invariant under
  lane regrouping, and preserves duplicate and cross-partition collision
  detection. The theorem also proves the two receipt partitions have
  independent bounds and constructs positive, strictly sorted, unique,
  globally valid partitions that the removed combined-count rule rejects.
- Runtime regression links are
  `recursive_prop_receipt_roots_are_invariant_to_lane_interleaving` and the
  cross-lane duplicate rejects in v1, plus
  `accepted_and_rejected_receipt_partitions_each_use_the_v1_bound` and the
  independent bound-plus-one rejects in v2.
- The Lean model does not prove SHA-256, Postcard framing, RISC0 or VM
  soundness, Rust compilation, `sort_unstable` refinement, or Rust-to-Lean
  refinement. Those remain separate obligations.

Remaining theorem targets:

- canonical length-prefix framing is injective over recursive statement fields;
- sorted-unique child IDs prevent duplicate child contribution within one root;
- exact-once admission prevents replay across accepted roots;
- represented-row conservation is preserved by aggregation;
- zUSD full lifecycle rows conserve supply once repay, redeem, burn, and
  liquidation rows exist.

Acceptance:

- No `sorry`.
- The theorem statement is narrow enough to match runtime code.
- Runtime tests link to the theorem scope.
- A proof failure is recorded as a gap, not hidden behind weaker claim language.

Checked commands:

```bash
cd lean-mathlib
lake env lean Proofs/RecursiveCanonicalSetComposition.lean
lake build Proofs.RecursiveCanonicalSetComposition
lake build
```

### Phase V6: Real Proof Smoke And Malformed-Proof Rejects

Purpose: prove the receipt path works with an actual recursive root proof.

Required artifacts:

- source-pinned recursive root proof generation command;
- successful root receipt verification command;
- malformed root journal reject;
- wrong image ID reject;
- wrong trusted expectation reject;
- dev/fake receipt reject;
- proof artifact hash and environment notes.

Acceptance:

- Local dev-mode proof output is labeled dev evidence.
- Production claim remains false until release profile, manifest, and public
  replay requirements are satisfied.

The outer verifier must authenticate one submitted recursive root receipt
exactly once per request. The production authenticator returns a module-private
receipt/profile pair whose fields have no production constructor outside that
boundary. The verifier checks metadata, ledger-owned expectations, and exact
disclosure recomposition before constructing `VerifiedRecursiveFacts`.
Response rendering consumes only those facts and cannot reopen, decode, or
cryptographically verify the receipt. The Rust test
`recursive_request_authenticates_receipt_once_and_preserves_response_schema`
uses a test-only `FnOnce` authenticator port to enforce one boundary invocation
while preserving the existing response schema. The separate
`recursive_production_path_has_one_cryptographic_verify_call_site` ratchet
requires one production root authenticator call, one profile-decoder call, and
one `Receipt::verify(image_id)` call site.

Local proof command shape:

```bash
cd zk/state_proof_risc0
RISC0_FORCE_BUILD=1 cargo +risc0 run --locked \
  -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  spot "$SPOT_IMAGE_ID_HEX" > /tmp/recursive-stark-spot.request.json
RISC0_PROVER=ipc RISC0_FORCE_BUILD=1 cargo +risc0 run --locked \
  -p tau-state-proof-risc0-cli \
  < /tmp/recursive-stark-spot.request.json \
  > /tmp/recursive-stark-spot.proof.json
# Build the root request from that proof, prove it, then verify with the exact
# recursive_input and ledger-owned recursive_expectations disclosure.
```

The recursive-v2 build must invoke the pinned Cargo binary directly and put its
directory first on `PATH`, so `risc0-build` resolves the same executable for the
nested guest build:

```bash
PINNED_BIN="$HOME/.risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin"
PATH="$PINNED_BIN:$PATH" "$PINNED_BIN/cargo" build \
  --frozen --release --target x86_64-unknown-linux-gnu \
  -p tau-state-proof-risc0-recursive-v2-harness
```

Both recursive workspaces now carry a source-root `.cargo/config.toml` that
makes nested Cargo offline. `CARGO_NET_OFFLINE=true` alone is insufficient
because `risc0-build` removes that variable. The offline configuration is part
of the checked source closure for the replacement evidence.

Historical revoked run: the 2026-07-09 RISC0 1.2.6 run produced a 299,316-byte
base64 Succinct spot receipt and a 300,076-byte base64 Succinct aggregate
receipt. Its verification behavior remains useful as a regression recipe, but
GHSA-jqq4-c7wq-36h7 invalidates the receipts, image IDs, root journal hash, and
proof hashes as soundness evidence.

Historical pre-composition-repair local evidence: the exact RISC0 3.0.5 build produced spot image ID
`06c9b076474666d1ef594600ba6c5e648427f66a2db0983ef8f1b118fb34ae3e`
and aggregate image ID
`8e99bfa7eb8e576c1758be41a796294238b9535d070d6a7fc2dab7379b3268f5`.
The aggregate proof SHA-256 is
`1e1ba6cdb6c21fb140b956a16509c0a2d81daa7c2ce6f5a7df3c9132a09d8b81`.
The static verifier SHA-256 is
`54e80622715976049c2c02232d5e361b140626592875939a6c98eccb06627141`.
This advanced `RS-CBC-014` only for the historical pre-repair image at that
time. The current closure is recorded separately below. The
separate same-host clean-rebuild comparison reproduced these local artifacts
only while
compiler-visible dependency and home paths remained unchanged. A nested-offline
build with those paths fixed reproduced the authenticated verification
transcript with SHA-256
`c4ad88fcb3009ef721399f68b36927f136c199232bb0316d98248f69be6eec4d`.
The committed v1 artifact checker authenticates only a
`pinned_rebuild_artifact_match` and does not attest execution provenance.
Relocating those
paths under a nested-offline Cargo build changed all six combined-program hashes
and the static verifier hash. All six independently computed image IDs changed,
and guest strings expose the differing Cargo dependency paths. That historical
proof is bound to the reference images and does not verify against those
relocated images or the repaired current source. These hashes and comparisons
do not establish path-independent or cross-host equality, a reproducible
release, public replay, source or builder
authenticity, separately governed authority, settlement authorization, or
production readiness.

Current post-composition-repair v1 local evidence:

- spot and aggregate image IDs:
  `1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403`
  and `a34b6d075465a7ae4e562463c9f2b356542aca1030f34cd28dc5c5f589c00cdf`;
- aggregate combined-program SHA-256:
  `bbc64916ff42389fce5f4e76fe4b52e4f3eaad70d27813aef7156f372d5ded5e`;
- bounded all-regular-file v1 source-closure SHA-256:
  `76a267fd6cbd51c8397073af5553d8a5877945dbf3d18cde2ac262c149366d50`;
- spot and aggregate artifact-file SHA-256 values:
  `4ce7db31e6ae5e5af53b4ef67fb0cd6ebb1dcae9cf05ee9f73b4511c10db20b9`
  and `061f99b459e54a0bef821880f43049bb2120d5ff427439067950141286d533dd`;
- static PIE verifier SHA-256:
  `49d83f7c08256677e9b9aed993a7db59c46875aa96ab08791e0b1d60ad06acd9`;
- accepted strict-verification transcript SHA-256:
  `af2a660f10f3b4eb01811cb4215f01546679618296dcd369e3f6d542bfae5c8a`;
- positive strict-verification request SHA-256:
  `0fe3653f523b3be3f6b0fe9506ab9f40b393f66619f6d504cd14ef60f934b941`;
- one-bit malformed seal proof and request SHA-256 values:
  `00fcd3567344a531a58a6a56407c9be80024163af805f847d947d2a1503684c1`
  and `303fa61728433cc595afae6e1e8d4dbc4b3972264afd842ef3315b8b919227e0`;
- canonical cryptographic-invalid transcript SHA-256:
  `206918c41a0f9f05cb34dbdbf15aa972d726ec50a38a217f8640f59e47912dba`;
- v1 reference-v2 canonical SHA-256:
  `0603e3cf3fc76b5226f319dc82724a8d8fc8c972a0e8f63a99645a7cb79c14c8`.

The V1 adapter separately retains the historical proof-generation source root
`7a3bed2a1d8fff3ad2e93f2d406df435a9990d1a9c0462ff3323fb028327564e`.
That immutable compatibility provenance is distinct from the current rebuild
closure above; both resolve to the same pinned Spot guest program and image ID.

The malformed proof flips only bit zero of Succinct seal word 27,833
(`662339219` to `662339218`). The decoded receipt bytes differ at exactly one
byte; the claim, journal, control ID, verifier parameters, metadata, trusted
expectations, and recursive disclosure remain unchanged. The verifier returned
the exact cryptographic-invalid response with process exit code zero. The
checker therefore treats the response object as the decision and binds the
mutation shape, request parity, and response bytes independently.

Independent `r0vm --id` checks matched all six current combined programs. The
strict verifier first rejected the root helper's child-derived receipt control
ID, then accepted when supplied the pinned aggregate receipt profile. This is
fail-closed behavior and exposes a fixture-bootstrap boundary: request metadata
derived from a child receipt cannot authorize the aggregate receipt profile.
Production admission must obtain that expectation from separately governed
ledger or release configuration. The v1 checker status remains local and
pinned; it does not execute the verifier or establish transcript provenance,
public replay, cross-host equality, release or settlement authority, privacy,
or production readiness.

Historical pre-composition-repair fixed-height recursive-v2 local evidence:

- canonical inner receipt SHA-256:
  `c0c10d68d54fffa9d84a909586b1428f08a4fefc7e3ef13aa9d7ed5836d4df34`;
- canonical epoch-root receipt SHA-256:
  `14258883ad986df9834a413de11fefe83c22d5951cd4f35a44b3049afd2ba289`;
- inner and epoch-root artifact-file SHA-256 values:
  `dbb02eb8afa97f6ee498169601560842dda1c2b989d5c40a6e30565d386e0f5d`
  and `102253beb0098bd983e2c6f2ecf3dcea16fdba0779c2e27c19becbea21c5a41a`;
- inner authenticated journal SHA-256:
  `3cc399f8b8da2a56b1c60f11765ddf0989285dea1b7932871a8eb987e069d9ee`;
- epoch-root authenticated journal SHA-256:
  `55660a3a1d8a70f37463718804b608f3cb2e91512e3e8e53091606e2d79c4ecb`;
- missing-child execution rejected with the exact RISC0 assumption claim;
- pair-verifier status: `recursive_v2_pair_verified`.

This is historical one-leaf, fixed-height local evidence. It does not evidence
the repaired current source. The harness derives scheduling and data-availability
values as commitment-only smoke inputs. Its local v1
image allowlist has no registry authority. The guest journal's `self_image_id`
is host supplied, so every external verifier must bind the actual receipt image
ID to the authenticated journal before admission.

Current post-composition-repair fixed-height recursive-v2 local evidence:

- aggregate-v2 combined-program SHA-256:
  `3fc45f1cfc7ffd401119ad8eb3779db19d4a060942de70e25c7c9b706e1c8376`;
- aggregate-v2 image ID:
  `fe131b0ec697a9bd703218f3733e44b84c8e347eb8ebfc8776be2200958fbe53`;
- canonical inner and epoch-root receipt SHA-256 values:
  `7f513a978b9d34e219cf96672cec92b46245d2627c8b4d1cd16d1a2dfabd72b1`
  and `d315b3c463a13127f896a5ebc34c39dac30fd58894e87cd742536fa3c5197a69`;
- inner and epoch-root artifact-file SHA-256 values:
  `9aa0bd06a2c0e31f6f9b17375a85bced5a65b9b774350eb80a919b2a5b87ff9b`
  and `8fb245914b38726b67ebed74c6210c06660156fc17772f679d225381401e26e7`;
- inner and epoch-root authenticated journal SHA-256 values:
  `0f48196d86fe5c5551449d56f783cae81d6a1349933045c3ae53350424abc95b`
  and `af9485a9ef9e12020f11b20ac385a91a8d13910428ca8f6851e4882e291a7139`;
- pinned host pair-verifier SHA-256:
  `79f16282cd5146a6407b995d32dbbfa9e9eea7fb7b5f6e7e6146c66b88d5360e`;
- pair-verifier output SHA-256:
  `469573a876ff43695b440b63fb589cbfdf071c6f36c266c507be9af24c13219b`;
- missing-assumption transcript SHA-256:
  `dc7fa4bbe2d0bca183d6bd38cc4a4973a6ebe3e82350b7e563dcc7d0e40a36e0`;
- pair-verifier status: `recursive_v2_pair_verified`.

The pinned reference is
`config/proof_profiles/risc0_recursive_v2_rebuild_reference.json`. Its candidate
checker accepted the exact program, receipts, journals, security parameters,
verifier, and negative transcript. A second target-absent, source-closure-checked
build reproduced the program, raw ELF, and host verifier, then reran live
proof-pair verification with nested Cargo observed and offline. The host
verifier is
dynamically linked; the reference schema retains the historical field name
`static_verifier`, and `runtime_rootfs_authenticated` remains false. This is
one-leaf, fixed-height, constrained same-host local evidence. It does not
establish proof-regeneration determinism, whole-build network isolation, public
replay, cross-host or reproducible-release equality, source or builder
authenticity, release authority, settlement authority, ledger admission,
privacy, or production readiness.

The current fixed-height smoke uses a spot leaf with empty recursive
accepted and rejected receipt-ID partitions. Nonempty partition interleavings
have source-level and host-boundary regression tests, while real-proof evidence
for that witness branch remains pending.

## BDD User Stories

### Story 1: Operator Rejects Unauthorized Recursive Root

Persona: governance or release operator.

```gherkin
Given a recursive root proof whose journal is internally self-consistent
And the proof was built with a prover-chosen verifier_set_root
When the operator verifies the proof without matching trusted expectations
Then verification fails closed
And no ledger admission state changes
And the receipt cannot be described as production-ready evidence
```

Acceptance evidence:

- CLI test for missing `recursive_expectations`.
- CLI test for mismatched `verifier_set_root`.
- CBC matrix entry `RS-CBC-003` remains implemented with code and test refs.

### Story 2: Aggregator Cannot Swap Child Program

Persona: honest proof aggregator defending against Mallory-supplied child data.

```gherkin
Given Mallory supplies child journal bytes and a child image ID
And the child summary claims a different image ID
When the aggregate guest verifies the child receipt
Then the guest verifies the receipt before decoding the journal
And the decoded summary image ID must equal the verified image ID
And the aggregate aborts on mismatch
```

Acceptance evidence:

- Mutation test kills decode-before-verify mutation.
- Mutation test kills removed image-id equality mutation.
- Existing shared and guest tests remain green.

### Story 3: Security Reviewer Sees Boundary Mutations Killed

Persona: security reviewer.

```gherkin
Given the reviewer runs the recursive STARK boundary mutation suite
When each known Fable-class bug is reintroduced as a mutant
Then every critical mutant is killed by a named test
And any surviving mutant creates a pending CBC obligation
```

Acceptance evidence:

- Mutation report lists killed and survived mutants.
- CI fails on a survived critical mutant.
- CBC matrix is updated for any survivor before merge.

### Story 4: Ledger Rejects Cross-Root Replay

Persona: ledger admission operator.

```gherkin
Given a recursive root has already been admitted for chain C and epoch E
When the same root, child leaf, or message ID is submitted again
Then admission rejects the duplicate
And the rejection reason names the replay class
And committed ledger state is unchanged
```

Acceptance evidence:

- Stateful integration test for duplicate root.
- Stateful integration test for duplicate child leaf.
- Stateful integration test for duplicate message ID.
- Reject-is-no-op assertion for each case.

### Story 5: zUSD Maintainer Cannot Overclaim Lifecycle Coverage

Persona: zUSD maintainer.

```gherkin
Given the current recursive zUSD leaf only emits deposit-mint rows
When a repay, redeem, burn, or liquidation operation is routed into the leaf
Then the operation is rejected or excluded with explicit unsupported-operation
language
And no UI, docs, or claims registry entry may say full zUSD lifecycle coverage
```

Acceptance evidence:

- zUSD zero-mint unsupported-operation test.
- Future lifecycle row tests for repay, redeem, burn, and liquidation before
  claim promotion.
- CBC matrix keeps full zUSD coverage as a non-claim until rows exist.

### Story 6: Perps Engineer Separates Local Proof From Global Conservation

Persona: perps engineer.

```gherkin
Given perps recursive rows are currently self-balancing
When an aggregate root includes perps collateral movement
Then the aggregate may claim local perps transition row-root binding
And it must not claim global cross-lane collateral source finality
Until explicit external inflow/outflow rows or a chain-balance lane exist
```

Acceptance evidence:

- SMT counterexample or bounded model showing self-balancing rows are
  insufficient for global source finality.
- New row design with missing-counterparty negative tests before promotion.

### Story 7: DA Root Does Not Become False Authority

Persona: protocol reviewer.

```gherkin
Given a recursive root commits data_availability_root and conflict_schedule_hash
When no DA policy verifier or schedule verifier has accepted those roots
Then the proof may claim commitment to those roots
And it must not claim DA availability or schedule correctness
```

Acceptance evidence:

- CBC matrix keeps DA/schedule verification pending.
- Claims checker or docs review rejects stronger DA language.
- Future DA verifier has malformed certificate tests.

### Story 8: Release Manager Requires Real Proof Evidence

Persona: release manager.

```gherkin
Given local unit tests and composition checks pass
When recursive aggregation is proposed for release-backed status
Then the release manager requires a real recursive root proof smoke
And malformed-proof rejects
And release manifest evidence
And independent review
```

Acceptance evidence:

- Real proof smoke command and artifact hash.
- Wrong journal, wrong image ID, wrong trusted expectation, and fake/dev receipt
  reject tests.
- Claims registry updated only after all promotion gates pass.

### Story 9: Formal Engineer Promotes Only Stable Theorems

Persona: Lean or formal-methods engineer.

```gherkin
Given a runtime invariant has stabilized
And the runtime tests already define its operational boundary
When the formal engineer writes a Lean or SMT statement
Then the statement must match the runtime boundary
And proof failure records a gap
And the public claim remains scoped until the proof and runtime tests agree
```

Acceptance evidence:

- Lean build or SMT report.
- Runtime test link for the theorem scope.
- No claim promotion from theorem-shaped prose alone.

## Implementation Backlog

| Order | Work Item | Primary Evidence |
| --- | --- | --- |
| 1 | Add mutation harness for recursive verifier boundary | killed-mutant report |
| 2 | Complete: stateful exact-once reference admission tests | reject-is-no-op pytest scenarios |
| 3 | Add property tests for recursive composition | deterministic generated corpus |
| 4 | Add malformed request fuzzing | minimized regression corpus |
| 5 | Complete bounded lane: exact-once and conservation SMT models | SAT/UNSAT reports |
| 6 | Add perps source-finality row design | missing-counterparty negative tests |
| 7 | Add zUSD full lifecycle row extractors | lifecycle row tests |
| 8 | Complete: receipt kind/profile policy | receipt-kind mismatch tests |
| 9 | Complete: current-image one-level and fixed-height two-level local proof smokes on pinned RISC0 3.0.5 | pinned proof hashes, negative transcripts, and pair-verifier report |
| 10 | Partial: prove canonical receipt-set composition; extend Lean coverage to framing, exact-once, and conservation | current module and full `lake build` with no `sorry`; runtime refinement remains pending |
| 11 | Run external Fable/Codex review on final packet | disposition matrix |
| 12 | Update release manifest and claims registry | production gate output |
| 13 | Complete local reference: committed recursive-v2 source/artifact reference and rebuild checker | fail-closed v2 provenance report; cross-host release evidence remains pending |
| 14 | Complete regression lane: source-built ZRPF V3 exact retained-receipt replay | seven verified Succinct receipts, exact root-seal mutation rejection, normal/dev parity, and eight host-boundary negative controls; proof-generation provenance remains pending |

## Promotion Rule

The recursive lane cannot advance to production-ready language until the CBC
matrix shows no pending critical obligations and this vericoding spec has
evidence for:

- killed verifier-boundary mutations;
- stateful replay rejects;
- property/fuzz coverage for malformed inputs;
- bounded formal model or proof for exact-once and conservation;
- real recursive root proof smoke;
- durable atomic replay-state admission;
- depth and fanout evidence matching any general recursive-tree claim;
- source-pinned guest compiler and image build;
- current dependency-advisory review with affected evidence revoked;
- depth-limited versioned receipt codec and verified receipt-profile binding;
- release manifest and claims registry gates;
- independent review.

If any item is missing, the correct public posture is:

```text
recursive aggregation is a local RISC0 scaling lane under active hardening
```
