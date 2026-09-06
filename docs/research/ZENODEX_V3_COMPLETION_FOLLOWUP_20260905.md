# V3 completion follow-up: arithmetic, liquidity and measured publication

Implementation base: `f7b287da51d0cb3f50a557fe7df567313e0bce57` on the V3
integration branch. This record reports separate obligations. It does not close
W00-W13, change the active-plan registry, activate a profile or certify a release.
Exact changed source and test bytes are declared by the accompanying THV1 packets.

## Publication outcome knowledge: W06 and W11

The isolated publisher now distinguishes a precommit refusal from response loss
after commit even without an external monotonic anchor. After an unknown journal
outcome, it reads complete validated history and compares the exact canonical
epoch bundle. A different writer's bundle does not establish this occurrence's
commit. An unreadable or inconsistent observation remains indeterminate.

`GlobalEconomicPublicationIndeterminateV1` is the common runtime error for
publication uncertainty. The existing anchor-specific error remains available
as its subclass. A successful journal commit followed by failed response
projection is indeterminate. A returned journal refusal stays known even if
projection or subsequent history access fails. Process-control exceptions retain
their original control-flow behavior.

Independent review identified and the implementation repaired two additional
cases: a known stale refusal beside a competing writer, and a historical exact
retry while a newer committed epoch still needs anchor recovery. The retained
tests observe complete SQLite rows and exact retries; they do not equate
physical file equality with logical rejection purity.

This changes response classification and adds a read-only recovery observation.
The economic transaction and its linearization point are unchanged. The
publisher and journal remain large inherited adapters; the new classifier is
separate, and unrelated migration/bootstrap refactoring is outside this change.

Validation:

```bash
python3 -B -m pytest -q \
  tests/integration/test_global_economic_publication_outcomes_v1.py \
  tests/integration/test_global_economic_known_outcomes_v1.py \
  tests/integration/test_global_economic_durable_publisher_v1.py
```

The initial failing-evidence run observed both unanchored postcommit errors
escaping without an indeterminate type. After repair, this suite and the focused
LP/replay suites passed 143 cases together. The publisher fixtures use real BLS
and synthetic RISC0 replies. This result does not qualify a real proof chain or
close the existing authority-inode, separate-migration, restored-store,
writer-fencing or deployment obligations.

## Checked aggregation: W09

`CheckedEconomicAggregationV1.lean` proves success iff every relevant ordered
prefix remains within the supplied signed bounds, and proves the exact sum for
every complete `(kind, principal, asset, domain)` key on success. It includes
both i128 overflow directions where later cancellation makes the final
mathematical sum representable. Such a final sum does not rescue an earlier
checked overflow.

The 16 theorem statements are checked by independent consumer signatures and an
axiom allowlist. Twelve tests compile the proof, compare 34 actual Python fee
materialization cases and 66 actual composition cases, check separate stage
boundaries, execute 259 small ordered traces, and reject five executable
guard/key-coordinate model mutants. Root review reran these tests successfully.

```bash
python3 -B -m pytest -q tests/formal/test_lean_checked_economic_aggregation_v1.py
```

The theorem is universal over its explicitly defined arithmetic model. Runtime
correspondence remains finite. Dictionary representation, canonical decoding,
Rust/compiler refinement, complete authorization, cryptography and publication
are outside this proof. W09 remains open.

## Reserved liquidity ownership: W07

The reserved LP lock cannot be spent through legacy REMOVE_LIQUIDITY. The
producer, both accepted-fill appliers, strong replay and Rust shared transition
now refuse the reserved principal before any mutation. The applier guard also
protects against a caller supplying an already-accepted fill. Existing amount,
pool-status and slippage validation order is retained within each path. Fee
rounding, lock constants and ordinary holder withdrawal amounts are unchanged.

The focused Python suite passed 83 tests. The new scenarios cover one atom,
the complete minimum locked share, zero-amount precedence, an inactive pool,
ordinary withdrawal and complete input snapshots after rejection. A fixed
positive/negative vector is mirrored in Rust. These are bounded transition
checks; they do not establish a complete pool-close policy, universal runtime
refinement or the V3 Spot lane lifecycle.

The shared Rust host suite passed all four `remove_liquidity` cases, including
the reserved-lock vector, plus the existing liquidity rejection/no-mutation
case. Root review replayed the four-case suite. The 23-package host dependency
closure was checked against the unchanged Cargo lock, with missing official
archives supplied in an isolated temporary override. The host target used
53 MB. Existing workspace-profile and `cfg(kani)` warnings remain; no guest,
methods, CLI or proof was built.

```bash
# From zk/state_proof_risc0, with the exact locked dependencies available.
cargo test --offline --locked -p tau-state-proof-risc0-shared --lib remove_liquidity
cargo test --offline --locked -p tau-state-proof-risc0-shared --lib \
  liquidity_rejections_do_not_mutate_balances_or_pools
```

The changed shared transition must be included in any newly qualified guest
build. Historical images and receipts cannot establish this guard for the new
source.

## Measured native BLS execution: W03

The new standalone native endpoint and Python adapter implement raw-message
G2 Basic verification under a new protocol root. They retain the existing
algorithm's public-key/signature representation and exact NUL domain separator.
The endpoint checks subgroup membership, rejects infinity and requires canonical
compressed re-encoding. Responses bind an exact Boolean result to SHA256 of the
complete request.

The Python loader acquires immutable ELF bytes once. Each call executes a sealed
memfd containing those same bytes. The existing bounded pipe exchange is reused
as transport; it contributes no receipt identity or receipt authority. The
transport rejects nonzero exit, stderr, timeout, output overflow, unknown framing
and mismatched response digests.

The checksum-verified candidate has SHA-256
`597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee` and is
508,672 bytes. All 24 third-party registry archives matched the committed lock.
The native suite passed five tests and Clippy. A separate real sealed-execution
run passed all 27 Python tests, including 18 independent `py_ecc` comparisons.
An additional 22 real-execution cases use independent curve arithmetic to
check four on-curve points outside the prime-order subgroup, malformed
compression and three noncanonical field aliases of valid points. Each case
requires a cryptographic false response; an operational failure cannot pass.
The ordinary sandbox denied memfd execution; the successful real replay used
scoped local execution permission. No network or economic publication occurred
in that replay.

```bash
# Build the isolated crate with checksum-matching registry or directory sources.
cargo test --manifest-path zk/economic_command_bls_verifier_v1/Cargo.toml --offline --locked

# This variable must name the measured, built native endpoint.
ZENODEX_BLS_VERIFIER_TEST_BINARY=/path/to/qualified-candidate \
  python3 -B -m pytest -q tests/integration/test_sealed_bls_command_verifier_v1.py
```

Without that explicit binary, the real-execution test skips. Such a default run
does not qualify cryptography. The cached advisory check found no listed
vulnerabilities, but advisory freshness is unproved. Binary reproducibility,
compiler correctness, dynamic-loader/libc/libgcc integrity, the kernel and the
Python publisher process remain assumptions or open qualification obligations.
The timeout covers pipe exchange, excluding acquisition and process creation;
this adapter is not an OS sandbox or a complete process-resource limit.

The native qualification archive preserves the exact ELF, checksum-verified
dependency sources, crate source and replay record. Its SHA-256 is
`1313193c1be8517d54a5692024badd473f246076ee5424840ad939a59887169d`.
This is a 2,491,779-byte private retained artifact, not a self-contained archive
of the entire Python runtime or publication pipeline.

## Signature release and execution binding: W03 and W06

Separate Python and Rust successor binders require the G2 Basic protocol root,
98-byte public-key token ceiling and 96-byte signature ceiling. Closed protocol
variants determine these requirements. The shell reads the artifact once,
constructs the sealed backend internally and supplies those same immutable
bytes to release admission. Both languages retain the protocol and isolated
binding-root golden vectors. Caller-supplied evidence roots are synthetic in
these tests and do not qualify a governed release.

Root review found that the old Rust legacy binder admitted SHADOW and
VERIFY_ONLY releases when their new-authentication flag was false. Its default
production entrypoint now requires ACTIVE_NEW, matching Python's production
purpose. A retained negative regression checks both rejected lifecycle states
and the unchanged active binding root. Existing Rust callers are test support
and use ACTIVE_NEW. This is an intentional admission restriction. Each
language retains its own first-error ordering for compound-invalid inputs;
full rejection-precedence parity is not claimed.

The real sealed transport, group-validation, successor core and shell suites
passed 61 tests together on the measured ELF. Historical protocol roots,
profile bytes and receipts retain their original meanings. A fresh qualified
release and genuine receipt chain for the selected source remain required.

The new `bind_isolated_asset_receipt_pipeline_with_sealed_bls_v1` factory fixes
the measured backend explicitly. The legacy factory retains its original
backend and validation order. Both share context snapshot/port validation and
private registry minting; neither accepts a caller-selected backend. The
inherited large adapter remains, with the common constructor steps extracted
without changing per-command verification semantics.

The sealed pipeline's retained scenario first rejects an invalid signature
without changing any logical ledger row or calling a receipt verifier. A valid
signature then commits the exact canonical epoch bundle, and an exact retry
returns ALREADY_COMMITTED without another ledger change. A separate test
refuses the legacy protocol before pipeline authority is minted. The test
explicitly separates the real BLS transport from synthetic RISC0 transport.

```bash
ZENODEX_BLS_VERIFIER_TEST_BINARY=/path/to/qualified-candidate \
  python3 -B -m pytest -q \
  tests/integration/test_global_economic_sealed_bls_pipeline_v1.py \
  tests/integration/test_isolated_asset_receipt_pipeline_v1.py
```

These tests qualify isolated test-state integration. They do not supply fresh
genuine RISC0 receipts, mount the custody successor or authorize production.
Root replay passed all 37 sealed/legacy pipeline cases together.

## Shared validation and remaining environment gates

The complete critical-quality script passed after the LP and pipeline source
changes: Ruff, the gate's 25-file MyPy scope, 433 acceptance tests and 834
critical tests, with 89% coverage for the gate's declared coverage scope. A
separate Ruff/MyPy pass covered all 23 changed Python source/test/renderer
files. Coverage outside the gate's selected files is not inferred.

The Rust ABI successor deployment, legacy deployment, authentication and lane
receipt-binding suites passed 4, 7, 12 and 78 tests respectively. Source-pinned
hygiene admission covers all 21 declared critical paths in this batch. The
production-boundary checker passed its 14 checks while retaining
`m6_production_mounted=false` and `BLOCKED_OPEN_COVERAGE`.

```bash
# Set PYTHON to an environment containing the gate's pinned test tools.
bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status

# From zk/global_settlement_abi_v1.
cargo test --offline --locked \
  --test bls_command_verifier_deployment \
  --test economic_command_signature_verifier_deployment \
  --test economic_command_authentication \
  --test lane_module_release_route_binding
```

The permissionless-assurance status command succeeds but reports missing ESSO
and Tau mounts for its broader proof/release lanes in this worktree. No full
Lean/Mathlib build, full RISC0 workspace test/Clippy run, Kani campaign, solver
replay, guest rebuild or genuine receipt generation was performed for this
batch. Those missing qualifications remain explicit release obligations.

## Remaining V3 work

The subsequent [checked epoch accounting proof](ZENODEX_CHECKED_EPOCH_ACCOUNTING_COMPOSITION_20260905.md)
connects ordered signed-prefix aggregation to the existing balance, custody,
liability and reserve table relation. Its per-route premises and runtime
refinement limits remain explicit.

The repository's earlier genuine five-receipt qualification and its later
mounted isolated pipeline are distinct evidence subjects. The former covers an
older zero-custody profile. The latter reauthenticates commands and derives
allocation from a committed predecessor, but its retained integration fixtures
use synthetic RISC0 replies. The custody successor, new signature-verifier
release and any further changed selected guests need fresh image measurements
and genuine receipts under one exact profile.

Full V3 completion still requires selected semantics and complete positive and
terminal lifecycles across all twelve lanes; their complete allocation
producers; the four required routes; universal formal/runtime refinement;
actual route/epoch proof qualification; concrete writer fencing, migration,
restart and committed-delivery ancestry; independent release assessment; and
the corresponding product workflows. Existing policy-blocked and disabled
command surfaces remain interlocks and cannot count as completed features.

The original 103-capability floor and V3 claim ceilings remain unchanged.
Neither these test results nor the new theorem count establish formal-core or
whole-program completion. Runpod was unavailable during this continuation;
no guest builds or proof generation are reported here.

## Evidence regeneration

```bash
python3 -B -m experiments.v3_completion_followup_v1.render_evidence
```

This command pins declared source and test bytes only. It does not execute any
test or promote an observation into proof or publication authority.
