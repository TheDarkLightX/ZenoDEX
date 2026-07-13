# ZRPF V6 Identity Executor Security Review

Date: 2026-07-13  
Reviewed commit: `9b147dcbaa4e5765bc098de25b04d3e62e094498`  
Disposition: request changes before using the executor as candidate identity
evidence

## Scope

This review covers the authority-neutral Spot V6 identity rebuild executor,
its private Git snapshot, the no-network Docker build runner, its deterministic
repin chain, and the observation checker.

The executor is intended to establish a candidate source-to-program identity
chain. It does not generate proofs, verify receipts, or grant release,
settlement, or production authority.

## Blockers found

### Complete live source inventory was missing

The source snapshot root hashed the frozen Git entry list. It did not enumerate
the live snapshot tree. Unknown compiler-visible files could therefore be added
without changing the observed root.

An adversarial probe added persistent `.cargo/config.toml` and
`evil-wrapper` files during the first build. The full primary, two-pass, final,
and host-verifier sequence completed, and the checker returned
`candidate_repin_chain_observations_validated` while both undeclared files
remained in the snapshot.

A separate probe modified a tracked source file after one post-build check and
before the next stage. The next stage accepted the new root because the
executor did not maintain an exact expected state-transition chain.

Required closure:

```text
exact expected live file map
  -> complete lstat inventory
  -> reject unknown files, symlinks, special files, and unsafe hardlinks
  -> prove each governed mutation changes only declared paths
  -> require every build pre-root to equal the expected current root
```

### The run-root parent was not trusted

The executor required an absent, canonical, external run-root path, but it did
not require the parent directory to have trusted ownership and permissions. A
non-sticky world-writable parent was accepted. Another user with write access to
that parent could rename or replace the private child run root.

Required closure includes stable parent and run-root directory identities,
safe ownership and mode checks, descriptor-relative creation, and rejection of
group- or world-writable parents for this profile.

## Further candidate-evidence requirements

### Toolchain and dependency input stability

The Docker runner authenticated `cargo`, `rustc`, `r0vm`, and
`cargo-risczero` once, then reopened mutable path directories for later builds.
The Cargo registry was not represented by a complete input root. A stable
substitution across both build passes could therefore produce a checker-accepted
candidate while the report retained the original tool identities.

The minimum candidate gate must reauthenticate stable tool and dependency-input
identities before and after every build. It must retain these nonclaims:

```text
same_uid_resistance = false
complete_build_input_closure_verified = false
source_to_program_binary_provenance_verified = false
```

Release authority requires immutable, content-addressed compiler, sysroot,
linker, dependency, and runtime inputs, preferably in a root-owned read-only
filesystem or a governed build image.

### Bounded writable build storage and verified cleanup

CPU, memory, process count, network, console output, and wall-clock execution
were bounded. Writable target and output bind mounts had no byte quota. A build
script could exhaust the host volume.

Failure cleanup also ignored Docker removal errors and did not confirm that the
container became absent. A surviving container could continue consuming
resources after executor cleanup.

The minimum candidate gate requires quota-bounded writable build storage and a
fail-visible remove-and-inspect-to-absent teardown contract. Cleanup failure
must retain the container identity for operator remediation.

### Build-job claim precision

The outer Cargo configuration used two jobs, while closer workspace Cargo
configuration could request eight jobs for nested RISC0 builds. The two-CPU
container limit remained effective. Evidence must either enforce the nested
job count or identify the field as the outer-job setting rather than claiming
that every nested build used exactly two jobs.

## Positive findings

- Governed commands and paths were reconstructed from exact plan constants.
- Shell arguments were quoted, and no command-injection path was found.
- Repin parsing was narrow, exact-width, and rejected ambiguous declarations.
- Output artifacts were reread as bounded regular files and cross-checked
  against runner-reported size and hash.
- The build image was digest-pinned, with no network, a read-only root,
  dropped capabilities, `no-new-privileges`, a fixed unprivileged user, and
  CPU, memory, PID, output, and time bounds.
- Observation and report encodings were canonical and exact-field checked.
- All proof, receipt, release, settlement, production, complete-closure, and
  source-to-binary authority fields remained false.

## Required negative controls

Before the executor can again produce candidate identity evidence, tests must
reject:

1. an unknown Cargo configuration file;
2. an unknown executable wrapper;
3. an undeclared tracked-file change between stages;
4. a group- or world-writable run-root parent;
5. a tool replacement before or during a build;
6. a dependency-input mutation;
7. target or output quota exhaustion;
8. failed container removal or a container still present after removal.

## Evidence run during review

```text
executor tests: 17 passed
planner tests: 16 passed
Ruff: passed
Mypy: passed
git diff checks: passed
security red-flag scan: no advisory findings
```

The three adversarial probes described above were accepted by the reviewed
revision. They are counterexamples to the executor's candidate identity claim
and justify this request-changes disposition.

## Promotion boundary

After the minimum fixes, the executor may support this narrow claim:

> A bounded candidate identity rebuild used an exact governed source-state
> transition chain and stable observed build inputs under the recorded local
> isolation profile.

It still may not support cross-host reproducibility, proof regeneration,
source-to-binary release provenance, release authority, settlement authority,
production authority, privacy, same-UID resistance, or covert-channel freedom.
