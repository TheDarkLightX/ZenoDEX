# RISC0 Retained-Image Dependency Disposition

Date: 2026-07-11

Status: historical for source-pinned retained-receipt verification; current
source uses patched `anyhow 1.0.103`

## Decision

The historical V1 state-proof identity retained `anyhow 1.0.100`, and the
historical recursive-v2 identity retained `anyhow 1.0.102`. Those exact
exceptions remain relevant only when verifying their source-pinned retained
artifacts.

The current source changes perps aggregation behavior, updates both workspaces
to `anyhow 1.0.103`, and removes both unsoundness dispositions. Historical
program and receipt identities are therefore pre-change evidence. They cannot
authorize a current-source proof claim.

The governing machine-readable policy is
`config/proof_profiles/risc0_dependency_audit_policy_v2.json`, SHA-256
`8151b95fce9764e26da463d0a2a6ca2bb75b7495debf6686dfae159611cceb81`.
The checker rejects other workspace, category, advisory, package, or version
combinations and rejects unused dispositions. The historical policy SHA-256
was `f4d1aa8bcd7fb19fe983ba797eb9cca5e273831d1418ef26c2f53640ac3d03ae`.

## Advisory

`RUSTSEC-2026-0190` marks `anyhow` versions below `1.0.103` as unsound. The
affected function is:

```text
anyhow::Error::downcast_mut
```

The defect can violate borrow rules when mutable downcasting follows attached
error context. Cargo Audit 0.22.1 reports this advisory under
`warnings.unsound`. The advisory database revision used for this disposition
is:

```text
1090288da789aaf84278006fad35a36bfcfcbd67
```

## Counterfactual Rebuild Result

The initial lock refresh changed `anyhow` and `quinn-proto` together. That
changed every V1 guest program and the recursive-v2 aggregate guest, which made
the retained receipts incompatible with the current image IDs.

Two isolated counterfactual rebuilds separated the dependencies:

| Workspace | Retained `anyhow` | Patched `quinn-proto` | Result |
| --- | ---: | ---: | --- |
| V1 state proof | `1.0.100` | `0.11.15` | all six program bytes and image IDs matched the retained reference |
| recursive v2 | `1.0.102` | `0.11.15` | program, raw ELF, image ID, and both verifier outputs matched the retained reference |

The current source lock identities are:

```text
state_proof_risc0 Cargo.lock
d30f07417921c475d99826eb10a45c17ec059c88b53c3f835702f27b509442ba

recursive_stark_v2_risc0 Cargo.lock
45cd06efebd2a989b7a1061e4958a45520cec388fe0ac9f8987c16fe9a5fef64
```

The historical retained-identity source closures were:

```text
V1
76a267fd6cbd51c8397073af5553d8a5877945dbf3d18cde2ac262c149366d50

recursive v2
20e5587e3ed7b8f6c561295a04f2cc2de92b90fd38c070de08a33d55b5f7572a
```

The canonical-path recursive-v2 clean-rebuild report is:

```text
a366d6e0d00f963c061cd7c9be9bbc531d6502f49950834f4297b773db05aeb1
```

Current post-guard source closures and guest images remain pending. The CBC
checker rejects the historical closure identities against current source.

## Reachability Review

For the historical retained identities, the affected package was
dependency-reachable through RISC0 3.0.5 guest and host crates. Historical
package reachability therefore remains true.

The scoped function review found:

- no `anyhow::Error::downcast_mut` call in the exact V1 or recursive-v2
  workspace sources;
- no affected call in the exact dependent RISC0, Prost, or build-tool sources
  included by the rebuilds;
- no affected demangled symbol or string in any of the six V1 guest ELFs;
- no affected demangled symbol or string in the recursive-v2 guest ELF;
- no affected symbol in the rebuilt V1 static verifier or either recursive-v2
  verifier.

For recursive v2, the compiler-input scan covered 3,843 Rust files. Its only
`anyhow` occurrence was the affected method definition inside the pinned
`anyhow` source. Other `downcast_mut` strings belonged to unrelated APIs.

This is historical bounded non-reachability evidence for the affected function
in the retained binaries. Current source no longer needs that exception. It is
not a general proof that the dependency graph is safe.

## Promotion Boundary

The historical disposition is acceptable only when replaying the exact
source-pinned retained artifacts and every condition below remains true:

```text
workspace identity is exact
advisory ID is RUSTSEC-2026-0190
warning category is unsound
package and version are exact
retained program and image identities remain exact
affected function remains absent from the scoped source and binaries
no secret input enters the lane
production_authority == false
settlement_authority == false
new_proof_generation_authority == false
```

Current source satisfies the `anyhow >= 1.0.103` requirement. Any new guest,
image ID, receipt, or proof claim still requires regenerated source and proof
evidence.

## Commands Executed

```bash
cargo audit --version
cargo audit --json --no-fetch --file <workspace>/Cargo.lock
cargo update -p anyhow --precise <retained-version> --offline
cargo update -p anyhow@1.0.100 --precise 1.0.103 --offline
cargo update -p anyhow@1.0.102 --precise 1.0.103 --offline
python3 tools/check_risc0_recursive_rebuild_evidence.py ...
python3 tools/check_risc0_recursive_v2_rebuild_evidence.py ...
nm -C <guest-or-verifier>
strings <guest-or-verifier>
python3 tools/check_risc0_dependency_audit.py --no-fetch
```

The rebuild commands used absent external target roots, pinned RISC0 3.0.5
tools, pinned Rust/Cargo 1.94.1, locked offline dependencies, and networkless
containers for the decisive canonical-path comparison.
