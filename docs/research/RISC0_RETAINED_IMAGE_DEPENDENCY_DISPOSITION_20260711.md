# RISC0 Retained-Image Dependency Disposition

Date: 2026-07-11

Status: superseded on 2026-07-12; retained as historical evidence

## Superseding Decision

The active V1 state-proof and recursive-v2 workspaces now pin `anyhow 1.0.103`.
The active dependency policy no longer permits an unsound-warning disposition.
The previous lockfiles, image IDs, and receipts remain historical evidence and
cannot authorize current proof generation, release, settlement, or production.

The active lock identities are:

```text
state_proof_risc0 Cargo.lock
d30f07417921c475d99826eb10a45c17ec059c88b53c3f835702f27b509442ba

recursive_stark_v2_risc0 Cargo.lock
45cd06efebd2a989b7a1061e4958a45520cec388fe0ac9f8987c16fe9a5fef64
```

The governing active policy is
`config/proof_profiles/risc0_dependency_audit_policy_v2.json`, SHA-256
`0a55219b1f250ffdd3469869b0152b7a928c987bc2cd67d0dedb79e2d2542356`.
Fresh image IDs and fresh receipt evidence are required before either workspace
can regain current proof-evidence status.

## Historical Decision

The V1 state-proof workspace retains `anyhow 1.0.100`. The recursive-v2
workspace retains `anyhow 1.0.102`. Both workspaces update `quinn-proto` from
`0.11.14` to `0.11.15`.

This is an exact, bounded exception for two historical guest identities. It
does not authorize either affected `anyhow` version for new proof-generation,
release, settlement, or production profiles.

The original machine-readable exception policy had SHA-256
`f4d1aa8bcd7fb19fe983ba797eb9cca5e273831d1418ef26c2f53640ac3d03ae`.
The later same-host V1 replay record used the superseded policy revision with
SHA-256
`8d7273e02a454f47813f0115f5a2fb2abc970841c60c3d16b7b0a44b41970fe5`.
Both are historical. The active policy identified above contains no unsound
disposition.
The checker rejects other workspace, category, advisory, package, or version
combinations and rejects unused dispositions. It also binds the exact lockfile
and rebuild-reference bytes, recomputes every referenced current source-file
identity and source-closure root, and rejects an affected `downcast_mut` token
in the governed repository source.

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

The historical counterfactual lock identities were:

```text
state_proof_risc0 Cargo.lock
f7d854a75aea4d9626719587bb8870d67a7891c9dfb93a28842df09bf934c4b1

recursive_stark_v2_risc0 Cargo.lock
8fb6d7f66790920e44278d56e33cff1c344dd15ca6c3f96f4abf2a727a7e9f23
```

The refreshed source closures are:

```text
V1
81f5dc170de45306b7427f8379ea23add429f5c6325a06c0bb4fa6c4315f78bf

recursive v2
20e5587e3ed7b8f6c561295a04f2cc2de92b90fd38c070de08a33d55b5f7572a
```

The canonical-path recursive-v2 clean-rebuild report is:

```text
a366d6e0d00f963c061cd7c9be9bbc531d6502f49950834f4297b773db05aeb1
```

## Reachability Review

The affected package remains dependency-reachable through RISC0 3.0.5 guest
and host crates. Package reachability therefore remains true.

The scoped function review found:

- no `anyhow::Error::downcast_mut` call in the exact V1 or recursive-v2
  workspace sources;
- no affected call in the exact dependent RISC0, Prost, or build-tool sources
  included by the rebuilds;
- no affected demangled symbol or string in any of the six V1 guest ELFs;
- no affected demangled symbol or string in the recursive-v2 guest ELF;
- no affected symbol in the rebuilt V1 static verifier or either recursive-v2
  verifier.

The July 12 V1 refresh repeated that review after strict JSON ingress,
closed-wire validation, and single-verification control flow changed the host
source. The 30-file closure contains no `downcast_mut` token. The current
static PIE verifier SHA-256 is
`8836f22431e2ce241eec9e6503f741b92673e2fec054208b0c36dea4f1bcf146`;
its demangled symbols and strings contain no affected function. All six guest
programs remained byte-identical to the retained reference, and none contains
the affected function string. No proof was regenerated.

For recursive v2, the compiler-input scan covered 3,843 Rust files. Its only
`anyhow` occurrence was the affected method definition inside the pinned
`anyhow` source. Other `downcast_mut` strings belonged to unrelated APIs.

This is bounded non-reachability evidence for the affected function in the
retained binaries. It is not a general proof that the dependency graph is safe.

## Promotion Boundary

The disposition is acceptable only while every condition below remains true:

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

Any new guest, source behavior, image ID, receipt generation, production claim,
or affected-function reachability requires `anyhow >= 1.0.103` and regenerated
proof evidence.

## Commands Executed

```bash
cargo audit --version
cargo audit --json --no-fetch --file <workspace>/Cargo.lock
cargo update -p anyhow --precise <retained-version> --offline
python3 tools/check_risc0_recursive_rebuild_evidence.py ...
python3 tools/check_risc0_recursive_v2_rebuild_evidence.py ...
nm -C <guest-or-verifier>
strings <guest-or-verifier>
python3 tools/check_risc0_dependency_audit.py --no-fetch
```

The rebuild commands used absent external target roots, pinned RISC0 3.0.5
tools, pinned Rust/Cargo 1.94.1, locked offline dependencies, and networkless
containers for the decisive canonical-path comparison.
