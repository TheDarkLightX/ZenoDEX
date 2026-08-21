# G1 RISC0 RunPod CUDA Evidence V1

Status: `TESTED_RESEARCH_ONLY`

Evidence head: `6aa4333cc6104136bb8a19b6207c53226e3b760b`

Proof evidence head: `6c0594b7e6fdf8fbfebc21d7e3b95ea1126f56c8`

Production authority: `NONE`

## Result

The RunPod replay closed the previously deferred real-proof work for the first
`ASSET_TRANSFER` module, its release-aware lane coordinator, and the bounded
global-epoch recursion shape. Every accepted proof returned a `Succinct`
receipt, matched its exact canonical journal, and verified under the expected
image ID.

The global-epoch boundary replay covered real receipt topologies at `1`, `8`,
`9`, and `64` commands. At evidence head `6aa4333cc`, isolated non-proving
preflight fixtures supply invalid boundary evidence at `0`, direct-path `9`,
aggregated-path `8`, and `65`. The zero fixtures clear every parallel command
vector, direct `9` retains direct-mode metadata, and aggregated `8` retains the
aggregated-mode marker.

## Environment

- GPU: NVIDIA L40S with 46,068 MiB
- driver: `570.124.06`
- CUDA compiler: `12.4`, `V12.4.131`
- Rust host: `rustc 1.90.0`, `cargo 1.90.0`
- RISC Zero: `cargo-risczero 3.0.6`, `risc0-zkvm 3.0.6`
- prover selection: `RISC0_PROVER=local`, host feature `cuda`
- sampled peak GPU use: 100% compute, 68% memory controller, 13,703 MiB
  framebuffer

`/root/zenodex-target` was used because `/dev/shm` was mounted `noexec` and the
network-backed workspace was unsuitable for linker output. Before the largest
run, the root volume had 42 GB free and 1% inode use.

## Real proof matrix

| Statement | Source | Receipts | Test time | Result |
|---|---|---:|---:|---|
| Asset module | `f574f677c` | 1 | 37.53 s | PASS |
| Release-aware asset lane | `5d3bc1928` | 2 | 99.46 s | PASS |
| One-command epoch statements | `6c0594b7e` | 3 | 24.71 s | PASS |
| Eight-command direct boundary | `6c0594b7e` | 9 | 87.49 s | PASS |
| Nine-command fanout crossing | `6c0594b7e` | 12 | 117.54 s | PASS |
| Sixty-four-command maximum | `6c0594b7e` | 73 | 748.41 s | PASS |

The asset workspace did not change from `f574f677c` through the evidence head.
The lane workspace did not change from `5d3bc1928` through the evidence head.
Exact source and lockfile hashes are recorded in the adjacent JSON artifact.

The release-aware lane replay also produced verified-lane binding root
`0x8afbb9391f2f4fa0e850253aaf0093b14c7e848ff51d000d3bb6e02f3fa30877`.

## Method bindings

| Method | Image root | Generated method `.bin` SHA-256 |
|---|---|---|
| Asset transfer | `0x8e9974a15d41c8c379513af03ab1750c6c5a23ad4299c94fb8c3ebb29ceb5df2` | `4affdf1877192a51fff973aab9051aaeb36eb548f650baa7e82882bbabd68283` |
| Asset lane | `0x5174cfd94e4577be2c342bb9eca6f6d23f72c3a0d08f05bda57101c0cb55947d` | `a555abc0a29c02942df847d2e4b3fb2dfac2b7b2a07a9888945b395c3e3bf157` |
| Economic epoch | `0x0b2bbc04abe3cf8839c6e7763fcb403b5f3ba9473c07efe66f47e815e0435331` | `6ea9191aa391a1961692e18825aa2380ed173715d252bb7aa465cb6bddaee5b2` |
| Quarantined structural leaf | `0xbce4d1087bba50d24e26848a83740cb3a41019e8af90d81f4bfd088059024a40` | `838b14b0ce37e50b949c31f748b282b6b71c788efea184c3a174dba3bd91bf02` |

The structural leaf merely commits supplied journal bytes. Its only purpose is
to exercise recursion, ordering, fanout, exact-assumption resolution, and root
compression. It supplies no economic or release authority.

## Non-proving gates

- global epoch at proof evidence head: 12 passed, 0 failed
- post-review global-epoch shared boundary suite at evidence head: 9 passed,
  0 failed
- asset transfer: 7 passed, 0 failed
- asset lane: 7 passed, 0 failed
- warning-denying clippy: passed for all three workspaces with
  `--workspace --lib --tests -- -D warnings`; this lint scope covers host,
  shared, and integration-test Rust targets and excludes zkVM guest binaries
- formatting and `git diff --check`: passed

An exploratory `cargo test --all-targets` command was unsuitable because that
flag explicitly asks Cargo to execute zkVM guest entrypoints as native Linux
targets. The guest syscall boundary aborted as designed. The valid broad test
gate uses `--lib --tests` and passed. A CUDA-enabled clippy run was stopped while
redundantly rebuilding native PTX kernels; the CUDA feature had already compiled
and executed in the stronger real-proof runs. Clippy then passed over the Rust
host, shared, and integration-test surfaces with guest builds skipped. No
separate native guest-binary lint claim is made; the real proof builds and
executes the guest through the RISC Zero toolchain.

## Claim boundary

- No production authority, profile activation, settlement mount, writer
  rotation, or value-moving publication authority.
- No persisted release receipt or Groth16 receipt.
- No throughput, production resource ceiling, crash-safe publication,
  migration, or whole-economy proof claim.
- The real economic proof covers one `ASSET_TRANSFER` transition shape and its
  lane composition. Other M6 value-moving lanes remain separate obligations.
- The 64-command replay validates bounded recursive topology using quarantined
  structural leaves. It does not prove 64 economic commands.
