# ZRPF prover compute qualification V1

Date: 2026-07-14

Status: authority-neutral operational plan

## Decision

An H100 is not required for proof validity. A valid RISC Zero receipt can be
produced by the CPU prover, Metal, or a compatible CUDA prover. Hardware changes
latency and cost. It does not change the statement or verification result.

One H100 80 GB is the first remote qualification target for the final bounded
V6/V7 evidence chain. No evidence currently supports a multi-H100 requirement.
The chain must first be measured by execution-only cycle profiling and one
small real CUDA proof. A full paid run is forbidden until those checks close.

## Current machine facts

The local Linux workstation reported:

```text
GPU: NVIDIA GeForce GTX 1060 3GB
compute capability: 6.1
VRAM: 3072 MiB
CUDA compiler: 12.0
installed RISC Zero r0vm: 3.0.5 CPU release
installed r0vm bytes: 108,998,816
installed r0vm SHA-256:
36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b
```

The 3 GB GPU is below the memory range recommended for ordinary local RISC
Zero proving and is not an H100 build target. It may be used for a separately
scoped CUDA-path smoke test. It is not the final proof machine.

The 128 GB Apple M3 laptop run remained CPU-bound and produced no result after
30 minutes. No governed cycle or stage record was captured. That observation
disqualifies the tested Apple CPU route for this evidence run. It is not
evidence about a Metal prover because the executed process did not establish
Metal use.

The prior Linux CPU run exceeded 12 hours without completing its target. Its
installed `r0vm` was CPU-only. That run does not predict H100 latency.

## Exact RISC Zero topology

RISC Zero 3.0.5 supports the following external-prover path:

```text
RISC0_PROVER=ipc
  -> exact RISC0_SERVER_PATH
  -> r0vm --port on loopback
  -> selected ProverOpts
  -> RV32IM or recursion prover
  -> CUDA HAL when the exact r0vm was compiled with cuda
```

Official source anchors:

- <https://github.com/risc0/risc0/blob/v3.0.5/risc0/zkvm/src/host/client/prove/mod.rs#L167-L193>
- <https://github.com/risc0/risc0/blob/v3.0.5/risc0/zkvm/src/host/client/prove/external.rs#L42-L57>
- <https://github.com/risc0/risc0/blob/v3.0.5/risc0/circuit/rv32im/src/prove/mod.rs#L45-L53>
- <https://github.com/risc0/risc0/blob/v3.0.5/risc0/circuit/recursion/src/prove/mod.rs#L82-L90>
- <https://github.com/risc0/risc0/blob/v3.0.5/risc0/r0vm/Cargo.toml#L59-L65>

All seven current ZRPF proving commands call `default_prover()` with Succinct
options. The handoff therefore uses the same exact IPC mediation for source,
adapter, leaf, L1, L2, settlement, and V7 proving.

## Implemented execution-only profile

The V7 harness now has an exact `--profile-only` mode. Proof and profile modes
share one preparation path. That path verifies the exact V6 settlement child,
recomposes the expected V7 journal, constructs the same framed executor input,
and then either proves or executes without proving.

The canonical execution record binds:

```text
program bytes and image ID
exact guest-input bytes
ordered assumption receipt identities
expected and observed journal identities
receipt-claim digest
segment limit and ordered segment rows
user cycles and padded cycle capacity
exact r0vm bytes
compute-profile request ID
```

Every proof, accelerator, release, settlement, and production authority field
is fixed to false. An independent Python checker reopens the exact program,
input, assumptions, and `r0vm` and rejects substitution, noncanonical JSON,
reordered segment rows, integer/Boolean ambiguity, and authority promotion.

The remote handoff schedules execution profiles before source and V7 proving
and rechecks each profile as a proof-stage precondition. These are bounded
workload records. CPU execution cycles do not measure Succinct CUDA proving
time.

## CUDA r0vm build contract

The paid runner must not compile its prover during the billed proof window. A
governed build should produce the CUDA `r0vm` before the H100 is allocated.

Required source identity:

```text
repository: https://github.com/risc0/risc0
tag: v3.0.5
commit: 8eb06ab020a92dc5b63ba6dd0836d432aba6d890
package: risc0-r0vm
features: cuda,disable-dev-mode
Rust toolchain: 1.89
```

Required build form for H100:

```bash
NVCC_APPEND_FLAGS='--generate-code arch=compute_90,code=sm_90' \
cargo build \
  --locked \
  --release \
  -p risc0-r0vm \
  --no-default-features \
  --features cuda,disable-dev-mode
```

The final build record must also bind:

```text
Cargo.lock SHA-256
complete dependency-source root
builder OCI image digest
CUDA toolkit and nvcc versions
NVCC flags
host target and linker
output byte length and SHA-256
runtime dependency root
source archive root
```

Once the build record is accepted, create the CUDA handoff with the resulting
artifact identity:

```bash
python3 tools/plan_zrpf_remote_reproof_handoff_v2.py plan \
  --repository <clean-worker-checkout> \
  --c0-commit <C0> \
  --worker-commit <governed-worker-commit> \
  --prover-compute-profile \
    risc0_ipc_cuda_single_visible_device_build_request_v1 \
  --prover-r0vm-sha256 <cuda-r0vm-sha256> \
  --prover-r0vm-bytes <cuda-r0vm-byte-length> \
  --output <handoff.json>
```

The planner rejects the known official CPU-only `r0vm` identity for this CUDA
profile. A distinct hash is still only a byte identity. Source-to-binary CUDA
provenance and live accelerator use remain separate required evidence.

RISC Zero's CUDA build defaults to `-arch=native` when no NVCC flag is set.
Building on the GTX 1060 with that default would target the wrong architecture.

## Paid-run gate

Let:

```text
B = remaining dollar budget
P = actual pod price in dollars per hour
T_budget = floor(3600 * B / P)
```

The public RunPod prices inspected on 2026-07-14 put a single H100 near the
range where a four-dollar balance buys roughly 80 to 120 minutes. The console
price at deployment time is authoritative for cost routing.

Before the full chain, perform these bounded stages:

1. Freeze the exact ZenoDEX source and build all guest and host artifacts.
2. Produce and validate the governed CUDA-r0vm build record.
3. Execute every guest without proving and record cycles, segment count, and
   per-segment `po2` values.
4. Start one H100 pod from a digest-pinned image with one visible GPU.
5. Verify compute capability 9.0, VRAM, driver, container, and exact r0vm hash.
6. Run one source-leaf Succinct proof under the initial attempt deadline.
7. Stop the pod and preserve artifacts whether the proof succeeds, fails, or
   reaches the deadline.

The implemented `zrpf_initial_paid_calibration_attempt/v1` checker permits one
initial attempt only. It remains `UNKNOWN` unless it binds all of:

```text
stage execution profiles
CUDA r0vm source/build record
single-H100 hardware and runtime preflight
the exact source-proof execution packet
integer-only price, budget, and deadline arithmetic
```

The attempt budget is capped at 4,000,000 microusd and the proof deadline is
capped at 1,800,000 milliseconds. The worker recomputes the qualification from
its private packet and input snapshots, requires byte-exact agreement with the
checker output, and applies the resulting deadline before launching the proof
command. A valid execution profile alone cannot start paid proving.

The checker result is a public, canonical protocol record. Its inputs must
contain no credentials or secret workload data. The result carries governed
content identities and selected public hardware, price, and deadline facts; it
does not carry input filesystem paths or raw input-file contents. A dedicated
negative test uses a unique private-path sentinel and requires it to remain
absent from stdout.

The checker does not authorize a continuation or additional spend. A later
continuation design requires direct verification of the completed receipt and
worker-owned live GPU telemetry. Caller-supplied booleans or projected
remaining time are insufficient.

Pod allocation, setup, and deallocation occur outside the checker. The cloud
controller must enforce an independent pod TTL from allocation time. The
30-minute proof deadline is not a bound on total cloud billing. The controller
TTL also owns a process-launch or pre-exec stall because Python's subprocess
timeout begins only after process creation returns. The worker rejects a
completed command whose total measured elapsed time exceeds its bound, while
the external TTL provides the active stop boundary during launch.

The H100 worker environment is:

```text
RISC0_PROVER=ipc
RISC0_EXECUTOR=ipc
RISC0_SERVER_PATH=<private packet-pinned CUDA r0vm>
CUDA_VISIBLE_DEVICES=0
```

The CPU fallback environment fixes `CUDA_VISIBLE_DEVICES=-1`. Ambient Bonsai,
dev mode, local prover, server path, and GPU-count variables do not cross the
worker boundary.

## Interpretation of the old runtime

The earlier twelve-hour CPU result shows that the present CPU route is not an
acceptable operational proving path for the expensive stage. It does not show
that the proof is intractable, and it does not show that an H100 will finish
within the remaining budget. The missing variables are the exact cycle count,
segment profile, and CUDA-stage measurements.

RISC Zero's published performance material shows that proving cost grows with
execution cycles and that memory can be traded against continuation segment
size. Those tables are hardware- and version-specific. They are useful for
capacity planning after the ZRPF cycle profile is known, not as ZRPF evidence.

## Authority and non-claims

This qualification plan and every compute capture remain authority-neutral.
They do not establish:

```text
CUDA source-to-binary provenance before the build record exists
GPU use before the live telemetry control passes
an H100 latency guarantee
a multi-GPU requirement
proof validity from timing or telemetry
fresh V6/V7 receipts
release authority
settlement authority
production readiness
```

Receipt verification under the governed program, profile, and journal remains
the proof authority boundary.
