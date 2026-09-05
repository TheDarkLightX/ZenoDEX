# V3 remote receipt qualification jobs

Status: genuine structural receipts passed the measured bridge and all 16 checks.
The first native ASSET_TRANSFER receipt passed all 17 measured-bridge and
endpoint controls. A final-source rebuild remains separate from that frozen
qualification subject.
This note is research evidence. It selects no release, active profile, writer,
balance migration, or publication authority.

## Exact statement and scope

W03 first exercises the existing epoch guest with its quarantined structural
test leaf. The leaf commits supplied bytes. The epoch guest validates its input
structure and resolves the exact child-image and journal assumption. Neither
guest proves an ASSET_TRANSFER transition. The structural result qualifies
this cryptographic bridge slice and does not itself establish economic module
qualification or W06 publication.

The test exporter reuses the retained `host/tests/real_composition.rs` fixture.
It creates three genuine Succinct receipts: a structural child, the composed
epoch, and a foreign structural guest committing the same epoch journal.
The last case isolates image binding from journal mismatch. A fake receipt,
a corrupt seal, and malformed encodings are negative controls only.

The selected Rust endpoint verifies the actual rebuilt epoch ELF image, exact
journal bytes, successful execution, empty assumptions, and Succinct receipt
kind. The Python adapter measures and seals the ELF executable before launch.
Neither component admits a policy or publishes state. The process, operating
system, dynamic loader, linked libraries, cryptographic implementation, and
configured binary provenance remain trusted assumptions.

## Source and artifact subjects

The plan commit is `bde0fac341f312b8b12b96d0bf1477a7091cdc3f`.
Implementation files were uncommitted when this job was prepared; the file
manifest, rather than the plan commit, identifies the uploaded implementation.

Initial upload contains 32 files, totaling 56,342 compressed bytes: the tracked
`zk/global_economic_epoch_risc0` workspace, its new verifier endpoint/protocol
and structural exporter, the Python adapter and package initializers, and the
job runner. It excludes credentials, Git history, local agent state, unrelated
economic lanes, and build caches.

```text
source.sha256 file SHA256:
8ef8abc0c9465a87f92096b0fc4311788d5bc53129d0b5b23cecaa48f6132d5e
source.tar.gz SHA256:
328e5b2772a08b6eaa5620f976b7ba295f3a292283451c85e41ea4b7af3c2d44
```

The upload was initially blocked by automatic approval review with the reason:
"This uploads a private source bundle to an external Runpod host; the user
authorized remote proof work but did not specifically authorize exporting this
source payload to that destination." The original transfer was paused. The
user subsequently explicitly approved that exact bundle and authorized useful
work on the supplied Runpod host. The retry used the same archive hash.

## Environment and bounded execution

The user-provided container was observed on 2026-09-04 local time with Ubuntu
22.04.5, x86-64 Linux, NVIDIA L40 with 46,068 MiB VRAM, driver 580.178.04,
CUDA compiler 12.4.131, cgroup CPU quota 27.2 cores, and memory limit
249,999,998,976 bytes. The host-visible CPU and RAM totals exceed those cgroup
allocations. The container filesystem initially had about 111 GB available;
`/workspace` was mounted separately. Its filesystem-wide free-space report
does not establish the user's storage quota.

Host Rust is pinned to 1.90.0. The initial planned guest component was 1.94.1;
retained build outputs establish that another job's shared-default update
caused the actual compilation to use 1.97.0. The SDK and build crates remained
locked at 3.0.6. The guest compiler has its own version. The successful receipt
evidence is tied to the actual 1.97.0 build and retained ELF, with no claim
that the intended 1.94.1 pin held.
Local proving uses `risc0-zkvm/cuda`, which implies `prove` in the pinned SDK,
and `RISC0_PROVER=local`. No external proving service is selected.

RISC Zero supports x86-64 Linux and recommends individually pinned components
for CI. Its sample version numbers are examples, not the project's pins.
[Official installation documentation](https://dev.risczero.com/api/zkvm/install).
Build and proof costs depend on guest workload and acceleration; this job's
actual measurements determine its evidence, not old benchmark timings.
[Official benchmarks](https://dev.risczero.com/api/zkvm/benchmarks).

The runner sets eight Cargo, CMake, and Rayon workers; selects one GPU;
requires 40 GiB initially free; caps each output file at 2 GiB; and uses two
one-hour build deadlines and a thirty-minute proof deadline, each with a
thirty-second termination grace period. The existing container cgroup bounds
memory. These are job controls, not proven minimum hardware requirements.
There is no provisioner, cleanup command, credential upload, or automatic
publication in the runner. Preserve outputs before releasing the host.
Runpod storage persistence depends on the storage type and Pod lifecycle.
[Official storage documentation](https://docs.runpod.io/pods/storage/types).

## Replay and acceptance

After installing the pinned toolchains and native compiler prerequisites on an
authorized host, extract the reviewed source archive into a new directory with
`tar --no-same-owner`. Native prerequisites include GCC/G++, CUDA nvcc, CMake,
pkg-config, OpenSSL headers, protobuf-compiler, and libclang development files.
Invoke from that source root, using an output directory that does not exist:

```bash
bash tools/run_whole_program_v3_remote_receipt_job.sh \
  source.sha256 /workspace/zenodex-receipt-evidence/run01
```

The script checks every manifest hash before and after execution. It first
builds and preserves the verifier without CUDA dependencies, then builds and
runs only the explicitly selected ignored structural exporter with CUDA.
It exports both guest ELFs, their independently recomputed image IDs, exact
epoch journal, postcard input, receipts, request/response frames, artifact
SHA256 values and sizes, source manifest, logs, and `qualification.json`.

The measured Python bridge must accept the genuine epoch receipt for its exact
image and journal. It must reject wrong journal, requested image, configured
image, executable hash, unavailable executable, genuine foreign-image receipt
with the same journal, fake receipt, corrupt seal, malformed receipt, truncated
receipt, and trailing bytes. Separately constructed process frames check the
Rust endpoint's success response and precise foreign, fake, corrupt, and
malformed rejection classes. A passing direct process check cannot substitute
for the sealed Python launch. Transport fixtures never count as cryptographic
evidence.

No success report is produced until every case passes. Failure logs are retained
and require diagnosis; zero-image placeholders, dev proofs, unavailable tools,
and skipped guest builds cannot produce qualification.

## Remaining obligations

The structural proof and bridge results below leave the existing
`zk/asset_transfer_module_risc0` and `zk/asset_lane_coordinator_risc0` guests
requiring source-specific integration and genuine receipt qualification, followed
by route and epoch proof composition. They were initially absent from the
sparse worktree; their presence in the Git tree corrects the initial discovery
gap. Store authenticity, current-head admission,
allocation continuity, release policy, publication atomicity, restart authority,
and whole-program safety are outside this structural job.

Local preparation checks: `bash -n` on the runner, Rust formatting on the
exporter, and the focused red-flag scan passed. No local heavy build was run.

## Retained build observations

The first build failed when LLVM attempted to write a proc-macro shared object
on the mounted network filesystem. Its output and logs were retained. The
unchanged source then built the verifier successfully on the container's
ordinary filesystem. Use that filesystem for Cargo target output and copy the
compact evidence back to persistent storage after qualification.

The resulting CPU verifier is about 2.6 MiB with SHA256
`e3dfc37fc64134a087d1a0790ae671f8c697b1ba2ab58f34ee211a79d038a096`.
This executable passed the genuine receipt qualification below. The actual Python
adapter also successfully launched a sealed `/usr/bin/true` executable on the
remote host. That observation establishes transport compatibility only.

The first CUDA dependency build found a missing `protoc`. The native
protobuf-compiler and libclang prerequisites were then installed. That failure
and its logs remain retained. The cached CUDA exporter retry compiled
successfully in 8 minutes 54 seconds. The three genuine Succinct receipts then
completed in 3.29 seconds. All 16 measured-bridge and endpoint checks passed.
The retry explicitly sets `RISC0_BUILD_LOCKED=1` so nested guest Cargo commands
also require the lockfile. The reviewed script's CUDA and verification tail is
reused verbatim, with a separate retry log and the same source manifest.

The rebuilt epoch image observed in generated methods is
`0x0b2bbc04abe3cf8839c6e7763fcb403b5f3ba9473c07efe66f47e815e0435331`.
It differs from the historical README image. This job requires verification
against the actual rebuilt method; it makes no historical image equivalence
or compatibility claim.

The read-only GPU trace retained 239 samples, with observed peaks of 54 percent
utilization and 4,759 MiB allocated. These samples establish activity for this
run; they are not throughput benchmarks or minimum-memory measurements.

```text
qualification.json SHA256:
14ca1bba6a679059b067d3944cc5ee8536a89dd8a09b1fa996ebda786f0f39fe
structural-qualification-v1.tar.gz SHA256 (2,303,135 bytes):
b149d69a4f2425fc12797b7806e1a59652fab0c36196708b228ca7198d7b7dd5
epoch receipt SHA256 (274,264 bytes):
cd6f0eed1bdd97b3e71397a81f5e8092df11340436cd13125496c4e50d0977aa
epoch journal SHA256 (1,556 bytes):
9d98a3da05c794e399b426eb24ba50c6cda6ef9e8cf15cc94df1adcafd01cef5
epoch ELF SHA256 (285,728 bytes):
6ea9191aa391a1961692e18825aa2380ed173715d252bb7aa465cb6bddaee5b2
```

All 12 archived artifact lengths and hashes were independently rechecked after
download. A separate immutable provenance sidecar retains the actual compiler
paths from generated build outputs and the compiler executable hash:

```text
actual-toolchain-v1.tar.gz SHA256 (1,207 bytes):
503f8ade694e8bf0ff46810306587dac9bd238a680c440a3abdbd209e3edff16
actual guest rustc 1.97.0 executable SHA256:
288ee1994dd8ec08184686e7a52b779c9b075498ffe73003884fefe60389c351
```

The original evidence archive remains unchanged. Its startup compiler
observation described the 1.94.1 rustup alias; the sidecar corrects that
observation with actual build selection. Future runner executions construct
a separate `RISC0_HOME` from a known version-only configuration, select the
installed 1.97.0 directory explicitly, and check the compiler executable hash.
They do not alter another job's default. The initial successful runner and
verifier remain preserved in the source archive; later helper factoring and
runner changes require their own binary measurement and replay.

The installed rzup library ignores symlinks at the version-directory level.
The isolated selection therefore uses a real version directory whose children
link to the exact installed public compiler directory. The runner checks its
rustc executable hash. Compiler libraries, Cargo, native tools, and the
operating system remain trusted build inputs.

## Resolved dependency closure limitation

The archived workspace lock contains 371 packages and omits optional CUDA
prover dependencies. Despite `--locked`, the successful host build resolved
those dependencies. This behavior was reproduced with offline Cargo metadata
on an ordinary filesystem: the lock hash stayed unchanged while metadata
contained 535 packages, including 529 registry packages. Consequently the
source lock alone does not establish this build's complete dependency closure.

The retained metadata explicitly records the CUDA/prove feature graph. Each
of its 529 cached registry archives was hashed and matched to the checksum for
that exact version in the cached crates.io index. The resulting observation
is `resolved-cuda-dependencies-v1.json`, SHA256
`4f66b7b1bca056b6b3ef876e1bb742051956bb863e6275799239e133baff8a07`.
The metadata SHA256 is
`70cfe1abf8a6fd0651888c7f2beeb98e6c682e5da622f88e65f797315629e060`.
The host Cargo executable hash matched the local official 1.90.0 executable:
`51de284e8bb0d03dcee595a0fb1cb3a952fe9e7e4b953a8b1467b7f71725b561`.

This is an observed dependency resolution, including platform packages that
need not have been compiled. Future guest manifests must declare the CUDA
feature and retain a reviewed complete lock for that resolution. The initial
cryptographic acceptance result does not close dependency-pinning or release
qualification obligations.

## First retained native ASSET_TRANSFER receipt

The next source bundle contains 225 files from the epoch, module, coordinator,
and global ABI workspaces, the shared verification endpoint, Python bridge,
and runner. Its Git context is
`9e1531539a5a25a7e1a55c70db014bc18dc1dd62`; uncommitted endpoint and exporter
files are identified by the complete file manifest. Later ABI changes are
outside this frozen subject.

```text
source archive SHA256 (551,671 bytes):
cfb5eff1db86aca0d7f8110a336934fdf01b60a8b6c756a33f4bd57be8cf4ed6
source manifest SHA256:
8f6aea98e8ba956e4d4ba5e6a50179e2ccd866a4bdaa20c734ba4e33f4d77888
```

The ignored `export_real_asset_transfer_bridge_receipt_v1` test reuses the
existing accepted-transfer fixture: Alice starts with 100 atoms, Bob with 10,
and treasury with 5. The command transfers 30 atoms and charges a 2-atom fee.
The guest executes the existing module transition and proves its exact journal.
The fixture supplies the context and prestate; neither their authenticity nor
a signature or publisher admission is established by this test.

The authorized CUDA run began at 2026-09-05 04:09:24 UTC. With eight workers and
the prior Cargo-managed cache, its build finished in 2 minutes 10 seconds.
The real Succinct proof, native Rust verification, negative seal check, and
artifact export then passed in 8.57 seconds. Receipt encoding remains the
existing native `serde_json` encoding. Both genuine and negative-control
receipts, canonical input, accepted state, exact journal, and ELF were retained.

```text
module image:
0x01a30913b8ad85743c155c7503a85cd0972ef76c0ed3ba75b822593d94c1ffe4
module ELF SHA256 (534,568 bytes):
087777a763c95b1be9d04de592e3a3594a667a6f1b8401072d5330afa3b7de66
module receipt SHA256 (589,091 bytes):
d70553406aee7314fd522c6f6c80851599b7d5d5dcb797c3d422ff730ab1fcf3
module journal SHA256 (1,015 bytes):
974d6c3960ee2ee8c5f37b22d9b4b8eac988fa8e94d74c0442bfefb80fdd7969
module input SHA256 (1,454 bytes):
26d63edc8d1d3517f8b6bc9495672c2a54713ccc57d12e3aa6082329e1423237
CPU verifier SHA256:
6747f55562cc9606b370093590feab9a796509fb62682e8fca1cb2ed99377735
native qualification report SHA256:
d9489b65430172f9a473a850212022f6aced844b042521dca5b3ca70b1251fde
native evidence archive SHA256 (3,911,626 bytes):
e24dd488241854fc9a3ed2f6a754114b85a0f4c90043400ddeec0efdc9184162
```

The new shared endpoint uses a statically supplied decoder. The native module
and coordinator wrappers accept only their existing producer's exact JSON
encoding. The epoch and root wrappers select canonical postcard. No caller
selects or negotiates the codec or compiled guest image. Seven module endpoint
tests passed, covering frame bounds, placeholder rejection, fake receipt kind,
and exact native encoding. These unit tests do not establish cryptographic
acceptance. The retained real receipt is the positive control for the measured
Python replay, which passed all 17 controls. The measured bridge accepted the
genuine receipt and rejected wrong journal, requested and configured image,
fake and corrupt receipt, malformed or truncated receipt, trailing bytes,
noncanonical JSON whitespace, postcard codec mismatch, wrong executable hash,
and unavailable verifier. Four direct endpoint checks separately observed
the exact rejection classes for fake, corrupt, noncanonical, and wrong-codec
receipts. The independent successful frame and response were retained.

A genuine foreign-image receipt in native JSON has not yet been exercised
against this module executable. The prior structural job's foreign-image
result belongs to its separately measured postcard endpoint. Unit tests or
the prior executable's result do not silently promote this missing control.

The module CUDA metadata observation contains 534 packages, with SHA256
`4031d8792d0fed8213e453fa6e7f1859fef5a4221b305fd1736ba8d271d013c7`.
The uploaded source manifest still passed before and after that metadata
observation. The lock-only dependency-closure limitation above remains open.
The module job selected the isolated 1.97.0 guest compiler explicitly and
retained the generated methods build outputs. No shared toolchain default was
changed.

The archived GPU trace contains 44 samples within the recorded module run,
from 04:11:35.223 to 04:11:43.875 UTC. Its observed peaks were 100 percent GPU
utilization and 13,831 MiB. Later samples are excluded from this module result.
All 529 registry archives in the module metadata matched the earlier retained
exact-version checksum report; there were no unmatched packages. The compact
archive was downloaded, and all ten qualification artifact hashes and lengths,
the verifier hash, and the source manifest hash were independently rechecked.

The coordinator's historical fixed module image differs from this rebuilt
image. Its candidate replacement uses the subsequent ABI-frozen module below.
Replacing the pin changes the coordinator statement and requires new
coordinator image and composition evidence. Existing journals, native receipt
codecs, historical Git subjects, and publication authority are not reinterpreted
by this qualification work.

## Final ABI module rebuild

The final ABI update includes the checked public allocation relation and its
unchanged-history guard. The history guard is committed at `7b2467067` and
requires `current.history_root == predecessor.history_root` under the existing
typed rejection. Its proof and runtime scope belong to the allocation work;
this job measures the resulting module executable without attributing that
global relation to an accepted-transfer guest that does not invoke it.

The source amendment contains those two ABI Rust files, the regenerated
allocation fixture, and a second ignored structural exporter. That exporter
can prove a bounded supplied journal under the existing quarantined leaf and
retain both native JSON and postcard encodings for foreign-image negatives.
The remaining 222 files match the prior bundle exactly. All 226 source hashes
were checked after applying the amendment to a fresh source copy.

```text
four-source-file amendment archive SHA256 (27,416 bytes):
9fd09052bf218c862608540a2f5b9f6121c4ad26d08ba70196386789ccca7ff0
complete final source manifest SHA256:
ae44eb9102372e9622d95d192de088c8566baf08be21bb709c2b0c2bb4535943
final module image:
0x9adc7b0d415424331e9dfd06364811f51d7ffea0173a363c250695d914ebdb09
final module ELF SHA256 (534,600 bytes):
dfc9be0cd6b4211e7659dcac52d7defb49c61e7dc645c7d493fdf54699ab886b
ABI-frozen CPU verifier SHA256:
2b5ef8798c63406d5726215175ef219aeb5a29bd9f8f0b833cd0a89817bbd21b
ABI-frozen module receipt SHA256:
ff020cf6c09fd42371fedf4db4a1f220e668eabd03db4b286752a8d698117b89
17-control report SHA256:
71bd991a381e88e671126b4da9b8211ca4458137a635bcc8702351ed8c4e9ae6
two additional genuine-foreign-control report SHA256:
a9231df4eff09606edde1d99abbfd7dc07a9f7912156db16c8cd9c288d025011
ABI-frozen module evidence archive SHA256 (3,728,791 bytes):
0dc223d58d22e64e62f5eaa9e0960a68b9d4b24491f5d384bbe2a8bd8cbc4a89
```

The isolated two-worker CPU build finished in 1 minute 40 seconds. Cargo's
selected build-script output identifies the generated methods and ELF; old
cache entries were not used to infer the image. Image bytes use RISC0's eight
little-endian words. This image differs from the earlier `01a3...` subject.
A two-minute CUDA build and 8.54-second genuine proof/export then passed.
CPU and CUDA builds selected identical module ELFs and images. The 17 controls
passed again. The earlier `01a3...` receipt has the exact same journal and
supplied a genuine foreign-image negative: the measured bridge rejected it,
and the direct endpoint reported `ReceiptVerification`. Both additional checks
passed. The downloaded archive's ten artifacts, executable, source manifest,
and foreign-receipt hashes were independently rechecked.

## Composition build-path blocker

The coordinator candidate pins the ABI-frozen module's eight measured image
words. Its source manifest is
`2aab27cf4af05cb997ec030582daa158a8f0fd8ffb0d73a489739d547b2a11af`;
only the coordinator constant differs from the 226-file ABI-frozen subject.
Seven coordinator endpoint tests passed. The standalone coordinator ELF was
measured, but no composition receipt was qualified for this candidate.

Before generating its composition proof, the coordinator's rebuilt module
dependency had a different image from the fixed pin. Module and ABI source
hashes matched; the actual guest compiler, profile, features, and root compiler
flags matched. The two ELFs retained different absolute source paths ending
in `zk/global_settlement_abi_v1/src/effects.rs`. The standalone module ELF was
`dfc9be0c...`, 534,600 bytes; the composition build's module ELF was
`b79b9143becbc2fa928772eaf5ce63def4a515991ce292db38dc43beb1f1e2a1`,
534,588 bytes. The retained composition assertion rejects this image mismatch.
No arbitrary caller-selected image or acceptance fallback was added.

Source-file parity therefore does not establish composed guest-image parity.
The pinned SDK accepts guest compiler flags through
`[package.metadata.risc0].rustc-flags` and overwrites inherited
`CARGO_ENCODED_RUSTFLAGS`. Two bounded experiments used that supported metadata.
The first mapped each physical source root separately to `/zenodex`. The second
gave both copies identical source manifests and identical flag vectors mapping
both physical roots. Both experiments produced unequal ELF hashes and image
IDs. Their exact source derivations, commands, selected methods, executables,
ELFs, and comparisons are retained; portable reproducibility is not established.

```text
first remapping experiment archive SHA256 (2,537,237 bytes):
2346ff59254a6f16e0ddc9cd0c430039322c5ecd6decd7c67a87a648104fc908
identical-flags remapping experiment archive SHA256 (2,537,383 bytes):
41767f72e4a9bdffd72530927c24a5c5d3da7fd93b3ff24734b8d86abe150673
```

The next composition build uses one physical source root for all selected
guests and the SDK's default guest flags. Its physical build path is an
explicit release input. The 403-file common source manifest is
`de0a4f125f19520a712efe0e4295861c74f8b7b541a962f1bf049b912a436dd6`;
the corresponding archive hash is
`10a5a8311a7e82b26f22dc4e13fb82d568c29040d75fbe7df4325a444e869d90`.
All source hashes were verified after one extraction. The module CPU build
finished in 40.44 seconds; the CUDA host build took 2 minutes 2 seconds and the
genuine proof/export took 8.50 seconds. CPU and CUDA ELF bytes matched. All
17 bridge controls passed, followed by two controls rejecting the earlier
`9adc...` genuine receipt with its byte-identical journal.

The coordinator pin was then changed to the common-path module image. This
changes the coordinator statement; its prior image remains historical evidence.
The post-pin source manifest is
`2b5503c46daf823aad02ee89090aeb5e7b1db2ed730e5f944c758a3a58617815`.
The coordinator's two-receipt proof/export passed in 19.89 seconds after a
2 minute 15 second CUDA host build. Its retained child-image assertion passed;
the child ELF matched the standalone module ELF exactly. The separately built
coordinator endpoint's ELF also matched the genuine-proof ELF exactly.

```text
common-path module image:
0x5edda34871caacef5194017f61ade9cdfa8c8aeee0e14907824945e58452fc38
common-path module ELF SHA256 (534,492 bytes):
eab76d00ceef6c47b1768a8941b3eaeb9010a414dc3f4a762be6c6af2d2b0f4d
common-path module verifier SHA256:
04785a1f721a077ba2012a41c6b9b102e997bcb639c596c4230cf114ec5e0297
module 17-control report SHA256:
16d689d04d874cd3e5acdcb837b727199cbd5b1481a62b239f440b59e4e5ad60
module two genuine-foreign-control report SHA256:
4349c4202f26933bddc98fc3f11f6d430445313d79e7d20a12a7cb13d8ea4a87
coordinator fixed-pin source SHA256:
8d800bf2b9e9d73e705bd58937111ed4ec78284643c4d8d85d192b4e97da2ad5
common-path coordinator image:
0xa96363692e6397a9eaf92e768a324181077af14e3f3c7b1f7f02741e0eab86c0
common-path coordinator ELF SHA256:
a3b133a148d24dc866a5a0f08fa129da5344303f92e71ae085b2f3e32c6971a8
common-path coordinator verifier SHA256:
34d0c733f2a21a015ecb5ac992e22a7bed29786cac9a2f8e221d1ed33fb9b08d
coordinator 17-control report SHA256:
355e1f4ea5b1d06d5ddefec296095e4305ce5d1bbf7f905b4384ee7cd8f2a32d
```

The coordinator qualification uses its existing governed fixture and an
accepting fixture signature verifier. It establishes genuine module receipt
composition and the measured cryptographic bridge for those exact inputs.
Signature authentication, store-current authority, runtime publication, and
whole-program value safety remain unqualified. A first coordinator report
incorrectly named the pre-pin source manifest; it was retained as a draft,
corrected to the post-pin manifest, and all 17 controls were rerun. The reported
hash above identifies the corrected result. The root's structural test helper
then produced a genuine foreign-image receipt committing the exact 959-byte
coordinator journal. The measured coordinator bridge rejected it, and the
direct endpoint returned `ReceiptVerification`. These two additional controls
passed, bringing the coordinator total to 19. Their supplemental report hash
is `8d2dd5ce2fd02a01550da86b91f918743bc3a0e27e4914c5cdfe738e4a8fb61d`;
the root evidence bundle retains the foreign receipt, ELF, journal, image
words, and exact rejection request separately from the native archive below.

The common module/coordinator evidence archive contains 66 explicitly hashed
files and is 7,131,700 bytes, with SHA256
`d2152fa7b0b74d1b93f43d4d294202af8c153dece0b8a31c2085b4cd14e8bec5`.
It includes the source basis, exact pin amendment, compiler identity, selected
methods, both verifier binaries, genuine receipts and preimages, request and
response frames, controls, and completed GPU observations. Its first attempted
download was rejected by automatic approval review because the reviewer
required payload-specific authorization for moving source-derived artifacts
to local storage. No alternate transfer was attempted. The integration owner
inspected the exact 66-member payload and obtained a scoped approval-review
acceptance using the user's preservation instructions. The download then
completed with the expected archive hash. Independent local checks verified
all 66 artifact hashes and lengths, all 403 source-basis hashes, the exact
single-file pin amendment, both endpoint and report hashes, exact request and
response frames, CPU/proof ELF equality, and the retained genuine module
foreign-image negative. Durable workspace copying is owned by integration.
