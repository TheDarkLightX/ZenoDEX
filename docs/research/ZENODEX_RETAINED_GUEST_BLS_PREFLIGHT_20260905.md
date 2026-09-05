# Retained guest source preflight for isolated BLS inputs

Date: 2026-09-05. Status: **native retained-source replay passed**. This extends
the [BLS input preparation replay](ZENODEX_WHOLE_PROGRAM_V3_BLS_INPUT_PREPARATION_REPLAY.md).
No fresh receipt, guest ELF execution or publication authority is claimed.

The new native harness called the exact retained shared libraries for all five
prepared inputs: initialization, ASSET_TRANSFER module, coordinator, route and
direct epoch. Every canonical journal matched its prepared expectation byte for
byte. The fixed module/coordinator/route child-image requirements and both ROOT
image requirements matched the four retained images. Child journals and the
initial/pre/post state-root chain also matched. Five noncanonical/trailing-data
controls rejected.

## Exact subject and evidence

The retained final-chain source04 manifest is
`134bb02ef7ed2b655acae2bce5b90aae8a24cb0efd2fdf13882236ef3b50dc2a`.
All 404 source files and all 458 original archive members matched their recorded
hashes and sizes. The original source remained unchanged. All 27 prepared BLS
artifacts matched input manifest
`17fcaff8896718456524e89615199d45276faceb6f1d4c5744f4718c81dc4c5e`.
Source and input checks repeated after replay.

The added evidence exporter is separate from the unchanged retained libraries.
Its native build used Rust 1.90.0, two workers, ordinary Cargo fingerprints and
offline dependencies. All 40 selected registry entries exactly matched retained
ROOT lock versions and checksums. An initial offline resolution selected
`syn 3.0.4`; it was corrected to retained `3.0.3` before compilation. Both lock
records remain in the evidence. Native compilation took 24.19 seconds.

| Stage | Canonical bytes | SHA256 of matching journal |
|---|---:|---|
| Initialization | 1368 | `d1e36faca4779c43109a569ffacbb45b1fa35cc217606aa69dec64a018ab22ea` |
| Module | 1025 | `fab0cc3ea808521a5c6f0299eb188779f8bd658b39120b8628e8047b6a5b2b91` |
| Coordinator | 959 | `443cff5be3a3d2185b61707c247a3ab4c66738d34e0aec29603f059fa09a70fc` |
| Route | 926 | `41ee7bcb992e86d0ed970903abc6f52715c1c171e12131f93f736a87c98a1026` |
| Epoch | 1569 | `e428d0dbcdde0b61f047568f60ec67bbeee0c28f534f6a831acd7fcfda6aaf4d` |

The three module/coordinator/route journals also matched the independent prepared
Python reference objects. Initialization and epoch expectations were taken from
their prepared statement/certificate inputs; those two byte comparisons are not
independent reconstruction oracles.

The replay reproduced allocation projection root
`0xdf9b02f3eb5b411480792a872c4a159fb519b22447f2b77e74a98bae5ec0dff8`
and refinement root
`0x4069e076b2fd4adfaa11f96be8a0dc011a145ca53c4879b658afb5659689acc7`,
matching the previously recorded current-source replay. All embedded roots and
the little-endian image-word comparisons are retained in
`outputs/verified-evidence.json`.

Evidence archive: `zenodex-v3-bls-retained-replay01.tar.gz`, 5,380,079 bytes,
SHA256 `e9a335efd2793da97e26bfa13c850e65b40cf22b509d37914494a21fec6321f9`.
Its manifest is
`eb5b1d2a491972a1c208d8e75c3aa4b3818efb1f3e37e80ee73db677736034a1`
and covers 464 files, plus the manifest itself. It contains the native harness,
retained source copy, prepared inputs, expected and actual journals, tagged ROOT
frames, toolchain/dependency records, complete output and verification scripts.
It contains no Cargo target cache. The added native executable is identified by
hash; it is not a receipt verifier or publication capability.

From a fresh extracted archive with the same installed compiler and cached
dependencies:

```sh
CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 cargo +1.90.0 run --offline --locked --manifest-path harness/Cargo.toml -- inputs .
python3 verify_evidence.py inputs
```

## Claim ceiling and next proof batch

The selected profile is
`0x0dd53a549df3b3c045f0932ad2f3176c871d6fbdcf90d1c426a00a292dd7a9f8`.
Its signature verifier stays SHADOW / `ISOLATED_QUALIFICATION`. The earlier input
preparation verified a genuine BLS signature using a disclosed public test scalar.
This native replay consumes the resulting binding root. The retained module
guest does not perform BLS verification.

This evidence establishes compatibility of the prepared inputs with the retained
shared preflight implementation. It does not establish guest execution, native
to guest refinement, cryptographic child-assumption verification or the measured
publisher's full acceptance of new receipts. Genesis ownership, external data
availability/finality, loaded-code correspondence and retained economic release
evidence labels remain explicit assumptions. A source-manifest digest in the
fixture's availability field is a local commitment, with no external attestation.

No input incompatibility was found. The next scoped GPU batch still requires
exactly five genuine Succinct receipts: initialization, module, coordinator with
the module receipt, route with the coordinator receipt, and direct epoch with the
route receipt. The earlier GPU batch completed for its own saved profile and
inputs. This later BLS profile changes authorization and statement roots, so that
earlier completion does not cover the five new receipts. The user intentionally
shut down the GPU host; this note requests no restart or remote action.

The four actual guest-program byte artifacts are retained and match the durable
final-root-route archive, rather than only being represented by image IDs.
The exported `.elf` files contain an `R0BF` wrapper and embedded RISC-V ELF data
at offset 32. Preserve the complete program bytes. Genesis and epoch ROOT
programs are byte-identical. The artifacts total 3,213,436 bytes:

| Export | Bytes | SHA-256 |
| --- | ---: | --- |
| `transfer/module.elf` | 534492 | `eab76d00ceef6c47b1768a8941b3eaeb9010a414dc3f4a762be6c6af2d2b0f4d` |
| `transfer/coordinator.elf` | 659568 | `a3b133a148d24dc866a5a0f08fa129da5344303f92e71ae085b2f3e32c6971a8` |
| `transfer/route.elf` | 1320764 | `27e152d409415796c59307886f50f1713dd2c1774a3e4ddcda81308f623c2445` |
| `genesis/root.elf` | 698612 | `872ed5e6e945f1285ad74bc9c46ccd77c722af6f7ead8e9f99cc5e8e217833ab` |

These can be supplied to a reviewed native prover driver with pinned SDK/CUDA
dependencies, avoiding guest rebuilds. That driver is not qualified by artifact
availability. Recompute each program image before use and match the prepared
subject; the prior path-sensitive
build behavior makes silent image substitutions unacceptable. If rebuilding via
the retained hosts, require the same images before proving.

Preserve the exact payloads, child assumptions, journals and native receipt codecs
(JSON for the three economic guests, postcard for ROOT). Replay measured bridge
positive/negative controls and the raw-auth isolated publisher path afterward.
Reacquire the selected shell evidence snapshot before that replay; source/runtime
drift requires a new prepared subject and affected proofs. Old receipts bind a
different profile. No remote job, guest/proof build, dependency download or
production activation occurred in this task.
