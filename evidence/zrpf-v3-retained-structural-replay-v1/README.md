# ZRPF V3 Retained Structural Receipt Replay

This directory contains eight exact retained RISC0 3.0.5 receipt artifacts for
the bounded ZenoDEX ZRPF V3 structural profile:

- four V1 adapter leaf receipts;
- two level-one structural receipts;
- one level-two structural root receipt;
- one level-two receipt with exactly seal word 1 XORed by 1.

The `receipts/` directory intentionally contains only those eight files. The
source-built replay verifier requires that exact inventory and binds every file
by fixed name, byte length, and SHA-256 before receipt verification.

The current retained root receipt is
`edd25fca20b0205c2f778b866605b343922615623256abcc1a098957664c2d16`.
It authenticates root journal
`2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768`.
The earlier historical local receipt `021af130...fd33` authenticates the same
journal and remains in its original evidence record. The two receipt byte
instances do not establish receipt-byte determinism.

`firecracker-governed-output-payload.json` is the exact 5,920-byte payload
committed by the governed direct Firecracker replay. Its SHA-256 is
`7751395663a33c1ae58fa403346dc90618e842dd1df2f2fdc37f18599e50c288`.
The scoped Firecracker evidence checker combines these bytes with the governed
request to reconstruct and validate the complete 16 MiB output protocol,
including its header, zero padding, final marker, and output SHA-256.

Run the static evidence gate from the repository root:

```bash
python3 tools/check_zrpf_v3_replay_verifier_evidence.py --json
```

The static gate checks canonical record bytes, pinned source and receipt
material, and the bounded raw-byte privacy policy over the governed public
artifact inventory. It does not reperform receipt verification. Use `--live`
for current source-built replay and negative-control evidence.

Run a fresh same-host build and replay with a new external target directory:

```bash
python3 tools/check_zrpf_v3_replay_verifier_evidence.py \
  --live \
  --risc0-home "$HOME/.risc0" \
  --target-dir "<NEW_EXTERNAL_TARGET_DIRECTORY>" \
  --json
```

The live gate builds only the source replay verifier, verifies all seven valid
Succinct receipts, independently recomposes both level-one journals and the
level-two journal, verifies the reviewed root and topology, and requires the
exact seal mutation to reject as `receipt_verification_failed`. It also runs
altered-byte, swapped-node, extra/missing-inventory, receipt-symlink, FIFO,
directory-symlink, and missing-argument controls. The freshly built verifier is
copied into a fully sealed Linux memfd before execution, so later pathname
replacement cannot substitute different bytes for that run.

No native verifier binary, guest ELF, proof-generation input, toolchain copy,
raw 16 MiB Firecracker output, or full local execution report is stored here.
The exact output payload is public replay data. This retained-byte regression
lane does not attest proof generation, guest source-to-image correspondence,
complete build-input, compiler, linker, dependency-cache, or runtime-rootfs
identity, cross-host reproducibility, a release build, semantic
aggregation, conservation, data availability, carry or scheduling, ledger or
settlement admission, privacy, transaction counts, throughput, or production
authority. Its `operation_count` unit is `source_transition_receipt_v3`.
