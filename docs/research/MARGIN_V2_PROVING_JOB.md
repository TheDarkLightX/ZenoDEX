# Isolated margin V2 proving job

Scope: three real Succinct receipts for the rebuilt margin guest, followed by
local verification and the existing isolated atomic publisher. The public test
genesis/key and other economic release/evidence labels remain fixture assumptions.
There is no production, custody-transfer, finality or release-promotion claim.

The [preparation/replay tool](../../tools/qualify_margin_receipts_v2.py) preserves
the existing policy values and rebuilds the signing policy, profile, predecessor,
commands and signatures from the measured BLS executable. The margin role binds
the [measured guest](../../zk/perps_margin_global_risc0/README.md). No remote
configuration or claimed post-state is accepted by the replay tool.

Prepare with the pinned executables and a new packet directory:

```bash
python3 tools/qualify_margin_receipts_v2.py prepare \
  --signature-verifier "$BLS_VERIFIER" --receipt-verifier "$MARGIN_VERIFIER" \
  --output "$MARGIN_PACKET"
```

This runs three real BLS checks and writes `01` deposit, `02` withdrawal and
`03` close inputs, journals and an advisory manifest. Existing output directories
are refused. Input sizes measured on September 13 are 6,295, 7,159 and 6,965 bytes.
Actual guest execution matched every expected journal and used 7,658,512,
7,907,114 and 7,184,547 user cycles: 22,750,173 total. These are execution
measurements, not proof-runtime or memory estimates. The provisional per-command
session ceiling is 16,777,216 cycles.

On the authorized proof host, use SDK 3.0.6 and the compiled
`prove_margin_receipt_v2` described in the workspace README. The executable
requires compatible Linux runtime libraries; rebuild from the pinned workspace
if the transferred binary is incompatible. Full proving has not yet run.

```bash
mkdir "$MARGIN_RECEIPTS"
for step in 01 02 03; do
  RISC0_DEV_MODE=0 "$MARGIN_PROVER" "$R0VM" \
    < "$MARGIN_PACKET/$step.input.bin" \
    > "$MARGIN_RECEIPTS/$step.receipt.json" || exit 1
done
```

Keep the prover diagnostics and receipts. Return only receipts for admission;
the local runner derives expected context from its source and selected executable
pins. The prover itself checks image, journal and cryptographic receipt validity
before writing a result; local acceptance verifies independently again.

```bash
python3 tools/qualify_margin_receipts_v2.py publish \
  --signature-verifier "$BLS_VERIFIER" --receipt-verifier "$MARGIN_VERIFIER" \
  --receipts "$MARGIN_RECEIPTS" --output "$FRESH_ISOLATED_DATABASE"
```

The runner checks complete successor state, restart and exact retries. Commands
commit individually; a failed run may retain an earlier successfully committed
prefix in its isolated database. Its successful report alone does not close AS02:
replay the configured integration tests and required genuine-proof substitutions
before independent qualification. Set `ZENODEX_BLS_VERIFIER_TEST_BINARY`,
`ZENODEX_MARGIN_EXECUTOR`, `ZENODEX_MARGIN_R0VM` and `ZENODEX_MARGIN_RECEIPTS`, then:

```bash
python3 -m pytest -q tests/integration/test_margin_receipt_qualification_v2.py
```

Absent receipts explicitly skip genuine publication. The retained preparation,
real execution and negative-store checks do not count that skip as qualification.
