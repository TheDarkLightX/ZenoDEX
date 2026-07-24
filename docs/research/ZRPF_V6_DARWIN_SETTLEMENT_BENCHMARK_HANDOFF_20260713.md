# ZRPF V6 Apple Silicon settlement benchmark handoff

This handoff runs the same source-opened Spot V6 settlement stage that remained
active for more than twelve hours on the four-logical-CPU Linux host. It uses
the exact completed local L2 receipt, exact source envelope, and exact prebuilt
L2 and settlement guest programs. The worker verifies every transferred byte,
recomputes both program image IDs, verifies the L2 receipt inside the governed
settlement path, creates a fresh Succinct settlement receipt, rejects its exact
seal mutation, and publishes a content-bound candidate result atomically.

This is candidate performance and proof-generation evidence. Every release,
ledger, settlement, and production authority field remains false.

## Governed identities

```text
worker commit:
  4e701f9ecc7540f65899f311d0a9f31fbcbed44d

task ID:
  f21fd4053426212241cc2331525d6753473af949b30e4f2dd3fcefd2526293e1

task manifest SHA-256:
  f0ec588ddd6d93f1f7a8e5aaf29106660c046eeb5fd77e3a49286dd3cf9ba28c

archive SHA-256:
  f900ca9f8ebf4e29b22e3230e639d44eb7ebe82cf2545c35ff4a28fdcb740cf4

archive bytes:
  1,975,901
```

The archive includes the positive leaf, level-one, and level-two candidate
receipts and reports so that the Mac receives the completed local proof prefix.
Earlier leaf/L1/L2 mutation receipts are omitted because this task does not use
them. The Mac worker creates and rejects a new settlement mutation. A complete
chain replay remains a separate post-proof check.

## Mac prerequisites

Use native Apple Silicon tools. Rosetta/x86 execution is rejected.

```bash
rustup toolchain install 1.94.1

curl -L https://risczero.com/install | bash
rzup install cargo-risczero 3.0.5
rzup install r0vm 3.0.5

rustc +1.94.1 --version
cargo +1.94.1 --version
cargo +1.94.1 risczero --version
r0vm --version
python3 --version
```

The exact accepted tool outputs are:

```text
rustc 1.94.1 (e408947bf 2026-03-25)
cargo 1.94.1 (29ea6fb6a 2026-03-24)
cargo-risczero 3.0.5
risc0-r0vm 3.0.5
```

## Fetch and run

```bash
git fetch origin agent/zrpf-completion-integration-20260712
git switch --detach 4e701f9ecc7540f65899f311d0a9f31fbcbed44d

gh release download zrpf-v6-darwin-settlement-benchmark-task-v1-20260713 \
  --repo TheDarkLightX/ZenoDEX \
  --pattern zrpf-v6-darwin-settlement-benchmark-task-v1-20260713.tar.gz

echo 'f900ca9f8ebf4e29b22e3230e639d44eb7ebe82cf2545c35ff4a28fdcb740cf4  zrpf-v6-darwin-settlement-benchmark-task-v1-20260713.tar.gz' \
  | shasum -a 256 -c -

tar -xzf zrpf-v6-darwin-settlement-benchmark-task-v1-20260713.tar.gz

cargo +1.94.1 fetch --locked \
  --manifest-path zk/zrpf_risc0/Cargo.toml

TASK_DIR="$PWD/zrpf-v6-darwin-settlement-benchmark-task-staging-20260713"
OUTPUT_DIR="$HOME/zrpf-v6-darwin-settlement-result-20260713"

python3 tools/run_zrpf_source_opened_spot_v6_darwin_settlement_benchmark.py \
  --task "$TASK_DIR/task.json" \
  --output "$OUTPUT_DIR"
```

The online `cargo fetch` step populates the exact lockfile dependencies. The
worker itself builds with `--locked --offline`. Put the extracted task outside
the repository checkout so it cannot affect the governed source-status check.

While it runs, this command shows whether the native prover remains active:

```bash
ps -Ao pid,etime,%cpu,rss,command | grep '[r]0vm'
```

The worker publishes no partial accepted output. A successful run creates
`$OUTPUT_DIR` only after the proof, exact mutation rejection, six-artifact
binding, and report validation all succeed.

## Return the result

Preserve the complete output directory. From its parent directory:

```bash
tar -czf zrpf-v6-darwin-settlement-result-20260713.tar.gz \
  zrpf-v6-darwin-settlement-result-20260713
shasum -a 256 zrpf-v6-darwin-settlement-result-20260713.tar.gz
```

The returned result still has no proof or settlement authority. It must pass an
independent cryptographic full-chain replay and evidence review before any
claim can advance.
