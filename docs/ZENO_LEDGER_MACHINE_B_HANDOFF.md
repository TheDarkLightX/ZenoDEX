# ZenoLedger Machine B Handoff

This note is for the agent operating Machine B in the two-machine ZenoLedger
latest-pushed-commit evidence run.

## Target

Machine A and Machine B must run the same latest pushed commit on:

```text
codex/zeno-ledger-public-testnet-20260514
```

The coordinator will provide the exact commit SHA after this note lands. Verify
the checkout before starting:

```bash
git fetch origin codex/zeno-ledger-public-testnet-20260514
git checkout --detach <latest-pushed-commit-sha>
git rev-parse HEAD
```

The printed SHA must exactly match the coordinator-supplied
`<latest-pushed-commit-sha>`.

Do not edit, commit, or push during the evidence run.

## Join Machine A

Replace `<MACHINE_A_IP>` with the address Machine B can reach:

```bash
python3 tools/zeno_ledger_node.py join-network \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --serve
```

Confirm Machine B can see Machine A:

```bash
python3 tools/zeno_ledger_node.py check-peers \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787
```

Expected result: `ok: true`, matching `network_id`, matching `chain_id`,
matching `feature_suite_hash`, and matching common header hash.

Inspect Machine B mode:

```bash
curl http://127.0.0.1:8788/network
```

If Machine B is forwarding testnet submissions to Machine A,
`capabilities.submission_forwarding_enabled` should be `true`.

## Build Machine B Evidence

After Machine B has caught up to Machine A and the fake-token or forwarded
faucet activity is complete, generate the Machine B evidence files:

```bash
mkdir -p /tmp/zeno-ledger-evidence

python3 tools/build_zeno_ledger_node_evidence_input.py \
  --data-dir /tmp/zeno-ledger-node-b \
  --network-config /tmp/zeno-ledger-node-b/public_network_config.json \
  --machine-out /tmp/zeno-ledger-evidence/machine_b.json \
  --attestation-out /tmp/zeno-ledger-evidence/machine_b_watcher_attestation.json \
  --commit-sha <latest-pushed-commit-sha> \
  --pretty
```

Send these two files back to the coordinator:

```text
/tmp/zeno-ledger-evidence/machine_b.json
/tmp/zeno-ledger-evidence/machine_b_watcher_attestation.json
```

Also report the output of:

```bash
python3 --version

python3 tools/zeno_ledger_node.py check-peers \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787

curl http://127.0.0.1:8788/network
```

Do not send auth tokens. The coordinator only needs evidence JSON, hashes,
counts, and checker output.
