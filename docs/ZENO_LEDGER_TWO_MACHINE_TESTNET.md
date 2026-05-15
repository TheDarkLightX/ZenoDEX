# ZenoLedger Two-Machine Testnet Rehearsal

This runbook describes the current ZenoLedger v0 public-testnet shape. It is a
deterministic follower/watcher network with one designated writer node for live
testnet blocks and any number of follower nodes that verify the bootstrap
bundle, serve status, forward submissions, and replay live blocks from peers.

## Current Mode

ZenoLedger v0 gives ZenoDEX a Tau Net independent rehearsal layer:

- Machine A builds and serves the public-testnet bundle.
- Machine A runs the writer node with testnet intake and faucet enabled.
- Machine B joins from the public HTTP mirror, verifies all bundle hashes, and
  runs as a follower/watcher.
- Machine B can expose `POST /tx`, `POST /faucet`, and `POST /tokens`, forward
  those submissions to Machine A, and then replay Machine A's resulting live
  blocks.
- Both machines can check that they share the same network ID, chain ID,
  feature-suite hash, and common header hash.

The current mode is enough for a two-machine public-testnet rehearsal with fake
tokens and elaborate ZenoDEX feature tests. It is still a designated-writer
testnet, so validator scheduling, open P2P block gossip, and fork-choice remain
future network work.

## Prerequisites

Both machines should run from the same Git commit:

```bash
git clone https://github.com/TheDarkLightX/ZenoDEX.git
cd ZenoDEX
git pull --ff-only origin main
python3 --version
```

Machine A must expose two reachable ports:

- `8000` for the static bootstrap mirror.
- `8787` for the writer node HTTP API.

Machine B defaults to `8788` for its follower node server.

Optional preflight:

```bash
python3 tools/zeno_ledger_node.py doctor
```

## Machine A: Build, Mirror, And Run Writer

Build the public-testnet bundle:

```bash
python3 tools/zeno_ledger_node.py bootstrap \
  --out-dir /tmp/zeno-ledger-public-testnet \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0 \
  --token-symbol tZENO
```

Serve the bundle as an HTTP mirror:

```bash
cd /tmp/zeno-ledger-public-testnet
python3 -m http.server 8000
```

In another terminal, run the writer node:

```bash
python3 tools/zeno_ledger_node.py run \
  --bundle-root /tmp/zeno-ledger-public-testnet \
  --node-id operator-a \
  --data-dir /tmp/zeno-ledger-node-a \
  --peer-watcher-attestation \
    /tmp/zeno-ledger-public-testnet/bootstrap/watcher_attestations/bootstrap_range_1_5.json \
  --serve \
  --host 0.0.0.0 \
  --port 8787 \
  --enable-testnet-intake \
  --enable-testnet-faucet
```

Publish a network config into the mirrored bundle directory. Replace
`<MACHINE_A_IP>` with the address Machine B can reach.

```bash
python3 tools/zeno_ledger_node.py write-network-config \
  --bundle-root /tmp/zeno-ledger-public-testnet \
  --mirror-base-url http://<MACHINE_A_IP>:8000/ \
  --writer-url http://<MACHINE_A_IP>:8787 \
  --out /tmp/zeno-ledger-public-testnet/public_network_config.json
```

Record the printed `network_config_hash`. Share it beside the URL when
possible, so Machine B can reject a stale or unintended config.

Machine A exposes:

- `GET /health`
- `GET /status`
- `GET /network`
- `GET /features`
- `GET /tokens`
- `GET /live`
- `GET /follow`
- `POST /tx`
- `POST /faucet`
- `POST /tokens`

## Machine B: Join And Follow

Join from the public network config:

```bash
python3 tools/zeno_ledger_node.py doctor \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --expected-network-config-hash <NETWORK_CONFIG_HASH>

python3 tools/zeno_ledger_node.py join-network \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --expected-network-config-hash <NETWORK_CONFIG_HASH> \
  --serve
```

The join command downloads the network config, verifies its hash when present,
downloads the mirror, verifies the mirror indexes, replays the bundle, emits a
watcher attestation, checks the configured peer, and starts the node server.
When `poll_seconds` is positive in the published network config, the served
follower also polls peers for live blocks in the background and writes
`peer_follow_state.json`.

For a one-command Machine B acceptance run, use:

```bash
python3 tools/zeno_ledger_machine_b_acceptance.py \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --expected-network-config-hash <NETWORK_CONFIG_HASH> \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --token-symbol tMANGO \
  --out /tmp/zeno-ledger-node-b/machine_b_acceptance_report.json
```

This command runs remote doctor checks, joins the network, submits the named
test token to Machine A, follows the resulting live block, writes
`evidence_report.json`, and writes
`two_machine_evidence_verification.json`.

Use a different `--token-symbol` if the same Machine A writer already created
`tMANGO` in an earlier run.

## Verify Both Nodes

On Machine B:

```bash
python3 tools/zeno_ledger_node.py check-peers \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787
```

Expected result:

- `ok: true`
- matching `network_id`
- matching `chain_id`
- matching `feature_suite_hash`
- matching common header hash

Write a portable evidence report from Machine B:

```bash
python3 tools/zeno_ledger_node.py evidence \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787 \
  --out /tmp/zeno-ledger-node-b/evidence_report.json
```

Verify that the evidence report satisfies the two-machine acceptance gate:

```bash
python3 tools/zeno_ledger_verify_two_machine_evidence.py \
  --evidence-report /tmp/zeno-ledger-node-b/evidence_report.json \
  --expected-created-token-symbol tMANGO \
  --min-height 13 \
  --out /tmp/zeno-ledger-node-b/two_machine_evidence_verification.json
```

Expected result:

- `ok: true`
- `peer_same_height` check is `true`
- `common_header_binding` check is `true`
- `created_test_tokens` check includes `tMANGO`

Inspect Machine B's mode:

```bash
curl http://127.0.0.1:8788/network
```

The `capabilities.submission_forwarding_enabled` field should be `true` when
Machine B is forwarding testnet submissions to Machine A.

## Test Fake Tokens

Create a named fake test token through Machine B. Machine B forwards it to
Machine A.

```bash
curl -sS http://127.0.0.1:8788/tokens \
  -H 'Content-Type: application/json' \
  -d '{
    "creator_pubkey": "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "decimals": 8,
    "name": "Test Mango Credit",
    "salt": "manual-two-machine-token-v0",
    "symbol": "tMANGO",
    "tx_id": "manual-create-test-token-v0"
  }'
```

The response includes `testnet_token.asset`. Use that asset ID in the faucet
request. This example uses a raw fixture asset ID, which is still accepted for
quick testing:

```bash
curl -sS http://127.0.0.1:8788/faucet \
  -H 'Content-Type: application/json' \
  -d '{
    "to_pubkey": "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "asset": "0x3333333333333333333333333333333333333333333333333333333333333333",
    "amount": 100000,
    "tx_id": "manual-fake-token-faucet-v0"
  }'
```

Then confirm Machine B catches up:

```bash
python3 tools/zeno_ledger_node.py follow-once \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787
```

The follower accepts a live block only when local deterministic replay produces
the same header as the writer node.

Inspect the latest follower-poll report:

```bash
curl http://127.0.0.1:8788/follow
```

Expected result:

- `ok: true`
- `peer_count` is at least `1`
- each successful peer entry includes the nested pull report and pulled height

Inspect the follower token registry:

```bash
curl http://127.0.0.1:8788/tokens
```

Expected result:

- `created_test_token_count` is at least `1` after the `POST /tokens` request.
- `created_test_tokens` includes `tMANGO`.
- `testnet_token_registry_hash` is present.

## Local Smoke Test

Run this on one machine before involving the MacBook:

```bash
python3 tools/zeno_ledger_public_network_smoke.py \
  --out-dir /tmp/zeno-ledger-public-network-smoke \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0
```

The smoke test builds a mirror, syncs two independent nodes, appends faucet and
swap blocks, registers a named fake token, creates a fake-token pool, adds and
removes liquidity in that pool, forwards a faucet request through the follower,
and verifies both nodes end on the same live header.
