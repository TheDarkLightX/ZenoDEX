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
- Machine B can expose `POST /tx` and `POST /faucet`, forward those submissions
  to Machine A, and then replay Machine A's resulting live blocks.
- Both machines can check that they share the same network ID, chain ID,
  feature-suite hash, and common header hash.

The current mode is enough for a two-machine public-testnet rehearsal with fake
tokens and elaborate ZenoDEX feature tests. It is still a designated-writer
testnet, so live rotating validators, open P2P block gossip, and production
fork-choice remain future network work.

The core ledger module now includes a first deterministic validator-schedule
boundary for local hardening:

- `validator_set_hash_v0` commits to a canonical validator set.
- `scheduled_validator_id_for_height_v0` chooses the expected proposer from
  height and voting power.
- `validate_body_validator_schedule_v0` checks that the body batch-cutoff
  sequencer matches the scheduled proposer.
- `detect_header_equivocations_v0` reports conflicting header hashes at the
  same chain height.
- `validate_header_chain_linkage_v0` checks that a local header segment has one
  chain id, unique consecutive heights, and parent hashes matching the previous
  canonical header hash.
- `canonical_header_chain_tip_v0` returns the deterministic tip hash after
  linkage validation.
- `evaluate_header_fork_choice_v0` selects a deterministic canonical branch
  from anchored local header segments by maximum tip height, then chain length,
  then lowest tip hash, while reporting orphan headers.
- `select_canonical_header_chain_v0` returns the selected header segment in
  ancestor order.

This is a local verifier surface. It does not yet implement live rotating
validators, open P2P block gossip, or production fork-choice under adversarial
network conditions.

## Machine A: Build, Mirror, And Run Writer

Run the local preflight first:

```bash
python3 tools/zeno_ledger_node.py --help
python3 tools/zeno_ledger_node.py preflight --help
python3 tools/permissionless_assurance.py status
python3 tools/check_tau_supported_runtime_subset.py
pytest -q tests/tau/test_tau_spec_assurance.py
```

Then run the same-machine smoke test once:

```bash
python3 tools/zeno_ledger_public_network_smoke.py \
  --out-dir /tmp/zeno-ledger-public-network-smoke \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0 \
  --report-out /tmp/zeno-ledger-public-network-smoke-report.json
```

Proceed to the two-machine flow only after the smoke test reports success.
For a broader local rehearsal gate that also checks node preflight coverage and
Tau experiment promotion metadata, run:

```bash
bash tools/run_public_testnet_candidate_gate.sh
```

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
export ZENO_LEDGER_WRITER_TOKEN='<replace-with-random-testnet-token>'

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
  --enable-testnet-faucet \
  --write-auth-token-env ZENO_LEDGER_WRITER_TOKEN
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

Machine A exposes:

- `GET /health`
- `GET /status`
- `GET /network`
- `GET /features`
- `GET /tokens`
- `GET /live`
- `POST /tx`
- `POST /faucet`

## Machine B: Join And Follow

For the shortest path, join from the public network config:

```bash
python3 tools/zeno_ledger_node.py join-network \
  --config-url http://<MACHINE_A_IP>:8000/public_network_config.json \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --serve
```

The join command downloads the network config, verifies its hash when present,
downloads the mirror, verifies the mirror indexes, replays the bundle, emits a
watcher attestation, checks the configured peer, and starts the node server.
Live pull now applies the same peer-admission gate before fetching block bodies:
the peer must expose a valid node-status hash, match network id, chain id, and
feature-suite hash, and share the local common header prefix.

For a preflightable operator config, write the equivalent local join config
first:

```bash
cat > /tmp/zeno-ledger-node-b-config.json <<'JSON'
{
  "schema": "zenodex.zeno_ledger.node_join_config.v0",
  "base_url": "http://<MACHINE_A_IP>:8000/",
  "bundle_root": "/tmp/zeno-ledger-public-testnet-synced",
  "node_id": "operator-b",
  "data_dir": "/tmp/zeno-ledger-node-b",
  "peer_urls": ["http://<MACHINE_A_IP>:8787"],
  "serve": true,
  "host": "0.0.0.0",
  "port": 8788,
  "poll_seconds": 5,
  "enable_testnet_intake": true,
  "enable_testnet_faucet": true,
  "submit_peer_url": "http://<MACHINE_A_IP>:8787",
  "write_auth_token_env": "ZENO_LEDGER_NODE_B_WRITE_TOKEN",
  "submit_peer_auth_token_env": "ZENO_LEDGER_WRITER_TOKEN"
}
JSON

export ZENO_LEDGER_NODE_B_WRITE_TOKEN='<replace-with-random-follower-token>'
export ZENO_LEDGER_WRITER_TOKEN='<same-token-used-on-machine-a>'

python3 tools/zeno_ledger_node.py preflight \
  --config /tmp/zeno-ledger-node-b-config.json

python3 tools/zeno_ledger_node.py join \
  --config /tmp/zeno-ledger-node-b-config.json
```

The preflight rejects malformed URLs, invalid ports, missing required fields,
bad local bundle paths, already-bound serve ports, missing auth-token
environment variables, and credentialed URLs. It also warns when testnet
faucet/intake endpoints are enabled or when the node binds to all interfaces.

Use strict exposure mode before placing a node on a public interface:

```bash
python3 tools/zeno_ledger_node.py preflight \
  --config /tmp/zeno-ledger-node-b-config.json \
  --strict-exposure
```

Strict exposure mode rejects all-interface binds with testnet intake or faucet
endpoints enabled. A public deployment should bind locally behind a separate
authenticated reverse proxy, or disable those fixture endpoints.

Use public-operator mode for configs that may sit behind an internet-facing
proxy:

```bash
python3 tools/zeno_ledger_node.py preflight \
  --config /tmp/zeno-ledger-node-b-config.json \
  --public-operator
```

Public-operator mode rejects inline auth tokens, requires `*_auth_token_env`
for enabled write or forwarding paths, and requires the node server to bind to
a local interface. For the fixture config above, change `"host"` to
`"127.0.0.1"` before using this gate.

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

`pull-live` rejects a peer before body fetch if that compatibility report is
rejected.

Inspect Machine B's mode:

```bash
curl http://127.0.0.1:8788/network
```

The `capabilities.submission_forwarding_enabled` field should be `true` when
Machine B is forwarding testnet submissions to Machine A.

## Archive Evidence

For a latest-main rehearsal, archive the machine-readable results from both
hosts after Machine B has caught up to Machine A. Each machine should first
build its own machine artifact and a watcher attestation bound to its local
tip. Run this on Machine A:

```bash
python3 tools/build_zeno_ledger_node_evidence_input.py \
  --data-dir /tmp/zeno-ledger-node-a \
  --network-config /tmp/zeno-ledger-public-testnet/public_network_config.json \
  --machine-out /tmp/zeno-ledger-evidence/machine_a.json \
  --attestation-out /tmp/zeno-ledger-evidence/machine_a_watcher_attestation.json \
  --commit-sha <latest-main-sha> \
  --pretty
```

Run this on Machine B:

```bash
python3 tools/build_zeno_ledger_node_evidence_input.py \
  --data-dir /tmp/zeno-ledger-node-b \
  --network-config /tmp/zeno-ledger-node-b/public_network_config.json \
  --machine-out /tmp/zeno-ledger-evidence/machine_b.json \
  --attestation-out /tmp/zeno-ledger-evidence/machine_b_watcher_attestation.json \
  --commit-sha <latest-main-sha> \
  --pretty
```

The helper verifies the node's full local range from height `1` to the current
tip, then writes a watcher attestation whose `last_header_hash` is the same tip
hash reported in the machine artifact. This is the attestation form the archive
checker expects after live fake-token activity. The older `/attestation`
endpoint is the bootstrap replay attestation and should only be used when the
claimed common header is still the bootstrap tip.

Copy the four output files and the accepted fake-token or forwarded-faucet
report to one host, build the canonical archive, and validate it before
promoting the run as evidence:

```bash
python3 tools/build_zeno_ledger_two_machine_evidence.py \
  --machine-a /tmp/zeno-ledger-evidence/machine_a.json \
  --machine-b /tmp/zeno-ledger-evidence/machine_b.json \
  --token-test-result /tmp/zeno-ledger-evidence/token_test_result.json \
  --watcher-attestation /tmp/zeno-ledger-evidence/machine_a_watcher_attestation.json \
  --watcher-attestation /tmp/zeno-ledger-evidence/machine_b_watcher_attestation.json \
  --accepted-tx-count <accepted-count> \
  --rejected-tx-count <rejected-count> \
  --latest-pushed-commit-sha <latest-main-sha> \
  --expected-commit <latest-main-sha> \
  --out /tmp/zeno-ledger-evidence/two_machine_evidence.json

python3 tools/check_zeno_ledger_two_machine_evidence.py \
  /tmp/zeno-ledger-evidence/two_machine_evidence.json \
  --expected-commit <latest-main-sha>

python3 tools/check_next_goal_backlog_completion.py \
  --latest-pushed-commit-sha <latest-main-sha> \
  --two-machine-evidence /tmp/zeno-ledger-evidence/two_machine_evidence.json \
  --run-supporting-gates \
  --pretty
```

The archive schema is
`zenodex.zeno_ledger.two_machine_latest_main_evidence.v0`. The checker requires:

- Each machine artifact supplied to the builder exposes `machine_id` or
  `node_id`, `commit_sha`, `python_version`, `network_config_hash`,
  `feature_suite_hash`, and a header field such as `header_hash` or
  `last_header_hash`.
- `commit_sha` and `latest_pushed_commit_sha` are the same lowercase 40-hex
  commit, and `--expected-commit` matches when supplied.
- Machine A and Machine B have distinct `machine_id` values.
- Each machine reports the same `commit_sha` as the archive and a parseable
  `python_version`.
- Both machines report the same network-config hash, feature-suite hash, and
  common header hash.
- `tx_counts.accepted` is positive and the fake-token test result is accepted.
- At least two unique watcher attestations are present, cover both machine ids,
  replay their own `attestation_hash`, and bind to the common header hash.

The builder assembles the archive from host artifacts and runs the same strict
validation before writing the output. The checker validates the archived
evidence shape and hash bindings. This flow still depends on operators
collecting the archive from real hosts and supplying the latest pushed commit
hash from the repository remote.

The checker report includes a `required_evidence_fields` map with booleans for
the explicit latest-main archive requirements: commit SHA, latest pushed commit,
both Python versions, network-config hash, feature-suite hash, common header
hash, accepted/rejected transaction counts, token-test result, watcher
attestations, and machine-id watcher coverage.

The next-goal completion audit is deliberately stricter than the archive
checker. It maps the full backlog to concrete artifacts and replay commands,
requires the real two-machine archive for the latest-main item, and reports any
supporting gate that was not run or did not pass. A source-tree gate, unit test,
or local smoke run is useful supporting evidence; it cannot stand in for the
real two-host archive.

## Test Fake Tokens

Submit a faucet request through Machine B. Machine B forwards it to Machine A.

```bash
curl -sS http://127.0.0.1:8788/faucet \
  -H 'Content-Type: application/json' \
  -H "Authorization: Bearer $ZENO_LEDGER_NODE_B_WRITE_TOKEN" \
  -d '{
    "to_pubkey": "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "asset": "0x3333333333333333333333333333333333333333333333333333333333333333",
    "amount": 100000,
    "tx_id": "manual-fake-token-faucet-v0"
  }'
```

Then confirm Machine B catches up:

```bash
python3 tools/zeno_ledger_node.py pull-live \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://<MACHINE_A_IP>:8787
```

The follower accepts a live block only when local deterministic replay produces
the same header as the writer node.

## Local Smoke Test

Run this on one machine before involving the MacBook:

```bash
python3 tools/zeno_ledger_public_network_smoke.py \
  --out-dir /tmp/zeno-ledger-public-network-smoke \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0 \
  --report-out /tmp/zeno-ledger-public-network-smoke-report.json
```

The smoke test builds a mirror, syncs two independent nodes, appends faucet and
swap blocks, creates a fake-token pool, adds and removes liquidity in that
pool, forwards a faucet request through the follower, and verifies both nodes
end on the same live header. The tool validates the exact expected height
sequence, records total `elapsed_ms`, and writes the JSON report when
`--report-out` is supplied.
