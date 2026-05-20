# ZenoLedger Multi-Machine Docker Test

This runbook exercises ZenoLedger with separate Docker containers for each
node. The default profile starts three node containers:

- `zeno-ledger-writer`: accepts authenticated testnet writes.
- `zeno-ledger-forwarder`: follows the writer and forwards authenticated writes.
- `zeno-ledger-readonly`: follows the writer and rejects mutation endpoints.

A fourth controller container drives the scenario and writes an evidence report.
The bootstrap container builds the shared public-testnet bundle first.

## Run

```bash
python3 tools/zenoctl.py testnet up --profile docker-multimachine
```

Equivalent Docker command:

```bash
docker compose -f docker-compose.multimachine.yml up --build --abort-on-container-exit --exit-code-from zeno-ledger-multidocker-controller
```

The controller writes:

```text
/app/data/multidocker/reports/multidocker_report.json
```

inside the `zeno-ledger-multidocker-data` Docker volume.

## Physical Two-Host Or Three-Host Run

Use this when the nodes are on separate machines but each node still runs in
Docker. Build the same image on every host from the same repo commit:

```bash
docker build -f Dockerfile.operator-tools -t zenodex/operator-tools:local .
```

On Machine A, build the bootstrap bundle and start the writer:

```bash
export ZENO_LEDGER_WRITER_TOKEN="$(openssl rand -hex 32)"
docker volume create zeno-ledger-machine-a-data

docker run --rm \
  -v zeno-ledger-machine-a-data:/app/data \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py bootstrap \
    --bundle-root /app/data/multidocker/bundle \
    --bundle-tar-out /app/data/multidocker/bundle.tar.gz \
    --network-id zeno-ledger-testnet-v0 \
    --chain-id zeno-ledger-testnet-v0 \
    --report-out /app/data/multidocker/reports/bootstrap.json

docker run --rm --name zeno-ledger-bundle-server \
  -p 8790:8790 \
  -v zeno-ledger-machine-a-data:/app/data:ro \
  zenodex/operator-tools:local \
  -m http.server 8790 --directory /app/data/multidocker

docker run --rm --name zeno-ledger-writer \
  -p 8787:8787 \
  -e ZENO_LEDGER_WRITER_TOKEN="$ZENO_LEDGER_WRITER_TOKEN" \
  -v zeno-ledger-machine-a-data:/app/data \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py serve-node \
    --role writer \
    --bundle-root /app/data/multidocker/bundle \
    --data-dir /app/data/multidocker/node-writer \
    --network-id zeno-ledger-testnet-v0 \
    --chain-id zeno-ledger-testnet-v0 \
    --host 0.0.0.0 \
    --port 8787 \
    --enable-testnet-intake \
    --enable-testnet-faucet \
    --write-auth-token-env ZENO_LEDGER_WRITER_TOKEN
```

Run the bundle server and writer in separate terminals, or run the bundle
server with `-d` and stop it after Machine B and Machine C have fetched the
bundle. Use the same `ZENO_LEDGER_WRITER_TOKEN` value on Machine B and on the
controller host.

On Machine B, fetch Machine A's bundle and start the forwarding follower:

```bash
docker volume create zeno-ledger-machine-b-data

docker run --rm \
  -v zeno-ledger-machine-b-data:/app/data \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py fetch-bundle \
    --bundle-url http://MACHINE_A_IP:8790/bundle.tar.gz \
    --bundle-root /app/data/multidocker/bundle \
    --report-out /app/data/multidocker/reports/fetch-bundle.json

docker run --rm --name zeno-ledger-forwarder \
  -p 8787:8787 \
  -e ZENO_LEDGER_WRITER_TOKEN="$ZENO_LEDGER_WRITER_TOKEN" \
  -v zeno-ledger-machine-b-data:/app/data \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py serve-node \
    --role forwarder \
    --bundle-root /app/data/multidocker/bundle \
    --data-dir /app/data/multidocker/node-forwarder \
    --network-id zeno-ledger-testnet-v0 \
    --chain-id zeno-ledger-testnet-v0 \
    --host 0.0.0.0 \
    --port 8787 \
    --peer-url http://MACHINE_A_IP:8787 \
    --poll-seconds 1 \
    --enable-testnet-intake \
    --enable-testnet-faucet \
    --submit-peer-url http://MACHINE_A_IP:8787 \
    --write-auth-token-env ZENO_LEDGER_WRITER_TOKEN \
    --submit-peer-auth-token-env ZENO_LEDGER_WRITER_TOKEN
```

On Machine C, if available, start a read-only follower:

```bash
docker volume create zeno-ledger-machine-c-data

docker run --rm \
  -v zeno-ledger-machine-c-data:/app/data \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py fetch-bundle \
    --bundle-url http://MACHINE_A_IP:8790/bundle.tar.gz \
    --bundle-root /app/data/multidocker/bundle \
    --report-out /app/data/multidocker/reports/fetch-bundle.json

docker run --rm --name zeno-ledger-readonly \
  -p 8787:8787 \
  -v zeno-ledger-machine-c-data:/app/data \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py serve-node \
    --role readonly \
    --bundle-root /app/data/multidocker/bundle \
    --data-dir /app/data/multidocker/node-readonly \
    --network-id zeno-ledger-testnet-v0 \
    --chain-id zeno-ledger-testnet-v0 \
    --host 0.0.0.0 \
    --port 8787 \
    --peer-url http://MACHINE_A_IP:8787 \
    --poll-seconds 1
```

Run the controller from any host that can reach all node URLs:

```bash
docker run --rm \
  -e ZENO_LEDGER_WRITER_TOKEN="$ZENO_LEDGER_WRITER_TOKEN" \
  -v "$PWD/runs/zeno_ledger_multidocker":/app/reports \
  zenodex/operator-tools:local \
  tools/zeno_ledger_multidocker_scenario.py controller \
    --machine-count 3 \
    --writer-url http://MACHINE_A_IP:8787 \
    --forwarder-url http://MACHINE_B_IP:8787 \
    --readonly-url http://MACHINE_C_IP:8787 \
    --network-id zeno-ledger-testnet-v0 \
    --chain-id zeno-ledger-testnet-v0 \
    --write-auth-token-env ZENO_LEDGER_WRITER_TOKEN \
    --report-out /app/reports/multihost_report.json \
    --timeout-seconds 300
```

For a two-host run, omit Machine C and pass `--machine-count 2` without
`--readonly-url`.

## What It Checks

The live network lane checks:

```text
writer faucet -> writer swap -> writer new-asset faucet
-> writer create pool -> writer add liquidity -> writer remove liquidity
-> follower forwarded faucet -> follower/read-only sync
```

The adversarial HTTP lane checks:

```text
unauthorized writer faucet is rejected
malformed writer transaction is rejected
oversized writer faucet is rejected
read-only follower mutation is rejected
```

The controller also runs the deterministic ZenoLedger chaos harness:

```text
peer churn
gossip flood
equivocation
fork choice
auth failures
validator schedule
live quorum
degraded network
```

## Node Hashes

Each node is identified by a chain-bound hash derived from stable Docker
identity material:

```text
node_hash = hash(network_id, chain_id, docker node public identity)
```

Human labels are only operator display hints. Evidence reports use hashes.

## Limits

This profile gives real multi-container evidence on one Docker network. It is a
strong local rehearsal for a physical two-machine or three-machine run, but it
does not prove wide-area network behavior, NAT traversal, or host firewall
configuration. Physical hosts should run the same node roles and preserve the
same evidence report shape.
