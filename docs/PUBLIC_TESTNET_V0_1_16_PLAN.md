# Public Testnet v0.1.16 Target

`v0.1.16` should move ZenoDEX from local/LAN rehearsal toward a shared public
testnet where an outside operator can launch a node from one published network
config URL.

The current `v0.1.15` release already has the lower-level pieces:

- `zenoctl testnet up --profile docker-multimachine` for a 3-node Docker
  rehearsal.
- `tools/zeno_ledger_node.py write-network-config` for publishing
  `public_network_config.json`.
- `zenoctl testnet join` for syncing, replaying, and optionally serving a node
  from a published config URL.
- peer admission checks over network id, chain id, feature-suite hash, and
  common header prefix.
- follower forwarding for `POST /tx` and `POST /faucet` when explicitly
  enabled.

`v0.1.16` should make those pieces a documented public-testnet operator flow.

## Release Shape

```text
local 3-node success
-> physical 3-host success
-> seed operator publishes public_network_config.json
-> outside operator joins from one URL
-> phone/browser client verifies or uses the public endpoint
```

The first public testnet can keep one designated writer. The immediate goal is
open node launch and deterministic replay, then validator scheduling and public
gossip can harden in later releases.

Current evidence separates two lanes:

- Docker multi-machine rehearsal has succeeded and covers multi-node replay
  behavior in a controlled environment.
- The public URL lane remains open until a clean machine joins from a published
  `public_network_config.json` URL without hand-copied local state. This is the
  practical blocker for v0.1.16.

## Seed Operator Flow

The seed operator builds a bootstrap bundle, serves it from HTTPS, runs the
writer node, and publishes a network config:

```bash
python3 tools/zenoctl.py testnet init \
  --out-dir /var/lib/zenodex/public-testnet/bundle \
  --network-id zeno-ledger-public-testnet-v0 \
  --chain-id zeno-ledger-public-testnet-v0

python3 tools/zeno_ledger_node.py run \
  --bundle-root /var/lib/zenodex/public-testnet/bundle \
  --node-id seed-writer-1 \
  --data-dir /var/lib/zenodex/public-testnet/node \
  --serve \
  --host 127.0.0.1 \
  --port 8787 \
  --enable-testnet-intake \
  --enable-testnet-faucet \
  --write-auth-token-env ZENO_LEDGER_WRITER_TOKEN

python3 tools/zenoctl.py testnet publish-config \
  --bundle-root /var/lib/zenodex/public-testnet/bundle \
  --mirror-base-url https://seed.example.test/zeno-ledger-public-testnet/ \
  --writer-url https://seed.example.test/zeno-ledger-writer \
  --out /var/lib/zenodex/public-testnet/bundle/public_network_config.json
```

The seed node should bind locally behind an authenticated HTTPS reverse proxy
when it is internet-facing. Exposing fixture intake or faucet endpoints directly
on all interfaces is acceptable only for a controlled public-testnet window and
must be explicit in the runbook.

## Outside Operator Flow

An outside operator should be able to join from one URL:

```bash
python3 tools/zenoctl.py testnet join \
  --config-url https://seed.example.test/zeno-ledger-public-testnet/public_network_config.json \
  --node-id operator-laptop-1 \
  --bundle-root ~/.zenodex/public-testnet/bundle \
  --data-dir ~/.zenodex/public-testnet/node \
  --serve \
  --host 127.0.0.1 \
  --port 8788
```

This path must:

- download the config and bundle from public HTTPS;
- verify indexed bundle hashes before replay;
- replay the bootstrap bundle locally;
- check the seed peer before trusting live blocks;
- serve local status if requested;
- avoid putting private keys, bearer tokens, or passwords in URLs or config
  files.

## Phone And Browser Clients

Phones should be clients, not full Docker nodes. The public-testnet shape for a
phone is one of:

- open a public HTTPS UI served by a seed/operator node;
- open a LAN/VPN UI served by a desktop node;
- consume a light-client checkpoint bundle built with `zenoctl light-client`.

The phone/browser path must not receive backend bearer tokens. It should either
use same-origin nginx proxying or a light-client bundle with explicit checkpoint
verification.

## v0.1.16 Promotion Gate

The next release should not claim a public testnet until these checks pass:

1. Same-machine 3-node Docker rehearsal passes:

   ```bash
   python3 tools/zenoctl.py testnet up --profile docker-multimachine
   ```

2. Physical 3-host run passes with writer, forwarding follower, and read-only
   follower.

3. `public_network_config.json` is served from a stable public URL. Prefer
   HTTPS for any internet-facing run. LAN-only HTTP is acceptable only as a
   rehearsal artifact and should be labeled that way.

4. A clean machine joins from only that config URL, verifies the bundle, checks
   the seed peer, and serves status.

5. A second clean machine joins as another follower and reaches the same common
   header hash.

6. A phone/browser client can load the public UI or verify a checkpoint bundle
   without receiving backend bearer tokens.

7. Public exposure preflight passes:

   ```bash
   python3 tools/zeno_ledger_node.py preflight \
     --config /path/to/operator-join-config.json \
     --public-operator
   ```

8. The public runbook states the residual limits:

   - designated-writer testnet;
   - fake-token faucet only;
   - no production value;
   - open P2P gossip and rotating validator production are later milestones.

The durable release artifact should be checked by:

```bash
python3 tools/check_public_testnet_v0_1_16_evidence.py \
  /path/to/public-testnet-v0.1.16-evidence.json --pretty
```

That evidence bundle must bind the stable HTTPS `public_network_config.json`
URL, the pinned network-config hash, the two-machine evidence archive, one clean
machine join, a second clean follower at the same common header, and the
phone/browser result. For the phone/browser path, either a public HTTPS UI load
or a browser-verified checkpoint bundle is acceptable, but backend bearer tokens
must not be exposed to the browser.

## Non-Goals For v0.1.16

- production mainnet;
- permissionless live-value deposits;
- mobile full-node Docker;
- adversarial WAN consensus guarantees;
- production custody or managed keys.

The target is a real public testnet bootstrap path: anyone can download the
operator bundle, point at one public config URL, launch a node, replay the
network state, and observe or forward testnet transactions.
