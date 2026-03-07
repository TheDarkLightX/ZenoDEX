# Permissionless Hosting

This repo can be deployed without depending on a specific cloud vendor.

The goal is not "find a decentralized AWS". The goal is:

- any operator can run the UI/API on commodity hardware
- the public path stays verifiable and deterministic
- remote infrastructure is optional, not required for correctness

## Operator priorities

1. Run the public DEX path without trusted cloud-only dependencies.
2. Prefer a local Tau node over a managed RPC endpoint.
3. Keep the frontend static so it can be mirrored or pinned anywhere.
4. Keep optional confidential / prover surfaces off the critical path.

## Recommended deployment shapes

### 1. Rootless container on a VPS, bare metal box, or home server

The shipped container already runs as a non-root user and is compatible with
read-only filesystems plus tmpfs mounts.

Use:

```bash
docker compose up -d
```

or a rootless engine such as Podman:

```bash
podman compose up -d
```

Best practice:

- leave `TAU_NET_RPC` unset unless you intentionally want a remote fallback
- keep `API_HOST=127.0.0.1` unless you explicitly expose the API
- keep `CORS_ORIGINS` empty for same-origin hosting
- set `DEMO_API_TOKEN` if demo/dev APIs are reachable from non-loopback binds

### 2. Local-node-first operator mode

The API/container should not depend on a hosted Tau RPC by default.

For serious operators, run a local Tau Testnet node and point any optional RPC
consumers at that node. The local node path is documented here:

- `docs/tau_testnet_local_node.md`

There is also an optional compose profile for packaged local-node hosting:

```bash
docker compose -f docker-compose.yml -f docker-compose.permissionless.yml --profile local-node up -d
```

That profile:

- starts an optional local Tau Testnet node on port `65432`
- reuses the existing DEX app bridge from this repo
- keeps the public path independent from a managed RPC vendor

Prerequisite:

- `external/tau-testnet` must exist in the repo checkout

### 3. Static frontend on IPFS or any static host

The React/Vite frontend can now be built with a relative base path, which makes
it suitable for:

- IPFS gateways
- IPNS
- ENS-backed static hosting
- ordinary static hosting behind nginx/Caddy

Build an IPFS-ready bundle:

```bash
bash tools/publish_ui_ipfs.sh
```

This uses:

- `VITE_BASE_PATH=./` so asset paths stay relative
- optional `VITE_API_BASE` so the static build can target a chosen API

If a local `ipfs` CLI is available, the script also pins the built UI and writes
the resulting CID to `generated/ipfs_ui/ipfs_publish.json`.

The publisher always writes a deterministic release manifest:

- `generated/ipfs_ui/release_manifest.json`

## Runtime frontend config

The static frontend reads an optional runtime config file:

- `tools/dex-ui/public/zenodex-config.json`

Operators can override:

- `apiBase`
- `demoMode`

That allows one static build shape to be reused across:

- same-origin nginx deployments
- IPFS-hosted frontend + external API endpoint
- demo-only offline/public mirrors

## What is not permissionless yet

- The proof-mining / useful-work distribution lane is still a prototype, not a
  finished public miner market.
- Confidential extensions remain optional specialist services.
- IPFS only covers the static frontend, not the Python API or Tau node.

## Objective operator earnings (current prototype lane)

The current shipped prototype for "hosts can earn by useful work" is the
deterministic route-improvement round:

- miners/solvers submit candidate witnesses
- the round replays each witness fail-closed
- the winner is selected by a total key
- an optional payout plan can be emitted from a fixed budget

Artifacts:

- `tools/gpu_jobs/improvement_bounty_round_route_v1.py`
- `tools/proof_verifiers/route_improvement_v1.py`

This is intentionally narrower than "mining":

- it is per-job, not chain-wide issuance
- it is no-minting by default
- it is objective only within a bounded verified round

Example:

```bash
python3 tools/gpu_jobs/improvement_bounty_round_route_v1.py \
  --submission alice=./witness_a.json \
  --submission bob=./witness_b.json \
  --output ./round.json \
  --emit-payout-plan ./payout.json \
  --round-id route-round-1 \
  --reward-pool-before 100 \
  --base-reward 10 \
  --improvement-reward-bps 2500 \
  --max-reward 25 \
  --require-positive-improvement
```

That produces:

- a replayable winner packet
- an optional deterministic payout plan from a fixed budget
- and it can be appended into a public hash-chained ledger:

```bash
python3 tools/permissionless_round_ledger.py \
  --ledger ./round_ledger.jsonl \
  --round ./round.json \
  --payout-plan ./payout.json
```

Verify later:

```bash
python3 tools/permissionless_round_ledger.py --ledger ./round_ledger.jsonl --verify-only --json
```

If you want the same round to bridge into the existing proof-mining reward gate,
emit a proof-mining-compatible claim instead of using the prototype payout plan:

```bash
python3 tools/permissionless_solver_proof_mining_claim.py \
  --round ./round.json \
  --output ./proof_claim.json \
  --round-id route-round-1 \
  --reward-pool-before 100 \
  --base-reward 16 \
  --epoch 2 \
  --proposal-slot 0 \
  --prover-id 0 \
  --chain-id tau-testnet-alpha \
  --prev-state-hash sha256:prev_state \
  --batch-hash sha256:batch \
  --dex-hash-after sha256:dex_after
```

That claim uses the same bounded halving schedule as
`src/tau_specs/proof_mining_reward_32_v1.tau`:

- `reward = max(1, base_reward >> epoch)`
- pool coverage is checked before payout
- the claim carries the exact `i1..i9` Tau inputs used by the gate

The public ledger can append either reward artifact:

```bash
python3 tools/permissionless_round_ledger.py \
  --ledger ./round_ledger.jsonl \
  --round ./round.json \
  --proof-mining-claim ./proof_claim.json
```

Current honest posture:

- the prototype payout plan is still useful for local/operator rounds
- the proof-mining claim is the fail-closed bridge to the existing Tau reward gate
- when explicit binding fields are supplied, uniqueness is tracked by `proposal_hash`
- without explicit binding fields, the claim falls back to a deterministic hash of
  `(round_id, job_digest, witness_hash)` so the artifact is still content-addressed
- neither path is yet a full chain-wide issuance market on its own

Operator preflight for the runtime reward path is exposed via `POST /api/dex/proof_mining_status`.
See `docs/PROOF_MINING_OPERATOR_API.md` for the request/response contract and the exact checks mirrored from the Tau plugin.
A shell wrapper is also available: `python3 tools/permissionless_proof_mining_status.py ...` for local or HTTP-backed preflight.

## Production posture

Current best-practice posture for the public path:

- rootless container or rootless Podman
- same-origin UI + API
- local Tau node where possible
- static frontend optionally mirrored to IPFS
- no mandatory cloud provider dependency

## Rootless Linux service mode

For long-lived Linux operator hosts, generate a user-systemd service:

```bash
python3 tools/generate_operator_systemd.py \
  --engine podman \
  --local-node \
  --out ~/.config/systemd/user/zenodex-operator.service

systemctl --user daemon-reload
systemctl --user enable --now zenodex-operator.service
```

Before enabling it, run a preflight:

```bash
python3 tools/permissionless_operator_preflight.py --engine podman --local-node --ipfs --json
```
