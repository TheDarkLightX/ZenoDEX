## Tau Testnet local node + DEX (app bridge)

This repo can run the Tau Testnet Alpha node locally and bind the DEX state into blocks via a **generic app bridge**.

### 1) Install dependencies

Recommended: use a venv.

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt -r external/tau-testnet/requirements.txt
```

### 2) Start a local Tau Testnet node (with the DEX plugin)

Quickest path (no Docker / no `tau` binary): run Tau in **test mode**:

```bash
export TAU_FORCE_TEST=1
export TAU_ENV=development

# Optional: keep networking local/off for single-node testing
export TAU_BOOTSTRAP_PEERS='[]'
export TAU_DHT_BOOTSTRAP='[]'

# If Tau Testnet defaults disable mining, set the PoA mining keypair explicitly
# (block signatures must verify against TAU_MINER_PUBKEY).
export TAU_MINER_PRIVKEY="11cebd90117355080b392cb7ef2fbdeff1150a124d29058ae48b19bebecd4f09"
export TAU_MINER_PUBKEY="91423993fe5c3a7e0c0d466d9a26f502adf9d39f370649d25d1a6c2500d277212e8aa23e0e10c887cb4b6340d2eebce6"

# Enable the generic app bridge and point it at this repo's DEX plugin
export TAU_APP_BRIDGE_SYS_PATH="$(pwd)"
export TAU_APP_BRIDGE_MODULE="src.integration.tau_testnet_dex_plugin"

# Test-only: allow op "4" minting of non-native assets inside the DEX state
export TAU_DEX_FAUCET=1

python3 external/tau-testnet/server.py --ephemeral-identity
```

Notes:
- `TAU_APP_BRIDGE_SYS_PATH` must include this repo root so tau-testnet can `import src...`.
- In real deployments, you should **not** set `TAU_FORCE_TEST=1` (it bypasses Tau execution) or `TAU_DEX_FAUCET=1`.

### 3) Run an end-to-end smoke test against the node

In another shell (same venv):

```bash
python3 tools/tau_testnet_local_smoke.py --host 127.0.0.1 --port 65432
```

This will:
- connect to the local node over TCP,
- submit a signed tx containing a DEX faucet op + a `CREATE_POOL` intent, then mine a block,
- submit a signed tx with a `SWAP_EXACT_IN` intent, then mine a block,
- query `getappstate full` and assert balances/pool state updated.

### Optional: enable per-block `state_proof` (debug or Risc0)

Debug-only (plumbing smoke test; **not ZK**):

```bash
TAU_STATE_PROOF_DEBUG=1 bash tools/run_tau_testnet_local_smoke.sh
```

Risc0 proof (real ZK receipts; requires the Risc0 toolchain):

```bash
rustup toolchain install risc0
rustup target add riscv32im-risc0-zkvm-elf --toolchain risc0

TAU_STATE_PROOF_RISC0=1 bash tools/run_tau_testnet_local_smoke.sh
```

The Risc0 mode publishes a receipt into `state_proof:<state_hash>` and locally verifies it from the node DB.
