#![no_std]

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cmp::Ordering;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const PROOF_TYPE: &str = "risc0.tauswap_transition.v1";
pub const JOURNAL_VERSION: u32 = 1;

pub const MIN_LP_LOCK: u128 = 1000;

pub const CURVE_TAG: &str = "CPMM";
pub const CURVE_PARAMS: &str = "";

pub const NATIVE_ASSET: &str = "0x0000000000000000000000000000000000000000000000000000000000000000";
pub const LP_LOCK_PUBKEY: &str =
    "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FaucetMintV1 {
    pub pubkey: String,
    pub asset: String,
    pub amount: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FeeAccumulatorV1 {
    pub dust: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VaultV1 {
    pub acc_reward_per_share: u128,
    pub last_update_acc: u128,
    pub pending_rewards: u128,
    pub reward_balance: u128,
    pub staked_lp_shares: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OracleV1 {
    pub max_staleness_seconds: u64,
    pub price_timestamp: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DexBalanceEntryV1 {
    pub pubkey: String,
    pub asset: String,
    pub amount: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DexPoolEntryV1 {
    pub pool_id: String,
    pub asset0: String,
    pub asset1: String,
    pub reserve0: u128,
    pub reserve1: u128,
    pub fee_bps: u32,
    pub lp_supply: u128,
    pub status: String,
    pub created_at: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DexLpBalanceEntryV1 {
    pub pubkey: String,
    pub pool_id: String,
    pub amount: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DexSnapshotV1 {
    pub version: u32,
    #[serde(default)]
    pub balances: Vec<DexBalanceEntryV1>,
    #[serde(default)]
    pub pools: Vec<DexPoolEntryV1>,
    #[serde(default)]
    pub lp_balances: Vec<DexLpBalanceEntryV1>,
    pub fee_accumulator: FeeAccumulatorV1,
    pub vault: Option<VaultV1>,
    pub oracle: Option<OracleV1>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChainBalanceV1 {
    pub pubkey: String,
    pub amount: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CreatePoolIntentV1 {
    pub module: String,
    pub version: String,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub asset0: String,
    pub asset1: String,
    pub fee_bps: u32,
    pub amount0: u128,
    pub amount1: u128,
    pub salt: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SwapExactInIntentV1 {
    pub module: String,
    pub version: String,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub pool_id: String,
    pub asset_in: String,
    pub asset_out: String,
    pub amount_in: u128,
    pub min_amount_out: u128,
    pub recipient: String,
    pub salt: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DexIntentV1 {
    CreatePool(CreatePoolIntentV1),
    SwapExactIn(SwapExactInIntentV1),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SignedIntentV1 {
    pub intent: DexIntentV1,
    pub signature: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TauTxAppOpsV1 {
    pub has_faucet: bool,
    #[serde(default)]
    pub faucet_mint: Vec<FaucetMintV1>,
    pub has_intents: bool,
    #[serde(default)]
    pub intents: Vec<SignedIntentV1>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TauTxV1 {
    pub sender_pubkey: String,
    pub app_ops: TauTxAppOpsV1,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateProofInputV1 {
    pub state_hash: [u8; 32],
    pub block_timestamp: u64,
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub pre_state: DexSnapshotV1,
    pub txs: Vec<TauTxV1>,
    pub chain_balances_post: Vec<ChainBalanceV1>,
    pub expected_post_app_hash: [u8; 32],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateProofJournalV1 {
    pub journal_version: u32,
    pub state_hash: [u8; 32],
    pub txs_commitment: [u8; 32],
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub post_app_hash: [u8; 32],
}

#[derive(Clone, Debug)]
pub enum TransitionError {
    InvalidInput(&'static str),
    Unsupported(&'static str),
    Arithmetic(&'static str),
}

#[derive(Clone, Debug)]
pub struct DexStateV1 {
    balances: BTreeMap<(String, String), u128>,
    pools: BTreeMap<String, DexPoolEntryV1>,
    lp_balances: BTreeMap<(String, String), u128>,
    fee_accumulator: FeeAccumulatorV1,
    vault: Option<VaultV1>,
    oracle: Option<OracleV1>,
}

impl DexStateV1 {
    pub fn empty() -> Self {
        Self {
            balances: BTreeMap::new(),
            pools: BTreeMap::new(),
            lp_balances: BTreeMap::new(),
            fee_accumulator: FeeAccumulatorV1 { dust: 0 },
            vault: None,
            oracle: None,
        }
    }

    pub fn from_snapshot(snapshot: DexSnapshotV1) -> Result<Self, TransitionError> {
        if snapshot.version != 1 {
            return Err(TransitionError::Unsupported("unsupported snapshot version"));
        }

        let mut balances: BTreeMap<(String, String), u128> = BTreeMap::new();
        for entry in snapshot.balances {
            if entry.pubkey.is_empty() || entry.asset.is_empty() {
                return Err(TransitionError::InvalidInput("snapshot balance pubkey/asset empty"));
            }
            if entry.amount == 0 {
                continue;
            }
            let key = (entry.pubkey, entry.asset);
            if balances.contains_key(&key) {
                return Err(TransitionError::InvalidInput("duplicate snapshot balance entry"));
            }
            balances.insert(key, entry.amount);
        }

        let mut pools: BTreeMap<String, DexPoolEntryV1> = BTreeMap::new();
        for pool in snapshot.pools {
            if pool.pool_id.is_empty() {
                return Err(TransitionError::InvalidInput("snapshot pool_id empty"));
            }
            if pools.contains_key(&pool.pool_id) {
                return Err(TransitionError::InvalidInput("duplicate snapshot pool_id"));
            }
            pools.insert(pool.pool_id.clone(), pool);
        }

        let mut lp_balances: BTreeMap<(String, String), u128> = BTreeMap::new();
        for entry in snapshot.lp_balances {
            if entry.pubkey.is_empty() || entry.pool_id.is_empty() {
                return Err(TransitionError::InvalidInput("snapshot lp entry pubkey/pool_id empty"));
            }
            if entry.amount == 0 {
                continue;
            }
            let key = (entry.pubkey, entry.pool_id);
            if lp_balances.contains_key(&key) {
                return Err(TransitionError::InvalidInput("duplicate snapshot lp entry"));
            }
            lp_balances.insert(key, entry.amount);
        }

        Ok(Self {
            balances,
            pools,
            lp_balances,
            fee_accumulator: snapshot.fee_accumulator,
            vault: snapshot.vault,
            oracle: snapshot.oracle,
        })
    }

    pub fn to_snapshot(&self) -> DexSnapshotV1 {
        let mut balances: Vec<DexBalanceEntryV1> = self
            .balances
            .iter()
            .map(|((pk, asset), amount)| DexBalanceEntryV1 {
                pubkey: pk.clone(),
                asset: asset.clone(),
                amount: *amount,
            })
            .collect();
        balances.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
            Ordering::Equal => a.asset.cmp(&b.asset),
            other => other,
        });

        let mut pools: Vec<DexPoolEntryV1> = self.pools.values().cloned().collect();
        pools.sort_by(|a, b| a.pool_id.cmp(&b.pool_id));

        let mut lp_balances: Vec<DexLpBalanceEntryV1> = self
            .lp_balances
            .iter()
            .map(|((pk, pool_id), amount)| DexLpBalanceEntryV1 {
                pubkey: pk.clone(),
                pool_id: pool_id.clone(),
                amount: *amount,
            })
            .collect();
        lp_balances.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
            Ordering::Equal => a.pool_id.cmp(&b.pool_id),
            other => other,
        });

        DexSnapshotV1 {
            version: 1,
            balances,
            pools,
            lp_balances,
            fee_accumulator: self.fee_accumulator.clone(),
            vault: self.vault.clone(),
            oracle: self.oracle.clone(),
        }
    }

    pub fn canonical_app_hash_sha256(&self) -> [u8; 32] {
        let snap = self.to_snapshot();
        sha256_canonical_dex_snapshot_v1(&snap)
    }

    pub fn set_balance(&mut self, pubkey: &str, asset: &str, amount: u128) {
        let key = (pubkey.to_string(), asset.to_string());
        if amount == 0 {
            self.balances.remove(&key);
        } else {
            self.balances.insert(key, amount);
        }
    }

    pub fn get_balance(&self, pubkey: &str, asset: &str) -> u128 {
        self.balances
            .get(&(pubkey.to_string(), asset.to_string()))
            .copied()
            .unwrap_or(0)
    }

    pub fn add_balance(&mut self, pubkey: &str, asset: &str, amount: u128) -> Result<(), TransitionError> {
        let current = self.get_balance(pubkey, asset);
        let next = current
            .checked_add(amount)
            .ok_or(TransitionError::Arithmetic("balance overflow"))?;
        self.set_balance(pubkey, asset, next);
        Ok(())
    }

    pub fn sub_balance(&mut self, pubkey: &str, asset: &str, amount: u128) -> Result<(), TransitionError> {
        let current = self.get_balance(pubkey, asset);
        if amount > current {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }
        self.set_balance(pubkey, asset, current - amount);
        Ok(())
    }

    pub fn set_lp(&mut self, pubkey: &str, pool_id: &str, amount: u128) {
        let key = (pubkey.to_string(), pool_id.to_string());
        if amount == 0 {
            self.lp_balances.remove(&key);
        } else {
            self.lp_balances.insert(key, amount);
        }
    }

    pub fn get_lp(&self, pubkey: &str, pool_id: &str) -> u128 {
        self.lp_balances
            .get(&(pubkey.to_string(), pool_id.to_string()))
            .copied()
            .unwrap_or(0)
    }

    pub fn add_lp(&mut self, pubkey: &str, pool_id: &str, amount: u128) -> Result<(), TransitionError> {
        let current = self.get_lp(pubkey, pool_id);
        let next = current
            .checked_add(amount)
            .ok_or(TransitionError::Arithmetic("lp overflow"))?;
        self.set_lp(pubkey, pool_id, next);
        Ok(())
    }

    pub fn sub_lp(&mut self, pubkey: &str, pool_id: &str, amount: u128) -> Result<(), TransitionError> {
        let current = self.get_lp(pubkey, pool_id);
        if amount > current {
            return Err(TransitionError::InvalidInput("insufficient lp balance"));
        }
        self.set_lp(pubkey, pool_id, current - amount);
        Ok(())
    }

    pub fn sync_native_balances_post(&mut self, chain_balances: &[ChainBalanceV1]) {
        // Drop any existing native entries.
        let native = NATIVE_ASSET.to_string();
        let keys_to_drop: Vec<(String, String)> = self
            .balances
            .keys()
            .filter(|(_pk, asset)| asset.as_str() == native.as_str())
            .cloned()
            .collect();
        for k in keys_to_drop {
            self.balances.remove(&k);
        }

        for entry in chain_balances {
            if entry.amount == 0 {
                continue;
            }
            self.set_balance(&entry.pubkey, NATIVE_ASSET, entry.amount);
        }
    }

    pub fn apply_faucet(&mut self, mints: &[FaucetMintV1]) -> Result<(), TransitionError> {
        for mint in mints {
            if mint.pubkey.is_empty() || mint.asset.is_empty() {
                return Err(TransitionError::InvalidInput("faucet mint pubkey/asset empty"));
            }
            if mint.asset == NATIVE_ASSET {
                return Err(TransitionError::InvalidInput("faucet cannot mint native asset"));
            }
            if mint.amount == 0 {
                return Err(TransitionError::InvalidInput("faucet mint amount must be positive"));
            }
            self.add_balance(&mint.pubkey, &mint.asset, mint.amount)?;
        }
        Ok(())
    }

    pub fn apply_tx(&mut self, tx: &TauTxV1, block_timestamp: u64) -> Result<(), TransitionError> {
        if tx.sender_pubkey.is_empty() {
            return Err(TransitionError::InvalidInput("tx.sender_pubkey empty"));
        }

        if tx.app_ops.has_faucet {
            self.apply_faucet(&tx.app_ops.faucet_mint)?;
        }

        if !tx.app_ops.has_intents {
            return Ok(());
        }
        if tx.app_ops.intents.len() > 1 {
            return Err(TransitionError::Unsupported(
                "multiple intents per tx unsupported in proof v1",
            ));
        }
        if tx.app_ops.intents.is_empty() {
            return Ok(());
        }

        let env = &tx.app_ops.intents[0];
        match &env.intent {
            DexIntentV1::CreatePool(intent) => self.apply_create_pool(intent, &tx.sender_pubkey, block_timestamp),
            DexIntentV1::SwapExactIn(intent) => self.apply_swap_exact_in(intent, &tx.sender_pubkey, block_timestamp),
        }
    }

    fn apply_create_pool(
        &mut self,
        intent: &CreatePoolIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput("intent.module must be TauSwap"));
        }
        if intent.kind_str() != "CREATE_POOL" {
            return Err(TransitionError::InvalidInput("intent.kind mismatch"));
        }
        if intent.sender_pubkey != tx_sender_pubkey {
            return Err(TransitionError::InvalidInput(
                "unsigned intent requires tx sender == intent.sender_pubkey",
            ));
        }
        if intent.deadline < block_timestamp {
            return Err(TransitionError::InvalidInput("intent expired"));
        }
        if intent.asset0 >= intent.asset1 {
            return Err(TransitionError::InvalidInput("assets must be in canonical order"));
        }
        if intent.asset0 == NATIVE_ASSET || intent.asset1 == NATIVE_ASSET {
            return Err(TransitionError::Unsupported("native asset unsupported in proof v1"));
        }
        if intent.amount0 == 0 || intent.amount1 == 0 {
            return Err(TransitionError::InvalidInput("initial deposits must be positive"));
        }
        if intent.fee_bps > 10_000 {
            return Err(TransitionError::InvalidInput("fee_bps out of range"));
        }

        let pool_id = compute_pool_id(&intent.asset0, &intent.asset1, intent.fee_bps, CURVE_TAG, CURVE_PARAMS);
        if self.pools.contains_key(&pool_id) {
            return Err(TransitionError::InvalidInput("pool already exists"));
        }

        // Withdraw from sender.
        self.sub_balance(&intent.sender_pubkey, &intent.asset0, intent.amount0)?;
        self.sub_balance(&intent.sender_pubkey, &intent.asset1, intent.amount1)?;

        // LP mint: total supply = floor(sqrt(amount0*amount1))
        let product = intent
            .amount0
            .checked_mul(intent.amount1)
            .ok_or(TransitionError::Arithmetic("amount0*amount1 overflow"))?;
        let lp_supply_total = isqrt_u128(product);
        if lp_supply_total <= MIN_LP_LOCK {
            return Err(TransitionError::InvalidInput("insufficient initial liquidity"));
        }
        let lp_to_creator = lp_supply_total - MIN_LP_LOCK;

        self.add_lp(&intent.sender_pubkey, &pool_id, lp_to_creator)?;
        self.add_lp(LP_LOCK_PUBKEY, &pool_id, MIN_LP_LOCK)?;

        self.pools.insert(
            pool_id.clone(),
            DexPoolEntryV1 {
                pool_id,
                asset0: intent.asset0.clone(),
                asset1: intent.asset1.clone(),
                reserve0: intent.amount0,
                reserve1: intent.amount1,
                fee_bps: intent.fee_bps,
                lp_supply: lp_supply_total,
                status: "ACTIVE".to_string(),
                created_at: 0,
            },
        );
        Ok(())
    }

    fn apply_swap_exact_in(
        &mut self,
        intent: &SwapExactInIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput("intent.module must be TauSwap"));
        }
        if intent.kind_str() != "SWAP_EXACT_IN" {
            return Err(TransitionError::InvalidInput("intent.kind mismatch"));
        }
        if intent.sender_pubkey != tx_sender_pubkey {
            return Err(TransitionError::InvalidInput(
                "unsigned intent requires tx sender == intent.sender_pubkey",
            ));
        }
        if intent.deadline < block_timestamp {
            return Err(TransitionError::InvalidInput("intent expired"));
        }
        if intent.amount_in == 0 {
            return Err(TransitionError::InvalidInput("amount_in must be positive"));
        }
        if intent.asset_in == NATIVE_ASSET || intent.asset_out == NATIVE_ASSET {
            return Err(TransitionError::Unsupported("native asset unsupported in proof v1"));
        }

        let pool = self
            .pools
            .get(&intent.pool_id)
            .cloned()
            .ok_or(TransitionError::InvalidInput("pool not found"))?;
        if pool.status != "ACTIVE" {
            return Err(TransitionError::InvalidInput("pool not active"));
        }
        if !((intent.asset_in == pool.asset0 && intent.asset_out == pool.asset1)
            || (intent.asset_in == pool.asset1 && intent.asset_out == pool.asset0))
        {
            return Err(TransitionError::InvalidInput("swap asset pair mismatch"));
        }

        // Withdraw input from sender.
        self.sub_balance(&intent.sender_pubkey, &intent.asset_in, intent.amount_in)?;

        let (reserve_in, reserve_out) = if intent.asset_in == pool.asset0 {
            (pool.reserve0, pool.reserve1)
        } else {
            (pool.reserve1, pool.reserve0)
        };

        if pool.fee_bps > 10_000 {
            return Err(TransitionError::InvalidInput("pool fee_bps out of range"));
        }
        let fee_total = ceil_div_u128(
            intent.amount_in
                .checked_mul(pool.fee_bps as u128)
                .ok_or(TransitionError::Arithmetic("fee mul overflow"))?,
            10_000,
        );
        if fee_total > intent.amount_in {
            return Err(TransitionError::Arithmetic("fee exceeds amount_in"));
        }
        let net_in = intent.amount_in - fee_total;
        // floor(reserve_out * net_in / (reserve_in + net_in))
        let denom = reserve_in
            .checked_add(net_in)
            .ok_or(TransitionError::Arithmetic("denom overflow"))?;
        if denom == 0 {
            return Err(TransitionError::InvalidInput("invalid reserves"));
        }
        let numerator = reserve_out
            .checked_mul(net_in)
            .ok_or(TransitionError::Arithmetic("numerator overflow"))?;
        let amount_out = numerator / denom;
        if amount_out < intent.min_amount_out {
            return Err(TransitionError::InvalidInput("min_amount_out not met"));
        }
        if amount_out > reserve_out {
            return Err(TransitionError::InvalidInput("insufficient pool reserve_out"));
        }

        // Credit output.
        self.add_balance(&intent.recipient, &intent.asset_out, amount_out)?;

        // Update pool reserves (fee stays in pool as part of amount_in).
        let mut next_pool = pool.clone();
        if intent.asset_in == next_pool.asset0 {
            next_pool.reserve0 = next_pool
                .reserve0
                .checked_add(intent.amount_in)
                .ok_or(TransitionError::Arithmetic("reserve0 overflow"))?;
            next_pool.reserve1 = next_pool
                .reserve1
                .checked_sub(amount_out)
                .ok_or(TransitionError::Arithmetic("reserve1 underflow"))?;
        } else {
            next_pool.reserve1 = next_pool
                .reserve1
                .checked_add(intent.amount_in)
                .ok_or(TransitionError::Arithmetic("reserve1 overflow"))?;
            next_pool.reserve0 = next_pool
                .reserve0
                .checked_sub(amount_out)
                .ok_or(TransitionError::Arithmetic("reserve0 underflow"))?;
        }
        self.pools.insert(intent.pool_id.clone(), next_pool);
        Ok(())
    }
}

impl CreatePoolIntentV1 {
    fn kind_str(&self) -> &'static str {
        "CREATE_POOL"
    }
}

impl SwapExactInIntentV1 {
    fn kind_str(&self) -> &'static str {
        "SWAP_EXACT_IN"
    }
}

pub fn compute_pool_id(asset0: &str, asset1: &str, fee_bps: u32, curve_tag: &str, curve_params: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"TauSwapPool");
    hasher.update(asset0.as_bytes());
    hasher.update(asset1.as_bytes());
    hasher.update((fee_bps as u64).to_string().as_bytes());
    hasher.update(curve_tag.as_bytes());
    hasher.update(curve_params.as_bytes());
    let digest = hasher.finalize();
    let mut out = String::from("0x");
    out.push_str(&hex_lower(&digest));
    out
}

pub fn txs_commitment_v1(txs: &[TauTxV1]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"tau_state_proof_txs_v1:");
    write_u32(&mut hasher, txs.len() as u32);
    for tx in txs {
        write_str(&mut hasher, &tx.sender_pubkey);
        hasher.update([tx.app_ops.has_faucet as u8]);
        if tx.app_ops.has_faucet {
            write_u32(&mut hasher, tx.app_ops.faucet_mint.len() as u32);
            for m in &tx.app_ops.faucet_mint {
                write_str(&mut hasher, &m.pubkey);
                write_str(&mut hasher, &m.asset);
                write_u128(&mut hasher, m.amount);
            }
        }
        hasher.update([tx.app_ops.has_intents as u8]);
        if tx.app_ops.has_intents {
            write_u32(&mut hasher, tx.app_ops.intents.len() as u32);
            for env in &tx.app_ops.intents {
                match &env.intent {
                    DexIntentV1::CreatePool(i) => {
                        hasher.update([0u8]);
                        write_str(&mut hasher, &i.module);
                        write_str(&mut hasher, &i.version);
                        write_str(&mut hasher, &i.intent_id);
                        write_str(&mut hasher, &i.sender_pubkey);
                        write_u64(&mut hasher, i.deadline);
                        write_opt_str(&mut hasher, i.salt.as_deref());
                        write_str(&mut hasher, &i.asset0);
                        write_str(&mut hasher, &i.asset1);
                        write_u32(&mut hasher, i.fee_bps);
                        write_u128(&mut hasher, i.amount0);
                        write_u128(&mut hasher, i.amount1);
                    }
                    DexIntentV1::SwapExactIn(i) => {
                        hasher.update([1u8]);
                        write_str(&mut hasher, &i.module);
                        write_str(&mut hasher, &i.version);
                        write_str(&mut hasher, &i.intent_id);
                        write_str(&mut hasher, &i.sender_pubkey);
                        write_u64(&mut hasher, i.deadline);
                        write_opt_str(&mut hasher, i.salt.as_deref());
                        write_str(&mut hasher, &i.pool_id);
                        write_str(&mut hasher, &i.asset_in);
                        write_str(&mut hasher, &i.asset_out);
                        write_u128(&mut hasher, i.amount_in);
                        write_u128(&mut hasher, i.min_amount_out);
                        write_str(&mut hasher, &i.recipient);
                    }
                }
                write_opt_str(&mut hasher, env.signature.as_deref());
            }
        }
    }
    hasher.finalize().into()
}

pub fn sha256_canonical_dex_snapshot_v1(snapshot: &DexSnapshotV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hash_canonical_dex_snapshot_v1(&mut hasher, snapshot);
    hasher.finalize().into()
}

fn hash_canonical_dex_snapshot_v1(hasher: &mut Sha256, snapshot: &DexSnapshotV1) {
    // Canonical JSON as per Python: json.dumps(sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    // Keys (sorted): balances, fee_accumulator, lp_balances, oracle, pools, vault, version
    hasher.update(b"{");

    // "balances": [...]
    hasher.update(b"\"balances\":");
    hash_balances(hasher, &snapshot.balances);

    hasher.update(b",\"fee_accumulator\":");
    hash_fee_acc(hasher, &snapshot.fee_accumulator);

    hasher.update(b",\"lp_balances\":");
    hash_lp_balances(hasher, &snapshot.lp_balances);

    hasher.update(b",\"oracle\":");
    match &snapshot.oracle {
        None => hasher.update(b"null"),
        Some(o) => hash_oracle(hasher, o),
    }

    hasher.update(b",\"pools\":");
    hash_pools(hasher, &snapshot.pools);

    hasher.update(b",\"vault\":");
    match &snapshot.vault {
        None => hasher.update(b"null"),
        Some(v) => hash_vault(hasher, v),
    }

    hasher.update(b",\"version\":");
    hash_u128_decimal(hasher, snapshot.version as u128);

    hasher.update(b"}");
}

fn hash_balances(hasher: &mut Sha256, balances: &[DexBalanceEntryV1]) {
    let mut entries: Vec<DexBalanceEntryV1> = balances.to_vec();
    entries.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
        Ordering::Equal => a.asset.cmp(&b.asset),
        other => other,
    });
    hasher.update(b"[");
    for (i, e) in entries.iter().enumerate() {
        if i > 0 {
            hasher.update(b",");
        }
        // keys sorted: amount, asset, pubkey
        hasher.update(b"{\"amount\":");
        hash_u128_decimal(hasher, e.amount);
        hasher.update(b",\"asset\":");
        hash_json_string(hasher, &e.asset);
        hasher.update(b",\"pubkey\":");
        hash_json_string(hasher, &e.pubkey);
        hasher.update(b"}");
    }
    hasher.update(b"]");
}

fn hash_pools(hasher: &mut Sha256, pools: &[DexPoolEntryV1]) {
    let mut entries: Vec<DexPoolEntryV1> = pools.to_vec();
    entries.sort_by(|a, b| a.pool_id.cmp(&b.pool_id));
    hasher.update(b"[");
    for (i, p) in entries.iter().enumerate() {
        if i > 0 {
            hasher.update(b",");
        }
        // keys sorted: asset0, asset1, created_at, fee_bps, lp_supply, pool_id, reserve0, reserve1, status
        hasher.update(b"{\"asset0\":");
        hash_json_string(hasher, &p.asset0);
        hasher.update(b",\"asset1\":");
        hash_json_string(hasher, &p.asset1);
        hasher.update(b",\"created_at\":");
        hash_u128_decimal(hasher, p.created_at as u128);
        hasher.update(b",\"fee_bps\":");
        hash_u128_decimal(hasher, p.fee_bps as u128);
        hasher.update(b",\"lp_supply\":");
        hash_u128_decimal(hasher, p.lp_supply);
        hasher.update(b",\"pool_id\":");
        hash_json_string(hasher, &p.pool_id);
        hasher.update(b",\"reserve0\":");
        hash_u128_decimal(hasher, p.reserve0);
        hasher.update(b",\"reserve1\":");
        hash_u128_decimal(hasher, p.reserve1);
        hasher.update(b",\"status\":");
        hash_json_string(hasher, &p.status);
        hasher.update(b"}");
    }
    hasher.update(b"]");
}

fn hash_lp_balances(hasher: &mut Sha256, balances: &[DexLpBalanceEntryV1]) {
    let mut entries: Vec<DexLpBalanceEntryV1> = balances.to_vec();
    entries.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
        Ordering::Equal => a.pool_id.cmp(&b.pool_id),
        other => other,
    });
    hasher.update(b"[");
    for (i, e) in entries.iter().enumerate() {
        if i > 0 {
            hasher.update(b",");
        }
        // keys sorted: amount, pool_id, pubkey
        hasher.update(b"{\"amount\":");
        hash_u128_decimal(hasher, e.amount);
        hasher.update(b",\"pool_id\":");
        hash_json_string(hasher, &e.pool_id);
        hasher.update(b",\"pubkey\":");
        hash_json_string(hasher, &e.pubkey);
        hasher.update(b"}");
    }
    hasher.update(b"]");
}

fn hash_fee_acc(hasher: &mut Sha256, fee: &FeeAccumulatorV1) {
    // keys sorted: dust
    hasher.update(b"{\"dust\":");
    hash_u128_decimal(hasher, fee.dust);
    hasher.update(b"}");
}

fn hash_vault(hasher: &mut Sha256, v: &VaultV1) {
    // keys sorted: acc_reward_per_share, last_update_acc, pending_rewards, reward_balance, staked_lp_shares
    hasher.update(b"{\"acc_reward_per_share\":");
    hash_u128_decimal(hasher, v.acc_reward_per_share);
    hasher.update(b",\"last_update_acc\":");
    hash_u128_decimal(hasher, v.last_update_acc);
    hasher.update(b",\"pending_rewards\":");
    hash_u128_decimal(hasher, v.pending_rewards);
    hasher.update(b",\"reward_balance\":");
    hash_u128_decimal(hasher, v.reward_balance);
    hasher.update(b",\"staked_lp_shares\":");
    hash_u128_decimal(hasher, v.staked_lp_shares);
    hasher.update(b"}");
}

fn hash_oracle(hasher: &mut Sha256, o: &OracleV1) {
    // keys sorted: max_staleness_seconds, price_timestamp
    hasher.update(b"{\"max_staleness_seconds\":");
    hash_u128_decimal(hasher, o.max_staleness_seconds as u128);
    hasher.update(b",\"price_timestamp\":");
    hash_u128_decimal(hasher, o.price_timestamp as u128);
    hasher.update(b"}");
}

fn hash_json_string(hasher: &mut Sha256, s: &str) {
    hasher.update(b"\"");
    for b in s.as_bytes() {
        match *b {
            b'"' => hasher.update(b"\\\""),
            b'\\' => hasher.update(b"\\\\"),
            b'\n' => hasher.update(b"\\n"),
            b'\r' => hasher.update(b"\\r"),
            b'\t' => hasher.update(b"\\t"),
            0x08 => hasher.update(b"\\b"),
            0x0c => hasher.update(b"\\f"),
            0x00..=0x1f => {
                // \u00XX
                let hi = (*b >> 4) & 0x0f;
                let lo = *b & 0x0f;
                hasher.update(b"\\u00");
                hasher.update([hex_nibble(hi), hex_nibble(lo)]);
            }
            _ => hasher.update([*b]),
        }
    }
    hasher.update(b"\"");
}

fn hex_nibble(n: u8) -> u8 {
    match n {
        0..=9 => b'0' + n,
        10..=15 => b'a' + (n - 10),
        _ => b'0',
    }
}

fn hash_u128_decimal(hasher: &mut Sha256, mut n: u128) {
    // Write decimal digits without allocation.
    let mut buf = [0u8; 39];
    let mut i = buf.len();
    if n == 0 {
        hasher.update(b"0");
        return;
    }
    while n > 0 {
        let digit = (n % 10) as u8;
        n /= 10;
        i -= 1;
        buf[i] = b'0' + digit;
    }
    hasher.update(&buf[i..]);
}

fn ceil_div_u128(numer: u128, denom: u128) -> u128 {
    if denom == 0 {
        return 0;
    }
    let q = numer / denom;
    let r = numer % denom;
    if r == 0 {
        q
    } else {
        q + 1
    }
}

fn isqrt_u128(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    // Newton method.
    let mut x0 = n;
    let mut x1 = (x0 + n / x0) / 2;
    while x1 < x0 {
        x0 = x1;
        x1 = (x0 + n / x0) / 2;
    }
    x0
}

fn hex_lower(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(hex_nibble((b >> 4) & 0x0f) as char);
        out.push(hex_nibble(b & 0x0f) as char);
    }
    out
}

fn write_u32(hasher: &mut Sha256, n: u32) {
    hasher.update(n.to_be_bytes());
}

fn write_u64(hasher: &mut Sha256, n: u64) {
    hasher.update(n.to_be_bytes());
}

fn write_u128(hasher: &mut Sha256, n: u128) {
    hasher.update(n.to_be_bytes());
}

fn write_str(hasher: &mut Sha256, s: &str) {
    let b = s.as_bytes();
    write_u32(hasher, b.len() as u32);
    hasher.update(b);
}

fn write_opt_str(hasher: &mut Sha256, s: Option<&str>) {
    match s {
        None => hasher.update([0u8]),
        Some(v) => {
            hasher.update([1u8]);
            write_str(hasher, v);
        }
    }
}
