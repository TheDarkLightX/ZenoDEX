#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cmp::Ordering;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const PROOF_TYPE: &str = "risc0.zenodex_spot_transition.v1";
pub const JOURNAL_VERSION: u32 = 1;

pub const MIN_LP_LOCK: u128 = 1000;

// DbC invariant: Risc0 proof execution must use the same finite liquidity
// domain as the authoritative Python/TauSwap consensus implementation.
pub const DEX_POOL_RESERVE_MAX: u128 = 3_000_000_000;
pub const DEX_LP_AMOUNT_MAX: u128 = 1_000_000_000;
pub const DEX_LP_SUPPLY_MAX: u128 = 3_000_000_000;

pub const CURVE_TAG: &str = "CPMM";
pub const CURVE_PARAMS: &str = "";

pub const NATIVE_ASSET: &str = "0x0000000000000000000000000000000000000000000000000000000000000000";
pub const LP_LOCK_PUBKEY: &str =
    "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";

// DbC precondition helper: reject any scalar outside its consensus domain
// before arithmetic or state mutation can observe it.
fn require_domain_max(
    name: &'static str,
    value: u128,
    maximum: u128,
) -> Result<(), TransitionError> {
    if value > maximum {
        return Err(TransitionError::InvalidInput(name));
    }

    Ok(())
}

fn require_pool_reserves_within_domain(pool: &DexPoolEntryV1) -> Result<(), TransitionError> {
    require_domain_max(
        "pool.reserve0 exceeds domain max",
        pool.reserve0,
        DEX_POOL_RESERVE_MAX,
    )?;
    require_domain_max(
        "pool.reserve1 exceeds domain max",
        pool.reserve1,
        DEX_POOL_RESERVE_MAX,
    )
}

fn require_pool_lp_supply_within_domain(pool: &DexPoolEntryV1) -> Result<(), TransitionError> {
    require_domain_max(
        "pool.lp_supply exceeds domain max",
        pool.lp_supply,
        DEX_LP_SUPPLY_MAX,
    )
}

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
pub struct AddLiquidityIntentV1 {
    pub module: String,
    pub version: String,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub pool_id: String,
    pub amount0_desired: u128,
    pub amount1_desired: u128,
    pub amount0_min: u128,
    pub amount1_min: u128,
    pub recipient: String,
    pub salt: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RemoveLiquidityIntentV1 {
    pub module: String,
    pub version: String,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub pool_id: String,
    pub lp_amount: u128,
    pub amount0_min: u128,
    pub amount1_min: u128,
    pub recipient: String,
    pub salt: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DexIntentV1 {
    CreatePool(CreatePoolIntentV1),
    SwapExactIn(SwapExactInIntentV1),
    AddLiquidity(AddLiquidityIntentV1),
    RemoveLiquidity(RemoveLiquidityIntentV1),
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
pub struct NonceEntryV1 {
    pub pubkey: String,
    pub next_nonce: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TxIngressFactV1 {
    pub sender_pubkey: String,
    pub nonce: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateProofInputV1 {
    pub state_hash: [u8; 32],
    pub block_timestamp: u64,
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub pre_state: DexSnapshotV1,
    pub txs: Vec<TauTxV1>,
    #[serde(default)]
    pub pre_nonces: Vec<NonceEntryV1>,
    #[serde(default)]
    pub tx_ingress: Vec<TxIngressFactV1>,
    pub chain_balances_post: Vec<ChainBalanceV1>,
    pub expected_post_app_hash: [u8; 32],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateProofJournalV1 {
    pub journal_version: u32,
    pub state_hash: [u8; 32],
    pub txs_commitment: [u8; 32],
    pub ingress_commitment: [u8; 32],
    pub pre_nonce_root: [u8; 32],
    pub post_nonce_root: [u8; 32],
    pub accepted_receipts_root: [u8; 32],
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub post_app_hash: [u8; 32],
}

pub fn execute_state_proof_input_v1(
    input: StateProofInputV1,
) -> Result<StateProofJournalV1, TransitionError> {
    let mut state = DexStateV1::from_snapshot(input.pre_state)?;
    let mut nonce_state = NonceStateV1::from_entries(input.pre_nonces)?;

    let computed_pre = state.canonical_app_hash_sha256();
    if input.pre_app_hash_present && computed_pre != input.pre_app_hash {
        return Err(TransitionError::InvalidInput("pre_app_hash mismatch"));
    }
    if input.tx_ingress.len() != input.txs.len() {
        return Err(TransitionError::InvalidInput("tx_ingress length mismatch"));
    }

    let txs_commitment = txs_commitment_v1(&input.txs);
    let ingress_commitment = ingress_commitment_v1(&input.tx_ingress);
    let pre_nonce_root = nonce_state.root();
    let accepted_receipts_root = accepted_receipts_root_v1(&input.txs, &input.tx_ingress)?;

    for (tx, ingress) in input.txs.iter().zip(input.tx_ingress.iter()) {
        nonce_state.apply_ingress(tx, ingress)?;
        state.apply_tx(tx, input.block_timestamp)?;
    }
    let post_nonce_root = nonce_state.root();

    state.sync_native_balances_post(&input.chain_balances_post);

    let post = state.canonical_app_hash_sha256();
    if post != input.expected_post_app_hash {
        return Err(TransitionError::InvalidInput("post_app_hash mismatch"));
    }

    Ok(StateProofJournalV1 {
        journal_version: JOURNAL_VERSION,
        state_hash: input.state_hash,
        txs_commitment,
        ingress_commitment,
        pre_nonce_root,
        post_nonce_root,
        accepted_receipts_root,
        pre_app_hash_present: input.pre_app_hash_present,
        pre_app_hash: input.pre_app_hash,
        post_app_hash: post,
    })
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

#[derive(Clone, Debug)]
pub struct NonceStateV1 {
    next_nonces: BTreeMap<String, u64>,
}

impl NonceStateV1 {
    pub fn from_entries(entries: Vec<NonceEntryV1>) -> Result<Self, TransitionError> {
        let mut next_nonces = BTreeMap::new();
        for entry in entries {
            if entry.pubkey.is_empty() {
                return Err(TransitionError::InvalidInput("nonce pubkey empty"));
            }
            if next_nonces.contains_key(&entry.pubkey) {
                return Err(TransitionError::InvalidInput("duplicate nonce entry"));
            }
            next_nonces.insert(entry.pubkey, entry.next_nonce);
        }
        Ok(Self { next_nonces })
    }

    pub fn root(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"tau_state_proof_nonce_root_v1:");
        write_u32(&mut hasher, self.next_nonces.len() as u32);
        for (pubkey, next_nonce) in &self.next_nonces {
            write_str(&mut hasher, pubkey);
            write_u64(&mut hasher, *next_nonce);
        }
        hasher.finalize().into()
    }

    pub fn apply_ingress(
        &mut self,
        tx: &TauTxV1,
        ingress: &TxIngressFactV1,
    ) -> Result<(), TransitionError> {
        if ingress.sender_pubkey.is_empty() {
            return Err(TransitionError::InvalidInput("ingress sender_pubkey empty"));
        }
        if ingress.sender_pubkey != tx.sender_pubkey {
            return Err(TransitionError::InvalidInput("ingress sender mismatch"));
        }
        let expected = self
            .next_nonces
            .get(&ingress.sender_pubkey)
            .copied()
            .unwrap_or(0);
        if ingress.nonce != expected {
            return Err(TransitionError::InvalidInput("ingress nonce mismatch"));
        }
        let next = expected
            .checked_add(1)
            .ok_or(TransitionError::Arithmetic("nonce overflow"))?;
        self.next_nonces.insert(ingress.sender_pubkey.clone(), next);
        Ok(())
    }
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
                return Err(TransitionError::InvalidInput(
                    "snapshot balance pubkey/asset empty",
                ));
            }
            if entry.amount == 0 {
                continue;
            }
            let key = (entry.pubkey, entry.asset);
            if balances.contains_key(&key) {
                return Err(TransitionError::InvalidInput(
                    "duplicate snapshot balance entry",
                ));
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
                return Err(TransitionError::InvalidInput(
                    "snapshot lp entry pubkey/pool_id empty",
                ));
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

    pub fn add_balance(
        &mut self,
        pubkey: &str,
        asset: &str,
        amount: u128,
    ) -> Result<(), TransitionError> {
        let current = self.get_balance(pubkey, asset);
        let next = current
            .checked_add(amount)
            .ok_or(TransitionError::Arithmetic("balance overflow"))?;
        self.set_balance(pubkey, asset, next);
        Ok(())
    }

    pub fn sub_balance(
        &mut self,
        pubkey: &str,
        asset: &str,
        amount: u128,
    ) -> Result<(), TransitionError> {
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

    pub fn add_lp(
        &mut self,
        pubkey: &str,
        pool_id: &str,
        amount: u128,
    ) -> Result<(), TransitionError> {
        let current = self.get_lp(pubkey, pool_id);
        let next = current
            .checked_add(amount)
            .ok_or(TransitionError::Arithmetic("lp overflow"))?;
        self.set_lp(pubkey, pool_id, next);
        Ok(())
    }

    pub fn sub_lp(
        &mut self,
        pubkey: &str,
        pool_id: &str,
        amount: u128,
    ) -> Result<(), TransitionError> {
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
                return Err(TransitionError::InvalidInput(
                    "faucet mint pubkey/asset empty",
                ));
            }
            if mint.asset == NATIVE_ASSET {
                return Err(TransitionError::InvalidInput(
                    "faucet cannot mint native asset",
                ));
            }
            if mint.amount == 0 {
                return Err(TransitionError::InvalidInput(
                    "faucet mint amount must be positive",
                ));
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
            DexIntentV1::CreatePool(intent) => {
                self.apply_create_pool(intent, &tx.sender_pubkey, block_timestamp)
            }
            DexIntentV1::SwapExactIn(intent) => {
                self.apply_swap_exact_in(intent, &tx.sender_pubkey, block_timestamp)
            }
            DexIntentV1::AddLiquidity(intent) => {
                self.apply_add_liquidity(intent, &tx.sender_pubkey, block_timestamp)
            }
            DexIntentV1::RemoveLiquidity(intent) => {
                self.apply_remove_liquidity(intent, &tx.sender_pubkey, block_timestamp)
            }
        }
    }

    fn apply_create_pool(
        &mut self,
        intent: &CreatePoolIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput(
                "intent.module must be TauSwap",
            ));
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
            return Err(TransitionError::InvalidInput(
                "assets must be in canonical order",
            ));
        }
        if intent.asset0 == NATIVE_ASSET || intent.asset1 == NATIVE_ASSET {
            return Err(TransitionError::Unsupported(
                "native asset unsupported in proof v1",
            ));
        }
        if intent.amount0 == 0 || intent.amount1 == 0 {
            return Err(TransitionError::InvalidInput(
                "initial deposits must be positive",
            ));
        }
        if intent.fee_bps > 10_000 {
            return Err(TransitionError::InvalidInput("fee_bps out of range"));
        }

        let pool_id = compute_pool_id(
            &intent.asset0,
            &intent.asset1,
            intent.fee_bps,
            CURVE_TAG,
            CURVE_PARAMS,
        );
        if self.pools.contains_key(&pool_id) {
            return Err(TransitionError::InvalidInput("pool already exists"));
        }
        if intent.amount0 > self.get_balance(&intent.sender_pubkey, &intent.asset0) {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }
        if intent.amount1 > self.get_balance(&intent.sender_pubkey, &intent.asset1) {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }

        // LP mint: total supply = floor(sqrt(amount0*amount1))
        let product = intent
            .amount0
            .checked_mul(intent.amount1)
            .ok_or(TransitionError::Arithmetic("amount0*amount1 overflow"))?;
        let lp_supply_total = isqrt_u128(product);
        if lp_supply_total <= MIN_LP_LOCK {
            return Err(TransitionError::InvalidInput(
                "insufficient initial liquidity",
            ));
        }
        let lp_to_creator = lp_supply_total - MIN_LP_LOCK;

        // Withdraw from sender only after all pool-creation validity checks pass.
        self.sub_balance(&intent.sender_pubkey, &intent.asset0, intent.amount0)?;
        self.sub_balance(&intent.sender_pubkey, &intent.asset1, intent.amount1)?;

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
            return Err(TransitionError::InvalidInput(
                "intent.module must be TauSwap",
            ));
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
            return Err(TransitionError::Unsupported(
                "native asset unsupported in proof v1",
            ));
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

        if intent.amount_in > self.get_balance(&intent.sender_pubkey, &intent.asset_in) {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }

        let (reserve_in, reserve_out) = if intent.asset_in == pool.asset0 {
            (pool.reserve0, pool.reserve1)
        } else {
            (pool.reserve1, pool.reserve0)
        };

        if pool.fee_bps > 10_000 {
            return Err(TransitionError::InvalidInput("pool fee_bps out of range"));
        }
        let fee_total = ceil_div_u128(
            intent
                .amount_in
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
        if amount_out == 0 {
            return Err(TransitionError::InvalidInput("amount_out is zero"));
        }
        if amount_out < intent.min_amount_out {
            return Err(TransitionError::InvalidInput("min_amount_out not met"));
        }
        if amount_out > reserve_out {
            return Err(TransitionError::InvalidInput(
                "insufficient pool reserve_out",
            ));
        }

        // Withdraw input from sender only after all quote validity checks pass.
        self.sub_balance(&intent.sender_pubkey, &intent.asset_in, intent.amount_in)?;

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

    fn apply_add_liquidity(
        &mut self,
        intent: &AddLiquidityIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput(
                "intent.module must be TauSwap",
            ));
        }
        if intent.kind_str() != "ADD_LIQUIDITY" {
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
        if intent.recipient.is_empty() {
            return Err(TransitionError::InvalidInput("recipient empty"));
        }
        if intent.amount0_desired == 0 || intent.amount1_desired == 0 {
            return Err(TransitionError::InvalidInput(
                "desired amounts must be positive",
            ));
        }
        require_domain_max(
            "amount0_desired exceeds domain max",
            intent.amount0_desired,
            DEX_LP_AMOUNT_MAX,
        )?;
        require_domain_max(
            "amount1_desired exceeds domain max",
            intent.amount1_desired,
            DEX_LP_AMOUNT_MAX,
        )?;
        require_domain_max(
            "amount0_min exceeds domain max",
            intent.amount0_min,
            DEX_LP_AMOUNT_MAX,
        )?;
        require_domain_max(
            "amount1_min exceeds domain max",
            intent.amount1_min,
            DEX_LP_AMOUNT_MAX,
        )?;

        let pool = self
            .pools
            .get(&intent.pool_id)
            .cloned()
            .ok_or(TransitionError::InvalidInput("pool not found"))?;
        if pool.status != "ACTIVE" {
            return Err(TransitionError::InvalidInput("pool not active"));
        }
        require_pool_reserves_within_domain(&pool)?;
        require_pool_lp_supply_within_domain(&pool)?;
        if pool.asset0 == NATIVE_ASSET || pool.asset1 == NATIVE_ASSET {
            return Err(TransitionError::Unsupported(
                "native asset unsupported in proof v1",
            ));
        }
        if pool.reserve0 == 0 || pool.reserve1 == 0 {
            return Err(TransitionError::InvalidInput(
                "cannot add liquidity to empty pool",
            ));
        }

        let lhs = intent
            .amount0_desired
            .checked_mul(pool.reserve1)
            .ok_or(TransitionError::Arithmetic("optimal lhs overflow"))?;
        let rhs = intent
            .amount1_desired
            .checked_mul(pool.reserve0)
            .ok_or(TransitionError::Arithmetic("optimal rhs overflow"))?;
        let (amount0_used, amount1_used) = if lhs <= rhs {
            (
                intent.amount0_desired,
                intent
                    .amount0_desired
                    .checked_mul(pool.reserve1)
                    .ok_or(TransitionError::Arithmetic("amount1_used overflow"))?
                    / pool.reserve0,
            )
        } else {
            (
                intent
                    .amount1_desired
                    .checked_mul(pool.reserve0)
                    .ok_or(TransitionError::Arithmetic("amount0_used overflow"))?
                    / pool.reserve1,
                intent.amount1_desired,
            )
        };

        if amount0_used < intent.amount0_min {
            return Err(TransitionError::InvalidInput("amount0_used below minimum"));
        }
        if amount1_used < intent.amount1_min {
            return Err(TransitionError::InvalidInput("amount1_used below minimum"));
        }

        let liquidity0 = amount0_used
            .checked_mul(pool.lp_supply)
            .ok_or(TransitionError::Arithmetic("liquidity0 overflow"))?
            / pool.reserve0;
        let liquidity1 = amount1_used
            .checked_mul(pool.lp_supply)
            .ok_or(TransitionError::Arithmetic("liquidity1 overflow"))?
            / pool.reserve1;
        let lp_minted = core::cmp::min(liquidity0, liquidity1);
        if lp_minted == 0 {
            return Err(TransitionError::InvalidInput("liquidity_minted is zero"));
        }

        if amount0_used > self.get_balance(&intent.sender_pubkey, &pool.asset0) {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }
        if amount1_used > self.get_balance(&intent.sender_pubkey, &pool.asset1) {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }

        let mut next_pool = pool.clone();
        next_pool.reserve0 = next_pool
            .reserve0
            .checked_add(amount0_used)
            .ok_or(TransitionError::Arithmetic("reserve0 overflow"))?;
        next_pool.reserve1 = next_pool
            .reserve1
            .checked_add(amount1_used)
            .ok_or(TransitionError::Arithmetic("reserve1 overflow"))?;
        next_pool.lp_supply = next_pool
            .lp_supply
            .checked_add(lp_minted)
            .ok_or(TransitionError::Arithmetic("lp_supply overflow"))?;
        // DbC postcondition: the committed pool state remains in the consensus domain.
        require_pool_reserves_within_domain(&next_pool)?;
        require_pool_lp_supply_within_domain(&next_pool)?;

        self.sub_balance(&intent.sender_pubkey, &pool.asset0, amount0_used)?;
        self.sub_balance(&intent.sender_pubkey, &pool.asset1, amount1_used)?;
        self.add_lp(&intent.recipient, &intent.pool_id, lp_minted)?;
        self.pools.insert(intent.pool_id.clone(), next_pool);
        Ok(())
    }

    fn apply_remove_liquidity(
        &mut self,
        intent: &RemoveLiquidityIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput(
                "intent.module must be TauSwap",
            ));
        }
        if intent.kind_str() != "REMOVE_LIQUIDITY" {
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
        if intent.recipient.is_empty() {
            return Err(TransitionError::InvalidInput("recipient empty"));
        }
        if intent.lp_amount == 0 {
            return Err(TransitionError::InvalidInput("lp_amount must be positive"));
        }
        require_domain_max(
            "lp_amount exceeds domain max",
            intent.lp_amount,
            DEX_LP_SUPPLY_MAX,
        )?;
        require_domain_max(
            "amount0_min exceeds domain max",
            intent.amount0_min,
            DEX_POOL_RESERVE_MAX,
        )?;
        require_domain_max(
            "amount1_min exceeds domain max",
            intent.amount1_min,
            DEX_POOL_RESERVE_MAX,
        )?;

        let pool = self
            .pools
            .get(&intent.pool_id)
            .cloned()
            .ok_or(TransitionError::InvalidInput("pool not found"))?;
        if pool.status != "ACTIVE" {
            return Err(TransitionError::InvalidInput("pool not active"));
        }
        require_pool_reserves_within_domain(&pool)?;
        require_pool_lp_supply_within_domain(&pool)?;
        if pool.asset0 == NATIVE_ASSET || pool.asset1 == NATIVE_ASSET {
            return Err(TransitionError::Unsupported(
                "native asset unsupported in proof v1",
            ));
        }
        if pool.lp_supply == 0 {
            return Err(TransitionError::InvalidInput("lp_supply must be positive"));
        }
        if intent.lp_amount > pool.lp_supply {
            return Err(TransitionError::InvalidInput(
                "cannot burn more LP than supply",
            ));
        }
        if intent.lp_amount > self.get_lp(&intent.sender_pubkey, &intent.pool_id) {
            return Err(TransitionError::InvalidInput("insufficient lp balance"));
        }

        let amount0_out = intent
            .lp_amount
            .checked_mul(pool.reserve0)
            .ok_or(TransitionError::Arithmetic("amount0_out overflow"))?
            / pool.lp_supply;
        let amount1_out = intent
            .lp_amount
            .checked_mul(pool.reserve1)
            .ok_or(TransitionError::Arithmetic("amount1_out overflow"))?
            / pool.lp_supply;
        if amount0_out < intent.amount0_min {
            return Err(TransitionError::InvalidInput("amount0_out below minimum"));
        }
        if amount1_out < intent.amount1_min {
            return Err(TransitionError::InvalidInput("amount1_out below minimum"));
        }

        self.sub_lp(&intent.sender_pubkey, &intent.pool_id, intent.lp_amount)?;
        self.add_balance(&intent.recipient, &pool.asset0, amount0_out)?;
        self.add_balance(&intent.recipient, &pool.asset1, amount1_out)?;

        let mut next_pool = pool.clone();
        next_pool.reserve0 = next_pool
            .reserve0
            .checked_sub(amount0_out)
            .ok_or(TransitionError::Arithmetic("reserve0 underflow"))?;
        next_pool.reserve1 = next_pool
            .reserve1
            .checked_sub(amount1_out)
            .ok_or(TransitionError::Arithmetic("reserve1 underflow"))?;
        next_pool.lp_supply = next_pool
            .lp_supply
            .checked_sub(intent.lp_amount)
            .ok_or(TransitionError::Arithmetic("lp_supply underflow"))?;
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

impl AddLiquidityIntentV1 {
    fn kind_str(&self) -> &'static str {
        "ADD_LIQUIDITY"
    }
}

impl RemoveLiquidityIntentV1 {
    fn kind_str(&self) -> &'static str {
        "REMOVE_LIQUIDITY"
    }
}

pub fn compute_pool_id(
    asset0: &str,
    asset1: &str,
    fee_bps: u32,
    curve_tag: &str,
    curve_params: &str,
) -> String {
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
        hash_tx_v1(&mut hasher, tx);
    }
    hasher.finalize().into()
}

pub fn ingress_commitment_v1(ingress: &[TxIngressFactV1]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"tau_state_proof_ingress_v1:");
    write_u32(&mut hasher, ingress.len() as u32);
    for fact in ingress {
        write_str(&mut hasher, &fact.sender_pubkey);
        write_u64(&mut hasher, fact.nonce);
    }
    hasher.finalize().into()
}

pub fn accepted_receipts_root_v1(
    txs: &[TauTxV1],
    ingress: &[TxIngressFactV1],
) -> Result<[u8; 32], TransitionError> {
    if txs.len() != ingress.len() {
        return Err(TransitionError::InvalidInput("receipt length mismatch"));
    }
    let mut hasher = Sha256::new();
    hasher.update(b"tau_state_proof_accepted_receipts_v1:");
    write_u32(&mut hasher, txs.len() as u32);
    for (idx, (tx, fact)) in txs.iter().zip(ingress.iter()).enumerate() {
        if tx.sender_pubkey != fact.sender_pubkey {
            return Err(TransitionError::InvalidInput("receipt sender mismatch"));
        }
        let tx_commitment = tx_commitment_v1(tx);
        write_u32(&mut hasher, idx as u32);
        write_str(&mut hasher, &fact.sender_pubkey);
        write_u64(&mut hasher, fact.nonce);
        hasher.update([1u8]); // accepted
        hasher.update(tx_commitment);
    }
    Ok(hasher.finalize().into())
}

pub fn tx_commitment_v1(tx: &TauTxV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"tau_state_proof_tx_v1:");
    hash_tx_v1(&mut hasher, tx);
    hasher.finalize().into()
}

fn hash_tx_v1(hasher: &mut Sha256, tx: &TauTxV1) {
    write_str(hasher, &tx.sender_pubkey);
    hasher.update([tx.app_ops.has_faucet as u8]);
    if tx.app_ops.has_faucet {
        write_u32(hasher, tx.app_ops.faucet_mint.len() as u32);
        for m in &tx.app_ops.faucet_mint {
            write_str(hasher, &m.pubkey);
            write_str(hasher, &m.asset);
            write_u128(hasher, m.amount);
        }
    }
    hasher.update([tx.app_ops.has_intents as u8]);
    if tx.app_ops.has_intents {
        write_u32(hasher, tx.app_ops.intents.len() as u32);
        for env in &tx.app_ops.intents {
            match &env.intent {
                DexIntentV1::CreatePool(i) => {
                    hasher.update([0u8]);
                    write_str(hasher, &i.module);
                    write_str(hasher, &i.version);
                    write_str(hasher, &i.intent_id);
                    write_str(hasher, &i.sender_pubkey);
                    write_u64(hasher, i.deadline);
                    write_opt_str(hasher, i.salt.as_deref());
                    write_str(hasher, &i.asset0);
                    write_str(hasher, &i.asset1);
                    write_u32(hasher, i.fee_bps);
                    write_u128(hasher, i.amount0);
                    write_u128(hasher, i.amount1);
                }
                DexIntentV1::SwapExactIn(i) => {
                    hasher.update([1u8]);
                    write_str(hasher, &i.module);
                    write_str(hasher, &i.version);
                    write_str(hasher, &i.intent_id);
                    write_str(hasher, &i.sender_pubkey);
                    write_u64(hasher, i.deadline);
                    write_opt_str(hasher, i.salt.as_deref());
                    write_str(hasher, &i.pool_id);
                    write_str(hasher, &i.asset_in);
                    write_str(hasher, &i.asset_out);
                    write_u128(hasher, i.amount_in);
                    write_u128(hasher, i.min_amount_out);
                    write_str(hasher, &i.recipient);
                }
                DexIntentV1::AddLiquidity(i) => {
                    hasher.update([2u8]);
                    write_str(hasher, &i.module);
                    write_str(hasher, &i.version);
                    write_str(hasher, &i.intent_id);
                    write_str(hasher, &i.sender_pubkey);
                    write_u64(hasher, i.deadline);
                    write_opt_str(hasher, i.salt.as_deref());
                    write_str(hasher, &i.pool_id);
                    write_u128(hasher, i.amount0_desired);
                    write_u128(hasher, i.amount1_desired);
                    write_u128(hasher, i.amount0_min);
                    write_u128(hasher, i.amount1_min);
                    write_str(hasher, &i.recipient);
                }
                DexIntentV1::RemoveLiquidity(i) => {
                    hasher.update([3u8]);
                    write_str(hasher, &i.module);
                    write_str(hasher, &i.version);
                    write_str(hasher, &i.intent_id);
                    write_str(hasher, &i.sender_pubkey);
                    write_u64(hasher, i.deadline);
                    write_opt_str(hasher, i.salt.as_deref());
                    write_str(hasher, &i.pool_id);
                    write_u128(hasher, i.lp_amount);
                    write_u128(hasher, i.amount0_min);
                    write_u128(hasher, i.amount1_min);
                    write_str(hasher, &i.recipient);
                }
            }
            write_opt_str(hasher, env.signature.as_deref());
        }
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    const ASSET0: &str = "0x1111111111111111111111111111111111111111111111111111111111111111";
    const ASSET1: &str = "0x2222222222222222222222222222222222222222222222222222222222222222";
    const SENDER: &str =
        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const RECIPIENT: &str =
        "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    const POOL_ID: &str = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686";

    fn empty_snapshot() -> DexSnapshotV1 {
        DexSnapshotV1 {
            version: 1,
            balances: Vec::new(),
            pools: Vec::new(),
            lp_balances: Vec::new(),
            fee_accumulator: FeeAccumulatorV1 { dust: 0 },
            vault: None,
            oracle: None,
        }
    }

    fn decode_hex_32(s: &str) -> [u8; 32] {
        let hex = s.strip_prefix("0x").unwrap_or(s);
        assert_eq!(hex.len(), 64);
        let mut out = [0u8; 32];
        for i in 0..32 {
            out[i] = u8::from_str_radix(&hex[(i * 2)..(i * 2 + 2)], 16).unwrap();
        }
        out
    }

    fn pool_entry(reserve0: u128, reserve1: u128) -> DexPoolEntryV1 {
        pool_entry_with_supply(reserve0, reserve1, 10_000)
    }

    fn pool_entry_with_supply(reserve0: u128, reserve1: u128, lp_supply: u128) -> DexPoolEntryV1 {
        DexPoolEntryV1 {
            pool_id: POOL_ID.to_string(),
            asset0: ASSET0.to_string(),
            asset1: ASSET1.to_string(),
            reserve0,
            reserve1,
            fee_bps: 30,
            lp_supply,
            status: "ACTIVE".to_string(),
            created_at: 0,
        }
    }

    #[test]
    fn pool_id_matches_python_fixture() {
        assert_eq!(
            compute_pool_id(ASSET0, ASSET1, 30, CURVE_TAG, CURVE_PARAMS),
            POOL_ID
        );
    }

    #[test]
    fn create_pool_transition_matches_python_fixture() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 10_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 20_000,
            },
        ];
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&snapshot),
            decode_hex_32("9fcb79d0240177f11f37905ed608fca2dc60b907a0d8de157ff68a22db2874e4"),
        );

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::CreatePool(CreatePoolIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "create-1".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        asset0: ASSET0.to_string(),
                        asset1: ASSET1.to_string(),
                        fee_bps: 30,
                        amount0: 10_000,
                        amount1: 10_000,
                        salt: None,
                    }),
                }],
            },
        };

        state.apply_tx(&tx, 1).unwrap();
        let post = state.to_snapshot();
        assert_eq!(state.get_balance(SENDER, ASSET0), 0);
        assert_eq!(state.get_balance(SENDER, ASSET1), 10_000);
        assert_eq!(state.get_lp(SENDER, POOL_ID), 9_000);
        assert_eq!(state.get_lp(LP_LOCK_PUBKEY, POOL_ID), MIN_LP_LOCK);
        assert_eq!(post.pools.len(), 1);
        assert_eq!(post.pools[0].pool_id, POOL_ID);
        assert_eq!(post.pools[0].asset0, ASSET0);
        assert_eq!(post.pools[0].asset1, ASSET1);
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].reserve1, 10_000);
        assert_eq!(post.pools[0].fee_bps, 30);
        assert_eq!(post.pools[0].lp_supply, 10_000);
        assert_eq!(post.pools[0].status, "ACTIVE");
        assert_eq!(post.pools[0].created_at, 0);
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&post),
            decode_hex_32("cdedb50a4a2388af0f479062e0ea6d5288b7c460b55237c419b46fc5dd7b6f75"),
        );
    }

    #[test]
    fn create_pool_insufficient_second_asset_rejects_without_mutation() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 10_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 9_999,
            },
        ];

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::CreatePool(CreatePoolIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "create-insufficient-balance".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        asset0: ASSET0.to_string(),
                        asset1: ASSET1.to_string(),
                        fee_bps: 30,
                        amount0: 10_000,
                        amount1: 10_000,
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1),
            Err(TransitionError::InvalidInput("insufficient balance"))
        ));
        assert_eq!(state.get_balance(SENDER, ASSET0), 10_000);
        assert_eq!(state.get_balance(SENDER, ASSET1), 9_999);
        assert_eq!(state.get_lp(SENDER, POOL_ID), 0);
        assert_eq!(state.get_lp(LP_LOCK_PUBKEY, POOL_ID), 0);
        assert!(state.to_snapshot().pools.is_empty());
    }

    #[test]
    fn create_pool_insufficient_initial_liquidity_rejects_without_mutation() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 1_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 1_000,
            },
        ];

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::CreatePool(CreatePoolIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "create-insufficient-liquidity".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        asset0: ASSET0.to_string(),
                        asset1: ASSET1.to_string(),
                        fee_bps: 30,
                        amount0: 1_000,
                        amount1: 1_000,
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1),
            Err(TransitionError::InvalidInput(
                "insufficient initial liquidity"
            ))
        ));
        assert_eq!(state.get_balance(SENDER, ASSET0), 1_000);
        assert_eq!(state.get_balance(SENDER, ASSET1), 1_000);
        assert_eq!(state.get_lp(SENDER, POOL_ID), 0);
        assert_eq!(state.get_lp(LP_LOCK_PUBKEY, POOL_ID), 0);
        assert!(state.to_snapshot().pools.is_empty());
    }

    #[test]
    fn swap_exact_in_transition_matches_python_fixture() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: ASSET0.to_string(),
            amount: 1_000,
        }];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&snapshot),
            decode_hex_32("daa4d1cdf1f5082e87030c1a2962de376d05c4e73bab26e8c2857520be699d02"),
        );

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactIn(SwapExactInIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "swap-1".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_in: 1_000,
                        min_amount_out: 900,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        state.apply_tx(&tx, 1).unwrap();
        let post = state.to_snapshot();
        assert_eq!(state.get_balance(SENDER, ASSET0), 0);
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 906);
        assert_eq!(post.pools.len(), 1);
        assert_eq!(post.pools[0].pool_id, POOL_ID);
        assert_eq!(post.pools[0].asset0, ASSET0);
        assert_eq!(post.pools[0].asset1, ASSET1);
        assert_eq!(post.pools[0].reserve0, 11_000);
        assert_eq!(post.pools[0].reserve1, 9_094);
        assert_eq!(post.pools[0].fee_bps, 30);
        assert_eq!(post.pools[0].lp_supply, 10_000);
        assert_eq!(post.pools[0].status, "ACTIVE");
        assert_eq!(post.pools[0].created_at, 0);
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&post),
            decode_hex_32("168c616c3e9cbc832f9accf6022fcf5153f4611de71115e36a6e540a1230101b"),
        );
    }

    #[test]
    fn add_liquidity_transition_matches_python_fixture() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 1_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 2_000,
            },
        ];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&snapshot),
            decode_hex_32("9e42b9bea6189b4661e752cafffd8a53848c60ffefc57c4e783820a32dc5f97c"),
        );

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::AddLiquidity(AddLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "add-1".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        amount0_desired: 1_000,
                        amount1_desired: 2_000,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        state.apply_tx(&tx, 1).unwrap();
        let post = state.to_snapshot();
        assert_eq!(state.get_balance(SENDER, ASSET0), 0);
        assert_eq!(state.get_balance(SENDER, ASSET1), 1_000);
        assert_eq!(state.get_lp(SENDER, POOL_ID), 1_000);
        assert_eq!(post.pools.len(), 1);
        assert_eq!(post.pools[0].reserve0, 11_000);
        assert_eq!(post.pools[0].reserve1, 11_000);
        assert_eq!(post.pools[0].lp_supply, 11_000);
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&post),
            decode_hex_32("671803d43d456dc0f418cf97700be3d13219c31ff98fa8253545deb6fb04ae4a"),
        );
    }

    #[test]
    fn remove_liquidity_transition_matches_python_fixture() {
        let mut snapshot = empty_snapshot();
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        snapshot.lp_balances = alloc::vec![DexLpBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            pool_id: POOL_ID.to_string(),
            amount: 1_000,
        }];
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&snapshot),
            decode_hex_32("453745178ee31ce1f80ec04b200655091061115dcef49fc5d7993a3ab4c3c785"),
        );

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::RemoveLiquidity(RemoveLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "remove-1".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        lp_amount: 1_000,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        state.apply_tx(&tx, 1).unwrap();
        let post = state.to_snapshot();
        assert_eq!(state.get_balance(SENDER, ASSET0), 1_000);
        assert_eq!(state.get_balance(SENDER, ASSET1), 1_000);
        assert_eq!(state.get_lp(SENDER, POOL_ID), 0);
        assert_eq!(post.pools.len(), 1);
        assert_eq!(post.pools[0].reserve0, 9_000);
        assert_eq!(post.pools[0].reserve1, 9_000);
        assert_eq!(post.pools[0].lp_supply, 9_000);
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&post),
            decode_hex_32("15ba48c3948611ea40af205be1f3186b17f34b77dcf8f88c3d8649dbf7f121ba"),
        );
    }

    #[test]
    fn liquidity_rejections_do_not_mutate_balances_or_pools() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: ASSET0.to_string(),
            amount: 999,
        }];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let add_tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::AddLiquidity(AddLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "add-insufficient-balance".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        amount0_desired: 1_000,
                        amount1_desired: 1_000,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&add_tx, 1),
            Err(TransitionError::InvalidInput("insufficient balance"))
        ));
        assert_eq!(state.get_balance(SENDER, ASSET0), 999);
        assert_eq!(state.get_balance(SENDER, ASSET1), 0);
        assert_eq!(state.get_lp(SENDER, POOL_ID), 0);
        let post = state.to_snapshot();
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].reserve1, 10_000);
        assert_eq!(post.pools[0].lp_supply, 10_000);

        let remove_tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::RemoveLiquidity(RemoveLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "remove-insufficient-lp".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        lp_amount: 1,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&remove_tx, 1),
            Err(TransitionError::InvalidInput("insufficient lp balance"))
        ));
        assert_eq!(state.get_balance(SENDER, ASSET0), 999);
        assert_eq!(state.get_balance(SENDER, ASSET1), 0);
        let post = state.to_snapshot();
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].reserve1, 10_000);
        assert_eq!(post.pools[0].lp_supply, 10_000);
    }

    #[test]
    fn add_liquidity_rejects_consensus_domain_violations() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: DEX_LP_AMOUNT_MAX + 1,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: DEX_LP_AMOUNT_MAX + 1,
            },
        ];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let oversized_add_tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::AddLiquidity(AddLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "add-amount-domain".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        amount0_desired: DEX_LP_AMOUNT_MAX + 1,
                        amount1_desired: 1,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&oversized_add_tx, 1),
            Err(TransitionError::InvalidInput(
                "amount0_desired exceeds domain max"
            ))
        ));
        let post = state.to_snapshot();
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].lp_supply, 10_000);

        let mut capped_snapshot = empty_snapshot();
        capped_snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 2_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 2_000,
            },
        ];
        capped_snapshot.pools = alloc::vec![pool_entry_with_supply(
            DEX_POOL_RESERVE_MAX - 1_000,
            DEX_POOL_RESERVE_MAX - 1_000,
            DEX_LP_SUPPLY_MAX - 1_000,
        )];
        let mut capped_state = DexStateV1::from_snapshot(capped_snapshot).unwrap();
        let cap_crossing_add_tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::AddLiquidity(AddLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "add-post-domain".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        amount0_desired: 1_001,
                        amount1_desired: 1_001,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            capped_state.apply_tx(&cap_crossing_add_tx, 1),
            Err(TransitionError::InvalidInput(
                "pool.reserve0 exceeds domain max"
            ))
        ));
        let capped_post = capped_state.to_snapshot();
        assert_eq!(capped_post.pools[0].reserve0, DEX_POOL_RESERVE_MAX - 1_000);
        assert_eq!(capped_post.pools[0].lp_supply, DEX_LP_SUPPLY_MAX - 1_000);
        assert_eq!(capped_state.get_balance(SENDER, ASSET0), 2_000);
    }

    #[test]
    fn remove_liquidity_rejects_consensus_domain_violations() {
        let mut snapshot = empty_snapshot();
        snapshot.pools = alloc::vec![pool_entry_with_supply(10_000, 10_000, 10_000)];
        snapshot.lp_balances = alloc::vec![DexLpBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            pool_id: POOL_ID.to_string(),
            amount: DEX_LP_SUPPLY_MAX + 1,
        }];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let oversized_remove_tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::RemoveLiquidity(RemoveLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "remove-amount-domain".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        lp_amount: DEX_LP_SUPPLY_MAX + 1,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&oversized_remove_tx, 1),
            Err(TransitionError::InvalidInput(
                "lp_amount exceeds domain max"
            ))
        ));
        let post = state.to_snapshot();
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].lp_supply, 10_000);

        let mut out_of_domain_snapshot = empty_snapshot();
        out_of_domain_snapshot.pools = alloc::vec![pool_entry_with_supply(
            DEX_POOL_RESERVE_MAX + 1,
            10_000,
            10_000,
        )];
        out_of_domain_snapshot.lp_balances = alloc::vec![DexLpBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            pool_id: POOL_ID.to_string(),
            amount: 1,
        }];
        let mut out_of_domain_state = DexStateV1::from_snapshot(out_of_domain_snapshot).unwrap();
        let remove_tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::RemoveLiquidity(RemoveLiquidityIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "remove-pool-domain".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        lp_amount: 1,
                        amount0_min: 0,
                        amount1_min: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            out_of_domain_state.apply_tx(&remove_tx, 1),
            Err(TransitionError::InvalidInput(
                "pool.reserve0 exceeds domain max"
            ))
        ));
        assert_eq!(out_of_domain_state.get_lp(SENDER, POOL_ID), 1);
    }

    #[test]
    fn state_proof_input_execution_commits_expected_journal() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: ASSET0.to_string(),
            amount: 1_000,
        }];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];

        let txs = alloc::vec![TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactIn(SwapExactInIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "swap-1".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_in: 1_000,
                        min_amount_out: 900,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        }];

        let input = StateProofInputV1 {
            state_hash: [7u8; 32],
            block_timestamp: 1,
            pre_app_hash_present: true,
            pre_app_hash: decode_hex_32(
                "daa4d1cdf1f5082e87030c1a2962de376d05c4e73bab26e8c2857520be699d02",
            ),
            pre_state: snapshot,
            txs: txs.clone(),
            pre_nonces: Vec::new(),
            tx_ingress: alloc::vec![TxIngressFactV1 {
                sender_pubkey: SENDER.to_string(),
                nonce: 0,
            }],
            chain_balances_post: Vec::new(),
            expected_post_app_hash: decode_hex_32(
                "168c616c3e9cbc832f9accf6022fcf5153f4611de71115e36a6e540a1230101b",
            ),
        };

        let journal = execute_state_proof_input_v1(input.clone()).unwrap();
        assert_eq!(journal.journal_version, JOURNAL_VERSION);
        assert_eq!(journal.state_hash, [7u8; 32]);
        assert_eq!(journal.txs_commitment, txs_commitment_v1(&txs));
        assert_eq!(
            journal.ingress_commitment,
            ingress_commitment_v1(&input.tx_ingress)
        );
        assert_eq!(
            journal.accepted_receipts_root,
            accepted_receipts_root_v1(&txs, &input.tx_ingress).unwrap()
        );
        assert!(journal.pre_app_hash_present);
        assert_eq!(journal.pre_app_hash, input.pre_app_hash);
        assert_eq!(journal.post_app_hash, input.expected_post_app_hash);

        let mut bad_pre = input.clone();
        bad_pre.pre_app_hash = [8u8; 32];
        assert!(matches!(
            execute_state_proof_input_v1(bad_pre),
            Err(TransitionError::InvalidInput("pre_app_hash mismatch"))
        ));

        let mut bad_post = input.clone();
        bad_post.expected_post_app_hash = [9u8; 32];
        assert!(matches!(
            execute_state_proof_input_v1(bad_post),
            Err(TransitionError::InvalidInput("post_app_hash mismatch"))
        ));

        let mut bad_nonce = input.clone();
        bad_nonce.tx_ingress[0].nonce = 1;
        assert!(matches!(
            execute_state_proof_input_v1(bad_nonce),
            Err(TransitionError::InvalidInput("ingress nonce mismatch"))
        ));
    }

    #[test]
    fn spot_block_liquidity_cycle_matches_python_fixture() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 20_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 20_000,
            },
        ];
        assert_eq!(
            sha256_canonical_dex_snapshot_v1(&snapshot),
            decode_hex_32("9037dde46a93d45ffc398eb1db6a609a8b7274e2530ade503a1e0e04d22b17e0"),
        );

        let txs = alloc::vec![
            TauTxV1 {
                sender_pubkey: SENDER.to_string(),
                app_ops: TauTxAppOpsV1 {
                    has_faucet: false,
                    faucet_mint: Vec::new(),
                    has_intents: true,
                    intents: alloc::vec![SignedIntentV1 {
                        signature: None,
                        intent: DexIntentV1::CreatePool(CreatePoolIntentV1 {
                            module: "TauSwap".to_string(),
                            version: "v1".to_string(),
                            intent_id: "create-1".to_string(),
                            sender_pubkey: SENDER.to_string(),
                            deadline: 100,
                            asset0: ASSET0.to_string(),
                            asset1: ASSET1.to_string(),
                            fee_bps: 30,
                            amount0: 10_000,
                            amount1: 10_000,
                            salt: None,
                        }),
                    }],
                },
            },
            TauTxV1 {
                sender_pubkey: SENDER.to_string(),
                app_ops: TauTxAppOpsV1 {
                    has_faucet: false,
                    faucet_mint: Vec::new(),
                    has_intents: true,
                    intents: alloc::vec![SignedIntentV1 {
                        signature: None,
                        intent: DexIntentV1::AddLiquidity(AddLiquidityIntentV1 {
                            module: "TauSwap".to_string(),
                            version: "v1".to_string(),
                            intent_id: "combo-add-1".to_string(),
                            sender_pubkey: SENDER.to_string(),
                            deadline: 100,
                            pool_id: POOL_ID.to_string(),
                            amount0_desired: 1_000,
                            amount1_desired: 2_000,
                            amount0_min: 0,
                            amount1_min: 0,
                            recipient: SENDER.to_string(),
                            salt: None,
                        }),
                    }],
                },
            },
            TauTxV1 {
                sender_pubkey: SENDER.to_string(),
                app_ops: TauTxAppOpsV1 {
                    has_faucet: false,
                    faucet_mint: Vec::new(),
                    has_intents: true,
                    intents: alloc::vec![SignedIntentV1 {
                        signature: None,
                        intent: DexIntentV1::SwapExactIn(SwapExactInIntentV1 {
                            module: "TauSwap".to_string(),
                            version: "v1".to_string(),
                            intent_id: "combo-swap-1".to_string(),
                            sender_pubkey: SENDER.to_string(),
                            deadline: 100,
                            pool_id: POOL_ID.to_string(),
                            asset_in: ASSET0.to_string(),
                            asset_out: ASSET1.to_string(),
                            amount_in: 1_000,
                            min_amount_out: 900,
                            recipient: RECIPIENT.to_string(),
                            salt: None,
                        }),
                    }],
                },
            },
            TauTxV1 {
                sender_pubkey: SENDER.to_string(),
                app_ops: TauTxAppOpsV1 {
                    has_faucet: false,
                    faucet_mint: Vec::new(),
                    has_intents: true,
                    intents: alloc::vec![SignedIntentV1 {
                        signature: None,
                        intent: DexIntentV1::RemoveLiquidity(RemoveLiquidityIntentV1 {
                            module: "TauSwap".to_string(),
                            version: "v1".to_string(),
                            intent_id: "combo-remove-1".to_string(),
                            sender_pubkey: SENDER.to_string(),
                            deadline: 100,
                            pool_id: POOL_ID.to_string(),
                            lp_amount: 500,
                            amount0_min: 0,
                            amount1_min: 0,
                            recipient: SENDER.to_string(),
                            salt: None,
                        }),
                    }],
                },
            },
        ];

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        for tx in &txs {
            state.apply_tx(tx, 1).unwrap();
        }
        let post_hash = state.canonical_app_hash_sha256();
        assert_eq!(
            hex_lower(&post_hash),
            "b158b93aae996b95f760edc8ac5003c79a6b93eeb821255248059360bb9410c6"
        );
    }

    #[test]
    fn swap_exact_in_zero_output_rejects_like_python_core() {
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: ASSET0.to_string(),
            amount: 2,
        }];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];

        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactIn(SwapExactInIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "swap-zero-output".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_in: 2,
                        min_amount_out: 0,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1),
            Err(TransitionError::InvalidInput("amount_out is zero"))
        ));
        assert_eq!(state.get_balance(SENDER, ASSET0), 2);
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 0);
        let post = state.to_snapshot();
        assert_eq!(post.pools.len(), 1);
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].reserve1, 10_000);
    }
}
