#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cmp::Ordering;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

mod surfaces;
pub use surfaces::*;

pub const PROOF_TYPE: &str = "risc0.zenodex_spot_transition.v1";
pub const JOURNAL_VERSION: u32 = 1;

pub const MIN_LP_LOCK: u128 = 1000;
pub const MAX_PRESTATE_TX_ORDER_ORACLE_TXS: usize = 8;
pub const MAX_FPT_ROUTE_PACKING_TXS: usize = 16;
pub const MAX_FPT_ROUTE_PACKING_POOL_IDS: usize = 64;
pub const MAX_FPT_PREFIX_PACKING_TXS: usize = 64;
pub const MAX_PREFIX_DP_TXS: usize = 32;
pub const MAX_PREFIX_DP_ROUTE_TXS: usize = 32;
pub const MAX_PREFIX_DP_STATES: usize = 50_000;

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
pub struct SwapExactOutIntentV1 {
    pub module: String,
    pub version: String,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub pool_id: String,
    pub asset_in: String,
    pub asset_out: String,
    pub amount_out: u128,
    pub max_amount_in: u128,
    pub recipient: String,
    pub salt: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RouteLegHopV1 {
    pub pool_id: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RouteLegV1 {
    pub hops: Vec<RouteLegHopV1>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RouteIntentV1 {
    pub module: String,
    pub version: String,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub quote_receipt_hash: String,
    pub asset_in: String,
    pub asset_out: String,
    pub leg_indices: Vec<u32>,
    pub legs: Vec<RouteLegV1>,
    pub kind: String,
    pub total_amount_in: u128,
    pub total_min_amount_out: u128,
    pub total_amount_out: u128,
    pub total_max_amount_in: u128,
    pub recipient: String,
    pub salt: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteConflictEdgeV1 {
    pub left_route_index: u32,
    pub right_route_index: u32,
    pub shared_pool_ids: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteConflictScheduleEntryV1 {
    pub route_index: u32,
    pub intent_id: String,
    pub accepted: bool,
    pub conflict_route_index: Option<u32>,
    pub pool_ids: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxPoolConflictScheduleEntryV1 {
    pub tx_index: u32,
    pub accepted: bool,
    pub conflict_tx_index: Option<u32>,
    pub route_read_pool_ids: Vec<String>,
    pub writer_pool_ids: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxPoolConflictOrderPlanV1 {
    pub ordered_tx_indices: Vec<u32>,
    pub accepted_route_count: u32,
    pub deferred_route_count: u32,
    pub schedule: Vec<TxPoolConflictScheduleEntryV1>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DexIntentV1 {
    CreatePool(CreatePoolIntentV1),
    SwapExactIn(SwapExactInIntentV1),
    AddLiquidity(AddLiquidityIntentV1),
    RemoveLiquidity(RemoveLiquidityIntentV1),
    SwapExactOut(SwapExactOutIntentV1),
    Route(RouteIntentV1),
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
    #[serde(default)]
    pub protocol_fee_share_bps: u32,
    #[serde(default)]
    pub protocol_fee_recipient_pubkey: Option<String>,
    #[serde(default)]
    pub tx_execution_order: Vec<u32>,
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
    pub protocol_fee_share_bps: u32,
    pub protocol_fee_recipient_pubkey: Option<String>,
    pub tx_execution_order_commitment: [u8; 32],
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

    if input.protocol_fee_share_bps > 10_000 {
        return Err(TransitionError::InvalidInput(
            "protocol_fee_share_bps out of range",
        ));
    }
    if input.protocol_fee_share_bps > 0 && input.protocol_fee_recipient_pubkey.is_none() {
        return Err(TransitionError::InvalidInput(
            "protocol_fee_recipient_pubkey required when share_bps > 0",
        ));
    }
    let fee_config = ProtocolFeeConfig {
        share_bps: input.protocol_fee_share_bps,
        recipient_pubkey: input.protocol_fee_recipient_pubkey.clone(),
    };

    let execution_order = resolve_tx_execution_order_v1(&input.txs, &input.tx_execution_order)?;
    let txs_commitment = txs_commitment_v1(&input.txs);
    let tx_execution_order_commitment = tx_execution_order_commitment_v1(&execution_order)?;
    let ingress_commitment = ingress_commitment_v1(&input.tx_ingress);
    let pre_nonce_root = nonce_state.root();
    let accepted_receipts_root = accepted_receipts_root_v1(&input.txs, &input.tx_ingress)?;

    for tx_index in execution_order {
        let tx = input.txs.get(tx_index).ok_or(TransitionError::Arithmetic(
            "execution order index out of range",
        ))?;
        let ingress = input
            .tx_ingress
            .get(tx_index)
            .ok_or(TransitionError::Arithmetic(
                "execution ingress index out of range",
            ))?;
        nonce_state.apply_ingress(tx, ingress)?;
        state.apply_tx(tx, input.block_timestamp, &fee_config)?;
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
        tx_execution_order_commitment,
        ingress_commitment,
        pre_nonce_root,
        post_nonce_root,
        accepted_receipts_root,
        pre_app_hash_present: input.pre_app_hash_present,
        pre_app_hash: input.pre_app_hash,
        post_app_hash: post,
        protocol_fee_share_bps: fee_config.share_bps,
        protocol_fee_recipient_pubkey: fee_config.recipient_pubkey.clone(),
    })
}

#[derive(Clone, Debug)]
pub enum TransitionError {
    InvalidInput(&'static str),
    Unsupported(&'static str),
    Arithmetic(&'static str),
}

#[derive(Clone, Debug, Default)]
pub struct ProtocolFeeConfig {
    pub share_bps: u32,
    pub recipient_pubkey: Option<String>,
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

/// Conservation audit inputs: verifies no value created or destroyed across a swap.
struct SwapConservationAudit<'a> {
    pre_state: &'a DexStateV1,
    pool_id: &'a str,
    asset_in: &'a str,
    asset_out: &'a str,
    sender: &'a str,
    recipient: &'a str,
    total_input: u128,
    recipient_credit_out: u128,
    protocol_fee_recipient: Option<&'a str>,
    protocol_fee_credit_in: u128,
}

/// Per-pool snapshot for route conservation audit.
struct RoutePoolAudit {
    pool_id: String,
    asset_in: String,
    asset_out: String,
    reserve_in_delta: u128,
    reserve_out_delta: u128,
    protocol_fee_credit_in: u128,
}

/// Create-pool conservation audit inputs.
struct CreatePoolConservationAudit<'a> {
    pre_state: &'a DexStateV1,
    pool_id: &'a str,
    sender: &'a str,
    asset0: &'a str,
    asset1: &'a str,
    amount0: u128,
    amount1: u128,
    lp_to_creator: u128,
    lp_locked: u128,
    lp_supply_total: u128,
}

/// Add-liquidity conservation audit inputs.
struct AddLiquidityConservationAudit<'a> {
    pre_state: &'a DexStateV1,
    pool_id: &'a str,
    sender: &'a str,
    lp_recipient: &'a str,
    asset0: &'a str,
    asset1: &'a str,
    amount0_used: u128,
    amount1_used: u128,
    lp_minted: u128,
}

/// Remove-liquidity conservation audit inputs.
struct RemoveLiquidityConservationAudit<'a> {
    pre_state: &'a DexStateV1,
    pool_id: &'a str,
    lp_sender: &'a str,
    recipient: &'a str,
    asset0: &'a str,
    asset1: &'a str,
    amount0_out: u128,
    amount1_out: u128,
    lp_amount: u128,
}

/// Route conservation audit: verifies the full value chain balances.
/// sender_debit -> pool_1_in -> pool_1_out -> pool_2_in -> ... -> recipient_credit
/// No value created or destroyed at any hop.
struct RouteConservationAudit<'a> {
    pre_state: &'a DexStateV1,
    sender: &'a str,
    asset_in: &'a str,
    sender_debit: u128,
    recipient: &'a str,
    asset_out: &'a str,
    recipient_credit: u128,
    protocol_fee_recipient: Option<&'a str>,
    pool_audits: Vec<RoutePoolAudit>,
}

fn record_expected_balance_debit(
    changes: &mut BTreeMap<(String, String), (u128, u128)>,
    pubkey: &str,
    asset: &str,
    amount: u128,
) -> Result<(), TransitionError> {
    if amount == 0 {
        return Ok(());
    }
    let entry = changes
        .entry((pubkey.to_string(), asset.to_string()))
        .or_insert((0, 0));
    entry.0 = entry
        .0
        .checked_add(amount)
        .ok_or(TransitionError::Arithmetic(
            "audit: expected debit overflow",
        ))?;
    Ok(())
}

fn record_expected_balance_credit(
    changes: &mut BTreeMap<(String, String), (u128, u128)>,
    pubkey: &str,
    asset: &str,
    amount: u128,
) -> Result<(), TransitionError> {
    if amount == 0 {
        return Ok(());
    }
    let entry = changes
        .entry((pubkey.to_string(), asset.to_string()))
        .or_insert((0, 0));
    entry.1 = entry
        .1
        .checked_add(amount)
        .ok_or(TransitionError::Arithmetic(
            "audit: expected credit overflow",
        ))?;
    Ok(())
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

    pub fn apply_tx(
        &mut self,
        tx: &TauTxV1,
        block_timestamp: u64,
        fee_config: &ProtocolFeeConfig,
    ) -> Result<(), TransitionError> {
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
                self.apply_swap_exact_in(intent, &tx.sender_pubkey, block_timestamp, fee_config)
            }
            DexIntentV1::AddLiquidity(intent) => {
                self.apply_add_liquidity(intent, &tx.sender_pubkey, block_timestamp)
            }
            DexIntentV1::RemoveLiquidity(intent) => {
                self.apply_remove_liquidity(intent, &tx.sender_pubkey, block_timestamp)
            }
            DexIntentV1::SwapExactOut(intent) => {
                self.apply_swap_exact_out(intent, &tx.sender_pubkey, block_timestamp, fee_config)
            }
            DexIntentV1::Route(intent) => {
                let mut staged = self.clone();
                staged.apply_route(intent, &tx.sender_pubkey, block_timestamp, fee_config)?;
                *self = staged;
                Ok(())
            }
        }
    }

    fn apply_create_pool(
        &mut self,
        intent: &CreatePoolIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
    ) -> Result<(), TransitionError> {
        let pre_state = self.clone();
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
        let asset0_canonical = canonical_pool_asset_id(&intent.asset0);
        let asset1_canonical = canonical_pool_asset_id(&intent.asset1);
        if asset0_canonical >= asset1_canonical {
            return Err(TransitionError::InvalidInput(
                "assets must be in canonical order",
            ));
        }
        if asset0_canonical == NATIVE_ASSET || asset1_canonical == NATIVE_ASSET {
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
            &asset0_canonical,
            &asset1_canonical,
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
                pool_id: pool_id.clone(),
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
        self.audit_create_pool_conservation(CreatePoolConservationAudit {
            pre_state: &pre_state,
            pool_id: &pool_id,
            sender: &intent.sender_pubkey,
            asset0: &intent.asset0,
            asset1: &intent.asset1,
            amount0: intent.amount0,
            amount1: intent.amount1,
            lp_to_creator,
            lp_locked: MIN_LP_LOCK,
            lp_supply_total,
        })?;
        Ok(())
    }

    /// Verify the constant-product invariant k' >= k after a swap.
    fn verify_k_invariant(&self, pool_id: &str, k_old: u128) -> Result<(), TransitionError> {
        let pool = self
            .pools
            .get(pool_id)
            .ok_or(TransitionError::InvalidInput("k-invariant: pool not found"))?;
        let k_new = pool
            .reserve0
            .checked_mul(pool.reserve1)
            .ok_or(TransitionError::Arithmetic("k_new overflow"))?;
        if k_new < k_old {
            return Err(TransitionError::Arithmetic(
                "k-invariant violated: k_new < k_old",
            ));
        }
        Ok(())
    }

    fn capture_protocol_fee(
        &mut self,
        fee_config: &ProtocolFeeConfig,
        asset_in: &str,
        fee_total: u128,
    ) -> Result<u128, TransitionError> {
        if fee_config.share_bps == 0 {
            return Ok(0);
        }
        let recipient = fee_config
            .recipient_pubkey
            .as_ref()
            .filter(|r| !r.trim().is_empty())
            .ok_or(TransitionError::InvalidInput(
                "protocol_fee_recipient_pubkey required when share_bps > 0",
            ))?;
        let protocol_fee = (fee_total
            .checked_mul(fee_config.share_bps as u128)
            .ok_or(TransitionError::Arithmetic("protocol_fee mul overflow"))?)
            / 10_000;
        if protocol_fee > fee_total {
            return Err(TransitionError::Arithmetic(
                "protocol_fee exceeds fee_total",
            ));
        }
        if protocol_fee > 0 {
            self.add_balance(recipient, asset_in, protocol_fee)?;
        }
        Ok(protocol_fee)
    }

    /// Mandatory conservation audit after any value-flow change.
    /// Verifies: (1) sender debited total_input, (2) recipient credited output,
    /// (3) input conservation: reserve_in_delta + protocol_fee_delta == total_input,
    /// (4) output conservation: reserve_out_delta == recipient_credit_delta,
    /// (5) protocol-fee credited as delta (not absolute balance).
    fn audit_swap_conservation(
        &self,
        audit: SwapConservationAudit<'_>,
    ) -> Result<(), TransitionError> {
        let pre_pool = audit
            .pre_state
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: pre pool not found"))?;
        let post_pool = self
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: post pool not found"))?;

        let (pre_rin, pre_rout) = if audit.asset_in == pre_pool.asset0 {
            (pre_pool.reserve0, pre_pool.reserve1)
        } else {
            (pre_pool.reserve1, pre_pool.reserve0)
        };
        let (post_rin, post_rout) = if audit.asset_in == post_pool.asset0 {
            (post_pool.reserve0, post_pool.reserve1)
        } else {
            (post_pool.reserve1, post_pool.reserve0)
        };

        let reserve_in_delta = post_rin
            .checked_sub(pre_rin)
            .ok_or(TransitionError::Arithmetic("audit: reserve_in decreased"))?;
        let reserve_out_delta = pre_rout
            .checked_sub(post_rout)
            .ok_or(TransitionError::Arithmetic("audit: reserve_out increased"))?;

        // Sender debit verification (HIGH finding fix)
        // When protocol_fee_recipient == sender, the sender's net debit is
        // total_input - protocol_fee_credit_in (fee credited back to sender).
        let pre_sender_in = audit.pre_state.get_balance(audit.sender, audit.asset_in);
        let post_sender_in = self.get_balance(audit.sender, audit.asset_in);
        let sender_net_delta =
            pre_sender_in
                .checked_sub(post_sender_in)
                .ok_or(TransitionError::Arithmetic(
                    "audit: sender balance increased",
                ))?;
        let expected_sender_debit = if audit.protocol_fee_recipient == Some(audit.sender) {
            audit
                .total_input
                .checked_sub(audit.protocol_fee_credit_in)
                .ok_or(TransitionError::Arithmetic(
                    "audit: pf credit > total_input",
                ))?
        } else {
            audit.total_input
        };
        if sender_net_delta != expected_sender_debit {
            return Err(TransitionError::Arithmetic(
                "audit: sender debit != total_input (net of pf credit)",
            ));
        }

        // Recipient credit verification as delta (not absolute)
        let pre_recipient_out = audit
            .pre_state
            .get_balance(audit.recipient, audit.asset_out);
        let post_recipient_out = self.get_balance(audit.recipient, audit.asset_out);
        let recipient_credit_delta = post_recipient_out.checked_sub(pre_recipient_out).ok_or(
            TransitionError::Arithmetic("audit: recipient balance decreased"),
        )?;
        if recipient_credit_delta != audit.recipient_credit_out {
            return Err(TransitionError::Arithmetic(
                "audit: recipient credit delta mismatch",
            ));
        }

        // Input conservation: reserve_in_delta + protocol_fee_delta == total_input
        let accounted_in = reserve_in_delta
            .checked_add(audit.protocol_fee_credit_in)
            .ok_or(TransitionError::Arithmetic("audit: accounted_in overflow"))?;
        if accounted_in != audit.total_input {
            return Err(TransitionError::Arithmetic(
                "audit: input conservation violated",
            ));
        }

        // Output conservation: reserve_out_delta == recipient_credit_delta
        if reserve_out_delta != audit.recipient_credit_out {
            return Err(TransitionError::Arithmetic(
                "audit: output conservation violated",
            ));
        }

        // Protocol-fee credit as delta (MEDIUM finding fix)
        // Fail-closed: nonzero credit without a recipient is an audit violation.
        // When recipient is configured and distinct from sender, enforce
        // delta == credit_in (including zero). When pf_recipient == sender,
        // the fee credit is embedded in the sender's net balance (already
        // verified by the net debit check above), so a separate delta check
        // would underflow and is skipped.
        if audit.protocol_fee_credit_in > 0 && audit.protocol_fee_recipient.is_none() {
            return Err(TransitionError::InvalidInput(
                "audit: protocol_fee_credit_in > 0 without recipient",
            ));
        }
        if let Some(pf_recipient) = audit.protocol_fee_recipient {
            if pf_recipient != audit.sender {
                let pre_pf = audit.pre_state.get_balance(pf_recipient, audit.asset_in);
                let post_pf = self.get_balance(pf_recipient, audit.asset_in);
                let pf_delta = post_pf
                    .checked_sub(pre_pf)
                    .ok_or(TransitionError::Arithmetic("audit: pf balance decreased"))?;
                if pf_delta != audit.protocol_fee_credit_in {
                    return Err(TransitionError::Arithmetic(
                        "audit: protocol fee delta mismatch",
                    ));
                }
            }
        }

        Ok(())
    }

    /// Audit route conservation: verify the full value chain balances.
    /// For each pool: reserve_in_delta >= reserve_out_delta (k-invariant implies this).
    /// Cross-chain: sender_debit == pool_0.reserve_in_delta (input enters first pool).
    /// Final: last_pool.reserve_out_delta == recipient_credit (output leaves last pool).
    /// Intermediate: pool_i.reserve_out_delta == pool_{i+1}.reserve_in_delta (chain).
    fn audit_route_conservation(
        &self,
        audit: RouteConservationAudit<'_>,
    ) -> Result<(), TransitionError> {
        if audit.pool_audits.is_empty() {
            return Err(TransitionError::InvalidInput("audit: no pools in route"));
        }

        let mut expected_balance_changes: BTreeMap<(String, String), (u128, u128)> =
            BTreeMap::new();
        record_expected_balance_debit(
            &mut expected_balance_changes,
            audit.sender,
            audit.asset_in,
            audit.sender_debit,
        )?;
        record_expected_balance_credit(
            &mut expected_balance_changes,
            audit.recipient,
            audit.asset_out,
            audit.recipient_credit,
        )?;
        if let Some(protocol_fee_recipient) = audit.protocol_fee_recipient {
            for pa in &audit.pool_audits {
                record_expected_balance_credit(
                    &mut expected_balance_changes,
                    protocol_fee_recipient,
                    &pa.asset_in,
                    pa.protocol_fee_credit_in,
                )?;
            }
        } else if audit
            .pool_audits
            .iter()
            .any(|pa| pa.protocol_fee_credit_in != 0)
        {
            return Err(TransitionError::InvalidInput(
                "audit: route protocol fee recipient missing",
            ));
        }

        for ((pubkey, asset), (expected_debit, expected_credit)) in expected_balance_changes {
            let pre_balance = audit.pre_state.get_balance(&pubkey, &asset);
            let post_balance = self.get_balance(&pubkey, &asset);
            let expected_post = pre_balance
                .checked_add(expected_credit)
                .ok_or(TransitionError::Arithmetic(
                    "audit: route expected balance credit overflow",
                ))?
                .checked_sub(expected_debit)
                .ok_or(TransitionError::Arithmetic(
                    "audit: route expected balance debit underflow",
                ))?;
            if post_balance != expected_post {
                return Err(TransitionError::Arithmetic(
                    "audit: route external balance delta mismatch",
                ));
            }
        }

        // Per-pool k-invariant check
        for pa in &audit.pool_audits {
            let pre_pool = audit
                .pre_state
                .pools
                .get(&pa.pool_id)
                .ok_or(TransitionError::InvalidInput("audit: pre pool not found"))?;
            let post_pool = self
                .pools
                .get(&pa.pool_id)
                .ok_or(TransitionError::InvalidInput("audit: post pool not found"))?;

            let (pre_rin, pre_rout) = if pa.asset_in == pre_pool.asset0 {
                (pre_pool.reserve0, pre_pool.reserve1)
            } else {
                (pre_pool.reserve1, pre_pool.reserve0)
            };
            let (post_rin, post_rout) = if pa.asset_in == post_pool.asset0 {
                (post_pool.reserve0, post_pool.reserve1)
            } else {
                (post_pool.reserve1, post_pool.reserve0)
            };

            let actual_rin_delta = post_rin
                .checked_sub(pre_rin)
                .ok_or(TransitionError::Arithmetic("audit: reserve_in decreased"))?;
            let actual_rout_delta = pre_rout
                .checked_sub(post_rout)
                .ok_or(TransitionError::Arithmetic("audit: reserve_out increased"))?;

            if actual_rin_delta != pa.reserve_in_delta {
                return Err(TransitionError::Arithmetic(
                    "audit: route reserve_in_delta mismatch",
                ));
            }
            if actual_rout_delta != pa.reserve_out_delta {
                return Err(TransitionError::Arithmetic(
                    "audit: route reserve_out_delta mismatch",
                ));
            }

            // k-invariant per pool
            let k_old = pre_rin
                .checked_mul(pre_rout)
                .ok_or(TransitionError::Arithmetic("audit: k_old overflow"))?;
            let k_new = post_rin
                .checked_mul(post_rout)
                .ok_or(TransitionError::Arithmetic("audit: k_new overflow"))?;
            if k_new < k_old {
                return Err(TransitionError::Arithmetic(
                    "audit: route k-invariant violated",
                ));
            }
        }

        // Per-pool asset-pair membership: asset_in and asset_out must be the pool's actual assets
        for pa in &audit.pool_audits {
            let pool = self
                .pools
                .get(&pa.pool_id)
                .ok_or(TransitionError::InvalidInput("audit: post pool not found"))?;
            let assets_match = (pa.asset_in == pool.asset0 && pa.asset_out == pool.asset1)
                || (pa.asset_in == pool.asset1 && pa.asset_out == pool.asset0);
            if !assets_match {
                return Err(TransitionError::InvalidInput(
                    "audit: route pool asset pair mismatch",
                ));
            }
        }

        // Boundary: first pool's asset_in == route's asset_in
        if audit.pool_audits[0].asset_in != audit.asset_in {
            return Err(TransitionError::InvalidInput(
                "audit: route first pool asset_in != route asset_in",
            ));
        }

        // Boundary: last pool's asset_out == route's asset_out
        let last = audit.pool_audits.last().unwrap();
        if last.asset_out != audit.asset_out {
            return Err(TransitionError::InvalidInput(
                "audit: route last pool asset_out != route asset_out",
            ));
        }

        // Chain conservation: sender_debit == first pool's reserve_in_delta + protocol_fee
        let first_accounted_in = audit.pool_audits[0]
            .reserve_in_delta
            .checked_add(audit.pool_audits[0].protocol_fee_credit_in)
            .ok_or(TransitionError::Arithmetic(
                "audit: route first accounted input overflow",
            ))?;
        if first_accounted_in != audit.sender_debit {
            return Err(TransitionError::Arithmetic(
                "audit: route input not fully deposited to first pool",
            ));
        }

        // Intermediate chain: pool_i.out == pool_{i+1}.in + protocol_fee (amount AND asset)
        for i in 0..audit.pool_audits.len().saturating_sub(1) {
            let next_accounted_in = audit.pool_audits[i + 1]
                .reserve_in_delta
                .checked_add(audit.pool_audits[i + 1].protocol_fee_credit_in)
                .ok_or(TransitionError::Arithmetic(
                    "audit: route intermediate accounted input overflow",
                ))?;
            if audit.pool_audits[i].reserve_out_delta != next_accounted_in {
                return Err(TransitionError::Arithmetic(
                    "audit: route chain broken at intermediate hop",
                ));
            }
            if audit.pool_audits[i].asset_out != audit.pool_audits[i + 1].asset_in {
                return Err(TransitionError::InvalidInput(
                    "audit: route asset chain mismatch at intermediate hop",
                ));
            }
        }

        // Final: last pool's reserve_out_delta == recipient_credit
        if last.reserve_out_delta != audit.recipient_credit {
            return Err(TransitionError::Arithmetic(
                "audit: route output not fully credited to recipient",
            ));
        }

        Ok(())
    }

    /// Audit add-liquidity conservation: sender debits == pool reserve increases.
    /// LP tokens are newly minted claims, not conserved value.
    fn audit_add_liquidity_conservation(
        &self,
        audit: AddLiquidityConservationAudit<'_>,
    ) -> Result<(), TransitionError> {
        let pre_pool = audit
            .pre_state
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: pre pool not found"))?;
        let post_pool = self
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: post pool not found"))?;

        let r0_delta = post_pool.reserve0.checked_sub(pre_pool.reserve0).ok_or(
            TransitionError::Arithmetic("audit: reserve0 decreased on add_liq"),
        )?;
        let r1_delta = post_pool.reserve1.checked_sub(pre_pool.reserve1).ok_or(
            TransitionError::Arithmetic("audit: reserve1 decreased on add_liq"),
        )?;
        let lp_supply_delta = post_pool.lp_supply.checked_sub(pre_pool.lp_supply).ok_or(
            TransitionError::Arithmetic("audit: lp_supply decreased on add_liq"),
        )?;

        if r0_delta != audit.amount0_used {
            return Err(TransitionError::Arithmetic(
                "audit: add_liq reserve0 delta != amount0_used",
            ));
        }
        if r1_delta != audit.amount1_used {
            return Err(TransitionError::Arithmetic(
                "audit: add_liq reserve1 delta != amount1_used",
            ));
        }
        if lp_supply_delta != audit.lp_minted {
            return Err(TransitionError::Arithmetic(
                "audit: add_liq lp_supply_delta != lp_minted",
            ));
        }

        let pre_s0 = audit.pre_state.get_balance(audit.sender, audit.asset0);
        let post_s0 = self.get_balance(audit.sender, audit.asset0);
        let s0_delta = pre_s0
            .checked_sub(post_s0)
            .ok_or(TransitionError::Arithmetic(
                "audit: sender asset0 increased on add_liq",
            ))?;
        if s0_delta != audit.amount0_used {
            return Err(TransitionError::Arithmetic(
                "audit: add_liq sender debit0 != amount0_used",
            ));
        }

        let pre_s1 = audit.pre_state.get_balance(audit.sender, audit.asset1);
        let post_s1 = self.get_balance(audit.sender, audit.asset1);
        let s1_delta = pre_s1
            .checked_sub(post_s1)
            .ok_or(TransitionError::Arithmetic(
                "audit: sender asset1 increased on add_liq",
            ))?;
        if s1_delta != audit.amount1_used {
            return Err(TransitionError::Arithmetic(
                "audit: add_liq sender debit1 != amount1_used",
            ));
        }

        let pre_lp = audit.pre_state.get_lp(audit.lp_recipient, audit.pool_id);
        let post_lp = self.get_lp(audit.lp_recipient, audit.pool_id);
        let lp_credit = post_lp
            .checked_sub(pre_lp)
            .ok_or(TransitionError::Arithmetic(
                "audit: add_liq lp recipient balance decreased",
            ))?;
        if lp_credit != audit.lp_minted {
            return Err(TransitionError::Arithmetic(
                "audit: add_liq lp recipient credit != lp_minted",
            ));
        }

        Ok(())
    }

    /// Audit remove-liquidity conservation: pool reserve decreases == recipient credits.
    /// LP tokens are burned claims, not conserved value.
    fn audit_remove_liquidity_conservation(
        &self,
        audit: RemoveLiquidityConservationAudit<'_>,
    ) -> Result<(), TransitionError> {
        let pre_pool = audit
            .pre_state
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: pre pool not found"))?;
        let post_pool = self
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: post pool not found"))?;

        let r0_delta = pre_pool.reserve0.checked_sub(post_pool.reserve0).ok_or(
            TransitionError::Arithmetic("audit: reserve0 increased on remove_liq"),
        )?;
        let r1_delta = pre_pool.reserve1.checked_sub(post_pool.reserve1).ok_or(
            TransitionError::Arithmetic("audit: reserve1 increased on remove_liq"),
        )?;
        let lp_delta = pre_pool.lp_supply.checked_sub(post_pool.lp_supply).ok_or(
            TransitionError::Arithmetic("audit: lp_supply increased on remove_liq"),
        )?;

        if r0_delta != audit.amount0_out {
            return Err(TransitionError::Arithmetic(
                "audit: remove_liq reserve0 delta != amount0_out",
            ));
        }
        if r1_delta != audit.amount1_out {
            return Err(TransitionError::Arithmetic(
                "audit: remove_liq reserve1 delta != amount1_out",
            ));
        }
        if lp_delta != audit.lp_amount {
            return Err(TransitionError::Arithmetic(
                "audit: remove_liq lp_supply delta != lp_amount",
            ));
        }

        let pre_lp = audit.pre_state.get_lp(audit.lp_sender, audit.pool_id);
        let post_lp = self.get_lp(audit.lp_sender, audit.pool_id);
        let lp_sender_delta = pre_lp
            .checked_sub(post_lp)
            .ok_or(TransitionError::Arithmetic(
                "audit: remove_liq lp sender balance increased",
            ))?;
        if lp_sender_delta != audit.lp_amount {
            return Err(TransitionError::Arithmetic(
                "audit: remove_liq lp sender debit != lp_amount",
            ));
        }

        let pre_r0 = audit.pre_state.get_balance(audit.recipient, audit.asset0);
        let post_r0 = self.get_balance(audit.recipient, audit.asset0);
        let r0_credit = post_r0
            .checked_sub(pre_r0)
            .ok_or(TransitionError::Arithmetic(
                "audit: recipient asset0 decreased",
            ))?;
        if r0_credit != audit.amount0_out {
            return Err(TransitionError::Arithmetic(
                "audit: remove_liq recipient credit0 != amount0_out",
            ));
        }

        let pre_r1 = audit.pre_state.get_balance(audit.recipient, audit.asset1);
        let post_r1 = self.get_balance(audit.recipient, audit.asset1);
        let r1_credit = post_r1
            .checked_sub(pre_r1)
            .ok_or(TransitionError::Arithmetic(
                "audit: recipient asset1 decreased",
            ))?;
        if r1_credit != audit.amount1_out {
            return Err(TransitionError::Arithmetic(
                "audit: remove_liq recipient credit1 != amount1_out",
            ));
        }

        Ok(())
    }

    /// Audit create-pool conservation: sender debits == pool reserves, LP token conservation.
    fn audit_create_pool_conservation(
        &self,
        audit: CreatePoolConservationAudit<'_>,
    ) -> Result<(), TransitionError> {
        let post_pool = self
            .pools
            .get(audit.pool_id)
            .ok_or(TransitionError::InvalidInput("audit: post pool not found"))?;

        if post_pool.reserve0 != audit.amount0 {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool reserve0 != amount0",
            ));
        }
        if post_pool.reserve1 != audit.amount1 {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool reserve1 != amount1",
            ));
        }
        if post_pool.lp_supply != audit.lp_supply_total {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool lp_supply != lp_supply_total",
            ));
        }

        let lp_sum = audit
            .lp_to_creator
            .checked_add(audit.lp_locked)
            .ok_or(TransitionError::Arithmetic("audit: lp sum overflow"))?;
        if lp_sum != audit.lp_supply_total {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool lp_to_creator + lp_locked != lp_supply_total",
            ));
        }

        let pre_s0 = audit.pre_state.get_balance(audit.sender, audit.asset0);
        let post_s0 = self.get_balance(audit.sender, audit.asset0);
        let s0_delta = pre_s0
            .checked_sub(post_s0)
            .ok_or(TransitionError::Arithmetic(
                "audit: sender asset0 increased on create_pool",
            ))?;
        if s0_delta != audit.amount0 {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool sender debit0 != amount0",
            ));
        }

        let pre_s1 = audit.pre_state.get_balance(audit.sender, audit.asset1);
        let post_s1 = self.get_balance(audit.sender, audit.asset1);
        let s1_delta = pre_s1
            .checked_sub(post_s1)
            .ok_or(TransitionError::Arithmetic(
                "audit: sender asset1 increased on create_pool",
            ))?;
        if s1_delta != audit.amount1 {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool sender debit1 != amount1",
            ));
        }

        // LP credits: creator gets lp_to_creator, lock gets lp_locked
        let pre_creator_lp = audit.pre_state.get_lp(audit.sender, audit.pool_id);
        let post_creator_lp = self.get_lp(audit.sender, audit.pool_id);
        let creator_lp_credit = post_creator_lp
            .checked_sub(pre_creator_lp)
            .ok_or(TransitionError::Arithmetic("audit: creator lp decreased"))?;
        if creator_lp_credit != audit.lp_to_creator {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool creator lp credit != lp_to_creator",
            ));
        }

        let pre_lock_lp = audit.pre_state.get_lp(LP_LOCK_PUBKEY, audit.pool_id);
        let post_lock_lp = self.get_lp(LP_LOCK_PUBKEY, audit.pool_id);
        let lock_lp_credit = post_lock_lp
            .checked_sub(pre_lock_lp)
            .ok_or(TransitionError::Arithmetic("audit: lock lp decreased"))?;
        if lock_lp_credit != audit.lp_locked {
            return Err(TransitionError::Arithmetic(
                "audit: create_pool lock lp credit != lp_locked",
            ));
        }

        Ok(())
    }

    fn apply_swap_exact_in(
        &mut self,
        intent: &SwapExactInIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
        fee_config: &ProtocolFeeConfig,
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

        let pre_state = self.clone();
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
        let k_old = pool
            .reserve0
            .checked_mul(pool.reserve1)
            .ok_or(TransitionError::Arithmetic("k_old overflow"))?;
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

        // Protocol fee capture: floor(fee_total * share_bps / 10000) in asset_in.
        // Python semantics: protocol_fee is deducted from reserve_in and credited
        // to the recipient in the input asset. amount_out is NOT reduced.
        let protocol_fee_amount =
            self.capture_protocol_fee(fee_config, &intent.asset_in, fee_total)?;

        // Withdraw input from sender only after all quote validity checks pass.
        self.sub_balance(&intent.sender_pubkey, &intent.asset_in, intent.amount_in)?;

        // Credit output to recipient (full amount_out, protocol fee is on input side).
        self.add_balance(&intent.recipient, &intent.asset_out, amount_out)?;

        // Update pool reserves: amount_in enters minus protocol_fee, amount_out leaves.
        let reserve_in_delta = intent.amount_in - protocol_fee_amount;
        let mut next_pool = pool.clone();
        if intent.asset_in == next_pool.asset0 {
            next_pool.reserve0 = next_pool
                .reserve0
                .checked_add(reserve_in_delta)
                .ok_or(TransitionError::Arithmetic("reserve0 overflow"))?;
            next_pool.reserve1 = next_pool
                .reserve1
                .checked_sub(amount_out)
                .ok_or(TransitionError::Arithmetic("reserve1 underflow"))?;
        } else {
            next_pool.reserve1 = next_pool
                .reserve1
                .checked_add(reserve_in_delta)
                .ok_or(TransitionError::Arithmetic("reserve1 overflow"))?;
            next_pool.reserve0 = next_pool
                .reserve0
                .checked_sub(amount_out)
                .ok_or(TransitionError::Arithmetic("reserve0 underflow"))?;
        }
        self.pools.insert(intent.pool_id.clone(), next_pool);
        self.verify_k_invariant(&intent.pool_id, k_old)?;
        self.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: &intent.pool_id,
            asset_in: &intent.asset_in,
            asset_out: &intent.asset_out,
            sender: &intent.sender_pubkey,
            recipient: &intent.recipient,
            total_input: intent.amount_in,
            recipient_credit_out: amount_out,
            protocol_fee_recipient: fee_config.recipient_pubkey.as_deref(),
            protocol_fee_credit_in: protocol_fee_amount,
        })?;
        Ok(())
    }

    fn apply_swap_exact_out(
        &mut self,
        intent: &SwapExactOutIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
        fee_config: &ProtocolFeeConfig,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput(
                "intent.module must be TauSwap",
            ));
        }
        if intent.kind_str() != "SWAP_EXACT_OUT" {
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
        if intent.amount_out == 0 {
            return Err(TransitionError::InvalidInput("amount_out must be positive"));
        }
        if intent.max_amount_in == 0 {
            return Err(TransitionError::InvalidInput(
                "max_amount_in must be positive",
            ));
        }
        if intent.asset_in == NATIVE_ASSET || intent.asset_out == NATIVE_ASSET {
            return Err(TransitionError::Unsupported(
                "native asset unsupported in proof v1",
            ));
        }

        let pre_state = self.clone();
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
        let k_old = pool
            .reserve0
            .checked_mul(pool.reserve1)
            .ok_or(TransitionError::Arithmetic("k_old overflow"))?;

        let (reserve_in, reserve_out) = if intent.asset_in == pool.asset0 {
            (pool.reserve0, pool.reserve1)
        } else {
            (pool.reserve1, pool.reserve0)
        };

        if pool.fee_bps > 10_000 {
            return Err(TransitionError::InvalidInput("pool fee_bps out of range"));
        }
        if intent.amount_out >= reserve_out {
            return Err(TransitionError::InvalidInput(
                "amount_out must be less than reserve_out",
            ));
        }

        // Compute amount_in needed to produce amount_out, accounting for fee.
        // CPMM: amount_out = floor(reserve_out * net_in / (reserve_in + net_in))
        // Solve for net_in: net_in = ceil(reserve_in * amount_out / (reserve_out - amount_out))
        let reserve_out_minus = reserve_out
            .checked_sub(intent.amount_out)
            .ok_or(TransitionError::Arithmetic("reserve_out underflow"))?;
        let net_in_num = reserve_in
            .checked_mul(intent.amount_out)
            .ok_or(TransitionError::Arithmetic("net_in numerator overflow"))?;
        let net_in = ceil_div_u128(net_in_num, reserve_out_minus);
        if net_in == 0 {
            return Err(TransitionError::InvalidInput("net_in is zero"));
        }
        // gross_in = ceil(net_in * 10000 / (10000 - fee_bps))
        let denom_fee = 10_000u128
            .checked_sub(pool.fee_bps as u128)
            .ok_or(TransitionError::Arithmetic("fee_bps exceeds 10000"))?;
        if denom_fee == 0 {
            return Err(TransitionError::InvalidInput("fee_bps is 10000"));
        }
        let gross_in = ceil_div_u128(
            net_in
                .checked_mul(10_000)
                .ok_or(TransitionError::Arithmetic("gross_in mul overflow"))?,
            denom_fee,
        );
        if gross_in > intent.max_amount_in {
            return Err(TransitionError::InvalidInput("max_amount_in exceeded"));
        }
        if gross_in > self.get_balance(&intent.sender_pubkey, &intent.asset_in) {
            return Err(TransitionError::InvalidInput("insufficient balance"));
        }

        let fee_total = gross_in - net_in;

        // Protocol fee capture: floor(fee_total * share_bps / 10000) in asset_in.
        let protocol_fee_amount =
            self.capture_protocol_fee(fee_config, &intent.asset_in, fee_total)?;

        // Withdraw input from sender.
        self.sub_balance(&intent.sender_pubkey, &intent.asset_in, gross_in)?;

        // Credit full amount_out to recipient (protocol fee is on input side).
        self.add_balance(&intent.recipient, &intent.asset_out, intent.amount_out)?;

        // Update pool reserves: gross_in enters minus protocol_fee, amount_out leaves.
        let reserve_in_delta = gross_in - protocol_fee_amount;
        let mut next_pool = pool.clone();
        if intent.asset_in == next_pool.asset0 {
            next_pool.reserve0 = next_pool
                .reserve0
                .checked_add(reserve_in_delta)
                .ok_or(TransitionError::Arithmetic("reserve0 overflow"))?;
            next_pool.reserve1 = next_pool
                .reserve1
                .checked_sub(intent.amount_out)
                .ok_or(TransitionError::Arithmetic("reserve1 underflow"))?;
        } else {
            next_pool.reserve1 = next_pool
                .reserve1
                .checked_add(reserve_in_delta)
                .ok_or(TransitionError::Arithmetic("reserve1 overflow"))?;
            next_pool.reserve0 = next_pool
                .reserve0
                .checked_sub(intent.amount_out)
                .ok_or(TransitionError::Arithmetic("reserve0 underflow"))?;
        }
        self.pools.insert(intent.pool_id.clone(), next_pool);
        self.verify_k_invariant(&intent.pool_id, k_old)?;
        self.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: &intent.pool_id,
            asset_in: &intent.asset_in,
            asset_out: &intent.asset_out,
            sender: &intent.sender_pubkey,
            recipient: &intent.recipient,
            total_input: gross_in,
            recipient_credit_out: intent.amount_out,
            protocol_fee_recipient: fee_config.recipient_pubkey.as_deref(),
            protocol_fee_credit_in: protocol_fee_amount,
        })?;
        Ok(())
    }

    fn apply_route(
        &mut self,
        intent: &RouteIntentV1,
        tx_sender_pubkey: &str,
        block_timestamp: u64,
        fee_config: &ProtocolFeeConfig,
    ) -> Result<(), TransitionError> {
        if intent.module != "TauSwap" {
            return Err(TransitionError::InvalidInput(
                "intent.module must be TauSwap",
            ));
        }
        let kind = intent.kind_str();
        if kind != "ROUTE_EXACT_IN" && kind != "ROUTE_EXACT_OUT" {
            return Err(TransitionError::InvalidInput("intent.kind mismatch"));
        }
        let pre_state = self.clone();
        if intent.sender_pubkey != tx_sender_pubkey {
            return Err(TransitionError::InvalidInput(
                "unsigned intent requires tx sender == intent.sender_pubkey",
            ));
        }
        if intent.deadline < block_timestamp {
            return Err(TransitionError::InvalidInput("intent expired"));
        }
        if intent.legs.is_empty() {
            return Err(TransitionError::InvalidInput("route has no legs"));
        }
        // Proof v1 only supports single-hop legs (one pool per leg).
        // Reject duplicate pool_ids across legs to prevent cyclic arbitrage.
        let mut seen_pool_ids: BTreeSet<String> = BTreeSet::new();
        for (i, leg) in intent.legs.iter().enumerate() {
            if leg.hops.len() != 1 {
                return Err(TransitionError::Unsupported("route_multihop_unsupported"));
            }
            let pool_id = &leg.hops[0].pool_id;
            if !seen_pool_ids.insert(pool_id.clone()) {
                return Err(TransitionError::InvalidInput(
                    "route duplicate pool_id across legs",
                ));
            }
            let _ = i;
        }
        // Verify leg_indices cover the full receipt [0, 1, ..., n-1].
        if intent.leg_indices.len() != intent.legs.len() {
            return Err(TransitionError::InvalidInput("leg_indices length mismatch"));
        }
        for (expected, actual) in intent.leg_indices.iter().enumerate() {
            if *actual != expected as u32 {
                return Err(TransitionError::InvalidInput(
                    "leg_indices must cover full receipt",
                ));
            }
        }
        if intent.quote_receipt_hash.is_empty() {
            return Err(TransitionError::InvalidInput("quote_receipt_hash required"));
        }
        let expected_quote_hash = route_quote_receipt_hash_v1(intent, &self.pools, fee_config)?;
        if intent.quote_receipt_hash != expected_quote_hash {
            return Err(TransitionError::InvalidInput("quote_receipt_hash mismatch"));
        }

        match kind {
            "ROUTE_EXACT_IN" => {
                if intent.total_amount_in == 0 {
                    return Err(TransitionError::InvalidInput(
                        "total_amount_in must be positive",
                    ));
                }
                if intent.total_amount_in
                    > self.get_balance(&intent.sender_pubkey, &intent.asset_in)
                {
                    return Err(TransitionError::InvalidInput("insufficient balance"));
                }
                // Execute legs sequentially: each leg is a single-pool swap.
                let mut current_asset = intent.asset_in.clone();
                let mut current_amount = intent.total_amount_in;
                let mut route_pool_audits: Vec<RoutePoolAudit> = Vec::new();
                self.sub_balance(
                    &intent.sender_pubkey,
                    &intent.asset_in,
                    intent.total_amount_in,
                )?;
                for leg in &intent.legs {
                    let pool_id = &leg.hops[0].pool_id;
                    let pool = self
                        .pools
                        .get(pool_id)
                        .cloned()
                        .ok_or(TransitionError::InvalidInput("route pool not found"))?;
                    if pool.status != "ACTIVE" {
                        return Err(TransitionError::InvalidInput("route pool not active"));
                    }
                    let asset_out = if current_asset == pool.asset0 {
                        pool.asset1.clone()
                    } else if current_asset == pool.asset1 {
                        pool.asset0.clone()
                    } else {
                        return Err(TransitionError::InvalidInput("route asset chain mismatch"));
                    };
                    let (reserve_in, reserve_out) = if current_asset == pool.asset0 {
                        (pool.reserve0, pool.reserve1)
                    } else {
                        (pool.reserve1, pool.reserve0)
                    };
                    let fee_total = ceil_div_u128(
                        current_amount
                            .checked_mul(pool.fee_bps as u128)
                            .ok_or(TransitionError::Arithmetic("route fee mul overflow"))?,
                        10_000,
                    );
                    if fee_total > current_amount {
                        return Err(TransitionError::Arithmetic("route fee exceeds amount"));
                    }
                    let net_in = current_amount - fee_total;
                    let denom = reserve_in
                        .checked_add(net_in)
                        .ok_or(TransitionError::Arithmetic("route denom overflow"))?;
                    if denom == 0 {
                        return Err(TransitionError::InvalidInput("route invalid reserves"));
                    }
                    let numerator = reserve_out
                        .checked_mul(net_in)
                        .ok_or(TransitionError::Arithmetic("route numerator overflow"))?;
                    let amount_out = numerator / denom;
                    if amount_out == 0 {
                        return Err(TransitionError::InvalidInput("route amount_out is zero"));
                    }
                    if amount_out > reserve_out {
                        return Err(TransitionError::InvalidInput(
                            "route insufficient reserve_out",
                        ));
                    }
                    let protocol_fee_amount =
                        self.capture_protocol_fee(fee_config, &current_asset, fee_total)?;
                    let reserve_in_delta = current_amount.checked_sub(protocol_fee_amount).ok_or(
                        TransitionError::Arithmetic("route protocol_fee exceeds amount"),
                    )?;
                    // Update pool reserves.
                    let mut next_pool = pool.clone();
                    if current_asset == next_pool.asset0 {
                        next_pool.reserve0 = next_pool
                            .reserve0
                            .checked_add(reserve_in_delta)
                            .ok_or(TransitionError::Arithmetic("route reserve0 overflow"))?;
                        next_pool.reserve1 = next_pool
                            .reserve1
                            .checked_sub(amount_out)
                            .ok_or(TransitionError::Arithmetic("route reserve1 underflow"))?;
                    } else {
                        next_pool.reserve1 = next_pool
                            .reserve1
                            .checked_add(reserve_in_delta)
                            .ok_or(TransitionError::Arithmetic("route reserve1 overflow"))?;
                        next_pool.reserve0 = next_pool
                            .reserve0
                            .checked_sub(amount_out)
                            .ok_or(TransitionError::Arithmetic("route reserve0 underflow"))?;
                    }
                    let leg_asset_in = current_asset.clone();
                    self.pools.insert(pool_id.clone(), next_pool);
                    route_pool_audits.push(RoutePoolAudit {
                        pool_id: pool_id.clone(),
                        asset_in: leg_asset_in,
                        asset_out: asset_out.clone(),
                        reserve_in_delta,
                        reserve_out_delta: amount_out,
                        protocol_fee_credit_in: protocol_fee_amount,
                    });
                    current_asset = asset_out;
                    current_amount = amount_out;
                }
                if current_asset != intent.asset_out {
                    return Err(TransitionError::InvalidInput("route final asset mismatch"));
                }
                if current_amount < intent.total_min_amount_out {
                    return Err(TransitionError::InvalidInput(
                        "route total_min_amount_out not met",
                    ));
                }
                self.add_balance(&intent.recipient, &intent.asset_out, current_amount)?;
                self.audit_route_conservation(RouteConservationAudit {
                    pre_state: &pre_state,
                    sender: &intent.sender_pubkey,
                    asset_in: &intent.asset_in,
                    sender_debit: intent.total_amount_in,
                    recipient: &intent.recipient,
                    asset_out: &intent.asset_out,
                    recipient_credit: current_amount,
                    protocol_fee_recipient: fee_config.recipient_pubkey.as_deref(),
                    pool_audits: route_pool_audits,
                })?;
            }
            "ROUTE_EXACT_OUT" => {
                if intent.total_amount_out == 0 {
                    return Err(TransitionError::InvalidInput(
                        "total_amount_out must be positive",
                    ));
                }
                // For exact-out route, walk legs in reverse to compute required input.
                // Each leg is a single-pool exact-out swap.
                let mut required_in = intent.total_amount_out;
                let mut assets: Vec<String> = Vec::new();
                let mut target_outs: Vec<u128> = Vec::new();
                assets.push(intent.asset_out.clone());
                for leg in intent.legs.iter().rev() {
                    let pool_id = &leg.hops[0].pool_id;
                    let pool = self
                        .pools
                        .get(pool_id)
                        .cloned()
                        .ok_or(TransitionError::InvalidInput("route pool not found"))?;
                    if pool.status != "ACTIVE" {
                        return Err(TransitionError::InvalidInput("route pool not active"));
                    }
                    let out_asset = assets.last().unwrap().clone();
                    let in_asset = if out_asset == pool.asset0 {
                        pool.asset1.clone()
                    } else if out_asset == pool.asset1 {
                        pool.asset0.clone()
                    } else {
                        return Err(TransitionError::InvalidInput("route asset chain mismatch"));
                    };
                    target_outs.push(required_in);
                    let (reserve_in, reserve_out) = if out_asset == pool.asset0 {
                        (pool.reserve1, pool.reserve0)
                    } else {
                        (pool.reserve0, pool.reserve1)
                    };
                    if required_in >= reserve_out {
                        return Err(TransitionError::InvalidInput(
                            "route amount_out >= reserve_out",
                        ));
                    }
                    let reserve_out_minus = reserve_out
                        .checked_sub(required_in)
                        .ok_or(TransitionError::Arithmetic("route reserve_out underflow"))?;
                    let net_in_num = reserve_in
                        .checked_mul(required_in)
                        .ok_or(TransitionError::Arithmetic("route net_in num overflow"))?;
                    let net_in = ceil_div_u128(net_in_num, reserve_out_minus);
                    let denom_fee = 10_000u128
                        .checked_sub(pool.fee_bps as u128)
                        .ok_or(TransitionError::Arithmetic("route fee_bps exceeds 10000"))?;
                    if denom_fee == 0 {
                        return Err(TransitionError::InvalidInput("route fee_bps is 10000"));
                    }
                    let gross_in = ceil_div_u128(
                        net_in
                            .checked_mul(10_000)
                            .ok_or(TransitionError::Arithmetic("route gross_in mul overflow"))?,
                        denom_fee,
                    );
                    required_in = gross_in;
                    assets.push(in_asset);
                }
                assets.reverse();
                target_outs.reverse();
                let route_asset_in = assets.first().unwrap().clone();
                if route_asset_in != intent.asset_in {
                    return Err(TransitionError::InvalidInput("route asset_in mismatch"));
                }
                if required_in > intent.total_max_amount_in {
                    return Err(TransitionError::InvalidInput(
                        "route total_max_amount_in exceeded",
                    ));
                }
                if required_in > self.get_balance(&intent.sender_pubkey, &intent.asset_in) {
                    return Err(TransitionError::InvalidInput("insufficient balance"));
                }
                // Now execute forward: withdraw input, swap through each leg.
                self.sub_balance(&intent.sender_pubkey, &intent.asset_in, required_in)?;
                let mut current_asset = intent.asset_in.clone();
                let mut current_amount = required_in;
                let mut route_pool_audits: Vec<RoutePoolAudit> = Vec::new();
                for (leg_index, leg) in intent.legs.iter().enumerate() {
                    let target_out = target_outs[leg_index];
                    let pool_id = &leg.hops[0].pool_id;
                    let pool = self
                        .pools
                        .get(pool_id)
                        .cloned()
                        .ok_or(TransitionError::InvalidInput("route pool not found"))?;
                    let asset_out = if current_asset == pool.asset0 {
                        pool.asset1.clone()
                    } else {
                        pool.asset0.clone()
                    };
                    let (reserve_in, reserve_out) = if current_asset == pool.asset0 {
                        (pool.reserve0, pool.reserve1)
                    } else {
                        (pool.reserve1, pool.reserve0)
                    };
                    let fee_total = ceil_div_u128(
                        current_amount
                            .checked_mul(pool.fee_bps as u128)
                            .ok_or(TransitionError::Arithmetic("route fee mul overflow"))?,
                        10_000,
                    );
                    let net_in = current_amount - fee_total;
                    let denom = reserve_in
                        .checked_add(net_in)
                        .ok_or(TransitionError::Arithmetic("route denom overflow"))?;
                    if denom == 0 {
                        return Err(TransitionError::InvalidInput("route invalid reserves"));
                    }
                    let numerator = reserve_out
                        .checked_mul(net_in)
                        .ok_or(TransitionError::Arithmetic("route numerator overflow"))?;
                    let amount_out = numerator / denom;
                    if amount_out < target_out {
                        return Err(TransitionError::InvalidInput(
                            "route exact-out target not met",
                        ));
                    }
                    if amount_out > reserve_out {
                        return Err(TransitionError::InvalidInput(
                            "route insufficient reserve_out",
                        ));
                    }
                    let protocol_fee_amount =
                        self.capture_protocol_fee(fee_config, &current_asset, fee_total)?;
                    let reserve_in_delta = current_amount.checked_sub(protocol_fee_amount).ok_or(
                        TransitionError::Arithmetic("route protocol_fee exceeds amount"),
                    )?;
                    let mut next_pool = pool.clone();
                    if current_asset == next_pool.asset0 {
                        next_pool.reserve0 = next_pool
                            .reserve0
                            .checked_add(reserve_in_delta)
                            .ok_or(TransitionError::Arithmetic("route reserve0 overflow"))?;
                        next_pool.reserve1 = next_pool
                            .reserve1
                            .checked_sub(target_out)
                            .ok_or(TransitionError::Arithmetic("route reserve1 underflow"))?;
                    } else {
                        next_pool.reserve1 = next_pool
                            .reserve1
                            .checked_add(reserve_in_delta)
                            .ok_or(TransitionError::Arithmetic("route reserve1 overflow"))?;
                        next_pool.reserve0 = next_pool
                            .reserve0
                            .checked_sub(target_out)
                            .ok_or(TransitionError::Arithmetic("route reserve0 underflow"))?;
                    }
                    let leg_asset_in = current_asset.clone();
                    self.pools.insert(pool_id.clone(), next_pool);
                    route_pool_audits.push(RoutePoolAudit {
                        pool_id: pool_id.clone(),
                        asset_in: leg_asset_in,
                        asset_out: asset_out.clone(),
                        reserve_in_delta,
                        reserve_out_delta: target_out,
                        protocol_fee_credit_in: protocol_fee_amount,
                    });
                    current_asset = asset_out;
                    current_amount = target_out;
                }
                if current_asset != intent.asset_out {
                    return Err(TransitionError::InvalidInput("route final asset mismatch"));
                }
                self.add_balance(&intent.recipient, &intent.asset_out, current_amount)?;
                self.audit_route_conservation(RouteConservationAudit {
                    pre_state: &pre_state,
                    sender: &intent.sender_pubkey,
                    asset_in: &intent.asset_in,
                    sender_debit: required_in,
                    recipient: &intent.recipient,
                    asset_out: &intent.asset_out,
                    recipient_credit: current_amount,
                    protocol_fee_recipient: fee_config.recipient_pubkey.as_deref(),
                    pool_audits: route_pool_audits,
                })?;
            }
            _ => {
                return Err(TransitionError::InvalidInput("unknown route kind"));
            }
        }
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

        let pre_state = self.clone();
        let pool = self
            .pools
            .get(&intent.pool_id)
            .cloned()
            .ok_or(TransitionError::InvalidInput("pool not found"))?;
        if pool.status != "ACTIVE" {
            return Err(TransitionError::InvalidInput("pool not active"));
        }
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

        self.sub_balance(&intent.sender_pubkey, &pool.asset0, amount0_used)?;
        self.sub_balance(&intent.sender_pubkey, &pool.asset1, amount1_used)?;
        self.add_lp(&intent.recipient, &intent.pool_id, lp_minted)?;

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
        self.pools.insert(intent.pool_id.clone(), next_pool);
        self.audit_add_liquidity_conservation(AddLiquidityConservationAudit {
            pre_state: &pre_state,
            pool_id: &intent.pool_id,
            sender: &intent.sender_pubkey,
            lp_recipient: &intent.recipient,
            asset0: &pool.asset0,
            asset1: &pool.asset1,
            amount0_used,
            amount1_used,
            lp_minted,
        })?;
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

        let pre_state = self.clone();
        let pool = self
            .pools
            .get(&intent.pool_id)
            .cloned()
            .ok_or(TransitionError::InvalidInput("pool not found"))?;
        if pool.status != "ACTIVE" {
            return Err(TransitionError::InvalidInput("pool not active"));
        }
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
        self.audit_remove_liquidity_conservation(RemoveLiquidityConservationAudit {
            pre_state: &pre_state,
            pool_id: &intent.pool_id,
            lp_sender: &intent.sender_pubkey,
            recipient: &intent.recipient,
            asset0: &pool.asset0,
            asset1: &pool.asset1,
            amount0_out,
            amount1_out,
            lp_amount: intent.lp_amount,
        })?;
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

impl SwapExactOutIntentV1 {
    fn kind_str(&self) -> &'static str {
        "SWAP_EXACT_OUT"
    }
}

impl RouteIntentV1 {
    fn kind_str(&self) -> &'static str {
        intent_kind_str(&self.kind)
    }
}

fn intent_kind_str(kind: &str) -> &'static str {
    match kind {
        "ROUTE_EXACT_IN" => "ROUTE_EXACT_IN",
        "ROUTE_EXACT_OUT" => "ROUTE_EXACT_OUT",
        _ => "UNKNOWN_ROUTE_KIND",
    }
}

pub fn route_read_set_v1(intent: &RouteIntentV1) -> Result<Vec<String>, TransitionError> {
    let kind = intent.kind_str();
    if kind != "ROUTE_EXACT_IN" && kind != "ROUTE_EXACT_OUT" {
        return Err(TransitionError::InvalidInput("intent.kind mismatch"));
    }
    if intent.legs.is_empty() {
        return Err(TransitionError::InvalidInput("route has no legs"));
    }
    if intent.leg_indices.len() != intent.legs.len() {
        return Err(TransitionError::InvalidInput("leg_indices length mismatch"));
    }
    for (expected, actual) in intent.leg_indices.iter().enumerate() {
        if *actual != expected as u32 {
            return Err(TransitionError::InvalidInput(
                "leg_indices must cover full receipt",
            ));
        }
    }

    let mut pool_ids: BTreeSet<String> = BTreeSet::new();
    for leg in &intent.legs {
        if leg.hops.len() != 1 {
            return Err(TransitionError::Unsupported("route_multihop_unsupported"));
        }
        let pool_id = &leg.hops[0].pool_id;
        if pool_id.is_empty() {
            return Err(TransitionError::InvalidInput("route pool_id empty"));
        }
        if !pool_ids.insert(pool_id.clone()) {
            return Err(TransitionError::InvalidInput(
                "route duplicate pool_id across legs",
            ));
        }
    }
    Ok(pool_ids.into_iter().collect())
}

pub fn route_conflict_edges_v1(
    routes: &[RouteIntentV1],
) -> Result<Vec<RouteConflictEdgeV1>, TransitionError> {
    let read_sets = route_read_sets_v1(routes)?;
    let mut edges = Vec::new();

    for (left_index, left_pools) in read_sets.iter().enumerate() {
        let left_pool_set: BTreeSet<&String> = left_pools.iter().collect();
        for (right_index, right_pools) in read_sets.iter().enumerate().skip(left_index + 1) {
            let shared_pool_ids: Vec<String> = right_pools
                .iter()
                .filter(|pool_id| left_pool_set.contains(pool_id))
                .cloned()
                .collect();
            if shared_pool_ids.is_empty() {
                continue;
            }
            edges.push(RouteConflictEdgeV1 {
                left_route_index: route_index_u32(left_index)?,
                right_route_index: route_index_u32(right_index)?,
                shared_pool_ids,
            });
        }
    }

    Ok(edges)
}

pub fn schedule_prestate_route_conflicts_v1(
    routes: &[RouteIntentV1],
) -> Result<Vec<RouteConflictScheduleEntryV1>, TransitionError> {
    let read_sets = route_read_sets_v1(routes)?;
    let mut owner_by_pool_id: BTreeMap<String, u32> = BTreeMap::new();
    let mut schedule = Vec::with_capacity(routes.len());

    for (route_index, (route, pool_ids)) in routes.iter().zip(read_sets.iter()).enumerate() {
        let mut conflict_route_index: Option<u32> = None;
        for pool_id in pool_ids {
            if let Some(owner) = owner_by_pool_id.get(pool_id) {
                conflict_route_index = Some(match conflict_route_index {
                    Some(existing) => existing.min(*owner),
                    None => *owner,
                });
            }
        }

        let route_index_u32 = route_index_u32(route_index)?;
        let accepted = conflict_route_index.is_none();
        if accepted {
            for pool_id in pool_ids {
                owner_by_pool_id.insert(pool_id.clone(), route_index_u32);
            }
        }

        schedule.push(RouteConflictScheduleEntryV1 {
            route_index: route_index_u32,
            intent_id: route.intent_id.clone(),
            accepted,
            conflict_route_index,
            pool_ids: pool_ids.clone(),
        });
    }

    Ok(schedule)
}

pub fn tx_route_read_set_v1(tx: &TauTxV1) -> Result<Vec<String>, TransitionError> {
    match proof_v1_single_intent(tx)? {
        Some(DexIntentV1::Route(intent)) => route_read_set_v1(intent),
        _ => Ok(Vec::new()),
    }
}

pub fn tx_pool_write_set_v1(tx: &TauTxV1) -> Result<Vec<String>, TransitionError> {
    match proof_v1_single_intent(tx)? {
        Some(DexIntentV1::CreatePool(intent)) => create_pool_write_set_v1(intent),
        Some(DexIntentV1::SwapExactIn(intent)) => pool_id_write_set_v1(&intent.pool_id),
        Some(DexIntentV1::AddLiquidity(intent)) => pool_id_write_set_v1(&intent.pool_id),
        Some(DexIntentV1::RemoveLiquidity(intent)) => pool_id_write_set_v1(&intent.pool_id),
        Some(DexIntentV1::SwapExactOut(intent)) => pool_id_write_set_v1(&intent.pool_id),
        Some(DexIntentV1::Route(intent)) => route_read_set_v1(intent),
        None => Ok(Vec::new()),
    }
}

pub fn schedule_prestate_tx_pool_conflicts_v1(
    txs: &[TauTxV1],
) -> Result<Vec<TxPoolConflictScheduleEntryV1>, TransitionError> {
    let mut first_writer_by_pool_id: BTreeMap<String, u32> = BTreeMap::new();
    let mut schedule = Vec::with_capacity(txs.len());

    for (tx_index, tx) in txs.iter().enumerate() {
        let route_read_pool_ids = tx_route_read_set_v1(tx)?;
        let writer_pool_ids = tx_pool_write_set_v1(tx)?;
        let mut conflict_tx_index: Option<u32> = None;

        for pool_id in &route_read_pool_ids {
            if let Some(owner) = first_writer_by_pool_id.get(pool_id) {
                conflict_tx_index = Some(match conflict_tx_index {
                    Some(existing) => existing.min(*owner),
                    None => *owner,
                });
            }
        }

        let tx_index_u32 = tx_index_u32(tx_index)?;
        let accepted = conflict_tx_index.is_none();
        if accepted {
            for pool_id in &writer_pool_ids {
                if !first_writer_by_pool_id.contains_key(pool_id) {
                    first_writer_by_pool_id.insert(pool_id.clone(), tx_index_u32);
                }
            }
        }

        schedule.push(TxPoolConflictScheduleEntryV1 {
            tx_index: tx_index_u32,
            accepted,
            conflict_tx_index,
            route_read_pool_ids,
            writer_pool_ids,
        });
    }

    Ok(schedule)
}

pub fn optimize_prestate_tx_order_bruteforce_v1(
    txs: &[TauTxV1],
) -> Result<TxPoolConflictOrderPlanV1, TransitionError> {
    if txs.len() > MAX_PRESTATE_TX_ORDER_ORACLE_TXS {
        return Err(TransitionError::Unsupported(
            "tx order oracle max_txs exceeded",
        ));
    }
    if txs.is_empty() {
        return Ok(TxPoolConflictOrderPlanV1 {
            ordered_tx_indices: Vec::new(),
            accepted_route_count: 0,
            deferred_route_count: 0,
            schedule: Vec::new(),
        });
    }

    let mut used = alloc::vec![false; txs.len()];
    let mut current_order: Vec<usize> = Vec::with_capacity(txs.len());
    let mut best: Option<TxPoolConflictOrderPlanV1> = None;

    search_prestate_tx_order_bruteforce(txs, &mut used, &mut current_order, &mut best)?;
    best.ok_or(TransitionError::InvalidInput(
        "tx order oracle found no order",
    ))
}

pub fn stable_route_lift_prestate_tx_order_v1(
    txs: &[TauTxV1],
) -> Result<TxPoolConflictOrderPlanV1, TransitionError> {
    let mut used = alloc::vec![false; txs.len()];
    let mut ordered_indices: Vec<usize> = Vec::with_capacity(txs.len());
    let mut accepted_writer_pool_ids: BTreeSet<String> = BTreeSet::new();

    while ordered_indices.len() < txs.len() {
        let mut best_index: Option<usize> = None;
        let mut best_priority = u8::MAX;

        for index in 0..txs.len() {
            if used[index] || !same_sender_precedence_ready(txs, &used, index) {
                continue;
            }

            let route_read_pool_ids = tx_route_read_set_v1(&txs[index])?;
            let has_route_read_set = !route_read_pool_ids.is_empty();
            let route_is_unstaled = has_route_read_set
                && route_read_pool_ids
                    .iter()
                    .all(|pool_id| !accepted_writer_pool_ids.contains(pool_id));
            let priority = if route_is_unstaled {
                0
            } else if has_route_read_set {
                1
            } else {
                2
            };

            if best_index.is_none() || priority < best_priority {
                best_index = Some(index);
                best_priority = priority;
            }
        }

        let Some(index) = best_index else {
            return Err(TransitionError::InvalidInput(
                "stable route lift found no ready tx",
            ));
        };

        let route_read_pool_ids = tx_route_read_set_v1(&txs[index])?;
        let writer_pool_ids = tx_pool_write_set_v1(&txs[index])?;
        let accepted_in_heuristic = route_read_pool_ids
            .iter()
            .all(|pool_id| !accepted_writer_pool_ids.contains(pool_id));
        if accepted_in_heuristic {
            for pool_id in writer_pool_ids {
                accepted_writer_pool_ids.insert(pool_id);
            }
        }

        used[index] = true;
        ordered_indices.push(index);
    }

    evaluate_prestate_tx_order(txs, &ordered_indices)
}

pub fn component_repair_prestate_tx_order_v1(
    txs: &[TauTxV1],
) -> Result<TxPoolConflictOrderPlanV1, TransitionError> {
    let components = prestate_tx_conflict_components(txs)?;
    let mut ordered_indices: Vec<usize> = Vec::with_capacity(txs.len());

    for component in components {
        let component_txs: Vec<TauTxV1> =
            component.iter().map(|index| txs[*index].clone()).collect();
        let component_plan = if component_txs.len() <= MAX_PRESTATE_TX_ORDER_ORACLE_TXS {
            optimize_prestate_tx_order_bruteforce_v1(&component_txs)?
        } else {
            route_packing_repair_prestate_tx_order_v1(&component_txs)?
        };

        for local_index in component_plan.ordered_tx_indices {
            let local_index_usize = usize::try_from(local_index)
                .map_err(|_| TransitionError::Arithmetic("component index overflow"))?;
            let Some(global_index) = component.get(local_index_usize) else {
                return Err(TransitionError::Arithmetic(
                    "component plan index out of range",
                ));
            };
            ordered_indices.push(*global_index);
        }
    }

    evaluate_prestate_tx_order(txs, &ordered_indices)
}

fn route_packing_repair_prestate_tx_order_v1(
    txs: &[TauTxV1],
) -> Result<TxPoolConflictOrderPlanV1, TransitionError> {
    let mut best = stable_route_lift_prestate_tx_order_v1(txs)?;

    if let Some(candidate) = prefix_constrained_route_packing_order(txs)? {
        if prestate_tx_order_is_better(&candidate, Some(&best)) {
            best = candidate;
        }
    }

    if let Some(candidate) = sender_prefix_dp_route_packing_order(txs)? {
        if prestate_tx_order_is_better(&candidate, Some(&best)) {
            best = candidate;
        }
    }

    let Some(route_candidates) = writer_aware_unique_sender_route_candidates(txs)? else {
        return Ok(best);
    };

    let route_masks: Vec<u128> = route_candidates
        .iter()
        .map(|(_tx_index, route_mask)| *route_mask)
        .collect();
    let selected_indices = exact_disjoint_route_pack_indices(&route_masks);
    let selected_tx_indices: Vec<usize> = selected_indices
        .iter()
        .map(|candidate_index| route_candidates[*candidate_index].0)
        .collect();
    let selected_set: BTreeSet<usize> = selected_tx_indices.iter().copied().collect();
    let mut ordered_indices: Vec<usize> = Vec::with_capacity(txs.len());

    for index in &selected_tx_indices {
        ordered_indices.push(*index);
    }
    for index in 0..txs.len() {
        if !selected_set.contains(&index) {
            ordered_indices.push(index);
        }
    }

    let candidate = evaluate_prestate_tx_order(txs, &ordered_indices)?;
    if prestate_tx_order_is_better(&candidate, Some(&best)) {
        best = candidate;
    }

    Ok(best)
}

fn writer_aware_unique_sender_route_candidates(
    txs: &[TauTxV1],
) -> Result<Option<Vec<(usize, u128)>>, TransitionError> {
    if txs.is_empty() {
        return Ok(None);
    }

    let mut seen_senders: BTreeSet<String> = BTreeSet::new();
    let mut pool_bit_by_id: BTreeMap<String, u32> = BTreeMap::new();
    let mut route_candidates: Vec<(usize, u128)> = Vec::new();

    for (tx_index, tx) in txs.iter().enumerate() {
        if !seen_senders.insert(tx.sender_pubkey.clone()) {
            return Ok(None);
        }

        let route_read_pool_ids = tx_route_read_set_v1(tx)?;
        if route_read_pool_ids.is_empty() {
            continue;
        }
        if route_candidates.len() >= MAX_FPT_ROUTE_PACKING_TXS {
            return Ok(None);
        }
        if tx_pool_write_set_v1(tx)? != route_read_pool_ids {
            return Ok(None);
        }

        let mut route_mask = 0u128;
        for pool_id in route_read_pool_ids {
            let bit = if let Some(bit) = pool_bit_by_id.get(&pool_id) {
                *bit
            } else {
                if pool_bit_by_id.len() >= MAX_FPT_ROUTE_PACKING_POOL_IDS {
                    return Ok(None);
                }
                let next_bit = u32::try_from(pool_bit_by_id.len())
                    .map_err(|_| TransitionError::Arithmetic("pool bit index overflow"))?;
                pool_bit_by_id.insert(pool_id.clone(), next_bit);
                next_bit
            };
            route_mask |= 1u128 << bit;
        }

        route_candidates.push((tx_index, route_mask));
    }

    if route_candidates.is_empty() {
        return Ok(None);
    }

    Ok(Some(route_candidates))
}

#[derive(Clone)]
struct PrefixDpTxMasks {
    route_mask: u128,
    writer_mask: u128,
}

#[derive(Clone)]
struct PrefixDpState {
    accepted_route_count: u32,
    order: Vec<usize>,
}

struct PrefixDpInputs {
    sender_groups: Vec<Vec<usize>>,
    tx_masks: Vec<PrefixDpTxMasks>,
}

fn sender_prefix_dp_route_packing_order(
    txs: &[TauTxV1],
) -> Result<Option<TxPoolConflictOrderPlanV1>, TransitionError> {
    if txs.is_empty() || txs.len() > MAX_PREFIX_DP_TXS {
        return Ok(None);
    }

    let Some(inputs) = sender_prefix_dp_inputs(txs)? else {
        return Ok(None);
    };

    let initial_positions = alloc::vec![0usize; inputs.sender_groups.len()];
    let mut states: BTreeMap<(Vec<usize>, u128), PrefixDpState> = BTreeMap::new();
    states.insert(
        (initial_positions, 0),
        PrefixDpState {
            accepted_route_count: 0,
            order: Vec::new(),
        },
    );

    for _step in 0..txs.len() {
        let mut next_states: BTreeMap<(Vec<usize>, u128), PrefixDpState> = BTreeMap::new();
        for ((positions, writer_mask), state) in states {
            for sender_index in 0..inputs.sender_groups.len() {
                if positions[sender_index] >= inputs.sender_groups[sender_index].len() {
                    continue;
                }
                let tx_index = inputs.sender_groups[sender_index][positions[sender_index]];
                let masks = &inputs.tx_masks[tx_index];
                let accepted = masks.route_mask == 0 || (masks.route_mask & writer_mask == 0);
                let next_writer_mask = if accepted {
                    writer_mask | masks.writer_mask
                } else {
                    writer_mask
                };
                let mut next_positions = positions.clone();
                next_positions[sender_index] += 1;
                let mut next_state = state.clone();
                next_state.order.push(tx_index);
                if accepted && masks.route_mask != 0 {
                    next_state.accepted_route_count =
                        next_state.accepted_route_count.checked_add(1).ok_or(
                            TransitionError::Arithmetic("prefix dp accepted count overflow"),
                        )?;
                }

                prefix_dp_insert_state(
                    &mut next_states,
                    next_positions,
                    next_writer_mask,
                    next_state,
                );
                if next_states.len() > MAX_PREFIX_DP_STATES {
                    return Ok(None);
                }
            }
        }
        states = next_states;
    }

    let mut best: Option<TxPoolConflictOrderPlanV1> = None;
    for (_key, state) in states {
        let candidate = evaluate_prestate_tx_order(txs, &state.order)?;
        if prestate_tx_order_is_better(&candidate, best.as_ref()) {
            best = Some(candidate);
        }
    }

    Ok(best)
}

fn sender_prefix_dp_inputs(txs: &[TauTxV1]) -> Result<Option<PrefixDpInputs>, TransitionError> {
    let mut sender_index_by_pubkey: BTreeMap<String, usize> = BTreeMap::new();
    let mut sender_groups: Vec<Vec<usize>> = Vec::new();
    let mut pool_bit_by_id: BTreeMap<String, u32> = BTreeMap::new();
    let mut tx_masks: Vec<PrefixDpTxMasks> = Vec::with_capacity(txs.len());
    let mut route_count = 0usize;

    for (tx_index, tx) in txs.iter().enumerate() {
        let sender_index = if let Some(sender_index) = sender_index_by_pubkey.get(&tx.sender_pubkey)
        {
            *sender_index
        } else {
            let sender_index = sender_groups.len();
            sender_index_by_pubkey.insert(tx.sender_pubkey.clone(), sender_index);
            sender_groups.push(Vec::new());
            sender_index
        };
        sender_groups[sender_index].push(tx_index);

        let route_read_pool_ids = tx_route_read_set_v1(tx)?;
        let writer_pool_ids = tx_pool_write_set_v1(tx)?;
        if !route_read_pool_ids.is_empty() {
            route_count += 1;
            if route_count > MAX_PREFIX_DP_ROUTE_TXS {
                return Ok(None);
            }
            if writer_pool_ids != route_read_pool_ids {
                return Ok(None);
            }
        }

        let Some(route_mask) = prefix_dp_pool_mask(route_read_pool_ids, &mut pool_bit_by_id)?
        else {
            return Ok(None);
        };
        let Some(writer_mask) = prefix_dp_pool_mask(writer_pool_ids, &mut pool_bit_by_id)? else {
            return Ok(None);
        };
        tx_masks.push(PrefixDpTxMasks {
            route_mask,
            writer_mask,
        });
    }

    if route_count == 0 {
        return Ok(None);
    }

    Ok(Some(PrefixDpInputs {
        sender_groups,
        tx_masks,
    }))
}

fn prefix_dp_pool_mask(
    pool_ids: Vec<String>,
    pool_bit_by_id: &mut BTreeMap<String, u32>,
) -> Result<Option<u128>, TransitionError> {
    let mut mask = 0u128;
    for pool_id in pool_ids {
        let bit = if let Some(bit) = pool_bit_by_id.get(&pool_id) {
            *bit
        } else {
            if pool_bit_by_id.len() >= MAX_FPT_ROUTE_PACKING_POOL_IDS {
                return Ok(None);
            }
            let next_bit = u32::try_from(pool_bit_by_id.len())
                .map_err(|_| TransitionError::Arithmetic("pool bit index overflow"))?;
            pool_bit_by_id.insert(pool_id.clone(), next_bit);
            next_bit
        };
        mask |= 1u128 << bit;
    }
    Ok(Some(mask))
}

fn prefix_dp_insert_state(
    states: &mut BTreeMap<(Vec<usize>, u128), PrefixDpState>,
    positions: Vec<usize>,
    writer_mask: u128,
    state: PrefixDpState,
) {
    let mut dominated_keys: Vec<(Vec<usize>, u128)> = Vec::new();

    for ((existing_positions, existing_mask), existing_state) in
        states.range((positions.clone(), 0)..=(positions.clone(), u128::MAX))
    {
        if existing_positions != &positions {
            continue;
        }
        if prefix_dp_state_dominates(*existing_mask, existing_state, writer_mask, &state) {
            return;
        }
        if prefix_dp_state_dominates(writer_mask, &state, *existing_mask, existing_state) {
            dominated_keys.push((existing_positions.clone(), *existing_mask));
        }
    }

    for key in dominated_keys {
        states.remove(&key);
    }
    states.insert((positions, writer_mask), state);
}

fn prefix_dp_state_dominates(
    left_mask: u128,
    left_state: &PrefixDpState,
    right_mask: u128,
    right_state: &PrefixDpState,
) -> bool {
    (left_mask & right_mask) == left_mask
        && (left_state.accepted_route_count > right_state.accepted_route_count
            || (left_state.accepted_route_count == right_state.accepted_route_count
                && left_state.order <= right_state.order))
}

fn prefix_constrained_route_packing_order(
    txs: &[TauTxV1],
) -> Result<Option<TxPoolConflictOrderPlanV1>, TransitionError> {
    if txs.is_empty() || txs.len() > MAX_FPT_PREFIX_PACKING_TXS {
        return Ok(None);
    }

    let Some(route_candidates) = prefix_constrained_route_candidates(txs)? else {
        return Ok(None);
    };

    let mut selected_candidate_indices: Vec<usize> = Vec::new();
    let mut best: Option<TxPoolConflictOrderPlanV1> = None;
    prefix_constrained_route_packing_search(
        txs,
        &route_candidates,
        0,
        &mut selected_candidate_indices,
        &mut best,
    )?;
    Ok(best)
}

fn prefix_constrained_route_candidates(
    txs: &[TauTxV1],
) -> Result<Option<Vec<(usize, u128)>>, TransitionError> {
    let mut pool_bit_by_id: BTreeMap<String, u32> = BTreeMap::new();
    let mut route_candidates: Vec<(usize, u128)> = Vec::new();

    for (tx_index, tx) in txs.iter().enumerate() {
        let route_read_pool_ids = tx_route_read_set_v1(tx)?;
        if route_read_pool_ids.is_empty() {
            continue;
        }
        if route_candidates.len() >= MAX_FPT_ROUTE_PACKING_TXS {
            return Ok(None);
        }
        if tx_pool_write_set_v1(tx)? != route_read_pool_ids {
            return Ok(None);
        }

        let mut route_mask = 0u128;
        for pool_id in route_read_pool_ids {
            let bit = if let Some(bit) = pool_bit_by_id.get(&pool_id) {
                *bit
            } else {
                if pool_bit_by_id.len() >= MAX_FPT_ROUTE_PACKING_POOL_IDS {
                    return Ok(None);
                }
                let next_bit = u32::try_from(pool_bit_by_id.len())
                    .map_err(|_| TransitionError::Arithmetic("pool bit index overflow"))?;
                pool_bit_by_id.insert(pool_id.clone(), next_bit);
                next_bit
            };
            route_mask |= 1u128 << bit;
        }

        route_candidates.push((tx_index, route_mask));
    }

    if route_candidates.is_empty() {
        return Ok(None);
    }

    Ok(Some(route_candidates))
}

fn prefix_constrained_route_packing_search(
    txs: &[TauTxV1],
    route_candidates: &[(usize, u128)],
    candidate_index: usize,
    selected_candidate_indices: &mut Vec<usize>,
    best: &mut Option<TxPoolConflictOrderPlanV1>,
) -> Result<(), TransitionError> {
    if candidate_index == route_candidates.len() {
        let order = prefix_constrained_order_for_selection(
            txs,
            route_candidates,
            selected_candidate_indices,
        );
        let candidate = evaluate_prestate_tx_order(txs, &order)?;
        if prestate_tx_order_is_better(&candidate, best.as_ref()) {
            *best = Some(candidate);
        }
        return Ok(());
    }

    selected_candidate_indices.push(candidate_index);
    prefix_constrained_route_packing_search(
        txs,
        route_candidates,
        candidate_index + 1,
        selected_candidate_indices,
        best,
    )?;
    selected_candidate_indices.pop();

    prefix_constrained_route_packing_search(
        txs,
        route_candidates,
        candidate_index + 1,
        selected_candidate_indices,
        best,
    )
}

fn prefix_constrained_order_for_selection(
    txs: &[TauTxV1],
    route_candidates: &[(usize, u128)],
    selected_candidate_indices: &[usize],
) -> Vec<usize> {
    let mut early_tx_indices: BTreeSet<usize> = BTreeSet::new();

    for candidate_index in selected_candidate_indices {
        let selected_tx_index = route_candidates[*candidate_index].0;
        for prior_index in 0..=selected_tx_index {
            if txs[prior_index].sender_pubkey == txs[selected_tx_index].sender_pubkey {
                early_tx_indices.insert(prior_index);
            }
        }
    }

    let mut ordered_indices: Vec<usize> = Vec::with_capacity(txs.len());
    for index in 0..txs.len() {
        if early_tx_indices.contains(&index) {
            ordered_indices.push(index);
        }
    }
    for index in 0..txs.len() {
        if !early_tx_indices.contains(&index) {
            ordered_indices.push(index);
        }
    }

    ordered_indices
}

fn exact_disjoint_route_pack_indices(route_masks: &[u128]) -> Vec<usize> {
    let mut current: Vec<usize> = Vec::new();
    let mut best: Vec<usize> = Vec::new();
    exact_disjoint_route_pack_search(route_masks, 0, 0, &mut current, &mut best);
    best
}

fn exact_disjoint_route_pack_search(
    route_masks: &[u128],
    index: usize,
    used_mask: u128,
    current: &mut Vec<usize>,
    best: &mut Vec<usize>,
) {
    if current.len() + route_masks.len().saturating_sub(index) < best.len() {
        return;
    }

    if index == route_masks.len() {
        if current.len() > best.len()
            || (current.len() == best.len() && current.as_slice() < best.as_slice())
        {
            *best = current.clone();
        }
        return;
    }

    if used_mask & route_masks[index] == 0 {
        current.push(index);
        exact_disjoint_route_pack_search(
            route_masks,
            index + 1,
            used_mask | route_masks[index],
            current,
            best,
        );
        current.pop();
    }

    exact_disjoint_route_pack_search(route_masks, index + 1, used_mask, current, best);
}

fn prestate_tx_conflict_components(txs: &[TauTxV1]) -> Result<Vec<Vec<usize>>, TransitionError> {
    let mut parent: Vec<usize> = (0..txs.len()).collect();
    let mut first_tx_by_pool_id: BTreeMap<String, usize> = BTreeMap::new();
    let mut first_tx_by_sender: BTreeMap<String, usize> = BTreeMap::new();

    for (index, tx) in txs.iter().enumerate() {
        let mut pool_ids: BTreeSet<String> = BTreeSet::new();
        for pool_id in tx_route_read_set_v1(tx)? {
            pool_ids.insert(pool_id);
        }
        for pool_id in tx_pool_write_set_v1(tx)? {
            pool_ids.insert(pool_id);
        }

        for pool_id in pool_ids {
            if let Some(owner) = first_tx_by_pool_id.get(&pool_id) {
                tx_component_union(&mut parent, index, *owner);
            } else {
                first_tx_by_pool_id.insert(pool_id, index);
            }
        }

        if let Some(owner) = first_tx_by_sender.get(&tx.sender_pubkey) {
            tx_component_union(&mut parent, index, *owner);
        } else {
            first_tx_by_sender.insert(tx.sender_pubkey.clone(), index);
        }
    }

    let mut components_by_root: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for index in 0..txs.len() {
        let root = tx_component_find(&mut parent, index);
        components_by_root.entry(root).or_default().push(index);
    }

    Ok(components_by_root.into_values().collect())
}

fn tx_component_union(parent: &mut [usize], left: usize, right: usize) {
    let left_root = tx_component_find(parent, left);
    let right_root = tx_component_find(parent, right);
    if left_root < right_root {
        parent[right_root] = left_root;
    } else if right_root < left_root {
        parent[left_root] = right_root;
    }
}

fn tx_component_find(parent: &mut [usize], index: usize) -> usize {
    if parent[index] != index {
        parent[index] = tx_component_find(parent, parent[index]);
    }
    parent[index]
}

fn search_prestate_tx_order_bruteforce(
    txs: &[TauTxV1],
    used: &mut [bool],
    current_order: &mut Vec<usize>,
    best: &mut Option<TxPoolConflictOrderPlanV1>,
) -> Result<(), TransitionError> {
    if current_order.len() == txs.len() {
        let candidate = evaluate_prestate_tx_order(txs, current_order)?;
        if prestate_tx_order_is_better(&candidate, best.as_ref()) {
            *best = Some(candidate);
        }
        return Ok(());
    }

    for index in 0..txs.len() {
        if used[index] || !same_sender_precedence_ready(txs, used, index) {
            continue;
        }
        used[index] = true;
        current_order.push(index);
        search_prestate_tx_order_bruteforce(txs, used, current_order, best)?;
        current_order.pop();
        used[index] = false;
    }

    Ok(())
}

fn evaluate_prestate_tx_order(
    txs: &[TauTxV1],
    order: &[usize],
) -> Result<TxPoolConflictOrderPlanV1, TransitionError> {
    let mut ordered_txs: Vec<TauTxV1> = Vec::with_capacity(order.len());
    let mut ordered_tx_indices: Vec<u32> = Vec::with_capacity(order.len());
    for index in order {
        ordered_txs.push(txs[*index].clone());
        ordered_tx_indices.push(tx_index_u32(*index)?);
    }
    let schedule = schedule_prestate_tx_pool_conflicts_v1(&ordered_txs)?;
    let accepted_route_count = count_routes_by_schedule_status(&schedule, true)?;
    let deferred_route_count = count_routes_by_schedule_status(&schedule, false)?;

    Ok(TxPoolConflictOrderPlanV1 {
        ordered_tx_indices,
        accepted_route_count,
        deferred_route_count,
        schedule,
    })
}

fn prestate_tx_order_is_better(
    candidate: &TxPoolConflictOrderPlanV1,
    current_best: Option<&TxPoolConflictOrderPlanV1>,
) -> bool {
    let Some(best) = current_best else {
        return true;
    };
    candidate.accepted_route_count > best.accepted_route_count
        || (candidate.accepted_route_count == best.accepted_route_count
            && candidate.ordered_tx_indices < best.ordered_tx_indices)
}

fn resolve_tx_execution_order_v1(
    txs: &[TauTxV1],
    certificate_order: &[u32],
) -> Result<Vec<usize>, TransitionError> {
    if certificate_order.is_empty() {
        return Ok((0..txs.len()).collect());
    }
    verify_tx_execution_order_certificate_v1(txs, certificate_order)?;
    decode_tx_execution_order_indices(txs.len(), certificate_order)
}

pub fn verify_tx_execution_order_certificate_v1(
    txs: &[TauTxV1],
    certificate_order: &[u32],
) -> Result<TxPoolConflictOrderPlanV1, TransitionError> {
    let order = decode_tx_execution_order_indices(txs.len(), certificate_order)?;
    verify_same_sender_order_v1(txs, &order)?;
    let candidate = evaluate_prestate_tx_order(txs, &order)?;
    let baseline = component_repair_prestate_tx_order_v1(txs)?;
    if candidate.accepted_route_count < baseline.accepted_route_count {
        return Err(TransitionError::InvalidInput(
            "tx_execution_order worsens route acceptance",
        ));
    }
    Ok(candidate)
}

fn decode_tx_execution_order_indices(
    tx_count: usize,
    certificate_order: &[u32],
) -> Result<Vec<usize>, TransitionError> {
    if certificate_order.len() != tx_count {
        return Err(TransitionError::InvalidInput(
            "tx_execution_order length mismatch",
        ));
    }

    let mut seen = alloc::vec![false; tx_count];
    let mut order: Vec<usize> = Vec::with_capacity(tx_count);
    for raw_index in certificate_order {
        let index = usize::try_from(*raw_index)
            .map_err(|_| TransitionError::Arithmetic("tx_execution_order index overflow"))?;
        if index >= tx_count {
            return Err(TransitionError::InvalidInput(
                "tx_execution_order index out of range",
            ));
        }
        if seen[index] {
            return Err(TransitionError::InvalidInput(
                "tx_execution_order duplicate index",
            ));
        }
        seen[index] = true;
        order.push(index);
    }
    Ok(order)
}

fn verify_same_sender_order_v1(txs: &[TauTxV1], order: &[usize]) -> Result<(), TransitionError> {
    let mut last_index_by_sender: BTreeMap<String, usize> = BTreeMap::new();
    for index in order {
        let sender = &txs[*index].sender_pubkey;
        if let Some(last_index) = last_index_by_sender.get(sender) {
            if index < last_index {
                return Err(TransitionError::InvalidInput(
                    "tx_execution_order violates same-sender order",
                ));
            }
        }
        last_index_by_sender.insert(sender.clone(), *index);
    }
    Ok(())
}

fn same_sender_precedence_ready(txs: &[TauTxV1], used: &[bool], candidate_index: usize) -> bool {
    for prior_index in 0..candidate_index {
        if txs[prior_index].sender_pubkey == txs[candidate_index].sender_pubkey
            && !used[prior_index]
        {
            return false;
        }
    }
    true
}

fn count_routes_by_schedule_status(
    schedule: &[TxPoolConflictScheduleEntryV1],
    accepted: bool,
) -> Result<u32, TransitionError> {
    let count = schedule
        .iter()
        .filter(|entry| entry.accepted == accepted && !entry.route_read_pool_ids.is_empty())
        .count();
    tx_index_u32(count)
}

fn route_read_sets_v1(routes: &[RouteIntentV1]) -> Result<Vec<Vec<String>>, TransitionError> {
    routes.iter().map(route_read_set_v1).collect()
}

fn proof_v1_single_intent(tx: &TauTxV1) -> Result<Option<&DexIntentV1>, TransitionError> {
    if !tx.app_ops.has_intents {
        return Ok(None);
    }
    if tx.app_ops.intents.len() > 1 {
        return Err(TransitionError::Unsupported(
            "multiple intents per tx unsupported in proof v1",
        ));
    }
    Ok(tx.app_ops.intents.first().map(|env| &env.intent))
}

fn create_pool_write_set_v1(intent: &CreatePoolIntentV1) -> Result<Vec<String>, TransitionError> {
    let asset0_canonical = canonical_pool_asset_id(&intent.asset0);
    let asset1_canonical = canonical_pool_asset_id(&intent.asset1);
    if asset0_canonical >= asset1_canonical {
        return Err(TransitionError::InvalidInput(
            "assets must be in canonical order",
        ));
    }
    if asset0_canonical == NATIVE_ASSET || asset1_canonical == NATIVE_ASSET {
        return Err(TransitionError::Unsupported(
            "native asset unsupported in proof v1",
        ));
    }
    pool_id_write_set_v1(&compute_pool_id(
        &asset0_canonical,
        &asset1_canonical,
        intent.fee_bps,
        CURVE_TAG,
        CURVE_PARAMS,
    ))
}

fn pool_id_write_set_v1(pool_id: &str) -> Result<Vec<String>, TransitionError> {
    if pool_id.is_empty() {
        return Err(TransitionError::InvalidInput("pool_id empty"));
    }
    Ok(alloc::vec![pool_id.to_string()])
}

fn route_index_u32(index: usize) -> Result<u32, TransitionError> {
    if index > u32::MAX as usize {
        return Err(TransitionError::InvalidInput("route index exceeds u32"));
    }
    Ok(index as u32)
}

fn tx_index_u32(index: usize) -> Result<u32, TransitionError> {
    if index > u32::MAX as usize {
        return Err(TransitionError::InvalidInput("tx index exceeds u32"));
    }
    Ok(index as u32)
}

fn route_quote_receipt_hash_v1(
    intent: &RouteIntentV1,
    pools: &BTreeMap<String, DexPoolEntryV1>,
    fee_config: &ProtocolFeeConfig,
) -> Result<String, TransitionError> {
    let kind = intent.kind_str();
    if kind != "ROUTE_EXACT_IN" && kind != "ROUTE_EXACT_OUT" {
        return Err(TransitionError::InvalidInput("intent.kind mismatch"));
    }
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.route_quote_receipt_binding.v1:");
    write_str(&mut hasher, kind);
    write_str(&mut hasher, &intent.asset_in);
    write_str(&mut hasher, &intent.asset_out);
    write_u128(&mut hasher, intent.total_amount_in);
    write_u128(&mut hasher, intent.total_min_amount_out);
    write_u128(&mut hasher, intent.total_amount_out);
    write_u128(&mut hasher, intent.total_max_amount_in);
    write_u32(&mut hasher, fee_config.share_bps);
    write_opt_str(&mut hasher, fee_config.recipient_pubkey.as_deref());
    write_u32(&mut hasher, intent.leg_indices.len() as u32);
    for index in &intent.leg_indices {
        write_u32(&mut hasher, *index);
    }
    write_u32(&mut hasher, intent.legs.len() as u32);
    for leg in &intent.legs {
        if leg.hops.len() != 1 {
            return Err(TransitionError::Unsupported("route_multihop_unsupported"));
        }
        write_u32(&mut hasher, 1);
        let pool_id = &leg.hops[0].pool_id;
        let pool = pools
            .get(pool_id)
            .ok_or(TransitionError::InvalidInput("route pool not found"))?;
        write_route_pool_snapshot(&mut hasher, pool);
    }
    let digest = hasher.finalize();
    let mut out = String::from("0x");
    out.push_str(&hex_lower(&digest));
    Ok(out)
}

fn write_route_pool_snapshot(hasher: &mut Sha256, pool: &DexPoolEntryV1) {
    write_str(hasher, &pool.pool_id);
    write_str(hasher, &pool.asset0);
    write_str(hasher, &pool.asset1);
    write_u128(hasher, pool.reserve0);
    write_u128(hasher, pool.reserve1);
    write_u32(hasher, pool.fee_bps);
    write_u128(hasher, pool.lp_supply);
    write_str(hasher, &pool.status);
    write_u64(hasher, pool.created_at);
}

fn canonical_pool_asset_id(asset: &str) -> String {
    let bytes = asset.as_bytes();
    if bytes.len() < 3 || !(bytes[0] == b'0' && (bytes[1] == b'x' || bytes[1] == b'X')) {
        return asset.to_string();
    }
    if !bytes[2..].iter().all(u8::is_ascii_hexdigit) {
        return asset.to_string();
    }

    let mut out = String::from("0x");
    for byte in &bytes[2..] {
        out.push(char::from(byte.to_ascii_lowercase()));
    }
    out
}

pub fn compute_pool_id(
    asset0: &str,
    asset1: &str,
    fee_bps: u32,
    curve_tag: &str,
    curve_params: &str,
) -> String {
    let asset0_hash = canonical_pool_asset_id(asset0);
    let asset1_hash = canonical_pool_asset_id(asset1);
    let mut hasher = Sha256::new();
    hasher.update(b"TauSwapPool");
    hasher.update(asset0_hash.as_bytes());
    hasher.update(asset1_hash.as_bytes());
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

pub fn tx_execution_order_commitment_v1(order: &[usize]) -> Result<[u8; 32], TransitionError> {
    let mut hasher = Sha256::new();
    hasher.update(b"tau_state_proof_tx_execution_order_v1:");
    write_u32(&mut hasher, order.len() as u32);
    for index in order {
        write_u32(
            &mut hasher,
            u32::try_from(*index)
                .map_err(|_| TransitionError::Arithmetic("tx order index overflow"))?,
        );
    }
    Ok(hasher.finalize().into())
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
                DexIntentV1::SwapExactOut(i) => {
                    hasher.update([4u8]);
                    write_str(hasher, &i.module);
                    write_str(hasher, &i.version);
                    write_str(hasher, &i.intent_id);
                    write_str(hasher, &i.sender_pubkey);
                    write_u64(hasher, i.deadline);
                    write_opt_str(hasher, i.salt.as_deref());
                    write_str(hasher, &i.pool_id);
                    write_str(hasher, &i.asset_in);
                    write_str(hasher, &i.asset_out);
                    write_u128(hasher, i.amount_out);
                    write_u128(hasher, i.max_amount_in);
                    write_str(hasher, &i.recipient);
                }
                DexIntentV1::Route(i) => {
                    hasher.update([5u8]);
                    write_str(hasher, &i.module);
                    write_str(hasher, &i.version);
                    write_str(hasher, &i.intent_id);
                    write_str(hasher, &i.sender_pubkey);
                    write_u64(hasher, i.deadline);
                    write_opt_str(hasher, i.salt.as_deref());
                    write_str(hasher, &i.quote_receipt_hash);
                    write_str(hasher, &i.asset_in);
                    write_str(hasher, &i.asset_out);
                    write_u32(hasher, i.leg_indices.len() as u32);
                    for idx in &i.leg_indices {
                        write_u32(hasher, *idx);
                    }
                    write_u32(hasher, i.legs.len() as u32);
                    for leg in &i.legs {
                        write_u32(hasher, leg.hops.len() as u32);
                        for hop in &leg.hops {
                            write_str(hasher, &hop.pool_id);
                        }
                    }
                    write_str(hasher, &i.kind);
                    write_u128(hasher, i.total_amount_in);
                    write_u128(hasher, i.total_min_amount_out);
                    write_u128(hasher, i.total_amount_out);
                    write_u128(hasher, i.total_max_amount_in);
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
    const ASSET2: &str = "0x3333333333333333333333333333333333333333333333333333333333333333";
    const ASSET3: &str = "0x4444444444444444444444444444444444444444444444444444444444444444";
    const SENDER: &str =
        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const OTHER_SENDER: &str =
        "0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
    const RECIPIENT: &str =
        "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    const PROTOCOL_FEE_RECIPIENT: &str =
        "0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    const POOL_ID: &str = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686";
    const POOL_ID_2: &str = "0xdd9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686";

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
        DexPoolEntryV1 {
            pool_id: POOL_ID.to_string(),
            asset0: ASSET0.to_string(),
            asset1: ASSET1.to_string(),
            reserve0,
            reserve1,
            fee_bps: 30,
            lp_supply: 10_000,
            status: "ACTIVE".to_string(),
            created_at: 0,
        }
    }

    fn second_pool_entry(reserve0: u128, reserve1: u128) -> DexPoolEntryV1 {
        DexPoolEntryV1 {
            pool_id: POOL_ID_2.to_string(),
            asset0: ASSET2.to_string(),
            asset1: ASSET3.to_string(),
            reserve0,
            reserve1,
            fee_bps: 30,
            lp_supply: 10_000,
            status: "ACTIVE".to_string(),
            created_at: 0,
        }
    }

    fn two_disjoint_pool_snapshot() -> DexSnapshotV1 {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: ASSET2.to_string(),
            amount: 10_000_000,
        });
        snapshot.pools.push(second_pool_entry(2_000_000, 3_000_000));
        snapshot
    }

    fn default_route_intent(
        intent_id: &str,
        kind: &str,
        total_amount_in: u128,
        total_min_amount_out: u128,
        total_amount_out: u128,
        total_max_amount_in: u128,
    ) -> RouteIntentV1 {
        RouteIntentV1 {
            module: "TauSwap".to_string(),
            version: "v1".to_string(),
            intent_id: intent_id.to_string(),
            sender_pubkey: SENDER.to_string(),
            deadline: 100,
            quote_receipt_hash: String::new(),
            asset_in: ASSET0.to_string(),
            asset_out: ASSET1.to_string(),
            leg_indices: alloc::vec![0],
            legs: alloc::vec![RouteLegV1 {
                hops: alloc::vec![RouteLegHopV1 {
                    pool_id: POOL_ID.to_string(),
                }],
            }],
            kind: kind.to_string(),
            total_amount_in,
            total_min_amount_out,
            total_amount_out,
            total_max_amount_in,
            recipient: RECIPIENT.to_string(),
            salt: None,
        }
    }

    fn second_pool_route_intent(intent_id: &str) -> RouteIntentV1 {
        let mut intent = default_route_intent(intent_id, "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        intent.asset_in = ASSET2.to_string();
        intent.asset_out = ASSET3.to_string();
        intent.legs[0].hops[0].pool_id = POOL_ID_2.to_string();
        intent
    }

    fn two_pool_route_intent(intent_id: &str) -> RouteIntentV1 {
        let mut intent = default_route_intent(intent_id, "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        intent.asset_out = ASSET3.to_string();
        intent.leg_indices = alloc::vec![0, 1];
        intent.legs = alloc::vec![
            RouteLegV1 {
                hops: alloc::vec![RouteLegHopV1 {
                    pool_id: POOL_ID.to_string(),
                }],
            },
            RouteLegV1 {
                hops: alloc::vec![RouteLegHopV1 {
                    pool_id: POOL_ID_2.to_string(),
                }],
            },
        ];
        intent
    }

    fn chained_two_pool_snapshot() -> DexSnapshotV1 {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET2.to_string(),
            amount: 0,
        });
        snapshot.pools.push(DexPoolEntryV1 {
            pool_id: "CHAIN_POOL".to_string(),
            asset0: ASSET1.to_string(),
            asset1: ASSET2.to_string(),
            reserve0: 1_500_000,
            reserve1: 3_000_000,
            fee_bps: 100,
            lp_supply: 10_000,
            status: "ACTIVE".to_string(),
            created_at: 0,
        });
        snapshot
    }

    fn chained_exact_in_route_intent(intent_id: &str) -> RouteIntentV1 {
        let mut intent = default_route_intent(intent_id, "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        intent.asset_out = ASSET2.to_string();
        intent.leg_indices = alloc::vec![0, 1];
        intent.legs = alloc::vec![
            RouteLegV1 {
                hops: alloc::vec![RouteLegHopV1 {
                    pool_id: POOL_ID.to_string(),
                }],
            },
            RouteLegV1 {
                hops: alloc::vec![RouteLegHopV1 {
                    pool_id: "CHAIN_POOL".to_string(),
                }],
            },
        ];
        intent
    }

    fn bind_route_hash(
        intent: &mut RouteIntentV1,
        state: &DexStateV1,
        fee_config: &ProtocolFeeConfig,
    ) {
        intent.quote_receipt_hash =
            route_quote_receipt_hash_v1(intent, &state.pools, fee_config).unwrap();
    }

    fn route_tx(intent: RouteIntentV1) -> TauTxV1 {
        TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::Route(intent),
                }],
            },
        }
    }

    fn route_tx_for_pool(intent_id: &str, pool_id: &str) -> TauTxV1 {
        let mut intent = default_route_intent(intent_id, "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        intent.legs[0].hops[0].pool_id = pool_id.to_string();
        route_tx(intent)
    }

    fn route_tx_for_pool_ids(intent_id: &str, pool_ids: &[String]) -> TauTxV1 {
        let mut intent = default_route_intent(intent_id, "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        intent.leg_indices = (0..pool_ids.len())
            .map(|index| u32::try_from(index).unwrap())
            .collect();
        intent.legs = pool_ids
            .iter()
            .map(|pool_id| RouteLegV1 {
                hops: alloc::vec![RouteLegHopV1 {
                    pool_id: pool_id.clone(),
                }],
            })
            .collect();
        route_tx(intent)
    }

    fn swap_exact_in_tx_for_pool(
        intent_id: &str,
        pool_id: &str,
        asset_in: &str,
        asset_out: &str,
    ) -> TauTxV1 {
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
                        intent_id: intent_id.to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: pool_id.to_string(),
                        asset_in: asset_in.to_string(),
                        asset_out: asset_out.to_string(),
                        amount_in: 100_000,
                        min_amount_out: 0,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        }
    }

    fn retarget_tx_sender(tx: &mut TauTxV1, sender: &str) {
        tx.sender_pubkey = sender.to_string();
        if let Some(env) = tx.app_ops.intents.first_mut() {
            match &mut env.intent {
                DexIntentV1::CreatePool(intent) => intent.sender_pubkey = sender.to_string(),
                DexIntentV1::SwapExactIn(intent) => intent.sender_pubkey = sender.to_string(),
                DexIntentV1::AddLiquidity(intent) => intent.sender_pubkey = sender.to_string(),
                DexIntentV1::RemoveLiquidity(intent) => intent.sender_pubkey = sender.to_string(),
                DexIntentV1::SwapExactOut(intent) => intent.sender_pubkey = sender.to_string(),
                DexIntentV1::Route(intent) => intent.sender_pubkey = sender.to_string(),
            }
        }
    }

    fn no_intent_tx(sender: &str) -> TauTxV1 {
        TauTxV1 {
            sender_pubkey: sender.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: false,
                intents: Vec::new(),
            },
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
    fn pool_id_normalizes_hex_asset_id_case() {
        let lower0 = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let lower1 = "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        let mixed0 = "0xAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAa";
        let mixed1 = "0xBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBbBb";

        assert_eq!(
            compute_pool_id(mixed0, mixed1, 30, CURVE_TAG, CURVE_PARAMS),
            compute_pool_id(lower0, lower1, 30, CURVE_TAG, CURVE_PARAMS)
        );
    }

    #[test]
    fn route_quote_receipt_hash_matches_python_known_vector() {
        let state = DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let intent = default_route_intent("route-known-vector", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        let hash =
            route_quote_receipt_hash_v1(&intent, &state.pools, &ProtocolFeeConfig::default())
                .unwrap();

        assert_eq!(
            hash,
            "0x29d7543ef7bac99812f3e37310f0960b168b36bfede112f6eaee7e1c58569acd"
        );
    }

    #[test]
    fn route_rejects_placeholder_quote_receipt_hash_without_mutation() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let mut intent =
            default_route_intent("route-placeholder-hash", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        intent.quote_receipt_hash = "0xabc".to_string();
        let tx = route_tx(intent);
        let pre_hash = state.canonical_app_hash_sha256();

        assert!(matches!(
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
            Err(TransitionError::InvalidInput("quote_receipt_hash mismatch"))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), pre_hash);
    }

    #[test]
    fn route_rejects_stale_pool_snapshot_quote_hash_without_mutation() {
        let quote_state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let fee_config = ProtocolFeeConfig::default();
        let mut intent =
            default_route_intent("route-stale-hash", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        bind_route_hash(&mut intent, &quote_state, &fee_config);
        let tx = route_tx(intent);
        let mut exec_snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        exec_snapshot.pools[0].reserve0 += 1;
        let mut exec_state = DexStateV1::from_snapshot(exec_snapshot).unwrap();
        let pre_hash = exec_state.canonical_app_hash_sha256();

        assert!(matches!(
            exec_state.apply_tx(&tx, 1, &fee_config),
            Err(TransitionError::InvalidInput("quote_receipt_hash mismatch"))
        ));
        assert_eq!(exec_state.canonical_app_hash_sha256(), pre_hash);
    }

    #[test]
    fn disjoint_prestate_route_hashes_coexecute() {
        let fee_config = ProtocolFeeConfig::default();
        let mut state = DexStateV1::from_snapshot(two_disjoint_pool_snapshot()).unwrap();
        let mut route_a =
            default_route_intent("route-disjoint-a", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        let mut route_b = second_pool_route_intent("route-disjoint-b");
        bind_route_hash(&mut route_a, &state, &fee_config);
        bind_route_hash(&mut route_b, &state, &fee_config);

        state.apply_tx(&route_tx(route_a), 1, &fee_config).unwrap();
        state.apply_tx(&route_tx(route_b), 1, &fee_config).unwrap();

        assert!(state.get_balance(RECIPIENT, ASSET1) > 0);
        assert!(state.get_balance(RECIPIENT, ASSET3) > 0);
    }

    #[test]
    fn same_pool_prestate_route_hashes_second_rejects_without_mutation() {
        let fee_config = ProtocolFeeConfig::default();
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let mut route_a =
            default_route_intent("route-same-pool-a", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        let mut route_b =
            default_route_intent("route-same-pool-b", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        bind_route_hash(&mut route_a, &state, &fee_config);
        bind_route_hash(&mut route_b, &state, &fee_config);

        state.apply_tx(&route_tx(route_a), 1, &fee_config).unwrap();
        let post_first_hash = state.canonical_app_hash_sha256();

        assert!(matches!(
            state.apply_tx(&route_tx(route_b), 1, &fee_config),
            Err(TransitionError::InvalidInput("quote_receipt_hash mismatch"))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), post_first_hash);
    }

    #[test]
    fn same_pool_sequentially_rebound_route_hashes_accept() {
        let fee_config = ProtocolFeeConfig::default();
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let mut route_a =
            default_route_intent("route-rebound-a", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        bind_route_hash(&mut route_a, &state, &fee_config);
        state.apply_tx(&route_tx(route_a), 1, &fee_config).unwrap();

        let mut route_b =
            default_route_intent("route-rebound-b", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        bind_route_hash(&mut route_b, &state, &fee_config);
        state.apply_tx(&route_tx(route_b), 1, &fee_config).unwrap();

        assert!(state.get_balance(RECIPIENT, ASSET1) > 0);
    }

    #[test]
    fn route_read_set_rejects_duplicate_pool_ids() {
        let mut route =
            default_route_intent("route-duplicate-read-set", "ROUTE_EXACT_IN", 0, 0, 0, 0);
        route.leg_indices = alloc::vec![0, 1];
        route.legs.push(RouteLegV1 {
            hops: alloc::vec![RouteLegHopV1 {
                pool_id: POOL_ID.to_string(),
            }],
        });

        assert!(matches!(
            route_read_set_v1(&route),
            Err(TransitionError::InvalidInput(
                "route duplicate pool_id across legs"
            ))
        ));
    }

    #[test]
    fn route_conflict_edges_identify_shared_pool() {
        let route_a = default_route_intent("route-edge-a", "ROUTE_EXACT_IN", 0, 0, 0, 0);
        let route_b = second_pool_route_intent("route-edge-b");
        let route_c = default_route_intent("route-edge-c", "ROUTE_EXACT_IN", 0, 0, 0, 0);

        let edges = route_conflict_edges_v1(&[route_a, route_b, route_c]).unwrap();

        assert_eq!(
            edges,
            alloc::vec![RouteConflictEdgeV1 {
                left_route_index: 0,
                right_route_index: 2,
                shared_pool_ids: alloc::vec![POOL_ID.to_string()],
            }]
        );
    }

    #[test]
    fn prestate_route_conflict_scheduler_accepts_maximal_disjoint_set() {
        let route_a = default_route_intent("route-schedule-a", "ROUTE_EXACT_IN", 0, 0, 0, 0);
        let route_b = second_pool_route_intent("route-schedule-b");
        let route_c = default_route_intent("route-schedule-c", "ROUTE_EXACT_IN", 0, 0, 0, 0);

        let schedule = schedule_prestate_route_conflicts_v1(&[route_a, route_b, route_c]).unwrap();

        assert_eq!(schedule.len(), 3);
        assert!(schedule[0].accepted);
        assert!(schedule[1].accepted);
        assert!(!schedule[2].accepted);
        assert_eq!(schedule[2].conflict_route_index, Some(0));
        assert_eq!(schedule[0].pool_ids, alloc::vec![POOL_ID.to_string()]);
        assert_eq!(schedule[1].pool_ids, alloc::vec![POOL_ID_2.to_string()]);
    }

    #[test]
    fn prestate_route_conflict_scheduler_is_not_maximum_solver() {
        let wide_route = two_pool_route_intent("route-greedy-wide");
        let narrow_a = default_route_intent("route-greedy-narrow-a", "ROUTE_EXACT_IN", 0, 0, 0, 0);
        let narrow_b = second_pool_route_intent("route-greedy-narrow-b");

        let schedule =
            schedule_prestate_route_conflicts_v1(&[wide_route, narrow_a.clone(), narrow_b.clone()])
                .unwrap();

        assert!(schedule[0].accepted);
        assert!(!schedule[1].accepted);
        assert!(!schedule[2].accepted);
        assert_eq!(schedule[1].conflict_route_index, Some(0));
        assert_eq!(schedule[2].conflict_route_index, Some(0));

        let narrow_a_pools = route_read_set_v1(&narrow_a).unwrap();
        let narrow_b_pools = route_read_set_v1(&narrow_b).unwrap();
        assert!(narrow_a_pools
            .iter()
            .all(|pool_id| !narrow_b_pools.contains(pool_id)));
    }

    #[test]
    fn mixed_tx_scheduler_defers_route_after_prior_pool_writer() {
        let writer_tx = swap_exact_in_tx_for_pool("swap-writer", POOL_ID, ASSET0, ASSET1);
        let route_tx = route_tx(default_route_intent(
            "route-after-writer",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));

        let schedule = schedule_prestate_tx_pool_conflicts_v1(&[writer_tx, route_tx]).unwrap();

        assert_eq!(schedule.len(), 2);
        assert!(schedule[0].accepted);
        assert!(!schedule[1].accepted);
        assert_eq!(schedule[1].conflict_tx_index, Some(0));
        assert_eq!(
            schedule[1].route_read_pool_ids,
            alloc::vec![POOL_ID.to_string()]
        );
        assert_eq!(
            schedule[0].writer_pool_ids,
            alloc::vec![POOL_ID.to_string()]
        );
    }

    #[test]
    fn mixed_tx_scheduler_accepts_route_before_later_pool_writer() {
        let route_tx = route_tx(default_route_intent(
            "route-before-writer",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let writer_tx = swap_exact_in_tx_for_pool("swap-after-route", POOL_ID, ASSET0, ASSET1);

        let schedule = schedule_prestate_tx_pool_conflicts_v1(&[route_tx, writer_tx]).unwrap();

        assert_eq!(schedule.len(), 2);
        assert!(schedule[0].accepted);
        assert!(schedule[1].accepted);
        assert_eq!(
            schedule[0].route_read_pool_ids,
            alloc::vec![POOL_ID.to_string()]
        );
        assert_eq!(
            schedule[1].writer_pool_ids,
            alloc::vec![POOL_ID.to_string()]
        );
    }

    #[test]
    fn mixed_tx_scheduler_allows_sequential_non_route_pool_writers() {
        let first_writer = swap_exact_in_tx_for_pool("swap-writer-a", POOL_ID, ASSET0, ASSET1);
        let second_writer = swap_exact_in_tx_for_pool("swap-writer-b", POOL_ID, ASSET0, ASSET1);

        let schedule =
            schedule_prestate_tx_pool_conflicts_v1(&[first_writer, second_writer]).unwrap();

        assert_eq!(schedule.len(), 2);
        assert!(schedule[0].accepted);
        assert!(schedule[1].accepted);
        assert!(schedule[0].route_read_pool_ids.is_empty());
        assert!(schedule[1].route_read_pool_ids.is_empty());
        assert_eq!(
            schedule[0].writer_pool_ids,
            alloc::vec![POOL_ID.to_string()]
        );
        assert_eq!(
            schedule[1].writer_pool_ids,
            alloc::vec![POOL_ID.to_string()]
        );
    }

    #[test]
    fn mixed_tx_scheduler_rejects_proof_v1_multi_intent_tx() {
        let mut tx = route_tx(default_route_intent(
            "route-multi-intent-a",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        tx.app_ops.intents.push(SignedIntentV1 {
            signature: None,
            intent: DexIntentV1::Route(default_route_intent(
                "route-multi-intent-b",
                "ROUTE_EXACT_IN",
                100_000,
                0,
                0,
                0,
            )),
        });

        assert!(matches!(
            schedule_prestate_tx_pool_conflicts_v1(&[tx]),
            Err(TransitionError::Unsupported(
                "multiple intents per tx unsupported in proof v1"
            ))
        ));
    }

    #[test]
    fn order_oracle_moves_route_before_different_sender_writer() {
        let mut writer_tx =
            swap_exact_in_tx_for_pool("swap-oracle-writer", POOL_ID, ASSET0, ASSET1);
        retarget_tx_sender(&mut writer_tx, OTHER_SENDER);
        let route = route_tx(default_route_intent(
            "route-oracle-lift",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let ingress_schedule =
            schedule_prestate_tx_pool_conflicts_v1(&[writer_tx.clone(), route.clone()]).unwrap();

        let plan = optimize_prestate_tx_order_bruteforce_v1(&[writer_tx, route]).unwrap();

        assert!(!ingress_schedule[1].accepted);
        assert_eq!(plan.ordered_tx_indices, alloc::vec![1, 0]);
        assert_eq!(plan.accepted_route_count, 1);
        assert_eq!(plan.deferred_route_count, 0);
        assert!(plan.schedule[0].accepted);
        assert!(plan.schedule[1].accepted);
    }

    #[test]
    fn tx_execution_order_certificate_rejects_malformed_and_weaker_orders() {
        let mut writer_tx = swap_exact_in_tx_for_pool("swap-order-writer", POOL_ID, ASSET0, ASSET1);
        retarget_tx_sender(&mut writer_tx, OTHER_SENDER);
        let route = route_tx(default_route_intent(
            "route-order-cert",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let txs = alloc::vec![writer_tx.clone(), route.clone()];

        assert!(matches!(
            verify_tx_execution_order_certificate_v1(&txs, &[0, 0]),
            Err(TransitionError::InvalidInput(
                "tx_execution_order duplicate index"
            ))
        ));
        assert!(matches!(
            verify_tx_execution_order_certificate_v1(&txs, &[0, 2]),
            Err(TransitionError::InvalidInput(
                "tx_execution_order index out of range"
            ))
        ));
        assert!(matches!(
            verify_tx_execution_order_certificate_v1(&txs, &[0, 1]),
            Err(TransitionError::InvalidInput(
                "tx_execution_order worsens route acceptance"
            ))
        ));

        let accepted = verify_tx_execution_order_certificate_v1(&txs, &[1, 0]).unwrap();
        assert_eq!(accepted.ordered_tx_indices, alloc::vec![1, 0]);
        assert_eq!(accepted.accepted_route_count, 1);
    }

    #[test]
    fn tx_execution_order_commitment_matches_python_known_vectors() {
        assert_eq!(
            hex_lower(&tx_execution_order_commitment_v1(&[]).unwrap()),
            "2309466a94ea0e9c2275f10c09ad88cd207537b0d88c3bcee898c0db82730ccf"
        );
        assert_eq!(
            hex_lower(&tx_execution_order_commitment_v1(&[0]).unwrap()),
            "d7f1768c9976ba2360fc74c14497cd262b727dce48bdc51becf39c729066d4cc"
        );
        assert_eq!(
            hex_lower(&tx_execution_order_commitment_v1(&[1, 0]).unwrap()),
            "119fdae071d9a00562a44ef55cd0233774eb8bc3527036d64e8d97db23984280"
        );
    }

    #[test]
    fn tx_execution_order_certificate_preserves_same_sender_order() {
        let first = swap_exact_in_tx_for_pool("swap-sender-first", POOL_ID, ASSET0, ASSET1);
        let second = route_tx(default_route_intent(
            "route-sender-second",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let txs = alloc::vec![first, second];

        assert!(matches!(
            verify_tx_execution_order_certificate_v1(&txs, &[1, 0]),
            Err(TransitionError::InvalidInput(
                "tx_execution_order violates same-sender order"
            ))
        ));
    }

    #[test]
    fn order_oracle_preserves_same_sender_barrier() {
        let writer_tx = swap_exact_in_tx_for_pool("swap-same-sender", POOL_ID, ASSET0, ASSET1);
        let route = route_tx(default_route_intent(
            "route-same-sender",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));

        let plan = optimize_prestate_tx_order_bruteforce_v1(&[writer_tx, route]).unwrap();

        assert_eq!(plan.ordered_tx_indices, alloc::vec![0, 1]);
        assert_eq!(plan.accepted_route_count, 0);
        assert_eq!(plan.deferred_route_count, 1);
        assert!(plan.schedule[0].accepted);
        assert!(!plan.schedule[1].accepted);
        assert_eq!(plan.schedule[1].conflict_tx_index, Some(0));
    }

    #[test]
    fn order_oracle_uses_lexicographic_tie_break() {
        let route_a = route_tx(default_route_intent(
            "route-tie-a",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let route_b = route_tx(second_pool_route_intent("route-tie-b"));

        let plan = optimize_prestate_tx_order_bruteforce_v1(&[route_a, route_b]).unwrap();

        assert_eq!(plan.ordered_tx_indices, alloc::vec![0, 1]);
        assert_eq!(plan.accepted_route_count, 2);
        assert_eq!(plan.deferred_route_count, 0);
    }

    #[test]
    fn order_oracle_rejects_above_bounded_cap() {
        let txs = alloc::vec![
            no_intent_tx("sender-0"),
            no_intent_tx("sender-1"),
            no_intent_tx("sender-2"),
            no_intent_tx("sender-3"),
            no_intent_tx("sender-4"),
            no_intent_tx("sender-5"),
            no_intent_tx("sender-6"),
            no_intent_tx("sender-7"),
            no_intent_tx("sender-8"),
        ];

        assert!(matches!(
            optimize_prestate_tx_order_bruteforce_v1(&txs),
            Err(TransitionError::Unsupported(
                "tx order oracle max_txs exceeded"
            ))
        ));
    }

    #[test]
    fn stable_route_lift_moves_route_before_different_sender_writer() {
        let mut writer_tx =
            swap_exact_in_tx_for_pool("swap-stable-writer", POOL_ID, ASSET0, ASSET1);
        retarget_tx_sender(&mut writer_tx, OTHER_SENDER);
        let route = route_tx(default_route_intent(
            "route-stable-lift",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));

        let plan = stable_route_lift_prestate_tx_order_v1(&[writer_tx, route]).unwrap();

        assert_eq!(plan.ordered_tx_indices, alloc::vec![1, 0]);
        assert_eq!(plan.accepted_route_count, 1);
        assert_eq!(plan.deferred_route_count, 0);
        assert!(plan.schedule[0].accepted);
        assert!(plan.schedule[1].accepted);
    }

    #[test]
    fn stable_route_lift_preserves_same_sender_barrier() {
        let writer_tx = swap_exact_in_tx_for_pool("swap-stable-same", POOL_ID, ASSET0, ASSET1);
        let route = route_tx(default_route_intent(
            "route-stable-same",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));

        let plan = stable_route_lift_prestate_tx_order_v1(&[writer_tx, route]).unwrap();

        assert_eq!(plan.ordered_tx_indices, alloc::vec![0, 1]);
        assert_eq!(plan.accepted_route_count, 0);
        assert_eq!(plan.deferred_route_count, 1);
        assert!(plan.schedule[0].accepted);
        assert!(!plan.schedule[1].accepted);
        assert_eq!(plan.schedule[1].conflict_tx_index, Some(0));
    }

    #[test]
    fn stable_route_lift_scales_past_bruteforce_oracle_cap() {
        let txs = alloc::vec![
            no_intent_tx("sender-0"),
            no_intent_tx("sender-1"),
            no_intent_tx("sender-2"),
            no_intent_tx("sender-3"),
            no_intent_tx("sender-4"),
            no_intent_tx("sender-5"),
            no_intent_tx("sender-6"),
            no_intent_tx("sender-7"),
            no_intent_tx("sender-8"),
        ];

        let plan = stable_route_lift_prestate_tx_order_v1(&txs).unwrap();

        assert_eq!(
            plan.ordered_tx_indices,
            alloc::vec![0, 1, 2, 3, 4, 5, 6, 7, 8]
        );
        assert_eq!(plan.accepted_route_count, 0);
        assert_eq!(plan.deferred_route_count, 0);
    }

    #[test]
    fn stable_route_lift_is_not_maximum_conflict_solver() {
        let mut wide = route_tx(two_pool_route_intent("route-stable-wide"));
        let mut narrow_a = route_tx(default_route_intent(
            "route-stable-narrow-a",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let mut narrow_b = route_tx(second_pool_route_intent("route-stable-narrow-b"));
        retarget_tx_sender(&mut wide, "sender-wide");
        retarget_tx_sender(&mut narrow_a, "sender-narrow-a");
        retarget_tx_sender(&mut narrow_b, "sender-narrow-b");

        let txs = alloc::vec![wide, narrow_a, narrow_b];
        let heuristic = stable_route_lift_prestate_tx_order_v1(&txs).unwrap();
        let oracle = optimize_prestate_tx_order_bruteforce_v1(&txs).unwrap();

        assert_eq!(heuristic.ordered_tx_indices, alloc::vec![0, 1, 2]);
        assert_eq!(heuristic.accepted_route_count, 1);
        assert_eq!(oracle.accepted_route_count, 2);
        assert_ne!(oracle.ordered_tx_indices, heuristic.ordered_tx_indices);
    }

    #[test]
    fn component_repair_beats_stable_route_lift_on_wide_route_witness() {
        let mut wide = route_tx(two_pool_route_intent("route-component-wide"));
        let mut narrow_a = route_tx(default_route_intent(
            "route-component-narrow-a",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let mut narrow_b = route_tx(second_pool_route_intent("route-component-narrow-b"));
        retarget_tx_sender(&mut wide, "component-wide");
        retarget_tx_sender(&mut narrow_a, "component-narrow-a");
        retarget_tx_sender(&mut narrow_b, "component-narrow-b");

        let txs = alloc::vec![wide, narrow_a, narrow_b];
        let stable = stable_route_lift_prestate_tx_order_v1(&txs)
            .expect("stable route lift should evaluate mixed writer witness");
        let repaired = component_repair_prestate_tx_order_v1(&txs)
            .expect("component repair should evaluate mixed writer witness");

        assert_eq!(stable.accepted_route_count, 1);
        assert_eq!(repaired.accepted_route_count, 2);
        assert_ne!(repaired.ordered_tx_indices, stable.ordered_tx_indices);
    }

    #[test]
    fn component_repair_matches_oracle_on_small_component() {
        let mut writer_tx =
            swap_exact_in_tx_for_pool("swap-component-writer", POOL_ID, ASSET0, ASSET1);
        retarget_tx_sender(&mut writer_tx, OTHER_SENDER);
        let route = route_tx(default_route_intent(
            "route-component-lift",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        ));
        let txs = alloc::vec![writer_tx, route];

        let repaired = component_repair_prestate_tx_order_v1(&txs).unwrap();
        let oracle = optimize_prestate_tx_order_bruteforce_v1(&txs).unwrap();

        assert_eq!(repaired, oracle);
    }

    #[test]
    fn component_repair_scales_by_repairing_small_components_past_global_cap() {
        let mut txs = Vec::new();
        for component_index in 0..5 {
            let pool_id = alloc::format!("component-pool-{component_index}");
            let mut writer_tx = swap_exact_in_tx_for_pool(
                &alloc::format!("swap-component-{component_index}"),
                &pool_id,
                ASSET0,
                ASSET1,
            );
            retarget_tx_sender(
                &mut writer_tx,
                &alloc::format!("component-writer-{component_index}"),
            );
            let mut route = route_tx_for_pool(
                &alloc::format!("route-component-{component_index}"),
                &pool_id,
            );
            retarget_tx_sender(
                &mut route,
                &alloc::format!("component-route-{component_index}"),
            );
            txs.push(writer_tx);
            txs.push(route);
        }

        let repaired = component_repair_prestate_tx_order_v1(&txs).unwrap();

        assert!(matches!(
            optimize_prestate_tx_order_bruteforce_v1(&txs),
            Err(TransitionError::Unsupported(
                "tx order oracle max_txs exceeded"
            ))
        ));
        assert_eq!(repaired.accepted_route_count, 5);
        assert_eq!(repaired.deferred_route_count, 0);
    }

    #[test]
    fn component_repair_fpt_beats_stable_lift_inside_large_route_component() {
        let pool_ids: Vec<String> = (0..9)
            .map(|pool_index| alloc::format!("fpt-pool-{pool_index}"))
            .collect();
        let mut txs = Vec::new();

        let mut wide = route_tx_for_pool_ids("route-fpt-wide", &pool_ids);
        retarget_tx_sender(&mut wide, "fpt-wide");
        txs.push(wide);

        for (pool_index, pool_id) in pool_ids.iter().enumerate() {
            let mut narrow = route_tx_for_pool_ids(
                &alloc::format!("route-fpt-narrow-{pool_index}"),
                &[pool_id.clone()],
            );
            retarget_tx_sender(&mut narrow, &alloc::format!("fpt-narrow-{pool_index}"));
            txs.push(narrow);
        }

        let stable = stable_route_lift_prestate_tx_order_v1(&txs).unwrap();
        let repaired = component_repair_prestate_tx_order_v1(&txs).unwrap();

        assert!(matches!(
            optimize_prestate_tx_order_bruteforce_v1(&txs),
            Err(TransitionError::Unsupported(
                "tx order oracle max_txs exceeded"
            ))
        ));
        assert_eq!(stable.accepted_route_count, 1);
        assert_eq!(repaired.accepted_route_count, 9);
        assert_eq!(repaired.ordered_tx_indices.len(), txs.len());
    }

    #[test]
    fn component_repair_fpt_falls_back_on_repeated_sender_barrier() {
        let pool_ids: Vec<String> = (0..9)
            .map(|pool_index| alloc::format!("barrier-pool-{pool_index}"))
            .collect();
        let mut txs = Vec::new();

        let mut wide = route_tx_for_pool_ids("route-fpt-barrier-wide", &pool_ids);
        retarget_tx_sender(&mut wide, "fpt-shared-sender");
        txs.push(wide);

        for (pool_index, pool_id) in pool_ids.iter().enumerate() {
            let mut narrow = route_tx_for_pool_ids(
                &alloc::format!("route-fpt-barrier-narrow-{pool_index}"),
                &[pool_id.clone()],
            );
            retarget_tx_sender(&mut narrow, "fpt-shared-sender");
            txs.push(narrow);
        }

        let stable = stable_route_lift_prestate_tx_order_v1(&txs).unwrap();
        let repaired = component_repair_prestate_tx_order_v1(&txs).unwrap();

        assert_eq!(repaired, stable);
        assert_eq!(
            repaired.ordered_tx_indices,
            alloc::vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
        assert_eq!(repaired.accepted_route_count, 1);
    }

    #[test]
    fn component_repair_writer_aware_fpt_beats_stable_lift_with_prior_writer() {
        let pool_ids: Vec<String> = (0..9)
            .map(|pool_index| alloc::format!("writer-aware-pool-{pool_index}"))
            .collect();
        let mut txs = Vec::new();

        let mut writer =
            swap_exact_in_tx_for_pool("swap-writer-aware", &pool_ids[0], ASSET0, ASSET1);
        retarget_tx_sender(&mut writer, "writer-aware-writer");
        txs.push(writer);

        let mut wide = route_tx_for_pool_ids("route-writer-aware-wide", &pool_ids);
        retarget_tx_sender(&mut wide, "writer-aware-wide");
        txs.push(wide);

        for (pool_index, pool_id) in pool_ids.iter().enumerate() {
            let mut narrow = route_tx_for_pool_ids(
                &alloc::format!("route-writer-aware-narrow-{pool_index}"),
                &[pool_id.clone()],
            );
            retarget_tx_sender(
                &mut narrow,
                &alloc::format!("writer-aware-narrow-{pool_index}"),
            );
            txs.push(narrow);
        }

        let stable = stable_route_lift_prestate_tx_order_v1(&txs).unwrap();
        let repaired = component_repair_prestate_tx_order_v1(&txs).unwrap();

        assert!(matches!(
            optimize_prestate_tx_order_bruteforce_v1(&txs),
            Err(TransitionError::Unsupported(
                "tx order oracle max_txs exceeded"
            ))
        ));
        assert_eq!(stable.accepted_route_count, 1);
        assert_eq!(repaired.accepted_route_count, 9);
        assert_eq!(repaired.ordered_tx_indices.len(), txs.len());
    }

    #[test]
    fn component_repair_prefix_fpt_improves_repeated_sender_tail_case(
    ) -> Result<(), TransitionError> {
        let pool_ids: Vec<String> = (0..9)
            .map(|pool_index| alloc::format!("prefix-fpt-pool-{pool_index}"))
            .collect();
        let mut txs = Vec::new();

        let mut wide = route_tx_for_pool_ids("route-prefix-tail-wide", &pool_ids);
        retarget_tx_sender(&mut wide, "prefix-tail-shared");
        txs.push(wide);

        let mut writer =
            swap_exact_in_tx_for_pool("swap-prefix-tail", &pool_ids[0], ASSET0, ASSET1);
        retarget_tx_sender(&mut writer, "prefix-tail-shared");
        txs.push(writer);

        for (pool_index, pool_id) in pool_ids.iter().enumerate() {
            let mut narrow = route_tx_for_pool_ids(
                &alloc::format!("route-prefix-tail-narrow-{pool_index}"),
                &[pool_id.clone()],
            );
            retarget_tx_sender(
                &mut narrow,
                &alloc::format!("prefix-tail-narrow-{pool_index}"),
            );
            txs.push(narrow);
        }

        let stable = stable_route_lift_prestate_tx_order_v1(&txs)?;
        let repaired = component_repair_prestate_tx_order_v1(&txs)?;

        assert_eq!(stable.accepted_route_count, 1);
        assert_eq!(repaired.accepted_route_count, 9);
        let wide_pos = repaired
            .ordered_tx_indices
            .iter()
            .position(|index| *index == 0);
        let writer_pos = repaired
            .ordered_tx_indices
            .iter()
            .position(|index| *index == 1);
        assert!(wide_pos.is_some());
        assert!(writer_pos.is_some());
        assert!(wide_pos < writer_pos);
        Ok(())
    }

    #[test]
    fn component_repair_prefix_fpt_preserves_blocking_sender_prefix() -> Result<(), TransitionError>
    {
        let mut txs = Vec::new();
        let mut writer = swap_exact_in_tx_for_pool("swap-prefix-blocker", POOL_ID, ASSET0, ASSET1);
        retarget_tx_sender(&mut writer, "prefix-blocked-sender");
        txs.push(writer);

        let mut route = route_tx_for_pool("route-prefix-blocked", POOL_ID);
        retarget_tx_sender(&mut route, "prefix-blocked-sender");
        txs.push(route);

        for tail_index in 0..9 {
            txs.push(no_intent_tx(&alloc::format!("prefix-tail-{tail_index}")));
        }

        let repaired = component_repair_prestate_tx_order_v1(&txs)?;
        let writer_pos = repaired
            .ordered_tx_indices
            .iter()
            .position(|index| *index == 0);
        let route_pos = repaired
            .ordered_tx_indices
            .iter()
            .position(|index| *index == 1);

        assert!(writer_pos.is_some());
        assert!(route_pos.is_some());
        assert!(writer_pos < route_pos);
        assert_eq!(repaired.accepted_route_count, 0);
        Ok(())
    }

    #[test]
    fn component_repair_sender_prefix_dp_handles_route_count_above_subset_cap(
    ) -> Result<(), TransitionError> {
        let pool_ids: Vec<String> = (0..18)
            .map(|pool_index| alloc::format!("prefix-dp-pool-{pool_index}"))
            .collect();
        let mut txs = Vec::new();

        let mut wide = route_tx_for_pool_ids("route-prefix-dp-wide", &pool_ids);
        retarget_tx_sender(&mut wide, "prefix-dp-wide");
        txs.push(wide);

        for (pool_index, pool_id) in pool_ids.iter().enumerate() {
            let mut narrow = route_tx_for_pool_ids(
                &alloc::format!("route-prefix-dp-narrow-{pool_index}"),
                &[pool_id.clone()],
            );
            retarget_tx_sender(
                &mut narrow,
                &alloc::format!("prefix-dp-narrow-sender-{}", pool_index / 3),
            );
            txs.push(narrow);
        }

        let stable = stable_route_lift_prestate_tx_order_v1(&txs)?;
        let repaired = component_repair_prestate_tx_order_v1(&txs)?;

        assert!(prefix_constrained_route_packing_order(&txs)?.is_none());
        assert!(writer_aware_unique_sender_route_candidates(&txs)?.is_none());
        assert_eq!(stable.accepted_route_count, 1);
        assert_eq!(repaired.accepted_route_count, 18);
        Ok(())
    }

    #[test]
    fn create_pool_rejects_canonical_equal_hex_asset_ids_without_mutation() {
        let asset0 = "0xAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAaAa";
        let asset1 = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        assert!(asset0 < asset1);
        assert_eq!(
            canonical_pool_asset_id(asset0),
            canonical_pool_asset_id(asset1)
        );

        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: asset0.to_string(),
                amount: 10_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: asset1.to_string(),
                amount: 10_000,
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
                        intent_id: "create-canonical-equal-assets".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        asset0: asset0.to_string(),
                        asset1: asset1.to_string(),
                        fee_bps: 30,
                        amount0: 10_000,
                        amount1: 10_000,
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
            Err(TransitionError::InvalidInput(
                "assets must be in canonical order"
            ))
        ));
        assert_eq!(state.get_balance(SENDER, asset0), 10_000);
        assert_eq!(state.get_balance(SENDER, asset1), 10_000);
        assert!(state.to_snapshot().pools.is_empty());
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

        state
            .apply_tx(&tx, 1, &ProtocolFeeConfig::default())
            .unwrap();
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
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
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
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
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

        state
            .apply_tx(&tx, 1, &ProtocolFeeConfig::default())
            .unwrap();
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

        state
            .apply_tx(&tx, 1, &ProtocolFeeConfig::default())
            .unwrap();
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

        state
            .apply_tx(&tx, 1, &ProtocolFeeConfig::default())
            .unwrap();
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
            state.apply_tx(&add_tx, 1, &ProtocolFeeConfig::default()),
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
            state.apply_tx(&remove_tx, 1, &ProtocolFeeConfig::default()),
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
            tx_execution_order: Vec::new(),
            pre_nonces: Vec::new(),
            tx_ingress: alloc::vec![TxIngressFactV1 {
                sender_pubkey: SENDER.to_string(),
                nonce: 0,
            }],
            chain_balances_post: Vec::new(),
            expected_post_app_hash: decode_hex_32(
                "168c616c3e9cbc832f9accf6022fcf5153f4611de71115e36a6e540a1230101b",
            ),
            protocol_fee_share_bps: 0,
            protocol_fee_recipient_pubkey: None,
        };

        let journal = execute_state_proof_input_v1(input.clone()).unwrap();
        assert_eq!(journal.journal_version, JOURNAL_VERSION);
        assert_eq!(journal.state_hash, [7u8; 32]);
        assert_eq!(journal.txs_commitment, txs_commitment_v1(&txs));
        assert_eq!(
            journal.tx_execution_order_commitment,
            tx_execution_order_commitment_v1(&[0]).unwrap()
        );
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
    fn state_proof_execution_uses_verified_tx_execution_order() {
        let fee_config = ProtocolFeeConfig::default();
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: OTHER_SENDER.to_string(),
            asset: ASSET0.to_string(),
            amount: 10_000_000,
        });
        let mut writer_tx = swap_exact_in_tx_for_pool("swap-order-exec", POOL_ID, ASSET0, ASSET1);
        retarget_tx_sender(&mut writer_tx, OTHER_SENDER);
        let quote_state = DexStateV1::from_snapshot(snapshot.clone()).unwrap();
        let mut route_intent =
            default_route_intent("route-order-exec", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        bind_route_hash(&mut route_intent, &quote_state, &fee_config);
        let route_tx = route_tx(route_intent);
        let txs = alloc::vec![writer_tx.clone(), route_tx.clone()];
        let tx_ingress = alloc::vec![
            TxIngressFactV1 {
                sender_pubkey: OTHER_SENDER.to_string(),
                nonce: 0,
            },
            TxIngressFactV1 {
                sender_pubkey: SENDER.to_string(),
                nonce: 0,
            },
        ];

        let mut expected_state = DexStateV1::from_snapshot(snapshot.clone()).unwrap();
        expected_state
            .apply_tx(&route_tx, 1, &fee_config)
            .expect("route first should match pre-state quote hash");
        expected_state
            .apply_tx(&writer_tx, 1, &fee_config)
            .expect("writer second should remain valid");
        let expected_post_app_hash = expected_state.canonical_app_hash_sha256();

        let input = StateProofInputV1 {
            state_hash: [9u8; 32],
            block_timestamp: 1,
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: snapshot,
            txs: txs.clone(),
            tx_execution_order: alloc::vec![1, 0],
            pre_nonces: Vec::new(),
            tx_ingress,
            chain_balances_post: Vec::new(),
            expected_post_app_hash,
            protocol_fee_share_bps: 0,
            protocol_fee_recipient_pubkey: None,
        };

        let journal = execute_state_proof_input_v1(input.clone()).unwrap();
        assert_eq!(
            journal.tx_execution_order_commitment,
            tx_execution_order_commitment_v1(&[1, 0]).unwrap()
        );
        assert_eq!(journal.post_app_hash, expected_post_app_hash);

        let mut default_order = input;
        default_order.tx_execution_order.clear();
        assert!(matches!(
            execute_state_proof_input_v1(default_order),
            Err(TransitionError::InvalidInput("quote_receipt_hash mismatch"))
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
            state
                .apply_tx(tx, 1, &ProtocolFeeConfig::default())
                .unwrap();
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
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
            Err(TransitionError::InvalidInput("amount_out is zero"))
        ));
        assert_eq!(state.get_balance(SENDER, ASSET0), 2);
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 0);
        let post = state.to_snapshot();
        assert_eq!(post.pools.len(), 1);
        assert_eq!(post.pools[0].reserve0, 10_000);
        assert_eq!(post.pools[0].reserve1, 10_000);
    }

    fn sender_balance_snapshot(asset: &str, amount: u128) -> DexSnapshotV1 {
        let mut s = empty_snapshot();
        s.balances = alloc::vec![DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: asset.to_string(),
            amount,
        }];
        s.pools = alloc::vec![pool_entry(1_000_000, 1_000_000)];
        s
    }

    #[test]
    fn swap_exact_out_transition_executes_and_credits_recipient() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactOut(SwapExactOutIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "swap-exact-out-1".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_out: 10_000,
                        max_amount_in: 20_000,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        state
            .apply_tx(&tx, 1, &ProtocolFeeConfig::default())
            .unwrap();
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 10_000);
        assert!(state.get_balance(SENDER, ASSET0) < 10_000_000);
        let post = state.to_snapshot();
        assert_eq!(post.pools[0].reserve1, 1_000_000 - 10_000);
    }

    #[test]
    fn swap_exact_out_rejects_when_max_amount_in_exceeded() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactOut(SwapExactOutIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "swap-exact-out-max".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_out: 500_000,
                        max_amount_in: 1,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
            Err(TransitionError::InvalidInput("max_amount_in exceeded"))
        ));
    }

    #[test]
    fn swap_exact_in_with_protocol_fee_credits_recipient_in_asset_in() {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let fee_config = ProtocolFeeConfig {
            share_bps: 5_000,
            recipient_pubkey: Some(RECIPIENT.to_string()),
        };
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
                        intent_id: "swap-protocol-fee".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_in: 100_000,
                        min_amount_out: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        state.apply_tx(&tx, 1, &fee_config).unwrap();
        // Protocol fee is credited in asset_in (ASSET0), not asset_out (ASSET1).
        let pf = state.get_balance(RECIPIENT, ASSET0);
        assert_eq!(pf, 150);
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 0);
        let post = state.to_snapshot();
        let pool = post
            .pools
            .iter()
            .find(|entry| entry.pool_id == POOL_ID)
            .unwrap();
        assert_eq!(pool.reserve0, 1_000_000 + 100_000 - pf);
    }

    #[test]
    fn swap_exact_in_with_protocol_fee_zero_share_does_not_credit() {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let fee_config = ProtocolFeeConfig::default();
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
                        intent_id: "swap-no-protocol-fee".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_in: 100_000,
                        min_amount_out: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        state.apply_tx(&tx, 1, &fee_config).unwrap();
        assert_eq!(state.get_balance(RECIPIENT, ASSET0), 0);
    }

    #[test]
    fn create_pool_conservation_audit_catches_lp_drift() {
        // Mutation-resistance: if lp_to_creator + lp_locked != lp_supply_total, audit catches it.
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 1_000_000,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 1_000_000,
            },
        ];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();

        // Manually create a pool with a bug: lp_supply_total is wrong
        let amount0 = 10_000u128;
        let amount1 = 10_000u128;
        let lp_supply_total = 10_000u128;
        let lp_to_creator = 9_999u128; // bug: should be 9_990 (lp_supply - MIN_LP_LOCK)
        let lp_locked = 10u128;

        state.sub_balance(SENDER, ASSET0, amount0).unwrap();
        state.sub_balance(SENDER, ASSET1, amount1).unwrap();
        state.add_lp(SENDER, "buggy-pool", lp_to_creator).unwrap();
        state
            .add_lp(LP_LOCK_PUBKEY, "buggy-pool", lp_locked)
            .unwrap();
        state.pools.insert(
            "buggy-pool".to_string(),
            DexPoolEntryV1 {
                pool_id: "buggy-pool".to_string(),
                asset0: ASSET0.to_string(),
                asset1: ASSET1.to_string(),
                reserve0: amount0,
                reserve1: amount1,
                fee_bps: 30,
                lp_supply: lp_supply_total,
                status: "ACTIVE".to_string(),
                created_at: 0,
            },
        );

        // lp_to_creator + lp_locked = 9999 + 10 = 10009 != 10000 = lp_supply_total
        let result = state.audit_create_pool_conservation(CreatePoolConservationAudit {
            pre_state: &pre_state,
            pool_id: "buggy-pool",
            sender: SENDER,
            asset0: ASSET0,
            asset1: ASSET1,
            amount0,
            amount1,
            lp_to_creator,
            lp_locked,
            lp_supply_total,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: create_pool lp_to_creator + lp_locked != lp_supply_total"
                ))
            ),
            "create_pool audit must catch LP drift: {:?}",
            result
        );
    }

    #[test]
    fn add_liquidity_conservation_audit_catches_reserve_drift() {
        // Mutation-resistance: if reserve delta != amount used, audit catches it.
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
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();

        // Simulate a bug: add extra to reserve0 (value created from nowhere)
        let amount0_used = 1_000u128;
        let amount1_used = 1_000u128;
        let mut pool = state.pools.get(POOL_ID).cloned().unwrap();
        pool.reserve0 += amount0_used + 100; // bug: extra 100
        pool.reserve1 += amount1_used;
        pool.lp_supply += 1_000;
        state.pools.insert(POOL_ID.to_string(), pool);
        state.sub_balance(SENDER, ASSET0, amount0_used).unwrap();
        state.sub_balance(SENDER, ASSET1, amount1_used).unwrap();
        state.add_lp(SENDER, POOL_ID, 1_000).unwrap();

        let result = state.audit_add_liquidity_conservation(AddLiquidityConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            sender: SENDER,
            lp_recipient: SENDER,
            asset0: ASSET0,
            asset1: ASSET1,
            amount0_used,
            amount1_used,
            lp_minted: 1_000,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: add_liq reserve0 delta != amount0_used"
                ))
            ),
            "add_liq audit must catch reserve drift: {:?}",
            result
        );
    }

    #[test]
    fn remove_liquidity_conservation_audit_catches_value_destruction() {
        // Mutation-resistance: if recipient gets less than what leaves pool, audit catches it.
        let mut snapshot = empty_snapshot();
        snapshot.balances = alloc::vec![
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET0.to_string(),
                amount: 0,
            },
            DexBalanceEntryV1 {
                pubkey: SENDER.to_string(),
                asset: ASSET1.to_string(),
                amount: 0,
            },
        ];
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        state.add_lp(SENDER, POOL_ID, 10_000).unwrap();
        let pre_state = state.clone();

        // Simulate a bug: subtract full amount from reserves but credit only half
        let amount0_out = 1_000u128;
        let amount1_out = 1_000u128;
        let lp_amount = 1_000u128;
        let buggy_credit0 = amount0_out / 2;

        let mut pool = state.pools.get(POOL_ID).cloned().unwrap();
        pool.reserve0 -= amount0_out;
        pool.reserve1 -= amount1_out;
        pool.lp_supply -= lp_amount;
        state.pools.insert(POOL_ID.to_string(), pool);
        state.sub_lp(SENDER, POOL_ID, lp_amount).unwrap();
        state.add_balance(SENDER, ASSET0, buggy_credit0).unwrap();
        state.add_balance(SENDER, ASSET1, amount1_out).unwrap();

        let result = state.audit_remove_liquidity_conservation(RemoveLiquidityConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            lp_sender: SENDER,
            recipient: SENDER,
            asset0: ASSET0,
            asset1: ASSET1,
            amount0_out,
            amount1_out,
            lp_amount,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: remove_liq recipient credit0 != amount0_out"
                ))
            ),
            "remove_liq audit must catch value destruction: {:?}",
            result
        );
    }

    #[test]
    fn route_exact_in_single_leg_executes_like_swap() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let fee_config = ProtocolFeeConfig::default();
        let mut intent =
            default_route_intent("route-exact-in-1", "ROUTE_EXACT_IN", 100_000, 0, 0, 0);
        bind_route_hash(&mut intent, &state, &fee_config);
        let tx = route_tx(intent);

        state.apply_tx(&tx, 1, &fee_config).unwrap();
        let recipient_out = state.get_balance(RECIPIENT, ASSET1);
        assert!(recipient_out > 0, "route should credit output to recipient");
    }

    #[test]
    fn route_exact_out_single_leg_executes_and_credits_exact_amount() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let fee_config = ProtocolFeeConfig::default();
        let mut intent = default_route_intent(
            "route-exact-out-1",
            "ROUTE_EXACT_OUT",
            0,
            0,
            10_000,
            100_000,
        );
        bind_route_hash(&mut intent, &state, &fee_config);
        let tx = route_tx(intent);

        state.apply_tx(&tx, 1, &fee_config).unwrap();
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 10_000);
    }

    #[test]
    fn route_exact_in_min_output_reject_is_noop() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let fee_config = ProtocolFeeConfig::default();
        let mut intent = default_route_intent(
            "route-min-out-noop",
            "ROUTE_EXACT_IN",
            100_000,
            1_000_000_000,
            0,
            0,
        );
        bind_route_hash(&mut intent, &state, &fee_config);
        let tx = route_tx(intent);
        let pre_hash = state.canonical_app_hash_sha256();

        assert!(matches!(
            state.apply_tx(&tx, 1, &fee_config),
            Err(TransitionError::InvalidInput(
                "route total_min_amount_out not met"
            ))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), pre_hash);
    }

    #[test]
    fn route_exact_out_overdelivery_gap_stays_in_pool_reserve() {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10);
        let mut pool = pool_entry(1, 4);
        pool.fee_bps = 0;
        snapshot.pools = alloc::vec![pool];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let fee_config = ProtocolFeeConfig::default();
        let mut intent =
            default_route_intent("route-overdelivery-reserve", "ROUTE_EXACT_OUT", 0, 0, 1, 1);
        bind_route_hash(&mut intent, &state, &fee_config);
        let tx = route_tx(intent);

        state.apply_tx(&tx, 1, &fee_config).unwrap();
        assert_eq!(state.get_balance(SENDER, ASSET0), 9);
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 1);
        let post = state.to_snapshot();
        assert_eq!(post.pools[0].reserve0, 2);
        assert_eq!(post.pools[0].reserve1, 3);
    }

    #[test]
    fn route_conservation_audit_catches_value_destruction() {
        // Mutation-resistance: if route credits less than what leaves pool,
        // the route conservation audit must catch it.
        let snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        // Simulate a route with a value destruction bug:
        // subtract full amount_out from reserves but credit only half.
        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;
        let buggy_credit = amount_out / 2;

        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);
        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();
        state.add_balance(RECIPIENT, ASSET1, buggy_credit).unwrap();

        let result = state.audit_route_conservation(RouteConservationAudit {
            pre_state: &pre_state,
            sender: SENDER,
            asset_in: ASSET0,
            sender_debit: amount_in,
            recipient: RECIPIENT,
            asset_out: ASSET1,
            recipient_credit: buggy_credit,
            protocol_fee_recipient: None,
            pool_audits: alloc::vec![RoutePoolAudit {
                pool_id: POOL_ID.to_string(),
                asset_in: ASSET0.to_string(),
                asset_out: ASSET1.to_string(),
                reserve_in_delta: amount_in,
                reserve_out_delta: amount_out,
                protocol_fee_credit_in: 0,
            }],
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: route output not fully credited to recipient"
                ))
            ),
            "route audit must catch value destruction: {:?}",
            result
        );
    }

    #[test]
    fn route_audit_catches_asset_chain_mismatch() {
        // Codex LOW finding: route audit must catch broken intermediate asset chain.
        // Two pools with correct per-pool asset pairs but broken chain:
        // pool_0 outputs ASSET1, pool_1 expects ASSET2 (not ASSET1).
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: "ASSET3".to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();

        // Create pool_2 with ASSET2/ASSET3 (different from pool_1's ASSET0/ASSET1)
        let pool2_id = "0xee9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686";
        state.pools.insert(
            pool2_id.to_string(),
            DexPoolEntryV1 {
                pool_id: pool2_id.to_string(),
                asset0: "ASSET2".to_string(),
                asset1: "ASSET3".to_string(),
                reserve0: 10_000,
                reserve1: 10_000,
                fee_bps: 30,
                lp_supply: 10_000,
                status: "ACTIVE".to_string(),
                created_at: 0,
            },
        );
        let pre_state = state.clone();

        // Apply reserve changes: pool_1 gets +1000/-100, pool_2 gets +100/-50
        let mut p1 = state.pools.get(POOL_ID).cloned().unwrap();
        p1.reserve0 += 1000;
        p1.reserve1 -= 100;
        state.pools.insert(POOL_ID.to_string(), p1);

        let mut p2 = state.pools.get(pool2_id).cloned().unwrap();
        p2.reserve0 += 100; // ASSET2 in
        p2.reserve1 -= 50; // ASSET3 out
        state.pools.insert(pool2_id.to_string(), p2);

        state.sub_balance(SENDER, ASSET0, 1000).unwrap();
        state.add_balance(RECIPIENT, "ASSET3", 50).unwrap();

        // pool_0: ASSET0->ASSET1 (correct pair), pool_1: ASSET2->ASSET3 (correct pair)
        // But pool_0.asset_out (ASSET1) != pool_1.asset_in (ASSET2) — chain broken
        let pool_audits = alloc::vec![
            RoutePoolAudit {
                pool_id: POOL_ID.to_string(),
                asset_in: ASSET0.to_string(),
                asset_out: ASSET1.to_string(),
                reserve_in_delta: 1000,
                reserve_out_delta: 100,
                protocol_fee_credit_in: 0,
            },
            RoutePoolAudit {
                pool_id: pool2_id.to_string(),
                asset_in: "ASSET2".to_string(),
                asset_out: "ASSET3".to_string(),
                reserve_in_delta: 100,
                reserve_out_delta: 50,
                protocol_fee_credit_in: 0,
            },
        ];

        let result = state.audit_route_conservation(RouteConservationAudit {
            pre_state: &pre_state,
            sender: SENDER,
            asset_in: ASSET0,
            sender_debit: 1000,
            recipient: RECIPIENT,
            asset_out: "ASSET3",
            recipient_credit: 50,
            protocol_fee_recipient: None,
            pool_audits,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::InvalidInput(
                    "audit: route asset chain mismatch at intermediate hop"
                ))
            ),
            "route audit must catch asset chain mismatch: {:?}",
            result
        );
    }

    #[test]
    fn route_conservation_audit_passes_on_correct_flow() {
        let snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;

        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);
        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();
        state.add_balance(RECIPIENT, ASSET1, amount_out).unwrap();

        let result = state.audit_route_conservation(RouteConservationAudit {
            pre_state: &pre_state,
            sender: SENDER,
            asset_in: ASSET0,
            sender_debit: amount_in,
            recipient: RECIPIENT,
            asset_out: ASSET1,
            recipient_credit: amount_out,
            protocol_fee_recipient: None,
            pool_audits: alloc::vec![RoutePoolAudit {
                pool_id: POOL_ID.to_string(),
                asset_in: ASSET0.to_string(),
                asset_out: ASSET1.to_string(),
                reserve_in_delta: amount_in,
                reserve_out_delta: amount_out,
                protocol_fee_credit_in: 0,
            }],
        });

        assert!(
            result.is_ok(),
            "route audit must pass on correct flow: {:?}",
            result
        );
    }

    #[test]
    fn route_conservation_audit_catches_broken_chain() {
        // Mutation-resistance: if intermediate chain is broken (pool_i.out != pool_{i+1}.in),
        // the audit must catch it. Simulate a 2-pool route where the chain is broken.
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let pool1 = pool_entry(1_000_000, 2_000_000);
        let mut pool2 = pool_entry(2_000_000, 1_000_000);
        pool2.pool_id = "POOL2".to_string();
        pool2.asset0 = ASSET1.to_string();
        pool2.asset1 = "ASSET2".to_string();
        snapshot.pools = alloc::vec![pool1, pool2];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();

        // Modify pools to match claimed deltas, but with a broken chain:
        // pool1 outputs 100 but pool2 receives only 50 (50 units vanish).
        {
            let mut p1 = state.pools.get(POOL_ID).cloned().unwrap();
            p1.reserve0 += 1000;
            p1.reserve1 -= 100;
            state.pools.insert(POOL_ID.to_string(), p1);
        }
        {
            let mut p2 = state.pools.get("POOL2").cloned().unwrap();
            p2.reserve0 += 50;
            p2.reserve1 -= 50;
            state.pools.insert("POOL2".to_string(), p2);
        }

        let result = state.audit_route_conservation(RouteConservationAudit {
            pre_state: &pre_state,
            sender: SENDER,
            asset_in: ASSET0,
            sender_debit: 1000,
            recipient: RECIPIENT,
            asset_out: "ASSET2",
            recipient_credit: 50,
            protocol_fee_recipient: None,
            pool_audits: alloc::vec![
                RoutePoolAudit {
                    pool_id: POOL_ID.to_string(),
                    asset_in: ASSET0.to_string(),
                    asset_out: ASSET1.to_string(),
                    reserve_in_delta: 1000,
                    reserve_out_delta: 100,
                    protocol_fee_credit_in: 0,
                },
                RoutePoolAudit {
                    pool_id: "POOL2".to_string(),
                    asset_in: ASSET1.to_string(),
                    asset_out: "ASSET2".to_string(),
                    reserve_in_delta: 50,
                    reserve_out_delta: 50,
                    protocol_fee_credit_in: 0,
                },
            ],
        });

        assert!(
            matches!(result, Err(TransitionError::Arithmetic(_))),
            "route audit must catch broken chain: {:?}",
            result
        );
    }

    #[test]
    fn route_rejects_multihop_legs() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::Route(RouteIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "route-multihop".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        quote_receipt_hash: "0xabc".to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        leg_indices: alloc::vec![0],
                        legs: alloc::vec![RouteLegV1 {
                            hops: alloc::vec![
                                RouteLegHopV1 {
                                    pool_id: POOL_ID.to_string(),
                                },
                                RouteLegHopV1 {
                                    pool_id: POOL_ID.to_string(),
                                },
                            ],
                        }],
                        kind: "ROUTE_EXACT_IN".to_string(),
                        total_amount_in: 100_000,
                        total_min_amount_out: 0,
                        total_amount_out: 0,
                        total_max_amount_in: 0,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
            Err(TransitionError::Unsupported("route_multihop_unsupported"))
        ));
    }

    #[test]
    fn protocol_fee_share_bps_over_10000_rejects_at_execute() {
        let snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let input = StateProofInputV1 {
            state_hash: [0u8; 32],
            block_timestamp: 1,
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: snapshot,
            txs: Vec::new(),
            tx_execution_order: Vec::new(),
            pre_nonces: Vec::new(),
            tx_ingress: Vec::new(),
            chain_balances_post: Vec::new(),
            expected_post_app_hash: [0u8; 32],
            protocol_fee_share_bps: 10_001,
            protocol_fee_recipient_pubkey: Some(RECIPIENT.to_string()),
        };
        assert!(matches!(
            execute_state_proof_input_v1(input),
            Err(TransitionError::InvalidInput(
                "protocol_fee_share_bps out of range"
            ))
        ));
    }

    #[test]
    fn route_rejects_duplicate_pool_id_across_legs() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::Route(RouteIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "route-dup-pool".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        quote_receipt_hash: "0xabc".to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        leg_indices: alloc::vec![0, 1],
                        legs: alloc::vec![
                            RouteLegV1 {
                                hops: alloc::vec![RouteLegHopV1 {
                                    pool_id: POOL_ID.to_string(),
                                }],
                            },
                            RouteLegV1 {
                                hops: alloc::vec![RouteLegHopV1 {
                                    pool_id: POOL_ID.to_string(),
                                }],
                            },
                        ],
                        kind: "ROUTE_EXACT_IN".to_string(),
                        total_amount_in: 100_000,
                        total_min_amount_out: 0,
                        total_amount_out: 0,
                        total_max_amount_in: 0,
                        recipient: RECIPIENT.to_string(),
                        salt: None,
                    }),
                }],
            },
        };

        assert!(matches!(
            state.apply_tx(&tx, 1, &ProtocolFeeConfig::default()),
            Err(TransitionError::InvalidInput(
                "route duplicate pool_id across legs"
            ))
        ));
    }

    #[test]
    fn swap_exact_in_k_invariant_holds_after_protocol_fee() {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();
        let k_before = pool.reserve0.checked_mul(pool.reserve1).unwrap();
        let fee_config = ProtocolFeeConfig {
            share_bps: 10_000,
            recipient_pubkey: Some(RECIPIENT.to_string()),
        };
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
                        intent_id: "swap-k-inv".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_in: 100_000,
                        min_amount_out: 0,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };
        state.apply_tx(&tx, 1, &fee_config).unwrap();
        let pool_after = state.pools.get(POOL_ID).cloned().unwrap();
        let k_after = pool_after
            .reserve0
            .checked_mul(pool_after.reserve1)
            .unwrap();
        assert!(
            k_after >= k_before,
            "k-invariant violated: {} < {}",
            k_after,
            k_before
        );
    }

    #[test]
    fn swap_exact_out_k_invariant_holds_after_protocol_fee() {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();
        let k_before = pool.reserve0.checked_mul(pool.reserve1).unwrap();
        let fee_config = ProtocolFeeConfig {
            share_bps: 10_000,
            recipient_pubkey: Some(RECIPIENT.to_string()),
        };
        let tx = TauTxV1 {
            sender_pubkey: SENDER.to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: alloc::vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactOut(SwapExactOutIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "swap-out-k-inv".to_string(),
                        sender_pubkey: SENDER.to_string(),
                        deadline: 100,
                        pool_id: POOL_ID.to_string(),
                        asset_in: ASSET0.to_string(),
                        asset_out: ASSET1.to_string(),
                        amount_out: 1_000,
                        max_amount_in: 10_000,
                        recipient: SENDER.to_string(),
                        salt: None,
                    }),
                }],
            },
        };
        state.apply_tx(&tx, 1, &fee_config).unwrap();
        let pool_after = state.pools.get(POOL_ID).cloned().unwrap();
        let k_after = pool_after
            .reserve0
            .checked_mul(pool_after.reserve1)
            .unwrap();
        assert!(
            k_after >= k_before,
            "k-invariant violated: {} < {}",
            k_after,
            k_before
        );
    }

    #[test]
    fn route_rejects_protocol_fee_without_recipient() {
        let mut state =
            DexStateV1::from_snapshot(sender_balance_snapshot(ASSET0, 10_000_000)).unwrap();
        let fee_config = ProtocolFeeConfig {
            share_bps: 1_000,
            recipient_pubkey: None,
        };
        let mut intent = default_route_intent(
            "route-fee-missing-recipient",
            "ROUTE_EXACT_IN",
            100_000,
            0,
            0,
            0,
        );
        bind_route_hash(&mut intent, &state, &fee_config);
        let tx = route_tx(intent);
        let pre_hash = state.canonical_app_hash_sha256();

        assert!(matches!(
            state.apply_tx(&tx, 1, &fee_config),
            Err(TransitionError::InvalidInput(
                "protocol_fee_recipient_pubkey required when share_bps > 0"
            ))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), pre_hash);
    }

    #[test]
    fn route_exact_in_captures_protocol_fee_per_leg() {
        let mut snapshot = chained_two_pool_snapshot();
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: PROTOCOL_FEE_RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 0,
        });
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: PROTOCOL_FEE_RECIPIENT.to_string(),
            asset: ASSET1.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let fee_config = ProtocolFeeConfig {
            share_bps: 5_000,
            recipient_pubkey: Some(PROTOCOL_FEE_RECIPIENT.to_string()),
        };
        let mut intent = chained_exact_in_route_intent("route-fee-exact-in");
        bind_route_hash(&mut intent, &state, &fee_config);
        let total_amount_in = intent.total_amount_in;

        let first_pool = state.pools.get(POOL_ID).cloned().unwrap();
        let second_pool = state.pools.get("CHAIN_POOL").cloned().unwrap();
        let first_fee = ceil_div_u128(total_amount_in * first_pool.fee_bps as u128, 10_000);
        let first_protocol_fee = first_fee * fee_config.share_bps as u128 / 10_000;
        let first_net_in = total_amount_in - first_fee;
        let first_out = first_pool.reserve1 * first_net_in / (first_pool.reserve0 + first_net_in);
        let second_fee = ceil_div_u128(first_out * second_pool.fee_bps as u128, 10_000);
        let second_protocol_fee = second_fee * fee_config.share_bps as u128 / 10_000;
        let second_net_in = first_out - second_fee;
        let second_out =
            second_pool.reserve1 * second_net_in / (second_pool.reserve0 + second_net_in);

        state.apply_tx(&route_tx(intent), 1, &fee_config).unwrap();

        assert_eq!(state.get_balance(SENDER, ASSET0), 9_900_000);
        assert_eq!(
            state.get_balance(PROTOCOL_FEE_RECIPIENT, ASSET0),
            first_protocol_fee
        );
        assert_eq!(
            state.get_balance(PROTOCOL_FEE_RECIPIENT, ASSET1),
            second_protocol_fee
        );
        assert_eq!(state.get_balance(RECIPIENT, ASSET2), second_out);
        let post_first = state.pools.get(POOL_ID).unwrap();
        assert_eq!(
            post_first.reserve0,
            first_pool.reserve0 + total_amount_in - first_protocol_fee
        );
        assert_eq!(post_first.reserve1, first_pool.reserve1 - first_out);
        let post_second = state.pools.get("CHAIN_POOL").unwrap();
        assert_eq!(
            post_second.reserve0,
            second_pool.reserve0 + first_out - second_protocol_fee
        );
        assert_eq!(post_second.reserve1, second_pool.reserve1 - second_out);
    }

    #[test]
    fn route_exact_out_captures_protocol_fee_in_input_asset() {
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: PROTOCOL_FEE_RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let fee_config = ProtocolFeeConfig {
            share_bps: 5_000,
            recipient_pubkey: Some(PROTOCOL_FEE_RECIPIENT.to_string()),
        };
        let mut intent = default_route_intent(
            "route-fee-exact-out",
            "ROUTE_EXACT_OUT",
            0,
            0,
            10_000,
            100_000,
        );
        bind_route_hash(&mut intent, &state, &fee_config);

        let pool = state.pools.get(POOL_ID).cloned().unwrap();
        let net_in = ceil_div_u128(
            pool.reserve0 * intent.total_amount_out,
            pool.reserve1 - intent.total_amount_out,
        );
        let gross_in = ceil_div_u128(net_in * 10_000, 10_000 - pool.fee_bps as u128);
        let fee_total = gross_in - net_in;
        let protocol_fee = fee_total * fee_config.share_bps as u128 / 10_000;

        state.apply_tx(&route_tx(intent), 1, &fee_config).unwrap();

        assert_eq!(state.get_balance(SENDER, ASSET0), 10_000_000 - gross_in);
        assert_eq!(
            state.get_balance(PROTOCOL_FEE_RECIPIENT, ASSET0),
            protocol_fee
        );
        assert_eq!(state.get_balance(RECIPIENT, ASSET1), 10_000);
        let post_pool = state.pools.get(POOL_ID).unwrap();
        assert_eq!(post_pool.reserve0, pool.reserve0 + gross_in - protocol_fee);
        assert_eq!(post_pool.reserve1, pool.reserve1 - 10_000);
    }

    #[test]
    fn route_audit_catches_wrong_final_asset() {
        // Codex round 3 MEDIUM: last pool asset_out must == route asset_out.
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: "WRONG_ASSET".to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();

        // Pool outputs ASSET1 (correct), but route claims WRONG_ASSET.
        // Credit recipient with WRONG_ASSET so recipient credit check passes,
        // then the boundary asset check fires.
        let mut pool = state.pools.get(POOL_ID).cloned().unwrap();
        pool.reserve0 += 1000;
        pool.reserve1 -= 100;
        state.pools.insert(POOL_ID.to_string(), pool);
        state.sub_balance(SENDER, ASSET0, 1000).unwrap();
        state.add_balance(RECIPIENT, "WRONG_ASSET", 100).unwrap();

        let result = state.audit_route_conservation(RouteConservationAudit {
            pre_state: &pre_state,
            sender: SENDER,
            asset_in: ASSET0,
            sender_debit: 1000,
            recipient: RECIPIENT,
            asset_out: "WRONG_ASSET",
            recipient_credit: 100,
            protocol_fee_recipient: None,
            pool_audits: alloc::vec![RoutePoolAudit {
                pool_id: POOL_ID.to_string(),
                asset_in: ASSET0.to_string(),
                asset_out: ASSET1.to_string(), // pool's actual output
                reserve_in_delta: 1000,
                reserve_out_delta: 100,
                protocol_fee_credit_in: 0,
            }],
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::InvalidInput(
                    "audit: route last pool asset_out != route asset_out"
                ))
            ),
            "route audit must catch wrong final asset: {:?}",
            result
        );
    }

    #[test]
    fn route_audit_catches_pool_asset_pair_mismatch() {
        // Codex round 3 MEDIUM: per-pool asset pair must match actual pool assets.
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: "WRONG_ASSET".to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();

        // Pool has ASSET0/ASSET1, but audit claims ASSET0/WRONG_ASSET.
        // Credit recipient with WRONG_ASSET so recipient credit check passes,
        // then the per-pool asset-pair check fires.
        let mut pool = state.pools.get(POOL_ID).cloned().unwrap();
        pool.reserve0 += 1000;
        pool.reserve1 -= 100;
        state.pools.insert(POOL_ID.to_string(), pool);
        state.sub_balance(SENDER, ASSET0, 1000).unwrap();
        state.add_balance(RECIPIENT, "WRONG_ASSET", 100).unwrap();

        let result = state.audit_route_conservation(RouteConservationAudit {
            pre_state: &pre_state,
            sender: SENDER,
            asset_in: ASSET0,
            sender_debit: 1000,
            recipient: RECIPIENT,
            recipient_credit: 100,
            asset_out: "WRONG_ASSET",
            protocol_fee_recipient: None,
            pool_audits: alloc::vec![RoutePoolAudit {
                pool_id: POOL_ID.to_string(),
                asset_in: ASSET0.to_string(),
                asset_out: "WRONG_ASSET".to_string(), // not in pool's asset pair
                reserve_in_delta: 1000,
                reserve_out_delta: 100,
                protocol_fee_credit_in: 0,
            }],
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::InvalidInput(
                    "audit: route pool asset pair mismatch"
                ))
            ),
            "route audit must catch pool asset pair mismatch: {:?}",
            result
        );
    }

    #[test]
    fn swap_exact_in_conservation_audit_catches_value_destruction() {
        // Mutation-resistance test: if the swap credits LESS output than what
        // leaves the pool reserves, the conservation audit must catch it.
        // This is the exact bug from the overdelivery conservation failure:
        // clamping credit while subtracting full amount from reserves.
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET1.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        // Simulate the bug: subtract full amount_out from reserves but credit less.
        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;

        // Credit only half the output (simulating the clamp bug)
        let buggy_credit = amount_out / 2;

        // Update reserves with FULL amount_out subtracted (the bug)
        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);
        state.add_balance(SENDER, ASSET1, buggy_credit).unwrap();
        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();

        // The audit must catch this: reserve_out_delta != recipient_credit_out
        let result = state.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            asset_in: ASSET0,
            asset_out: ASSET1,
            sender: SENDER,
            recipient: SENDER,
            total_input: amount_in,
            recipient_credit_out: buggy_credit,
            protocol_fee_recipient: None,
            protocol_fee_credit_in: 0,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: output conservation violated"
                ))
            ),
            "conservation audit must catch value destruction"
        );
    }

    #[test]
    fn swap_audit_catches_skipped_sender_debit() {
        // Codex HIGH finding: swap audit must verify sender debit.
        // If sender is not debited but pool deltas match, audit must catch it.
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET1.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;

        // Bug: update pool reserves and credit recipient, but DON'T debit sender
        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);
        state.add_balance(RECIPIENT, ASSET1, amount_out).unwrap();
        // Missing: state.sub_balance(SENDER, ASSET0, amount_in)

        let result = state.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            asset_in: ASSET0,
            asset_out: ASSET1,
            sender: SENDER,
            recipient: RECIPIENT,
            total_input: amount_in,
            recipient_credit_out: amount_out,
            protocol_fee_recipient: None,
            protocol_fee_credit_in: 0,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: sender debit != total_input (net of pf credit)"
                ))
            ),
            "audit must catch skipped sender debit: {:?}",
            result
        );
    }

    #[test]
    fn swap_audit_rejects_nonzero_fee_without_recipient() {
        // Codex round 5 LOW: fail-closed when protocol_fee_credit_in > 0
        // but protocol_fee_recipient is None.
        let snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        let amount_in = 100_000u128;
        let protocol_fee = 500u128;
        let net_in = amount_in - protocol_fee;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;

        // Pool gets amount_in - protocol_fee so input conservation passes:
        // reserve_in_delta + protocol_fee_credit_in == total_input
        let mut next_pool = pool.clone();
        next_pool.reserve0 += net_in;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);

        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();
        state.add_balance(RECIPIENT, ASSET1, amount_out).unwrap();

        let result = state.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            asset_in: ASSET0,
            asset_out: ASSET1,
            sender: SENDER,
            recipient: RECIPIENT,
            total_input: amount_in,
            recipient_credit_out: amount_out,
            protocol_fee_recipient: None,         // no recipient
            protocol_fee_credit_in: protocol_fee, // but nonzero credit claimed
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::InvalidInput(
                    "audit: protocol_fee_credit_in > 0 without recipient"
                ))
            ),
            "audit must reject nonzero fee without recipient: {:?}",
            result
        );
    }

    #[test]
    fn swap_audit_passes_when_protocol_fee_recipient_is_sender() {
        // Codex round 4 MEDIUM: when pf_recipient == sender, the fee credit
        // is embedded in the sender's net balance. The audit must accept
        // a valid swap where sender gets total_input - protocol_fee debited
        // (net), not total_input (gross).
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: SENDER.to_string(),
            asset: ASSET1.to_string(),
            amount: 0,
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;
        let protocol_fee = 500u128;

        // Pool gets amount_in - protocol_fee (since protocol fee is taken from input)
        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in - protocol_fee;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);

        // Sender is debited amount_in, then credited protocol_fee (net = amount_in - protocol_fee)
        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();
        state.add_balance(SENDER, ASSET0, protocol_fee).unwrap();
        state.add_balance(SENDER, ASSET1, amount_out).unwrap();

        let result = state.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            asset_in: ASSET0,
            asset_out: ASSET1,
            sender: SENDER,
            recipient: SENDER,
            total_input: amount_in,
            recipient_credit_out: amount_out,
            protocol_fee_recipient: Some(SENDER), // pf_recipient == sender
            protocol_fee_credit_in: protocol_fee,
        });

        assert!(
            result.is_ok(),
            "audit must accept valid swap when pf_recipient == sender: {:?}",
            result
        );
    }

    #[test]
    fn swap_audit_catches_missing_protocol_fee_with_existing_balance() {
        // Codex MEDIUM finding: protocol-fee credit must be checked as delta,
        // not absolute balance. If recipient already has funds, a missing
        // credit must still be caught.
        let mut snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: RECIPIENT.to_string(),
            asset: ASSET1.to_string(),
            amount: 0,
        });
        // Pre-credit the protocol fee recipient with existing balance
        snapshot.balances.push(DexBalanceEntryV1 {
            pubkey: PROTOCOL_FEE_RECIPIENT.to_string(),
            asset: ASSET0.to_string(),
            amount: 1_000_000, // already has funds
        });
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;
        let protocol_fee = 500u128; // claimed but NOT credited

        // Pool gets amount_in - protocol_fee (since protocol fee is taken from input)
        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in - protocol_fee;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);
        state.add_balance(RECIPIENT, ASSET1, amount_out).unwrap();
        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();
        // Missing: state.add_balance(PROTOCOL_FEE_RECIPIENT, ASSET0, protocol_fee)

        let result = state.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            asset_in: ASSET0,
            asset_out: ASSET1,
            sender: SENDER,
            recipient: RECIPIENT,
            total_input: amount_in,
            recipient_credit_out: amount_out,
            protocol_fee_recipient: Some(PROTOCOL_FEE_RECIPIENT),
            protocol_fee_credit_in: protocol_fee,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: protocol fee delta mismatch"
                ))
            ),
            "audit must catch missing protocol fee even with existing balance: {:?}",
            result
        );
    }

    #[test]
    fn add_liquidity_audit_catches_lp_supply_mismatch() {
        // Codex HIGH finding: LP supply delta must equal lp_minted.
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
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();

        let amount0_used = 1_000u128;
        let amount1_used = 1_000u128;
        let lp_minted = 1_000u128;

        // Bug: lp_supply increases by 999 instead of 1000
        let mut pool = state.pools.get(POOL_ID).cloned().unwrap();
        pool.reserve0 += amount0_used;
        pool.reserve1 += amount1_used;
        pool.lp_supply += lp_minted - 1; // bug
        state.pools.insert(POOL_ID.to_string(), pool);
        state.sub_balance(SENDER, ASSET0, amount0_used).unwrap();
        state.sub_balance(SENDER, ASSET1, amount1_used).unwrap();
        state.add_lp(SENDER, POOL_ID, lp_minted).unwrap();

        let result = state.audit_add_liquidity_conservation(AddLiquidityConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            sender: SENDER,
            lp_recipient: SENDER,
            asset0: ASSET0,
            asset1: ASSET1,
            amount0_used,
            amount1_used,
            lp_minted,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: add_liq lp_supply_delta != lp_minted"
                ))
            ),
            "audit must catch lp_supply mismatch: {:?}",
            result
        );
    }

    #[test]
    fn remove_liquidity_audit_catches_lp_sender_debit_mismatch() {
        // Codex HIGH finding: LP sender debit must equal lp_amount.
        let mut snapshot = empty_snapshot();
        snapshot.pools = alloc::vec![pool_entry(10_000, 10_000)];
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        state.add_lp(SENDER, POOL_ID, 10_000).unwrap();
        let pre_state = state.clone();

        let amount0_out = 1_000u128;
        let amount1_out = 1_000u128;
        let lp_amount = 1_000u128;

        // Bug: burn 999 LP instead of 1000
        let mut pool = state.pools.get(POOL_ID).cloned().unwrap();
        pool.reserve0 -= amount0_out;
        pool.reserve1 -= amount1_out;
        pool.lp_supply -= lp_amount;
        state.pools.insert(POOL_ID.to_string(), pool);
        state.sub_lp(SENDER, POOL_ID, lp_amount - 1).unwrap(); // bug
        state.add_balance(SENDER, ASSET0, amount0_out).unwrap();
        state.add_balance(SENDER, ASSET1, amount1_out).unwrap();

        let result = state.audit_remove_liquidity_conservation(RemoveLiquidityConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            lp_sender: SENDER,
            recipient: SENDER,
            asset0: ASSET0,
            asset1: ASSET1,
            amount0_out,
            amount1_out,
            lp_amount,
        });

        assert!(
            matches!(
                result,
                Err(TransitionError::Arithmetic(
                    "audit: remove_liq lp sender debit != lp_amount"
                ))
            ),
            "audit must catch lp sender debit mismatch: {:?}",
            result
        );
    }

    #[test]
    fn swap_exact_in_conservation_audit_passes_on_correct_flow() {
        // Positive test: when credits match reserve deltas, audit passes.
        let snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let mut state = DexStateV1::from_snapshot(snapshot).unwrap();
        let pre_state = state.clone();
        let pool = state.pools.get(POOL_ID).cloned().unwrap();

        let amount_in = 100_000u128;
        let fee_total = ceil_div_u128(amount_in * pool.fee_bps as u128, 10_000);
        let net_in = amount_in - fee_total;
        let denom = pool.reserve0 + net_in;
        let amount_out = (pool.reserve1 * net_in) / denom;

        let mut next_pool = pool.clone();
        next_pool.reserve0 += amount_in;
        next_pool.reserve1 -= amount_out;
        state.pools.insert(POOL_ID.to_string(), next_pool);
        state.add_balance(SENDER, ASSET1, amount_out).unwrap();
        state.sub_balance(SENDER, ASSET0, amount_in).unwrap();

        let result = state.audit_swap_conservation(SwapConservationAudit {
            pre_state: &pre_state,
            pool_id: POOL_ID,
            asset_in: ASSET0,
            asset_out: ASSET1,
            sender: SENDER,
            recipient: SENDER,
            total_input: amount_in,
            recipient_credit_out: amount_out,
            protocol_fee_recipient: None,
            protocol_fee_credit_in: 0,
        });

        assert!(
            result.is_ok(),
            "conservation audit must pass on correct flow"
        );
    }

    #[test]
    fn protocol_fee_share_bps_positive_without_recipient_rejects_at_execute() {
        let snapshot = sender_balance_snapshot(ASSET0, 10_000_000);
        let input = StateProofInputV1 {
            state_hash: [0u8; 32],
            block_timestamp: 1,
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: snapshot,
            txs: Vec::new(),
            tx_execution_order: Vec::new(),
            pre_nonces: Vec::new(),
            tx_ingress: Vec::new(),
            chain_balances_post: Vec::new(),
            expected_post_app_hash: [0u8; 32],
            protocol_fee_share_bps: 1_000,
            protocol_fee_recipient_pubkey: None,
        };
        assert!(matches!(
            execute_state_proof_input_v1(input),
            Err(TransitionError::InvalidInput(
                "protocol_fee_recipient_pubkey required when share_bps > 0"
            ))
        ));
    }
}
