extern crate alloc;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cmp::Ordering;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    validate_execution_context_hash_v1, RecursiveCompositionInputV1, StateProofInputV1,
    TransitionError, JOURNAL_VERSION,
};

pub const PROOF_TYPE_PERPS_NP: &str = "risc0.zenodex_perps_np_transition.v1";
pub const PROOF_TYPE_ZUSD: &str = "risc0.zenodex_zusd_transition.v1";

const BPS_SCALE_I128: i128 = 10_000;
const E8_I128: i128 = 100_000_000;
const BPS_SCALE_U128: u128 = 10_000;
const E8_U128: u128 = 100_000_000;
const MIN_PERPS_NP_EPOCH_PARTICIPANTS: usize = 4;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ZenoProofInputV1 {
    Spot(StateProofInputV1),
    PerpsNp(PerpsNpTransitionInputV1),
    Zusd(ZusdTransitionInputV1),
    Recursive(RecursiveCompositionInputV1),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OracleBindingV1 {
    pub oracle_bridge_id: String,
    pub oracle_bridge_hash: String,
    pub price_e8: i128,
    pub price_timestamp: u64,
    pub max_staleness_seconds: u64,
    pub observed_at: u64,
    pub pre_price_batch_commitment: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CollateralBindingV1 {
    // Hash-bound external reference only. The perps guest validates shape and
    // commits these fields; a caller must separately verify the source zUSD
    // receipt before treating the collateral movement as proved.
    pub source_proof_type: String,
    pub source_state_hash: String,
    pub balance_root_hash: String,
    pub balance_delta_hash: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsMarketParamsV1 {
    pub initial_margin_bps: u32,
    pub maintenance_margin_bps: u32,
    pub depeg_buffer_bps: u32,
    pub liquidation_penalty_bps: u32,
    pub max_oracle_move_bps: u32,
    pub funding_cap_bps: i32,
    pub max_position_abs: i128,
    pub min_notional_for_bounty_e8: i128,
}

impl Default for PerpsMarketParamsV1 {
    fn default() -> Self {
        Self {
            initial_margin_bps: 1_000,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            liquidation_penalty_bps: 50,
            max_oracle_move_bps: 500,
            funding_cap_bps: 100,
            max_position_abs: 1_000_000,
            min_notional_for_bounty_e8: E8_I128,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsAccountV1 {
    pub pubkey: String,
    pub position_base: i128,
    pub entry_price_e8: i128,
    pub collateral_e8: i128,
    pub funding_paid_cum_e8: i128,
    pub nonce: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsIntentV1 {
    pub pubkey: String,
    pub target_base: i128,
    #[serde(default)]
    pub limit_price_e8: i128,
    #[serde(default)]
    pub min_fill_base: i128,
    #[serde(default = "default_expiry_epoch")]
    pub expiry_epoch: u64,
    pub nonce: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsIntentReceiptV1 {
    pub pubkey: String,
    pub nonce: u64,
    pub status: String,
    pub delta: i128,
    pub reject_code: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsNpSnapshotV1 {
    pub version: u32,
    pub market_id: String,
    #[serde(default = "default_zusd_asset")]
    pub collateral_asset: String,
    pub index_price_e8: i128,
    pub params: PerpsMarketParamsV1,
    #[serde(default)]
    pub accounts: Vec<PerpsAccountV1>,
    #[serde(default)]
    pub pending_intents: Vec<PerpsIntentV1>,
    pub now_epoch: u64,
    pub fee_pool_e8: i128,
    pub insurance_e8: i128,
    pub insurance_ext_e8: i128,
    pub claims_paid_e8: i128,
    pub net_deposited_e8: i128,
}

impl PerpsNpSnapshotV1 {
    pub fn empty() -> Self {
        Self {
            version: 1,
            market_id: String::new(),
            collateral_asset: String::new(),
            index_price_e8: 0,
            params: PerpsMarketParamsV1::default(),
            accounts: Vec::new(),
            pending_intents: Vec::new(),
            now_epoch: 0,
            fee_pool_e8: 0,
            insurance_e8: 0,
            insurance_ext_e8: 0,
            claims_paid_e8: 0,
            net_deposited_e8: 0,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PerpsNpActionV1 {
    InitMarket {
        market_id: String,
        #[serde(default = "default_zusd_asset")]
        collateral_asset: String,
        index_price_e8: i128,
        #[serde(default)]
        params: PerpsMarketParamsV1,
        #[serde(default)]
        insurance_seed_e8: i128,
    },
    DepositCollateral {
        pubkey: String,
        #[serde(default = "default_zusd_asset")]
        asset: String,
        amount_e8: i128,
        nonce: u64,
        #[serde(default)]
        collateral_binding: Option<CollateralBindingV1>,
    },
    WithdrawCollateral {
        pubkey: String,
        #[serde(default = "default_zusd_asset")]
        asset: String,
        amount_e8: i128,
        nonce: u64,
    },
    SubmitIntent {
        intent: PerpsIntentV1,
    },
    RunEpoch {
        oracle: OracleBindingV1,
        clearing_price_e8: i128,
        funding_rate_bps: i32,
        #[serde(default)]
        intents: Vec<PerpsIntentV1>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsNpTransitionInputV1 {
    pub state_hash: [u8; 32],
    pub chain_id: String,
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub pre_state: PerpsNpSnapshotV1,
    pub actions: Vec<PerpsNpActionV1>,
    pub expected_post_app_hash: [u8; 32],
    pub risc0_image_id: [u32; 8],
    pub execution_context_hash: [u8; 32],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsNpTransitionJournalV1 {
    pub journal_version: u32,
    pub proof_type: String,
    pub state_hash: [u8; 32],
    pub chain_id: String,
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub post_app_hash: [u8; 32],
    pub operation_hash: [u8; 32],
    pub state_delta_hash: [u8; 32],
    pub oracle_binding_hash: [u8; 32],
    pub collateral_binding_hash: [u8; 32],
    pub participant_set_hash: [u8; 32],
    pub receipt_root: [u8; 32],
    pub risc0_image_id: [u32; 8],
    pub participant_count: u32,
    pub net_position_base: i128,
    pub total_collateral_e8: i128,
    pub funding_residual_e8: i128,
    pub matched_base_volume: i128,
    pub execution_context_hash: [u8; 32],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZusdVaultEntryV1 {
    pub pubkey: String,
    pub collateral_asset: String,
    pub collateral_amount_e8: u128,
    pub debt_zusd_e8: u128,
    pub nonce: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZusdBalanceEntryV1 {
    pub pubkey: String,
    pub amount_e8: u128,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZusdSnapshotV1 {
    pub version: u32,
    #[serde(default)]
    pub vaults: Vec<ZusdVaultEntryV1>,
    #[serde(default)]
    pub balances: Vec<ZusdBalanceEntryV1>,
    pub total_debt_zusd_e8: u128,
}

impl ZusdSnapshotV1 {
    pub fn empty() -> Self {
        Self {
            version: 1,
            vaults: Vec::new(),
            balances: Vec::new(),
            total_debt_zusd_e8: 0,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ZusdOperationV1 {
    DepositMint {
        pubkey: String,
        collateral_asset: String,
        deposit_amount_e8: u128,
        mint_amount_e8: u128,
        oracle: OracleBindingV1,
        mcr_bps: u32,
        nonce: u64,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZusdTransitionInputV1 {
    pub state_hash: [u8; 32],
    pub chain_id: String,
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub pre_state: ZusdSnapshotV1,
    pub operation: ZusdOperationV1,
    pub expected_post_app_hash: [u8; 32],
    pub risc0_image_id: [u32; 8],
    pub execution_context_hash: [u8; 32],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZusdTransitionJournalV1 {
    pub journal_version: u32,
    pub proof_type: String,
    pub state_hash: [u8; 32],
    pub chain_id: String,
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub post_app_hash: [u8; 32],
    pub operation_hash: [u8; 32],
    pub state_delta_hash: [u8; 32],
    pub oracle_binding_hash: [u8; 32],
    pub zusd_balance_root_hash: [u8; 32],
    pub zusd_vault_root_hash: [u8; 32],
    pub participant_set_hash: [u8; 32],
    pub risc0_image_id: [u32; 8],
    pub minted_zusd_e8: u128,
    pub collateral_value_e8: u128,
    pub mcr_bps: u32,
    pub execution_context_hash: [u8; 32],
}

pub fn execute_perps_np_transition_v1(
    input: PerpsNpTransitionInputV1,
) -> Result<PerpsNpTransitionJournalV1, TransitionError> {
    validate_execution_context_hash_v1(&input.execution_context_hash)?;
    if input.chain_id.is_empty() {
        return Err(TransitionError::InvalidInput("chain_id empty"));
    }
    if input.risc0_image_id.iter().all(|w| *w == 0) {
        return Err(TransitionError::InvalidInput("risc0 image id all-zero"));
    }
    let mut state = PerpsStateV1::from_snapshot(input.pre_state)?;
    let pre_hash = state.canonical_app_hash_sha256();
    if input.pre_app_hash_present && pre_hash != input.pre_app_hash {
        return Err(TransitionError::InvalidInput("pre_app_hash mismatch"));
    }

    let operation_hash = perps_np_operation_hash_v1(&input.actions);
    let mut receipt_roots = Vec::new();
    let mut oracle_hashes = Vec::new();
    let mut collateral_hashes = Vec::new();
    let mut funding_residual = 0i128;
    let mut matched_volume = 0i128;

    for action in input.actions {
        match action {
            PerpsNpActionV1::InitMarket {
                market_id,
                collateral_asset,
                index_price_e8,
                params,
                insurance_seed_e8,
            } => {
                state.init_market(
                    market_id,
                    collateral_asset,
                    index_price_e8,
                    params,
                    insurance_seed_e8,
                )?;
            }
            PerpsNpActionV1::DepositCollateral {
                pubkey,
                asset,
                amount_e8,
                nonce,
                collateral_binding,
            } => {
                let collateral_hash = perps_collateral_deposit_binding_hash_v1(
                    &pubkey,
                    &asset,
                    amount_e8,
                    nonce,
                    collateral_binding.as_ref(),
                )?;
                collateral_hashes.push(collateral_hash);
                state.deposit_collateral(pubkey, asset, amount_e8, nonce, collateral_binding)?;
            }
            PerpsNpActionV1::WithdrawCollateral {
                pubkey,
                asset,
                amount_e8,
                nonce,
            } => state.withdraw_collateral(pubkey, asset, amount_e8, nonce)?,
            PerpsNpActionV1::SubmitIntent { intent } => state.submit_intent(intent)?,
            PerpsNpActionV1::RunEpoch {
                oracle,
                clearing_price_e8,
                funding_rate_bps,
                intents,
            } => {
                validate_oracle_binding(&oracle)?;
                let oracle_hash = oracle_binding_hash_v1(&oracle);
                oracle_hashes.push(oracle_hash);
                let result =
                    state.run_epoch(oracle, clearing_price_e8, funding_rate_bps, intents)?;
                receipt_roots.push(perps_receipts_root_v1(&result.receipts));
                funding_residual = checked_add_i128(
                    funding_residual,
                    result.funding_residual_e8,
                    "funding residual overflow",
                )?;
                matched_volume = checked_add_i128(
                    matched_volume,
                    result.matched_base_volume,
                    "matched volume overflow",
                )?;
            }
        }
        if !state.check_invariants(true).is_empty() {
            return Err(TransitionError::InvalidInput("perps invariant violation"));
        }
    }

    let post = state.canonical_app_hash_sha256();
    if post != input.expected_post_app_hash {
        return Err(TransitionError::InvalidInput("post_app_hash mismatch"));
    }
    let participant_set_hash = state.participant_set_hash();
    Ok(PerpsNpTransitionJournalV1 {
        journal_version: JOURNAL_VERSION,
        proof_type: PROOF_TYPE_PERPS_NP.to_string(),
        state_hash: input.state_hash,
        chain_id: input.chain_id,
        pre_app_hash_present: input.pre_app_hash_present,
        pre_app_hash: input.pre_app_hash,
        post_app_hash: post,
        operation_hash,
        state_delta_hash: state_delta_hash_v1(pre_hash, post),
        oracle_binding_hash: oracle_bindings_hash_v1(&oracle_hashes),
        collateral_binding_hash: collateral_bindings_hash_v1(&collateral_hashes),
        participant_set_hash,
        receipt_root: receipt_roots_hash_v1(&receipt_roots),
        risc0_image_id: input.risc0_image_id,
        participant_count: state.accounts.len() as u32,
        net_position_base: state.net_position(),
        total_collateral_e8: state.total_collateral(),
        funding_residual_e8: funding_residual,
        matched_base_volume: matched_volume,
        execution_context_hash: input.execution_context_hash,
    })
}

pub fn execute_zusd_transition_v1(
    input: ZusdTransitionInputV1,
) -> Result<ZusdTransitionJournalV1, TransitionError> {
    validate_execution_context_hash_v1(&input.execution_context_hash)?;
    if input.chain_id.is_empty() {
        return Err(TransitionError::InvalidInput("chain_id empty"));
    }
    if input.risc0_image_id.iter().all(|w| *w == 0) {
        return Err(TransitionError::InvalidInput("risc0 image id all-zero"));
    }
    let mut state = ZusdStateV1::from_snapshot(input.pre_state)?;
    let pre_hash = state.canonical_app_hash_sha256();
    if input.pre_app_hash_present && pre_hash != input.pre_app_hash {
        return Err(TransitionError::InvalidInput("pre_app_hash mismatch"));
    }
    let operation_hash = zusd_operation_hash_v1(&input.operation);
    let (oracle_hash, minted_zusd_e8, collateral_value_e8, mcr_bps) =
        state.apply_operation(input.operation)?;
    let balance_root = state.balance_root_hash();
    let vault_root = state.vault_root_hash();
    let post = state.canonical_app_hash_sha256();
    if post != input.expected_post_app_hash {
        return Err(TransitionError::InvalidInput("post_app_hash mismatch"));
    }
    Ok(ZusdTransitionJournalV1 {
        journal_version: JOURNAL_VERSION,
        proof_type: PROOF_TYPE_ZUSD.to_string(),
        state_hash: input.state_hash,
        chain_id: input.chain_id,
        pre_app_hash_present: input.pre_app_hash_present,
        pre_app_hash: input.pre_app_hash,
        post_app_hash: post,
        operation_hash,
        state_delta_hash: state_delta_hash_v1(pre_hash, post),
        oracle_binding_hash: oracle_hash,
        zusd_balance_root_hash: balance_root,
        zusd_vault_root_hash: vault_root,
        participant_set_hash: state.participant_set_hash(),
        risc0_image_id: input.risc0_image_id,
        minted_zusd_e8,
        collateral_value_e8,
        mcr_bps,
        execution_context_hash: input.execution_context_hash,
    })
}

#[derive(Clone, Debug)]
struct PerpsStateV1 {
    market_id: String,
    collateral_asset: String,
    index_price_e8: i128,
    params: PerpsMarketParamsV1,
    accounts: BTreeMap<String, PerpsAccountV1>,
    pending_intents: Vec<PerpsIntentV1>,
    now_epoch: u64,
    fee_pool_e8: i128,
    insurance_e8: i128,
    insurance_ext_e8: i128,
    claims_paid_e8: i128,
    net_deposited_e8: i128,
}

#[derive(Clone, Debug)]
struct PerpsMatchResultV1 {
    receipts: Vec<PerpsIntentReceiptV1>,
    funding_residual_e8: i128,
    matched_base_volume: i128,
}

impl PerpsStateV1 {
    fn from_snapshot(snapshot: PerpsNpSnapshotV1) -> Result<Self, TransitionError> {
        if snapshot.version != 1 {
            return Err(TransitionError::Unsupported(
                "unsupported perps snapshot version",
            ));
        }
        validate_perps_params(&snapshot.params)?;
        if !snapshot.market_id.is_empty() && snapshot.index_price_e8 <= 0 {
            return Err(TransitionError::InvalidInput(
                "perps index price must be positive",
            ));
        }
        if !snapshot.market_id.is_empty() && snapshot.collateral_asset.is_empty() {
            return Err(TransitionError::InvalidInput(
                "perps collateral asset empty",
            ));
        }
        for value in [
            snapshot.fee_pool_e8,
            snapshot.insurance_e8,
            snapshot.insurance_ext_e8,
            snapshot.claims_paid_e8,
        ] {
            if value < 0 {
                return Err(TransitionError::InvalidInput("perps ledger field negative"));
            }
        }
        let mut accounts = BTreeMap::new();
        for account in snapshot.accounts {
            if account.pubkey.is_empty() {
                return Err(TransitionError::InvalidInput("perps account pubkey empty"));
            }
            if account.collateral_e8 < 0 {
                return Err(TransitionError::InvalidInput(
                    "perps account collateral negative",
                ));
            }
            if account.position_base == 0 && account.entry_price_e8 != 0 {
                return Err(TransitionError::InvalidInput(
                    "flat account entry price nonzero",
                ));
            }
            if account.position_base != 0 && account.entry_price_e8 != snapshot.index_price_e8 {
                return Err(TransitionError::InvalidInput(
                    "open account entry price mismatch",
                ));
            }
            if abs_i128(account.position_base)? > snapshot.params.max_position_abs {
                return Err(TransitionError::InvalidInput(
                    "perps position exceeds bound",
                ));
            }
            if accounts.insert(account.pubkey.clone(), account).is_some() {
                return Err(TransitionError::InvalidInput("duplicate perps account"));
            }
        }
        let state = Self {
            market_id: snapshot.market_id,
            collateral_asset: snapshot.collateral_asset,
            index_price_e8: snapshot.index_price_e8,
            params: snapshot.params,
            accounts,
            pending_intents: canonical_intents(snapshot.pending_intents),
            now_epoch: snapshot.now_epoch,
            fee_pool_e8: snapshot.fee_pool_e8,
            insurance_e8: snapshot.insurance_e8,
            insurance_ext_e8: snapshot.insurance_ext_e8,
            claims_paid_e8: snapshot.claims_paid_e8,
            net_deposited_e8: snapshot.net_deposited_e8,
        };
        if !state.market_id.is_empty() && !state.check_invariants(true).is_empty() {
            return Err(TransitionError::InvalidInput(
                "perps snapshot invariant violation",
            ));
        }
        Ok(state)
    }

    fn to_snapshot(&self) -> PerpsNpSnapshotV1 {
        PerpsNpSnapshotV1 {
            version: 1,
            market_id: self.market_id.clone(),
            collateral_asset: self.collateral_asset.clone(),
            index_price_e8: self.index_price_e8,
            params: self.params.clone(),
            accounts: self.accounts.values().cloned().collect(),
            pending_intents: canonical_intents(self.pending_intents.clone()),
            now_epoch: self.now_epoch,
            fee_pool_e8: self.fee_pool_e8,
            insurance_e8: self.insurance_e8,
            insurance_ext_e8: self.insurance_ext_e8,
            claims_paid_e8: self.claims_paid_e8,
            net_deposited_e8: self.net_deposited_e8,
        }
    }

    fn canonical_app_hash_sha256(&self) -> [u8; 32] {
        sha256_canonical_perps_np_snapshot_v1(&self.to_snapshot())
    }

    fn init_market(
        &mut self,
        market_id: String,
        collateral_asset: String,
        index_price_e8: i128,
        params: PerpsMarketParamsV1,
        insurance_seed_e8: i128,
    ) -> Result<(), TransitionError> {
        if !self.market_id.is_empty() || !self.accounts.is_empty() || self.index_price_e8 != 0 {
            return Err(TransitionError::InvalidInput(
                "perps market already initialized",
            ));
        }
        if market_id.is_empty() {
            return Err(TransitionError::InvalidInput("perps market_id empty"));
        }
        if collateral_asset.is_empty() {
            return Err(TransitionError::InvalidInput(
                "perps collateral asset empty",
            ));
        }
        if index_price_e8 <= 0 {
            return Err(TransitionError::InvalidInput(
                "perps index price must be positive",
            ));
        }
        if insurance_seed_e8 < 0 {
            return Err(TransitionError::InvalidInput("insurance seed negative"));
        }
        validate_perps_params(&params)?;
        self.market_id = market_id;
        self.collateral_asset = collateral_asset;
        self.index_price_e8 = index_price_e8;
        self.params = params;
        self.insurance_e8 = insurance_seed_e8;
        self.insurance_ext_e8 = insurance_seed_e8;
        Ok(())
    }

    fn require_initialized(&self) -> Result<(), TransitionError> {
        if self.market_id.is_empty() || self.index_price_e8 <= 0 {
            return Err(TransitionError::InvalidInput(
                "perps market not initialized",
            ));
        }
        Ok(())
    }

    fn deposit_collateral(
        &mut self,
        pubkey: String,
        asset: String,
        amount_e8: i128,
        nonce: u64,
        collateral_binding: Option<CollateralBindingV1>,
    ) -> Result<(), TransitionError> {
        self.require_initialized()?;
        if pubkey.is_empty() {
            return Err(TransitionError::InvalidInput("deposit pubkey empty"));
        }
        if amount_e8 <= 0 {
            return Err(TransitionError::InvalidInput("deposit must be positive"));
        }
        if asset != self.collateral_asset {
            return Err(TransitionError::InvalidInput(
                "deposit collateral asset mismatch",
            ));
        }
        if self.collateral_asset == default_zusd_asset() {
            let Some(binding) = collateral_binding.as_ref() else {
                return Err(TransitionError::InvalidInput(
                    "zUSD collateral binding missing",
                ));
            };
            validate_collateral_binding(binding)?;
        }
        let mut account = self
            .accounts
            .get(&pubkey)
            .cloned()
            .unwrap_or_else(|| PerpsAccountV1 {
                pubkey: pubkey.clone(),
                position_base: 0,
                entry_price_e8: 0,
                collateral_e8: 0,
                funding_paid_cum_e8: 0,
                nonce: 0,
            });
        if !is_next_nonce(account.nonce, nonce) {
            return Err(TransitionError::InvalidInput("deposit nonce mismatch"));
        }
        account.collateral_e8 =
            checked_add_i128(account.collateral_e8, amount_e8, "collateral overflow")?;
        account.nonce = nonce;
        self.net_deposited_e8 =
            checked_add_i128(self.net_deposited_e8, amount_e8, "net deposited overflow")?;
        self.accounts.insert(pubkey, account);
        Ok(())
    }

    fn withdraw_collateral(
        &mut self,
        pubkey: String,
        asset: String,
        amount_e8: i128,
        nonce: u64,
    ) -> Result<(), TransitionError> {
        self.require_initialized()?;
        if amount_e8 <= 0 {
            return Err(TransitionError::InvalidInput("withdraw must be positive"));
        }
        if asset != self.collateral_asset {
            return Err(TransitionError::InvalidInput(
                "withdraw collateral asset mismatch",
            ));
        }
        let mut account = self
            .accounts
            .get(&pubkey)
            .cloned()
            .ok_or(TransitionError::InvalidInput("withdraw account missing"))?;
        if !is_next_nonce(account.nonce, nonce) {
            return Err(TransitionError::InvalidInput("withdraw nonce mismatch"));
        }
        if amount_e8 > account.collateral_e8 {
            return Err(TransitionError::InvalidInput("withdraw exceeds collateral"));
        }
        let remaining = account.collateral_e8 - amount_e8;
        if account.position_base != 0 {
            let req = maint_req_e8(
                account.position_base,
                self.index_price_e8,
                self.params.maintenance_margin_bps,
                self.params.depeg_buffer_bps,
            )?;
            if remaining < req {
                return Err(TransitionError::InvalidInput(
                    "withdraw breaches maintenance",
                ));
            }
        }
        account.collateral_e8 = remaining;
        account.nonce = nonce;
        self.net_deposited_e8 =
            checked_sub_i128(self.net_deposited_e8, amount_e8, "net deposited underflow")?;
        self.accounts.insert(pubkey, account);
        Ok(())
    }

    fn submit_intent(&mut self, intent: PerpsIntentV1) -> Result<(), TransitionError> {
        self.require_initialized()?;
        if intent.pubkey.is_empty() {
            return Err(TransitionError::InvalidInput("intent pubkey empty"));
        }
        if !self.accounts.contains_key(&intent.pubkey) {
            return Err(TransitionError::InvalidInput("intent account missing"));
        }
        self.pending_intents.push(intent);
        self.pending_intents = canonical_intents(self.pending_intents.clone());
        Ok(())
    }

    fn run_epoch(
        &mut self,
        oracle: OracleBindingV1,
        clearing_price_e8: i128,
        funding_rate_bps: i32,
        mut intents: Vec<PerpsIntentV1>,
    ) -> Result<PerpsMatchResultV1, TransitionError> {
        self.require_initialized()?;
        if clearing_price_e8 != oracle.price_e8 {
            return Err(TransitionError::InvalidInput(
                "clearing price/oracle price mismatch",
            ));
        }
        let mut batch = self.pending_intents.clone();
        batch.append(&mut intents);
        batch = canonical_intents(batch);
        let participants = participant_set_from_accounts_and_intents(&self.accounts, &batch);
        if participants.len() < MIN_PERPS_NP_EPOCH_PARTICIPANTS {
            return Err(TransitionError::InvalidInput(
                "perps np epoch requires 4 participants",
            ));
        }
        self.pending_intents.clear();
        let (funding_residual_e8, settle_receipts) =
            self.apply_settle(clearing_price_e8, funding_rate_bps)?;
        let match_result = self.apply_match(batch)?;
        self.now_epoch = self
            .now_epoch
            .checked_add(1)
            .ok_or(TransitionError::Arithmetic("epoch overflow"))?;
        let mut receipts = settle_receipts;
        receipts.extend(match_result.receipts);
        Ok(PerpsMatchResultV1 {
            receipts,
            funding_residual_e8,
            matched_base_volume: match_result.matched_base_volume,
        })
    }

    fn apply_settle(
        &mut self,
        clearing_price_e8: i128,
        funding_rate_bps: i32,
    ) -> Result<(i128, Vec<PerpsIntentReceiptV1>), TransitionError> {
        if abs_i128(funding_rate_bps as i128)? > self.params.funding_cap_bps as i128 {
            return Err(TransitionError::InvalidInput("funding rate exceeds cap"));
        }
        let mark = self.index_price_e8;
        let settle_price =
            settle_price_e8(clearing_price_e8, mark, self.params.max_oracle_move_bps)?;
        let mut pnl_map: BTreeMap<String, i128> = BTreeMap::new();
        for account in self.accounts.values_mut() {
            let pnl = checked_mul_i128(
                account.position_base,
                checked_sub_i128(settle_price, mark, "settle diff underflow")?,
                "pnl overflow",
            )?;
            pnl_map.insert(account.pubkey.clone(), pnl);
            account.collateral_e8 =
                checked_add_i128(account.collateral_e8, pnl, "collateral pnl overflow")?;
            account.entry_price_e8 = if account.position_base != 0 {
                settle_price
            } else {
                0
            };
        }

        let (funding_residual, flagged) = self.apply_funding(settle_price, funding_rate_bps)?;
        self.apply_liquidation_adl(settle_price, &pnl_map, flagged)?;
        self.index_price_e8 = settle_price;
        Ok((funding_residual, Vec::new()))
    }

    fn apply_funding(
        &mut self,
        index_e8: i128,
        rate_bps: i32,
    ) -> Result<(i128, BTreeSet<String>), TransitionError> {
        if rate_bps == 0 {
            return Ok((0, BTreeSet::new()));
        }
        let mut payers: Vec<(String, i128)> = Vec::new();
        let mut payees: Vec<(String, i128)> = Vec::new();
        for account in self.accounts.values() {
            if account.position_base == 0 {
                continue;
            }
            let num = funding_num(account.position_base, index_e8, rate_bps)?;
            if is_funding_payer(account.position_base, rate_bps) {
                payers.push((
                    account.pubkey.clone(),
                    ceil_div_nonneg_i128(num, BPS_SCALE_I128)?,
                ));
            } else {
                payees.push((account.pubkey.clone(), num / BPS_SCALE_I128));
            }
        }

        let mut collected = 0i128;
        let mut flagged = BTreeSet::new();
        let mut paid_by: BTreeMap<String, i128> = BTreeMap::new();
        for (pk, owed) in payers {
            let account = self
                .accounts
                .get_mut(&pk)
                .ok_or(TransitionError::InvalidInput("funding payer missing"))?;
            let available = core::cmp::max(account.collateral_e8, 0);
            let pay = core::cmp::min(owed, available);
            account.collateral_e8 =
                checked_sub_i128(account.collateral_e8, pay, "payer underflow")?;
            collected = checked_add_i128(collected, pay, "funding collected overflow")?;
            paid_by.insert(pk.clone(), pay);
            if pay < owed {
                flagged.insert(pk);
            }
        }

        let mut credited: BTreeMap<String, i128> = BTreeMap::new();
        let total_owed = payees.iter().try_fold(0i128, |acc, (_, owed)| {
            checked_add_i128(acc, *owed, "funding owed overflow")
        })?;
        let residual;
        if total_owed <= collected {
            for (pk, owed) in payees {
                let account = self
                    .accounts
                    .get_mut(&pk)
                    .ok_or(TransitionError::InvalidInput("funding payee missing"))?;
                account.collateral_e8 =
                    checked_add_i128(account.collateral_e8, owed, "payee credit overflow")?;
                credited.insert(pk, owed);
            }
            residual = checked_sub_i128(collected, total_owed, "funding residual underflow")?;
            self.fee_pool_e8 = checked_add_i128(self.fee_pool_e8, residual, "fee pool overflow")?;
        } else {
            residual = 0;
            let weights: Vec<(usize, i128)> = payees
                .iter()
                .enumerate()
                .filter_map(|(idx, (_, owed))| if *owed > 0 { Some((idx, *owed)) } else { None })
                .collect();
            let alloc = ration_i128(&weights, collected)?;
            for (idx, (pk, _)) in payees.iter().enumerate() {
                let credit = alloc.get(&idx).copied().unwrap_or(0);
                if credit > 0 {
                    let account = self
                        .accounts
                        .get_mut(pk)
                        .ok_or(TransitionError::InvalidInput("funding payee missing"))?;
                    account.collateral_e8 =
                        checked_add_i128(account.collateral_e8, credit, "payee credit overflow")?;
                    credited.insert(pk.clone(), credit);
                }
            }
        }

        for account in self.accounts.values_mut() {
            let credit = credited.get(&account.pubkey).copied().unwrap_or(0);
            let paid = paid_by.get(&account.pubkey).copied().unwrap_or(0);
            let delta = checked_sub_i128(credit, paid, "funding delta underflow")?;
            account.funding_paid_cum_e8 = checked_sub_i128(
                account.funding_paid_cum_e8,
                delta,
                "funding paid cumulative underflow",
            )?;
        }
        Ok((residual, flagged))
    }

    fn apply_liquidation_adl(
        &mut self,
        settle_price: i128,
        pnl_map: &BTreeMap<String, i128>,
        flagged: BTreeSet<String>,
    ) -> Result<(), TransitionError> {
        let liquidated: Vec<String> = self
            .accounts
            .values()
            .filter(|account| {
                if account.position_base == 0 {
                    return false;
                }
                let req = maint_req_e8(
                    account.position_base,
                    settle_price,
                    self.params.maintenance_margin_bps,
                    self.params.depeg_buffer_bps,
                )
                .unwrap_or(i128::MAX);
                account.collateral_e8 < req || flagged.contains(&account.pubkey)
            })
            .map(|account| account.pubkey.clone())
            .collect();
        if liquidated.is_empty() {
            return Ok(());
        }

        let mut total_penalty = 0i128;
        for pk in &liquidated {
            let account = self
                .accounts
                .get_mut(pk)
                .ok_or(TransitionError::InvalidInput("liquidated account missing"))?;
            let notional = checked_mul_i128(
                abs_i128(account.position_base)?,
                settle_price,
                "notional overflow",
            )?;
            let penalty = liquidation_penalty_e8(
                notional,
                account.collateral_e8,
                self.params.liquidation_penalty_bps,
                self.params.min_notional_for_bounty_e8,
            )?;
            account.collateral_e8 = checked_sub_i128(
                account.collateral_e8,
                penalty,
                "liquidation penalty underflow",
            )?;
            total_penalty = checked_add_i128(total_penalty, penalty, "penalty overflow")?;
        }
        self.fee_pool_e8 =
            checked_add_i128(self.fee_pool_e8, total_penalty, "fee pool penalty overflow")?;

        let bad_debt = liquidated.iter().try_fold(0i128, |acc, pk| {
            let c = self
                .accounts
                .get(pk)
                .ok_or(TransitionError::InvalidInput("liquidated account missing"))?
                .collateral_e8;
            if c < 0 {
                checked_add_i128(acc, -c, "bad debt overflow")
            } else {
                Ok(acc)
            }
        })?;
        let d_ins = core::cmp::min(bad_debt, self.insurance_e8);
        let residual = checked_sub_i128(bad_debt, d_ins, "bad debt residual underflow")?;

        let liquidated_set: BTreeSet<String> = liquidated.iter().cloned().collect();
        let mut winners: Vec<(String, i128)> = self
            .accounts
            .values()
            .filter_map(|account| {
                if liquidated_set.contains(&account.pubkey) || account.collateral_e8 <= 0 {
                    return None;
                }
                let pnl = pnl_map.get(&account.pubkey).copied().unwrap_or(0);
                if pnl <= 0 {
                    return None;
                }
                Some((
                    account.pubkey.clone(),
                    core::cmp::min(pnl, account.collateral_e8),
                ))
            })
            .collect();
        winners.sort_by(|a, b| match b.1.cmp(&a.1) {
            Ordering::Equal => a.0.cmp(&b.0),
            other => other,
        });
        let winner_budget = winners.iter().try_fold(0i128, |acc, (_, amount)| {
            checked_add_i128(acc, *amount, "winner budget overflow")
        })?;
        if residual > winner_budget {
            return Err(TransitionError::InvalidInput("settle insolvent"));
        }
        self.insurance_e8 = checked_sub_i128(self.insurance_e8, d_ins, "insurance underflow")?;
        self.claims_paid_e8 = checked_add_i128(self.claims_paid_e8, d_ins, "claims paid overflow")?;

        for pk in &liquidated {
            let account = self
                .accounts
                .get_mut(pk)
                .ok_or(TransitionError::InvalidInput("liquidated account missing"))?;
            if account.collateral_e8 < 0 {
                account.collateral_e8 = 0;
            }
        }
        if residual > 0 {
            let weights: Vec<(usize, i128)> = winners
                .iter()
                .enumerate()
                .map(|(idx, (_, weight))| (idx, *weight))
                .collect();
            let haircuts = ration_i128(&weights, residual)?;
            for (idx, (pk, _)) in winners.iter().enumerate() {
                let haircut = haircuts.get(&idx).copied().unwrap_or(0);
                if haircut == 0 {
                    continue;
                }
                let account = self
                    .accounts
                    .get_mut(pk)
                    .ok_or(TransitionError::InvalidInput("winner account missing"))?;
                account.collateral_e8 =
                    checked_sub_i128(account.collateral_e8, haircut, "haircut underflow")?;
            }
        }

        let net_liq = liquidated.iter().try_fold(0i128, |acc, pk| {
            let pos = self
                .accounts
                .get(pk)
                .ok_or(TransitionError::InvalidInput("liquidated account missing"))?
                .position_base;
            checked_add_i128(acc, pos, "net liquidation overflow")
        })?;
        for pk in &liquidated {
            let account = self
                .accounts
                .get_mut(pk)
                .ok_or(TransitionError::InvalidInput("liquidated account missing"))?;
            account.position_base = 0;
            account.entry_price_e8 = 0;
        }
        if net_liq != 0 {
            let want_short_side = net_liq > 0;
            let mut candidates: Vec<(String, i128)> = self
                .accounts
                .values()
                .filter(|account| {
                    !liquidated_set.contains(&account.pubkey)
                        && account.position_base != 0
                        && (account.position_base < 0) == want_short_side
                })
                .map(|account| {
                    (
                        account.pubkey.clone(),
                        pnl_map.get(&account.pubkey).copied().unwrap_or(0),
                    )
                })
                .collect();
            candidates.sort_by(|a, b| match b.1.cmp(&a.1) {
                Ordering::Equal => a.0.cmp(&b.0),
                other => other,
            });
            let mut remaining = abs_i128(net_liq)?;
            let step = if net_liq > 0 { 1 } else { -1 };
            for (pk, _) in candidates {
                if remaining == 0 {
                    break;
                }
                let account = self
                    .accounts
                    .get_mut(&pk)
                    .ok_or(TransitionError::InvalidInput("adl account missing"))?;
                let take = core::cmp::min(abs_i128(account.position_base)?, remaining);
                account.position_base =
                    checked_add_i128(account.position_base, step * take, "adl position overflow")?;
                account.entry_price_e8 = if account.position_base != 0 {
                    settle_price
                } else {
                    0
                };
                remaining -= take;
            }
            if remaining != 0 {
                return Err(TransitionError::InvalidInput("adl could not rebalance"));
            }
        }
        Ok(())
    }

    fn apply_match(
        &mut self,
        intents: Vec<PerpsIntentV1>,
    ) -> Result<PerpsMatchOutcomeV1, TransitionError> {
        let result = match_intents_v1(
            &intents,
            &self.accounts,
            self.index_price_e8,
            self.now_epoch,
            &self.params,
        )?;
        for (pk, delta) in &result.deltas {
            let mut account = self
                .accounts
                .get(pk)
                .cloned()
                .ok_or(TransitionError::InvalidInput("matched account missing"))?;
            account.position_base =
                checked_add_i128(account.position_base, *delta, "position overflow")?;
            account.entry_price_e8 = if account.position_base != 0 {
                self.index_price_e8
            } else {
                0
            };
            self.accounts.insert(pk.clone(), account);
        }
        for receipt in &result.receipts {
            if receipt.status != "filled" {
                continue;
            }
            if let Some(account) = self.accounts.get_mut(&receipt.pubkey) {
                if receipt.nonce > account.nonce {
                    account.nonce = receipt.nonce;
                }
            }
        }
        Ok(result)
    }

    fn check_invariants(&self, require_margin: bool) -> Vec<String> {
        let mut violations = Vec::new();
        if self.market_id.is_empty() {
            return violations;
        }
        if self.net_position() != 0 {
            violations.push("net position nonzero".to_string());
        }
        let lhs =
            match checked_add_i128(self.net_deposited_e8, self.insurance_ext_e8, "lhs overflow") {
                Ok(v) => v,
                Err(_) => {
                    violations.push("conservation lhs overflow".to_string());
                    0
                }
            };
        let rhs = match checked_add_i128(self.total_collateral(), self.fee_pool_e8, "rhs overflow")
            .and_then(|v| checked_add_i128(v, self.insurance_e8, "rhs overflow"))
        {
            Ok(v) => v,
            Err(_) => {
                violations.push("conservation rhs overflow".to_string());
                0
            }
        };
        if lhs != rhs {
            violations.push("conservation mismatch".to_string());
        }
        if self.insurance_e8 != self.insurance_ext_e8 - self.claims_paid_e8 {
            violations.push("insurance ledger mismatch".to_string());
        }
        if self.insurance_e8 < 0 || self.fee_pool_e8 < 0 {
            violations.push("system balance negative".to_string());
        }
        for account in self.accounts.values() {
            if account.collateral_e8 < 0 {
                violations.push("account collateral negative".to_string());
            }
            if require_margin && account.position_base != 0 {
                match maint_req_e8(
                    account.position_base,
                    self.index_price_e8,
                    self.params.maintenance_margin_bps,
                    self.params.depeg_buffer_bps,
                ) {
                    Ok(req) if account.collateral_e8 >= req => {}
                    _ => violations.push("account below maintenance".to_string()),
                }
                if account.entry_price_e8 != self.index_price_e8 {
                    violations.push("entry price mismatch".to_string());
                }
            }
            if abs_i128(account.position_base).unwrap_or(i128::MAX) > self.params.max_position_abs {
                violations.push("position bound exceeded".to_string());
            }
        }
        violations
    }

    fn net_position(&self) -> i128 {
        self.accounts
            .values()
            .fold(0i128, |acc, account| acc + account.position_base)
    }

    fn total_collateral(&self) -> i128 {
        self.accounts
            .values()
            .fold(0i128, |acc, account| acc + account.collateral_e8)
    }

    fn participant_set_hash(&self) -> [u8; 32] {
        let participants: Vec<String> = self.accounts.keys().cloned().collect();
        participant_set_hash_v1(&participants)
    }
}

#[derive(Clone, Debug)]
struct PerpsMatchOutcomeV1 {
    deltas: BTreeMap<String, i128>,
    receipts: Vec<PerpsIntentReceiptV1>,
    matched_base_volume: i128,
}

#[derive(Clone, Debug)]
struct ZusdStateV1 {
    vaults: BTreeMap<(String, String), ZusdVaultEntryV1>,
    balances: BTreeMap<String, u128>,
    total_debt_zusd_e8: u128,
}

impl ZusdStateV1 {
    fn from_snapshot(snapshot: ZusdSnapshotV1) -> Result<Self, TransitionError> {
        if snapshot.version != 1 {
            return Err(TransitionError::Unsupported(
                "unsupported zusd snapshot version",
            ));
        }
        let mut vaults = BTreeMap::new();
        for vault in snapshot.vaults {
            if vault.pubkey.is_empty() || vault.collateral_asset.is_empty() {
                return Err(TransitionError::InvalidInput("zusd vault key empty"));
            }
            let key = (vault.pubkey.clone(), vault.collateral_asset.clone());
            if vaults.insert(key, vault).is_some() {
                return Err(TransitionError::InvalidInput("duplicate zusd vault"));
            }
        }
        let mut balances = BTreeMap::new();
        for balance in snapshot.balances {
            if balance.pubkey.is_empty() {
                return Err(TransitionError::InvalidInput("zusd balance pubkey empty"));
            }
            if balances.insert(balance.pubkey, balance.amount_e8).is_some() {
                return Err(TransitionError::InvalidInput("duplicate zusd balance"));
            }
        }
        let total_debt = vaults.values().try_fold(0u128, |acc, vault| {
            checked_add_u128(acc, vault.debt_zusd_e8, "debt overflow")
        })?;
        if total_debt != snapshot.total_debt_zusd_e8 {
            return Err(TransitionError::InvalidInput("zusd total debt mismatch"));
        }
        Ok(Self {
            vaults,
            balances,
            total_debt_zusd_e8: snapshot.total_debt_zusd_e8,
        })
    }

    fn to_snapshot(&self) -> ZusdSnapshotV1 {
        ZusdSnapshotV1 {
            version: 1,
            vaults: self.vaults.values().cloned().collect(),
            balances: self
                .balances
                .iter()
                .filter_map(|(pubkey, amount)| {
                    if *amount == 0 {
                        None
                    } else {
                        Some(ZusdBalanceEntryV1 {
                            pubkey: pubkey.clone(),
                            amount_e8: *amount,
                        })
                    }
                })
                .collect(),
            total_debt_zusd_e8: self.total_debt_zusd_e8,
        }
    }

    fn canonical_app_hash_sha256(&self) -> [u8; 32] {
        sha256_canonical_zusd_snapshot_v1(&self.to_snapshot())
    }

    fn balance_root_hash(&self) -> [u8; 32] {
        zusd_balance_root_hash_v1(&self.to_snapshot())
    }

    fn vault_root_hash(&self) -> [u8; 32] {
        zusd_vault_root_hash_v1(&self.to_snapshot())
    }

    fn apply_operation(
        &mut self,
        operation: ZusdOperationV1,
    ) -> Result<([u8; 32], u128, u128, u32), TransitionError> {
        match operation {
            ZusdOperationV1::DepositMint {
                pubkey,
                collateral_asset,
                deposit_amount_e8,
                mint_amount_e8,
                oracle,
                mcr_bps,
                nonce,
            } => {
                if pubkey.is_empty() || collateral_asset.is_empty() {
                    return Err(TransitionError::InvalidInput("zusd operation key empty"));
                }
                if deposit_amount_e8 == 0 || mint_amount_e8 == 0 {
                    return Err(TransitionError::InvalidInput(
                        "zusd deposit and mint positive",
                    ));
                }
                if mcr_bps <= BPS_SCALE_U128 as u32 {
                    return Err(TransitionError::InvalidInput(
                        "zusd mcr must exceed 10000 bps",
                    ));
                }
                validate_oracle_binding(&oracle)?;
                let oracle_price = u128::try_from(oracle.price_e8)
                    .map_err(|_| TransitionError::InvalidInput("zusd oracle price invalid"))?;
                let key = (pubkey.clone(), collateral_asset.clone());
                let mut vault = self.vaults.get(&key).cloned().unwrap_or(ZusdVaultEntryV1 {
                    pubkey: pubkey.clone(),
                    collateral_asset,
                    collateral_amount_e8: 0,
                    debt_zusd_e8: 0,
                    nonce: 0,
                });
                if !is_next_nonce(vault.nonce, nonce) {
                    return Err(TransitionError::InvalidInput("zusd nonce mismatch"));
                }
                vault.collateral_amount_e8 = checked_add_u128(
                    vault.collateral_amount_e8,
                    deposit_amount_e8,
                    "zusd collateral overflow",
                )?;
                vault.debt_zusd_e8 =
                    checked_add_u128(vault.debt_zusd_e8, mint_amount_e8, "zusd debt overflow")?;
                vault.nonce = nonce;
                let collateral_value_e8 = checked_div_u128(
                    checked_mul_u128(
                        vault.collateral_amount_e8,
                        oracle_price,
                        "zusd value overflow",
                    )?,
                    E8_U128,
                    "zusd value denominator",
                )?;
                if !mcr_ok_u128(
                    vault.collateral_amount_e8,
                    vault.debt_zusd_e8,
                    oracle_price,
                    mcr_bps,
                )? {
                    return Err(TransitionError::InvalidInput("zusd mint violates MCR"));
                }
                self.total_debt_zusd_e8 = checked_add_u128(
                    self.total_debt_zusd_e8,
                    mint_amount_e8,
                    "zusd total debt overflow",
                )?;
                let balance = self.balances.get(&pubkey).copied().unwrap_or(0);
                self.balances.insert(
                    pubkey,
                    checked_add_u128(balance, mint_amount_e8, "zusd balance overflow")?,
                );
                self.vaults.insert(key, vault);
                Ok((
                    oracle_binding_hash_v1(&oracle),
                    mint_amount_e8,
                    collateral_value_e8,
                    mcr_bps,
                ))
            }
        }
    }

    fn participant_set_hash(&self) -> [u8; 32] {
        let participants: Vec<String> = self
            .vaults
            .values()
            .map(|vault| vault.pubkey.clone())
            .collect();
        participant_set_hash_v1(&participants)
    }
}

fn default_expiry_epoch() -> u64 {
    1u64 << 62
}

fn default_zusd_asset() -> String {
    "zUSD".to_string()
}

fn validate_perps_params(params: &PerpsMarketParamsV1) -> Result<(), TransitionError> {
    if params.initial_margin_bps > 100_000
        || params.maintenance_margin_bps > 100_000
        || params.depeg_buffer_bps > 100_000
        || params.liquidation_penalty_bps > 100_000
        || params.max_oracle_move_bps > 100_000
        || params.funding_cap_bps < 0
        || params.max_position_abs <= 0
        || params.min_notional_for_bounty_e8 < 0
    {
        return Err(TransitionError::InvalidInput("perps params out of range"));
    }
    Ok(())
}

fn validate_oracle_binding(oracle: &OracleBindingV1) -> Result<(), TransitionError> {
    if oracle.oracle_bridge_id.is_empty() {
        return Err(TransitionError::InvalidInput("oracle bridge id empty"));
    }
    if oracle.price_e8 <= 0 {
        return Err(TransitionError::InvalidInput(
            "oracle price must be positive",
        ));
    }
    validate_hex32_text(&oracle.oracle_bridge_hash)?;
    validate_hex32_text(&oracle.pre_price_batch_commitment)?;
    if oracle.observed_at < oracle.price_timestamp {
        return Err(TransitionError::InvalidInput(
            "oracle observed before price timestamp",
        ));
    }
    let expires = oracle
        .price_timestamp
        .checked_add(oracle.max_staleness_seconds)
        .ok_or(TransitionError::Arithmetic("oracle staleness overflow"))?;
    if oracle.observed_at > expires {
        return Err(TransitionError::InvalidInput("oracle bridge stale"));
    }
    Ok(())
}

fn validate_collateral_binding(binding: &CollateralBindingV1) -> Result<(), TransitionError> {
    if binding.source_proof_type != PROOF_TYPE_ZUSD {
        return Err(TransitionError::InvalidInput(
            "collateral source proof type mismatch",
        ));
    }
    validate_hex32_text(&binding.source_state_hash)?;
    validate_hex32_text(&binding.balance_root_hash)?;
    validate_hex32_text(&binding.balance_delta_hash)?;
    Ok(())
}

fn settle_price_e8(
    clearing: i128,
    index: i128,
    max_move_bps: u32,
) -> Result<i128, TransitionError> {
    if clearing <= 0 {
        return Err(TransitionError::InvalidInput(
            "clearing price must be positive",
        ));
    }
    if index <= 0 {
        return Ok(clearing);
    }
    let diff = abs_i128(checked_sub_i128(clearing, index, "price diff underflow")?)?;
    let lhs = checked_mul_i128(diff, BPS_SCALE_I128, "price diff overflow")?;
    let rhs = checked_mul_i128(max_move_bps as i128, index, "price cap overflow")?;
    if lhs > rhs {
        let max_delta = ceil_div_nonneg_i128(
            checked_mul_i128(index, max_move_bps as i128, "max delta overflow")?,
            BPS_SCALE_I128,
        )?;
        if clearing > index {
            checked_add_i128(index, max_delta, "settle price overflow")
        } else {
            checked_sub_i128(index, max_delta, "settle price underflow")
        }
    } else {
        Ok(clearing)
    }
}

fn maint_req_e8(
    position_base: i128,
    price_e8: i128,
    maint_bps: u32,
    depeg_bps: u32,
) -> Result<i128, TransitionError> {
    let notional = checked_mul_i128(
        abs_i128(position_base)?,
        price_e8,
        "maintenance notional overflow",
    )?;
    let bps = (maint_bps as i128)
        .checked_add(depeg_bps as i128)
        .ok_or(TransitionError::Arithmetic("maintenance bps overflow"))?;
    ceil_div_nonneg_i128(
        checked_mul_i128(notional, bps, "maintenance requirement overflow")?,
        BPS_SCALE_I128,
    )
}

fn initial_margin_req_e8(
    target_base: i128,
    price_e8: i128,
    initial_margin_bps: u32,
) -> Result<i128, TransitionError> {
    let notional = checked_mul_i128(
        abs_i128(target_base)?,
        price_e8,
        "initial margin notional overflow",
    )?;
    ceil_div_nonneg_i128(
        checked_mul_i128(
            notional,
            initial_margin_bps as i128,
            "initial margin overflow",
        )?,
        BPS_SCALE_I128,
    )
}

fn liquidation_penalty_e8(
    notional_e8: i128,
    collateral_e8: i128,
    penalty_bps: u32,
    min_notional_e8: i128,
) -> Result<i128, TransitionError> {
    if notional_e8 < min_notional_e8 {
        return Ok(0);
    }
    let raw =
        checked_mul_i128(notional_e8, penalty_bps as i128, "penalty overflow")? / BPS_SCALE_I128;
    Ok(core::cmp::min(raw, core::cmp::max(collateral_e8, 0)))
}

fn funding_num(
    position_base: i128,
    index_e8: i128,
    rate_bps: i32,
) -> Result<i128, TransitionError> {
    checked_mul_i128(
        checked_mul_i128(
            abs_i128(position_base)?,
            index_e8,
            "funding notional overflow",
        )?,
        abs_i128(rate_bps as i128)?,
        "funding numerator overflow",
    )
}

fn is_funding_payer(position_base: i128, rate_bps: i32) -> bool {
    if position_base == 0 || rate_bps == 0 {
        return false;
    }
    (position_base > 0) == (rate_bps > 0)
}

fn is_next_nonce(last_nonce: u64, nonce: u64) -> bool {
    // Mirror the live tx-sequence replay layer: gaps are invalid, not merely stale.
    last_nonce
        .checked_add(1)
        .is_some_and(|expected| nonce == expected)
}

fn match_intents_v1(
    intents: &[PerpsIntentV1],
    accounts: &BTreeMap<String, PerpsAccountV1>,
    clearing_price_e8: i128,
    now_epoch: u64,
    params: &PerpsMarketParamsV1,
) -> Result<PerpsMatchOutcomeV1, TransitionError> {
    if clearing_price_e8 <= 0 {
        return Err(TransitionError::InvalidInput(
            "clearing price must be positive",
        ));
    }
    let mut receipts: BTreeMap<(String, u64), PerpsIntentReceiptV1> = BTreeMap::new();
    let mut by_pubkey: BTreeMap<String, Vec<PerpsIntentV1>> = BTreeMap::new();
    for intent in canonical_intents(intents.to_vec()) {
        by_pubkey
            .entry(intent.pubkey.clone())
            .or_default()
            .push(intent);
    }

    let mut survivors: Vec<(PerpsIntentV1, i128)> = Vec::new();
    for (pk, account_intents) in by_pubkey {
        let Some(account) = accounts.get(&pk) else {
            for intent in account_intents {
                receipts.insert(
                    (intent.pubkey.clone(), intent.nonce),
                    rejected_receipt(&intent, "REJ_ACCOUNT"),
                );
            }
            continue;
        };
        let current = account.position_base;
        let collateral = account.collateral_e8;
        let last_nonce = account.nonce;
        let mut nonce_cursor = last_nonce;
        let mut nonce_counts: BTreeMap<u64, u32> = BTreeMap::new();
        for intent in &account_intents {
            *nonce_counts.entry(intent.nonce).or_insert(0) += 1;
        }
        let mut chosen: Option<PerpsIntentV1> = None;
        for intent in account_intents {
            if nonce_counts.get(&intent.nonce).copied().unwrap_or(0) > 1 {
                receipts.insert(
                    (intent.pubkey.clone(), intent.nonce),
                    rejected_receipt(&intent, "REJ_DUP_NONCE"),
                );
                continue;
            }
            // Live admission accepts only contiguous per-account nonce ranges.
            // The matcher then applies orderbook semantics over that range:
            // the highest valid replacement wins, while a missing nonce stays
            // fail-closed instead of being certified as a gap intent.
            if !is_next_nonce(nonce_cursor, intent.nonce) {
                receipts.insert(
                    (intent.pubkey.clone(), intent.nonce),
                    rejected_receipt(&intent, "REJ_BAD_NONCE"),
                );
                continue;
            }
            nonce_cursor = intent.nonce;
            if let Some(code) = validate_perps_intent(
                &intent,
                current,
                collateral,
                clearing_price_e8,
                now_epoch,
                params,
            )? {
                receipts.insert(
                    (intent.pubkey.clone(), intent.nonce),
                    rejected_receipt(&intent, code),
                );
                continue;
            }
            if let Some(prev) = chosen.replace(intent.clone()) {
                receipts.insert(
                    (prev.pubkey.clone(), prev.nonce),
                    rejected_receipt(&prev, "REJ_SUPERSEDED"),
                );
            }
        }
        if let Some(intent) = chosen {
            let desired = checked_sub_i128(intent.target_base, current, "desired delta underflow")?;
            survivors.push((intent, desired));
        }
    }

    let mut revoked = BTreeSet::new();
    let deltas = loop {
        let desired: Vec<i128> = survivors
            .iter()
            .map(|(intent, d)| {
                if revoked.contains(&intent.pubkey) {
                    0
                } else {
                    *d
                }
            })
            .collect();
        let deltas = ration_net_zero_i128(&desired)?;
        let mut changed = false;
        for ((intent, _), delta) in survivors.iter().zip(deltas.iter()) {
            if revoked.contains(&intent.pubkey) {
                continue;
            }
            let abs_delta = abs_i128(*delta)?;
            if abs_delta > 0 && abs_delta < intent.min_fill_base {
                revoked.insert(intent.pubkey.clone());
                changed = true;
            }
        }
        if !changed {
            break deltas;
        }
    };

    let mut out_deltas = BTreeMap::new();
    for ((intent, _), delta) in survivors.iter().zip(deltas.iter()) {
        if revoked.contains(&intent.pubkey) {
            receipts.insert(
                (intent.pubkey.clone(), intent.nonce),
                PerpsIntentReceiptV1 {
                    pubkey: intent.pubkey.clone(),
                    nonce: intent.nonce,
                    status: "filled".to_string(),
                    delta: 0,
                    reject_code: None,
                },
            );
            continue;
        }
        let current = accounts
            .get(&intent.pubkey)
            .map(|a| a.position_base)
            .unwrap_or(0);
        let new_pos = checked_add_i128(current, *delta, "post match position overflow")?;
        let collateral = accounts
            .get(&intent.pubkey)
            .map(|a| a.collateral_e8)
            .unwrap_or(0);
        if increases_risk(current, new_pos)
            && collateral
                < initial_margin_req_e8(new_pos, clearing_price_e8, params.initial_margin_bps)?
        {
            receipts.insert(
                (intent.pubkey.clone(), intent.nonce),
                rejected_receipt(intent, "REJ_INVARIANT"),
            );
            continue;
        }
        receipts.insert(
            (intent.pubkey.clone(), intent.nonce),
            PerpsIntentReceiptV1 {
                pubkey: intent.pubkey.clone(),
                nonce: intent.nonce,
                status: "filled".to_string(),
                delta: *delta,
                reject_code: None,
            },
        );
        if *delta != 0 {
            out_deltas.insert(intent.pubkey.clone(), *delta);
        }
    }

    let net = out_deltas.values().try_fold(0i128, |acc, delta| {
        checked_add_i128(acc, *delta, "match net overflow")
    })?;
    if net != 0 {
        return Err(TransitionError::InvalidInput(
            "matcher produced nonzero net",
        ));
    }
    let matched_base_volume = out_deltas
        .values()
        .filter(|delta| **delta > 0)
        .try_fold(0i128, |acc, delta| {
            checked_add_i128(acc, *delta, "matched volume overflow")
        })?;

    Ok(PerpsMatchOutcomeV1 {
        deltas: out_deltas,
        receipts: receipts.values().cloned().collect(),
        matched_base_volume,
    })
}

fn validate_perps_intent(
    intent: &PerpsIntentV1,
    current: i128,
    collateral: i128,
    price_e8: i128,
    now_epoch: u64,
    params: &PerpsMarketParamsV1,
) -> Result<Option<&'static str>, TransitionError> {
    if intent.pubkey.is_empty() {
        return Ok(Some("REJ_PUBKEY"));
    }
    if intent.expiry_epoch < now_epoch {
        return Ok(Some("REJ_EXPIRED"));
    }
    if abs_i128(intent.target_base)? > params.max_position_abs {
        return Ok(Some("REJ_POS_BOUND"));
    }
    checked_mul_i128(
        abs_i128(intent.target_base)?,
        price_e8,
        "intent notional overflow",
    )?;
    if increases_risk(current, intent.target_base)
        && collateral
            < initial_margin_req_e8(intent.target_base, price_e8, params.initial_margin_bps)?
    {
        return Ok(Some("REJ_MARGIN"));
    }
    let desired = checked_sub_i128(intent.target_base, current, "desired delta underflow")?;
    if intent.limit_price_e8 != 0 && desired != 0 {
        if desired > 0 && price_e8 > intent.limit_price_e8 {
            return Ok(Some("REJ_PRICE"));
        }
        if desired < 0 && price_e8 < intent.limit_price_e8 {
            return Ok(Some("REJ_PRICE"));
        }
    }
    Ok(None)
}

fn rejected_receipt(intent: &PerpsIntentV1, code: &'static str) -> PerpsIntentReceiptV1 {
    PerpsIntentReceiptV1 {
        pubkey: intent.pubkey.clone(),
        nonce: intent.nonce,
        status: "rejected".to_string(),
        delta: 0,
        reject_code: Some(code.to_string()),
    }
}

fn increases_risk(current: i128, target: i128) -> bool {
    current.saturating_mul(target) < 0
        || abs_i128(target).unwrap_or(i128::MAX) > abs_i128(current).unwrap_or(0)
}

fn canonical_intents(mut intents: Vec<PerpsIntentV1>) -> Vec<PerpsIntentV1> {
    intents.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
        Ordering::Equal => a.nonce.cmp(&b.nonce),
        other => other,
    });
    intents
}

fn participant_set_from_accounts_and_intents(
    accounts: &BTreeMap<String, PerpsAccountV1>,
    intents: &[PerpsIntentV1],
) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = accounts.keys().cloned().collect();
    for intent in intents {
        out.insert(intent.pubkey.clone());
    }
    out
}

fn ration_net_zero_i128(desired: &[i128]) -> Result<Vec<i128>, TransitionError> {
    let buys: Vec<(usize, i128)> = desired
        .iter()
        .enumerate()
        .filter_map(|(idx, d)| if *d > 0 { Some((idx, *d)) } else { None })
        .collect();
    let sells: Vec<(usize, i128)> = desired
        .iter()
        .enumerate()
        .filter_map(|(idx, d)| if *d < 0 { Some((idx, -*d)) } else { None })
        .collect();
    let buy_total = buys.iter().try_fold(0i128, |acc, (_, w)| {
        checked_add_i128(acc, *w, "buy total overflow")
    })?;
    let sell_total = sells.iter().try_fold(0i128, |acc, (_, w)| {
        checked_add_i128(acc, *w, "sell total overflow")
    })?;
    let volume = core::cmp::min(buy_total, sell_total);
    let mut out = alloc::vec![0i128; desired.len()];
    if volume == 0 {
        return Ok(out);
    }
    for (idx, alloc) in ration_i128(&buys, volume)? {
        out[idx] = alloc;
    }
    for (idx, alloc) in ration_i128(&sells, volume)? {
        out[idx] = -alloc;
    }
    Ok(out)
}

fn ration_i128(
    weights: &[(usize, i128)],
    volume: i128,
) -> Result<BTreeMap<usize, i128>, TransitionError> {
    if volume < 0 {
        return Err(TransitionError::InvalidInput("ration volume negative"));
    }
    let total = weights.iter().try_fold(0i128, |acc, (_, w)| {
        if *w <= 0 {
            return Err(TransitionError::InvalidInput("ration weight nonpositive"));
        }
        checked_add_i128(acc, *w, "ration total overflow")
    })?;
    if total == 0 {
        return Ok(BTreeMap::new());
    }
    if volume > total {
        return Err(TransitionError::InvalidInput(
            "ration volume exceeds weights",
        ));
    }
    let mut base = BTreeMap::new();
    let mut remainders: Vec<(i128, usize)> = Vec::new();
    let mut allocated = 0i128;
    for (idx, w) in weights {
        let prod = checked_mul_i128(*w, volume, "ration product overflow")?;
        let b = prod / total;
        base.insert(*idx, b);
        allocated = checked_add_i128(allocated, b, "ration allocated overflow")?;
        remainders.push((prod - b * total, *idx));
    }
    let leftover = volume - allocated;
    remainders.sort_by(|a, b| match b.0.cmp(&a.0) {
        Ordering::Equal => a.1.cmp(&b.1),
        other => other,
    });
    let leftover_usize = usize::try_from(leftover)
        .map_err(|_| TransitionError::Arithmetic("ration leftover too large"))?;
    for (_, idx) in remainders.into_iter().take(leftover_usize) {
        let current = base.get(&idx).copied().unwrap_or(0);
        base.insert(idx, current + 1);
    }
    Ok(base)
}

fn mcr_ok_u128(
    collateral_e8: u128,
    debt_e8: u128,
    price_e8: u128,
    mcr_bps: u32,
) -> Result<bool, TransitionError> {
    if debt_e8 == 0 {
        return Ok(true);
    }
    let lhs = checked_mul_u128(
        checked_mul_u128(collateral_e8, price_e8, "mcr lhs overflow")?,
        BPS_SCALE_U128,
        "mcr lhs overflow",
    )?;
    let rhs = checked_mul_u128(
        checked_mul_u128(debt_e8, mcr_bps as u128, "mcr rhs overflow")?,
        E8_U128,
        "mcr rhs overflow",
    )?;
    Ok(lhs >= rhs)
}

fn checked_add_i128(a: i128, b: i128, msg: &'static str) -> Result<i128, TransitionError> {
    a.checked_add(b).ok_or(TransitionError::Arithmetic(msg))
}

fn checked_sub_i128(a: i128, b: i128, msg: &'static str) -> Result<i128, TransitionError> {
    a.checked_sub(b).ok_or(TransitionError::Arithmetic(msg))
}

fn checked_mul_i128(a: i128, b: i128, msg: &'static str) -> Result<i128, TransitionError> {
    a.checked_mul(b).ok_or(TransitionError::Arithmetic(msg))
}

fn checked_add_u128(a: u128, b: u128, msg: &'static str) -> Result<u128, TransitionError> {
    a.checked_add(b).ok_or(TransitionError::Arithmetic(msg))
}

fn checked_mul_u128(a: u128, b: u128, msg: &'static str) -> Result<u128, TransitionError> {
    a.checked_mul(b).ok_or(TransitionError::Arithmetic(msg))
}

fn checked_div_u128(a: u128, b: u128, msg: &'static str) -> Result<u128, TransitionError> {
    if b == 0 {
        return Err(TransitionError::Arithmetic(msg));
    }
    Ok(a / b)
}

fn abs_i128(v: i128) -> Result<i128, TransitionError> {
    v.checked_abs()
        .ok_or(TransitionError::Arithmetic("i128 abs overflow"))
}

fn ceil_div_nonneg_i128(numer: i128, denom: i128) -> Result<i128, TransitionError> {
    if numer < 0 || denom <= 0 {
        return Err(TransitionError::Arithmetic("invalid ceil_div operands"));
    }
    let q = numer / denom;
    let r = numer % denom;
    if r == 0 {
        Ok(q)
    } else {
        checked_add_i128(q, 1, "ceil_div overflow")
    }
}

fn validate_hex32_text(value: &str) -> Result<(), TransitionError> {
    let raw = value.strip_prefix("0x").unwrap_or(value);
    if raw.len() != 64 || !raw.as_bytes().iter().all(|b| b.is_ascii_hexdigit()) {
        return Err(TransitionError::InvalidInput("expected 32-byte hex text"));
    }
    Ok(())
}

fn normalized_hex32_text(value: &str) -> String {
    let raw = value.strip_prefix("0x").unwrap_or(value);
    raw.to_ascii_lowercase()
}

pub fn sha256_canonical_perps_np_snapshot_v1(snapshot: &PerpsNpSnapshotV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.perps_np.snapshot.v1:");
    write_u32(&mut hasher, snapshot.version);
    write_str(&mut hasher, &snapshot.market_id);
    write_str(&mut hasher, &snapshot.collateral_asset);
    write_i128(&mut hasher, snapshot.index_price_e8);
    hash_perps_params(&mut hasher, &snapshot.params);
    let mut accounts = snapshot.accounts.clone();
    accounts.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));
    write_u32(&mut hasher, accounts.len() as u32);
    for account in accounts {
        hash_perps_account(&mut hasher, &account);
    }
    let pending = canonical_intents(snapshot.pending_intents.clone());
    write_u32(&mut hasher, pending.len() as u32);
    for intent in pending {
        hash_perps_intent(&mut hasher, &intent);
    }
    write_u64(&mut hasher, snapshot.now_epoch);
    write_i128(&mut hasher, snapshot.fee_pool_e8);
    write_i128(&mut hasher, snapshot.insurance_e8);
    write_i128(&mut hasher, snapshot.insurance_ext_e8);
    write_i128(&mut hasher, snapshot.claims_paid_e8);
    write_i128(&mut hasher, snapshot.net_deposited_e8);
    hasher.finalize().into()
}

pub fn sha256_canonical_zusd_snapshot_v1(snapshot: &ZusdSnapshotV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.snapshot.v1:");
    write_u32(&mut hasher, snapshot.version);
    let mut vaults = snapshot.vaults.clone();
    vaults.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
        Ordering::Equal => a.collateral_asset.cmp(&b.collateral_asset),
        other => other,
    });
    write_u32(&mut hasher, vaults.len() as u32);
    for vault in vaults {
        write_str(&mut hasher, &vault.pubkey);
        write_str(&mut hasher, &vault.collateral_asset);
        write_u128(&mut hasher, vault.collateral_amount_e8);
        write_u128(&mut hasher, vault.debt_zusd_e8);
        write_u64(&mut hasher, vault.nonce);
    }
    let mut balances = snapshot.balances.clone();
    balances.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));
    write_u32(&mut hasher, balances.len() as u32);
    for balance in balances {
        write_str(&mut hasher, &balance.pubkey);
        write_u128(&mut hasher, balance.amount_e8);
    }
    write_u128(&mut hasher, snapshot.total_debt_zusd_e8);
    hasher.finalize().into()
}

pub fn zusd_balance_root_hash_v1(snapshot: &ZusdSnapshotV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.balance_root.v1:");
    let mut balances = snapshot.balances.clone();
    balances.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));
    write_u32(&mut hasher, balances.len() as u32);
    for balance in balances {
        write_str(&mut hasher, &balance.pubkey);
        write_u128(&mut hasher, balance.amount_e8);
    }
    hasher.finalize().into()
}

pub fn zusd_vault_root_hash_v1(snapshot: &ZusdSnapshotV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.vault_root.v1:");
    let mut vaults = snapshot.vaults.clone();
    vaults.sort_by(|a, b| match a.pubkey.cmp(&b.pubkey) {
        Ordering::Equal => a.collateral_asset.cmp(&b.collateral_asset),
        other => other,
    });
    write_u32(&mut hasher, vaults.len() as u32);
    for vault in vaults {
        write_str(&mut hasher, &vault.pubkey);
        write_str(&mut hasher, &vault.collateral_asset);
        write_u128(&mut hasher, vault.collateral_amount_e8);
        write_u128(&mut hasher, vault.debt_zusd_e8);
        write_u64(&mut hasher, vault.nonce);
    }
    hasher.finalize().into()
}

pub fn perps_np_operation_hash_v1(actions: &[PerpsNpActionV1]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.perps_np.operation.v1:");
    write_u32(&mut hasher, actions.len() as u32);
    for action in actions {
        match action {
            PerpsNpActionV1::InitMarket {
                market_id,
                collateral_asset,
                index_price_e8,
                params,
                insurance_seed_e8,
            } => {
                hasher.update([0u8]);
                write_str(&mut hasher, market_id);
                write_str(&mut hasher, collateral_asset);
                write_i128(&mut hasher, *index_price_e8);
                hash_perps_params(&mut hasher, params);
                write_i128(&mut hasher, *insurance_seed_e8);
            }
            PerpsNpActionV1::DepositCollateral {
                pubkey,
                asset,
                amount_e8,
                nonce,
                collateral_binding,
            } => {
                hasher.update([1u8]);
                write_str(&mut hasher, pubkey);
                write_str(&mut hasher, asset);
                write_i128(&mut hasher, *amount_e8);
                write_u64(&mut hasher, *nonce);
                hash_optional_collateral_binding(&mut hasher, collateral_binding.as_ref());
            }
            PerpsNpActionV1::WithdrawCollateral {
                pubkey,
                asset,
                amount_e8,
                nonce,
            } => {
                hasher.update([2u8]);
                write_str(&mut hasher, pubkey);
                write_str(&mut hasher, asset);
                write_i128(&mut hasher, *amount_e8);
                write_u64(&mut hasher, *nonce);
            }
            PerpsNpActionV1::SubmitIntent { intent } => {
                hasher.update([3u8]);
                hash_perps_intent(&mut hasher, intent);
            }
            PerpsNpActionV1::RunEpoch {
                oracle,
                clearing_price_e8,
                funding_rate_bps,
                intents,
            } => {
                hasher.update([4u8]);
                hash_oracle_binding(&mut hasher, oracle);
                write_i128(&mut hasher, *clearing_price_e8);
                write_i32(&mut hasher, *funding_rate_bps);
                let canonical = canonical_intents(intents.clone());
                write_u32(&mut hasher, canonical.len() as u32);
                for intent in canonical {
                    hash_perps_intent(&mut hasher, &intent);
                }
            }
        }
    }
    hasher.finalize().into()
}

pub fn perps_np_oracle_bindings_hash_v1(
    actions: &[PerpsNpActionV1],
) -> Result<[u8; 32], TransitionError> {
    let mut hashes = Vec::new();
    for action in actions {
        if let PerpsNpActionV1::RunEpoch { oracle, .. } = action {
            validate_oracle_binding(oracle)?;
            hashes.push(oracle_binding_hash_v1(oracle));
        }
    }
    Ok(oracle_bindings_hash_v1(&hashes))
}

pub fn perps_np_collateral_bindings_hash_v1(
    actions: &[PerpsNpActionV1],
) -> Result<[u8; 32], TransitionError> {
    let mut hashes = Vec::new();
    for action in actions {
        if let PerpsNpActionV1::DepositCollateral {
            pubkey,
            asset,
            amount_e8,
            nonce,
            collateral_binding,
        } = action
        {
            hashes.push(perps_collateral_deposit_binding_hash_v1(
                pubkey,
                asset,
                *amount_e8,
                *nonce,
                collateral_binding.as_ref(),
            )?);
        }
    }
    Ok(collateral_bindings_hash_v1(&hashes))
}

pub fn zusd_operation_hash_v1(operation: &ZusdOperationV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.operation.v1:");
    match operation {
        ZusdOperationV1::DepositMint {
            pubkey,
            collateral_asset,
            deposit_amount_e8,
            mint_amount_e8,
            oracle,
            mcr_bps,
            nonce,
        } => {
            hasher.update([0u8]);
            write_str(&mut hasher, pubkey);
            write_str(&mut hasher, collateral_asset);
            write_u128(&mut hasher, *deposit_amount_e8);
            write_u128(&mut hasher, *mint_amount_e8);
            hash_oracle_binding(&mut hasher, oracle);
            write_u32(&mut hasher, *mcr_bps);
            write_u64(&mut hasher, *nonce);
        }
    }
    hasher.finalize().into()
}

pub fn zusd_operation_oracle_binding_hash_v1(
    operation: &ZusdOperationV1,
) -> Result<[u8; 32], TransitionError> {
    match operation {
        ZusdOperationV1::DepositMint { oracle, .. } => {
            validate_oracle_binding(oracle)?;
            Ok(oracle_binding_hash_v1(oracle))
        }
    }
}

pub fn oracle_binding_hash_v1(oracle: &OracleBindingV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.oracle_binding.v1:");
    hash_oracle_binding(&mut hasher, oracle);
    hasher.finalize().into()
}

fn perps_collateral_deposit_binding_hash_v1(
    pubkey: &str,
    asset: &str,
    amount_e8: i128,
    nonce: u64,
    binding: Option<&CollateralBindingV1>,
) -> Result<[u8; 32], TransitionError> {
    if asset == default_zusd_asset() && binding.is_none() {
        return Err(TransitionError::InvalidInput(
            "zUSD collateral binding missing",
        ));
    }
    if let Some(binding) = binding {
        validate_collateral_binding(binding)?;
    }
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.perps_np.collateral_deposit_binding.v1:");
    write_str(&mut hasher, pubkey);
    write_str(&mut hasher, asset);
    write_i128(&mut hasher, amount_e8);
    write_u64(&mut hasher, nonce);
    hash_optional_collateral_binding(&mut hasher, binding);
    Ok(hasher.finalize().into())
}

fn collateral_bindings_hash_v1(hashes: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.perps_np.collateral_bindings.v1:");
    write_u32(&mut hasher, hashes.len() as u32);
    for hash in hashes {
        hasher.update(hash);
    }
    hasher.finalize().into()
}

fn oracle_bindings_hash_v1(hashes: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.oracle_bindings.v1:");
    write_u32(&mut hasher, hashes.len() as u32);
    for hash in hashes {
        hasher.update(hash);
    }
    hasher.finalize().into()
}

fn participant_set_hash_v1(participants: &[String]) -> [u8; 32] {
    let mut sorted = participants.to_vec();
    sorted.sort();
    sorted.dedup();
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.participant_set.v1:");
    write_u32(&mut hasher, sorted.len() as u32);
    for pk in sorted {
        write_str(&mut hasher, &pk);
    }
    hasher.finalize().into()
}

fn perps_receipts_root_v1(receipts: &[PerpsIntentReceiptV1]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.perps_np.receipts.v1:");
    write_u32(&mut hasher, receipts.len() as u32);
    for receipt in receipts {
        write_str(&mut hasher, &receipt.pubkey);
        write_u64(&mut hasher, receipt.nonce);
        write_str(&mut hasher, &receipt.status);
        write_i128(&mut hasher, receipt.delta);
        match receipt.reject_code.as_deref() {
            None => hasher.update([0u8]),
            Some(code) => {
                hasher.update([1u8]);
                write_str(&mut hasher, code);
            }
        }
    }
    hasher.finalize().into()
}

fn receipt_roots_hash_v1(roots: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.receipt_roots.v1:");
    write_u32(&mut hasher, roots.len() as u32);
    for root in roots {
        hasher.update(root);
    }
    hasher.finalize().into()
}

fn state_delta_hash_v1(pre: [u8; 32], post: [u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.state_delta.v1:");
    hasher.update(pre);
    hasher.update(post);
    hasher.finalize().into()
}

fn hash_perps_params(hasher: &mut Sha256, params: &PerpsMarketParamsV1) {
    write_u32(hasher, params.initial_margin_bps);
    write_u32(hasher, params.maintenance_margin_bps);
    write_u32(hasher, params.depeg_buffer_bps);
    write_u32(hasher, params.liquidation_penalty_bps);
    write_u32(hasher, params.max_oracle_move_bps);
    write_i32(hasher, params.funding_cap_bps);
    write_i128(hasher, params.max_position_abs);
    write_i128(hasher, params.min_notional_for_bounty_e8);
}

fn hash_perps_account(hasher: &mut Sha256, account: &PerpsAccountV1) {
    write_str(hasher, &account.pubkey);
    write_i128(hasher, account.position_base);
    write_i128(hasher, account.entry_price_e8);
    write_i128(hasher, account.collateral_e8);
    write_i128(hasher, account.funding_paid_cum_e8);
    write_u64(hasher, account.nonce);
}

fn hash_perps_intent(hasher: &mut Sha256, intent: &PerpsIntentV1) {
    write_str(hasher, &intent.pubkey);
    write_i128(hasher, intent.target_base);
    write_i128(hasher, intent.limit_price_e8);
    write_i128(hasher, intent.min_fill_base);
    write_u64(hasher, intent.expiry_epoch);
    write_u64(hasher, intent.nonce);
}

fn hash_oracle_binding(hasher: &mut Sha256, oracle: &OracleBindingV1) {
    write_str(hasher, &oracle.oracle_bridge_id);
    write_str(hasher, &normalized_hex32_text(&oracle.oracle_bridge_hash));
    write_i128(hasher, oracle.price_e8);
    write_u64(hasher, oracle.price_timestamp);
    write_u64(hasher, oracle.max_staleness_seconds);
    write_u64(hasher, oracle.observed_at);
    write_str(
        hasher,
        &normalized_hex32_text(&oracle.pre_price_batch_commitment),
    );
}

fn hash_optional_collateral_binding(hasher: &mut Sha256, binding: Option<&CollateralBindingV1>) {
    match binding {
        None => hasher.update([0u8]),
        Some(binding) => {
            hasher.update([1u8]);
            write_str(hasher, &binding.source_proof_type);
            write_str(hasher, &normalized_hex32_text(&binding.source_state_hash));
            write_str(hasher, &normalized_hex32_text(&binding.balance_root_hash));
            write_str(hasher, &normalized_hex32_text(&binding.balance_delta_hash));
        }
    }
}

fn write_u32(hasher: &mut Sha256, n: u32) {
    hasher.update(n.to_be_bytes());
}

fn write_i32(hasher: &mut Sha256, n: i32) {
    hasher.update(n.to_be_bytes());
}

fn write_u64(hasher: &mut Sha256, n: u64) {
    hasher.update(n.to_be_bytes());
}

fn write_u128(hasher: &mut Sha256, n: u128) {
    hasher.update(n.to_be_bytes());
}

fn write_i128(hasher: &mut Sha256, n: i128) {
    hasher.update(n.to_be_bytes());
}

fn write_str(hasher: &mut Sha256, s: &str) {
    let bytes = s.as_bytes();
    write_u32(hasher, bytes.len() as u32);
    hasher.update(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    const H: [u8; 32] = [7u8; 32];
    const IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

    fn oracle(price_e8: i128) -> OracleBindingV1 {
        OracleBindingV1 {
            oracle_bridge_id: "dev-oracle".to_string(),
            oracle_bridge_hash: "11".repeat(32),
            price_e8,
            price_timestamp: 10,
            max_staleness_seconds: 5,
            observed_at: 12,
            pre_price_batch_commitment: "22".repeat(32),
        }
    }

    fn collateral_binding(seed: u8) -> CollateralBindingV1 {
        CollateralBindingV1 {
            source_proof_type: PROOF_TYPE_ZUSD.to_string(),
            source_state_hash: format!("{seed:02x}").repeat(32),
            balance_root_hash: format!("{:02x}", seed.saturating_add(1)).repeat(32),
            balance_delta_hash: format!("{:02x}", seed.saturating_add(2)).repeat(32),
        }
    }

    fn init_action() -> PerpsNpActionV1 {
        PerpsNpActionV1::InitMarket {
            market_id: "BTC-PERP".to_string(),
            collateral_asset: default_zusd_asset(),
            index_price_e8: 100 * E8_I128,
            params: PerpsMarketParamsV1::default(),
            insurance_seed_e8: 1_000_000_000,
        }
    }

    fn intent(pubkey: &str, target_base: i128, nonce: u64) -> PerpsIntentV1 {
        PerpsIntentV1 {
            pubkey: pubkey.to_string(),
            target_base,
            limit_price_e8: 0,
            min_fill_base: 0,
            expiry_epoch: 10,
            nonce,
        }
    }

    fn initialized_four_wallet_state() -> PerpsStateV1 {
        let mut state = PerpsStateV1::from_snapshot(PerpsNpSnapshotV1::empty()).unwrap();
        state
            .init_market(
                "BTC-PERP".to_string(),
                default_zusd_asset(),
                100 * E8_I128,
                PerpsMarketParamsV1::default(),
                1_000_000_000,
            )
            .unwrap();
        for (idx, wallet) in ["wallet-a", "wallet-b", "wallet-c", "wallet-d"]
            .iter()
            .enumerate()
        {
            state
                .deposit_collateral(
                    (*wallet).to_string(),
                    default_zusd_asset(),
                    2_000 * E8_I128,
                    1,
                    Some(collateral_binding((idx + 1) as u8)),
                )
                .unwrap();
        }
        state
    }

    #[test]
    fn perps_np_transition_runs_settle_before_match_for_five_wallets() {
        let wallets = ["w1", "w2", "w3", "w4", "w5"];
        let mut actions = alloc::vec![init_action()];
        for (i, wallet) in wallets.iter().enumerate() {
            actions.push(PerpsNpActionV1::DepositCollateral {
                pubkey: wallet.to_string(),
                asset: default_zusd_asset(),
                amount_e8: 2_000 * E8_I128,
                nonce: 1,
                collateral_binding: Some(collateral_binding((i + 1) as u8)),
            });
            actions.push(PerpsNpActionV1::SubmitIntent {
                intent: PerpsIntentV1 {
                    pubkey: wallet.to_string(),
                    target_base: match i {
                        0 => 3,
                        1 => 2,
                        2 => -2,
                        3 => -2,
                        _ => -1,
                    },
                    limit_price_e8: 0,
                    min_fill_base: 0,
                    expiry_epoch: 10,
                    nonce: 2,
                },
            });
        }
        actions.push(PerpsNpActionV1::RunEpoch {
            oracle: oracle(101 * E8_I128),
            clearing_price_e8: 101 * E8_I128,
            funding_rate_bps: 1,
            intents: Vec::new(),
        });
        let mut state = PerpsStateV1::from_snapshot(PerpsNpSnapshotV1::empty()).unwrap();
        for action in actions.clone() {
            match action {
                PerpsNpActionV1::InitMarket {
                    market_id,
                    collateral_asset,
                    index_price_e8,
                    params,
                    insurance_seed_e8,
                } => state
                    .init_market(
                        market_id,
                        collateral_asset,
                        index_price_e8,
                        params,
                        insurance_seed_e8,
                    )
                    .unwrap(),
                PerpsNpActionV1::DepositCollateral {
                    pubkey,
                    asset,
                    amount_e8,
                    nonce,
                    collateral_binding,
                } => state
                    .deposit_collateral(pubkey, asset, amount_e8, nonce, collateral_binding)
                    .unwrap(),
                PerpsNpActionV1::SubmitIntent { intent } => state.submit_intent(intent).unwrap(),
                PerpsNpActionV1::RunEpoch {
                    oracle,
                    clearing_price_e8,
                    funding_rate_bps,
                    intents,
                } => {
                    let out = state
                        .run_epoch(oracle, clearing_price_e8, funding_rate_bps, intents)
                        .unwrap();
                    assert_eq!(out.matched_base_volume, 5);
                }
                PerpsNpActionV1::WithdrawCollateral { .. } => unreachable!(),
            }
        }
        let expected_post = state.canonical_app_hash_sha256();
        let expected_collateral_binding_hash =
            perps_np_collateral_bindings_hash_v1(&actions).unwrap();
        let expected_oracle_binding_hash = perps_np_oracle_bindings_hash_v1(&actions).unwrap();
        let input = PerpsNpTransitionInputV1 {
            execution_context_hash: [0xEC; 32],
            state_hash: H,
            chain_id: "devnet".to_string(),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: PerpsNpSnapshotV1::empty(),
            actions,
            expected_post_app_hash: expected_post,
            risc0_image_id: IMAGE_ID,
        };
        let journal = execute_perps_np_transition_v1(input.clone()).unwrap();
        assert_eq!(journal.proof_type, PROOF_TYPE_PERPS_NP);
        assert_eq!(journal.execution_context_hash, input.execution_context_hash);
        assert_eq!(journal.participant_count, 5);
        assert_eq!(journal.net_position_base, 0);
        assert!(journal.matched_base_volume >= 5);
        assert_eq!(
            journal.collateral_binding_hash,
            expected_collateral_binding_hash
        );
        assert_eq!(journal.oracle_binding_hash, expected_oracle_binding_hash);

        let mut missing_context = input;
        missing_context.execution_context_hash = [0u8; 32];
        assert!(matches!(
            execute_perps_np_transition_v1(missing_context),
            Err(TransitionError::InvalidInput(
                "execution_context_hash all-zero"
            ))
        ));
    }

    #[test]
    fn perps_np_rejects_three_party_epoch_surface() {
        let actions = alloc::vec![
            init_action(),
            PerpsNpActionV1::DepositCollateral {
                pubkey: "a".to_string(),
                asset: default_zusd_asset(),
                amount_e8: 2_000 * E8_I128,
                nonce: 1,
                collateral_binding: Some(collateral_binding(10)),
            },
            PerpsNpActionV1::DepositCollateral {
                pubkey: "b".to_string(),
                asset: default_zusd_asset(),
                amount_e8: 2_000 * E8_I128,
                nonce: 1,
                collateral_binding: Some(collateral_binding(20)),
            },
            PerpsNpActionV1::DepositCollateral {
                pubkey: "c".to_string(),
                asset: default_zusd_asset(),
                amount_e8: 2_000 * E8_I128,
                nonce: 1,
                collateral_binding: Some(collateral_binding(30)),
            },
            PerpsNpActionV1::RunEpoch {
                oracle: oracle(100 * E8_I128),
                clearing_price_e8: 100 * E8_I128,
                funding_rate_bps: 0,
                intents: alloc::vec![
                    PerpsIntentV1 {
                        pubkey: "a".to_string(),
                        target_base: 1,
                        limit_price_e8: 0,
                        min_fill_base: 0,
                        expiry_epoch: 10,
                        nonce: 2,
                    },
                    PerpsIntentV1 {
                        pubkey: "b".to_string(),
                        target_base: -1,
                        limit_price_e8: 0,
                        min_fill_base: 0,
                        expiry_epoch: 10,
                        nonce: 2,
                    },
                    PerpsIntentV1 {
                        pubkey: "c".to_string(),
                        target_base: 0,
                        limit_price_e8: 0,
                        min_fill_base: 0,
                        expiry_epoch: 10,
                        nonce: 2,
                    },
                ],
            },
        ];
        let input = PerpsNpTransitionInputV1 {
            execution_context_hash: [0xEC; 32],
            state_hash: H,
            chain_id: "devnet".to_string(),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: PerpsNpSnapshotV1::empty(),
            actions,
            expected_post_app_hash: [0u8; 32],
            risc0_image_id: IMAGE_ID,
        };
        assert!(matches!(
            execute_perps_np_transition_v1(input),
            Err(TransitionError::InvalidInput(
                "perps np epoch requires 4 participants"
            ))
        ));
    }

    #[test]
    fn perps_np_rejects_zusd_deposit_without_source_binding() {
        let actions = alloc::vec![
            init_action(),
            PerpsNpActionV1::DepositCollateral {
                pubkey: "wallet-a".to_string(),
                asset: default_zusd_asset(),
                amount_e8: 2_000 * E8_I128,
                nonce: 1,
                collateral_binding: None,
            },
        ];
        let input = PerpsNpTransitionInputV1 {
            execution_context_hash: [0xEC; 32],
            state_hash: H,
            chain_id: "devnet".to_string(),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: PerpsNpSnapshotV1::empty(),
            actions,
            expected_post_app_hash: [0u8; 32],
            risc0_image_id: IMAGE_ID,
        };
        assert!(matches!(
            execute_perps_np_transition_v1(input),
            Err(TransitionError::InvalidInput(
                "zUSD collateral binding missing"
            ))
        ));
    }

    #[test]
    fn perps_np_zusd_collateral_binding_is_hash_bound_external_reference() {
        let binding = CollateralBindingV1 {
            source_proof_type: PROOF_TYPE_ZUSD.to_string(),
            source_state_hash: "aa".repeat(32),
            balance_root_hash: "bb".repeat(32),
            balance_delta_hash: "cc".repeat(32),
        };
        let mut state = PerpsStateV1::from_snapshot(PerpsNpSnapshotV1::empty()).unwrap();
        state
            .init_market(
                "BTC-PERP".to_string(),
                default_zusd_asset(),
                100 * E8_I128,
                PerpsMarketParamsV1::default(),
                1_000_000_000,
            )
            .unwrap();
        state
            .deposit_collateral(
                "wallet-a".to_string(),
                default_zusd_asset(),
                2_000 * E8_I128,
                1,
                Some(binding.clone()),
            )
            .unwrap();

        let mut changed_binding = binding.clone();
        changed_binding.balance_delta_hash = "dd".repeat(32);
        let base = alloc::vec![PerpsNpActionV1::DepositCollateral {
            pubkey: "wallet-a".to_string(),
            asset: default_zusd_asset(),
            amount_e8: 2_000 * E8_I128,
            nonce: 1,
            collateral_binding: Some(binding),
        }];
        let changed = alloc::vec![PerpsNpActionV1::DepositCollateral {
            pubkey: "wallet-a".to_string(),
            asset: default_zusd_asset(),
            amount_e8: 2_000 * E8_I128,
            nonce: 1,
            collateral_binding: Some(changed_binding),
        }];
        assert_ne!(
            perps_np_collateral_bindings_hash_v1(&base).unwrap(),
            perps_np_collateral_bindings_hash_v1(&changed).unwrap()
        );
    }

    #[test]
    fn perps_np_deposit_and_withdraw_require_strict_next_nonce() {
        let mut state = PerpsStateV1::from_snapshot(PerpsNpSnapshotV1::empty()).unwrap();
        state
            .init_market(
                "BTC-PERP".to_string(),
                default_zusd_asset(),
                100 * E8_I128,
                PerpsMarketParamsV1::default(),
                1_000_000_000,
            )
            .unwrap();

        state
            .deposit_collateral(
                "wallet-a".to_string(),
                default_zusd_asset(),
                2_000 * E8_I128,
                1,
                Some(collateral_binding(10)),
            )
            .unwrap();

        let before_gap_deposit_hash = state.canonical_app_hash_sha256();
        assert!(matches!(
            state.deposit_collateral(
                "wallet-a".to_string(),
                default_zusd_asset(),
                1,
                3,
                Some(collateral_binding(11)),
            ),
            Err(TransitionError::InvalidInput("deposit nonce mismatch"))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), before_gap_deposit_hash);

        assert!(matches!(
            state.withdraw_collateral("wallet-a".to_string(), default_zusd_asset(), 1, 3),
            Err(TransitionError::InvalidInput("withdraw nonce mismatch"))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), before_gap_deposit_hash);

        state
            .withdraw_collateral("wallet-a".to_string(), default_zusd_asset(), 1, 2)
            .unwrap();
        let account = state.accounts.get("wallet-a").unwrap();
        assert_eq!(account.nonce, 2);
        assert_eq!(account.collateral_e8, 2_000 * E8_I128 - 1);
    }

    #[test]
    fn perps_np_rejects_nonce_after_u64_max_without_mutation() {
        let mut accounts = BTreeMap::new();
        accounts.insert(
            "wallet-a".to_string(),
            PerpsAccountV1 {
                pubkey: "wallet-a".to_string(),
                position_base: 0,
                entry_price_e8: 0,
                collateral_e8: 2_000 * E8_I128,
                funding_paid_cum_e8: 0,
                nonce: u64::MAX,
            },
        );
        let mut state = PerpsStateV1 {
            market_id: "BTC-PERP".to_string(),
            collateral_asset: default_zusd_asset(),
            index_price_e8: 100 * E8_I128,
            params: PerpsMarketParamsV1::default(),
            accounts,
            pending_intents: Vec::new(),
            now_epoch: 0,
            fee_pool_e8: 0,
            insurance_e8: 1_000_000_000,
            insurance_ext_e8: 1_000_000_000,
            claims_paid_e8: 0,
            net_deposited_e8: 2_000 * E8_I128,
        };

        let before_hash = state.canonical_app_hash_sha256();
        assert!(matches!(
            state.withdraw_collateral("wallet-a".to_string(), default_zusd_asset(), 1, u64::MAX),
            Err(TransitionError::InvalidInput("withdraw nonce mismatch"))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), before_hash);
    }

    #[test]
    fn perps_np_run_epoch_rejects_gap_intent_nonce() {
        let mut state = initialized_four_wallet_state();
        let result = state
            .run_epoch(
                oracle(100 * E8_I128),
                100 * E8_I128,
                0,
                alloc::vec![intent("wallet-a", 1, 3)],
            )
            .unwrap();

        let receipt = result
            .receipts
            .iter()
            .find(|receipt| receipt.pubkey == "wallet-a")
            .expect("gap nonce receipt");
        assert_eq!(receipt.status, "rejected");
        assert_eq!(receipt.reject_code.as_deref(), Some("REJ_BAD_NONCE"));
        assert_eq!(state.accounts.get("wallet-a").unwrap().nonce, 1);
        assert_eq!(state.accounts.get("wallet-a").unwrap().position_base, 0);
    }

    #[test]
    fn perps_np_run_epoch_accepts_contiguous_replacement_intent_nonce() {
        let mut state = initialized_four_wallet_state();
        let result = state
            .run_epoch(
                oracle(100 * E8_I128),
                100 * E8_I128,
                0,
                alloc::vec![
                    intent("wallet-a", 1, 2),
                    intent("wallet-a", 2, 3),
                    intent("wallet-b", -1, 2),
                    intent("wallet-c", -1, 2),
                    intent("wallet-d", 0, 2),
                ],
            )
            .unwrap();

        let superseded = result
            .receipts
            .iter()
            .find(|receipt| receipt.pubkey == "wallet-a" && receipt.nonce == 2)
            .expect("superseded wallet-a receipt");
        assert_eq!(superseded.status, "rejected");
        assert_eq!(superseded.reject_code.as_deref(), Some("REJ_SUPERSEDED"));

        let filled = result
            .receipts
            .iter()
            .find(|receipt| receipt.pubkey == "wallet-a" && receipt.nonce == 3)
            .expect("filled wallet-a receipt");
        assert_eq!(filled.status, "filled");
        assert_eq!(filled.delta, 2);

        let account = state.accounts.get("wallet-a").unwrap();
        assert_eq!(account.nonce, 3);
        assert_eq!(account.position_base, 2);
    }

    #[test]
    fn perps_np_run_epoch_rejects_unknown_account_intent() {
        let mut state = initialized_four_wallet_state();
        let result = state
            .run_epoch(
                oracle(100 * E8_I128),
                100 * E8_I128,
                0,
                alloc::vec![intent("wallet-missing", 0, 1)],
            )
            .unwrap();

        let receipt = result
            .receipts
            .iter()
            .find(|receipt| receipt.pubkey == "wallet-missing")
            .expect("unknown account receipt");
        assert_eq!(receipt.status, "rejected");
        assert_eq!(receipt.reject_code.as_deref(), Some("REJ_ACCOUNT"));
        assert!(!state.accounts.contains_key("wallet-missing"));
    }

    #[test]
    fn perps_np_rejects_stale_oracle_bridge() {
        let mut stale = oracle(100 * E8_I128);
        stale.observed_at = 20;
        let input = PerpsNpTransitionInputV1 {
            execution_context_hash: [0xEC; 32],
            state_hash: H,
            chain_id: "devnet".to_string(),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: PerpsNpSnapshotV1::empty(),
            actions: alloc::vec![
                init_action(),
                PerpsNpActionV1::RunEpoch {
                    oracle: stale,
                    clearing_price_e8: 100 * E8_I128,
                    funding_rate_bps: 0,
                    intents: Vec::new(),
                }
            ],
            expected_post_app_hash: [0u8; 32],
            risc0_image_id: IMAGE_ID,
        };
        assert!(matches!(
            execute_perps_np_transition_v1(input),
            Err(TransitionError::InvalidInput("oracle bridge stale"))
        ));
    }

    #[test]
    fn zusd_deposit_mint_binds_mcr_and_balance_root() {
        let operation = ZusdOperationV1::DepositMint {
            pubkey: "wallet-a".to_string(),
            collateral_asset: "tAGRS".to_string(),
            deposit_amount_e8: 2_000 * E8_U128,
            mint_amount_e8: 1_000 * E8_U128,
            oracle: oracle(E8_I128),
            mcr_bps: 11_000,
            nonce: 1,
        };
        let mut state = ZusdStateV1::from_snapshot(ZusdSnapshotV1::empty()).unwrap();
        state.apply_operation(operation.clone()).unwrap();
        let expected_post = state.canonical_app_hash_sha256();
        let expected_balance_root = state.balance_root_hash();
        let expected_vault_root = state.vault_root_hash();
        let input = ZusdTransitionInputV1 {
            execution_context_hash: [0xEC; 32],
            state_hash: H,
            chain_id: "devnet".to_string(),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: ZusdSnapshotV1::empty(),
            operation,
            expected_post_app_hash: expected_post,
            risc0_image_id: IMAGE_ID,
        };
        let journal = execute_zusd_transition_v1(input.clone()).unwrap();
        assert_eq!(journal.proof_type, PROOF_TYPE_ZUSD);
        assert_eq!(journal.execution_context_hash, input.execution_context_hash);
        assert_eq!(journal.minted_zusd_e8, 1_000 * E8_U128);
        assert_eq!(journal.mcr_bps, 11_000);
        assert_eq!(journal.zusd_balance_root_hash, expected_balance_root);
        assert_eq!(journal.zusd_vault_root_hash, expected_vault_root);

        let mut missing_context = input;
        missing_context.execution_context_hash = [0u8; 32];
        assert!(matches!(
            execute_zusd_transition_v1(missing_context),
            Err(TransitionError::InvalidInput(
                "execution_context_hash all-zero"
            ))
        ));
    }

    #[test]
    fn zusd_rejects_mcr_violation() {
        let input = ZusdTransitionInputV1 {
            execution_context_hash: [0xEC; 32],
            state_hash: H,
            chain_id: "devnet".to_string(),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            pre_state: ZusdSnapshotV1::empty(),
            operation: ZusdOperationV1::DepositMint {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                deposit_amount_e8: 100 * E8_U128,
                mint_amount_e8: 1_000 * E8_U128,
                oracle: oracle(E8_I128),
                mcr_bps: 11_000,
                nonce: 1,
            },
            expected_post_app_hash: [0u8; 32],
            risc0_image_id: IMAGE_ID,
        };
        assert!(matches!(
            execute_zusd_transition_v1(input),
            Err(TransitionError::InvalidInput("zusd mint violates MCR"))
        ));
    }

    #[test]
    fn zusd_rejects_gap_nonce_without_mutation() {
        let snapshot = ZusdSnapshotV1 {
            version: 1,
            vaults: alloc::vec![ZusdVaultEntryV1 {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                collateral_amount_e8: 2_000 * E8_U128,
                debt_zusd_e8: 1_000 * E8_U128,
                nonce: 1,
            }],
            balances: alloc::vec![ZusdBalanceEntryV1 {
                pubkey: "wallet-a".to_string(),
                amount_e8: 1_000 * E8_U128,
            }],
            total_debt_zusd_e8: 1_000 * E8_U128,
        };
        let mut state = ZusdStateV1::from_snapshot(snapshot).unwrap();
        let before_hash = state.canonical_app_hash_sha256();
        assert!(matches!(
            state.apply_operation(ZusdOperationV1::DepositMint {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                deposit_amount_e8: 100 * E8_U128,
                mint_amount_e8: 10 * E8_U128,
                oracle: oracle(E8_I128),
                mcr_bps: 11_000,
                nonce: 3,
            }),
            Err(TransitionError::InvalidInput("zusd nonce mismatch"))
        ));
        assert_eq!(state.canonical_app_hash_sha256(), before_hash);
    }
}
