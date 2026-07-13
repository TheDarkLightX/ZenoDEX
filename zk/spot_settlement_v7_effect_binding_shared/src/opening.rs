use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    DexBalanceEntryV1, DexLpBalanceEntryV1, DexPoolEntryV1, DexSnapshotV1, NonceEntryV1,
};
use zenodex_zrpf_protocol_v3::{
    AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2, CommitmentV3, EconomicActionIdV1,
    LedgerCellWriteInputV2, LedgerCellWriteV2, ValueHashV2,
};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    verify_restricted_spot_state_root_v5_transition_v1, ExpectedLegacySpotCommitmentsV1,
    ExpectedSpotStateRootsV5, RestrictedSpotStateRootV5ProfileV1,
    RestrictedSpotStateRootV5TransitionInputV1,
};
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    encode_spot_state_root_v7_semantic_journal_v1, SpotStateRootV7SemanticJournalV1,
};

use crate::SpotSettlementV7EffectBindingErrorV1;

const PUBKEY_BYTES: usize = 48;
const IDENTIFIER_BYTES: usize = 32;

const CELL_KEY_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_typed_cell_key.v1";
const CELL_VALUE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_typed_cell_value.v1";
const CELL_CHANGE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_typed_cell_change.v1";
const CELL_CHANGES_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_typed_cell_changes_root.v1";
const ACTION_SEMANTICS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_v7_action_semantics.v1";
const EFFECT_COMMITMENT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_v7_effect_projection.v1";
const SOURCE_JOURNAL_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_v7_semantic_journal.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotLedgerCellKindV1 {
    AccountBalance,
    PoolReserve,
}

impl SpotLedgerCellKindV1 {
    const fn code(self) -> u8 {
        match self {
            Self::AccountBalance => 1,
            Self::PoolReserve => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotLedgerCellRoleV1 {
    Debit,
    Credit,
}

impl SpotLedgerCellRoleV1 {
    const fn code(self) -> u8 {
        match self {
            Self::Debit => 1,
            Self::Credit => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SpotLedgerCellSubjectV1 {
    Account([u8; PUBKEY_BYTES]),
    Pool([u8; IDENTIFIER_BYTES]),
}

/// One typed value opening for an account-balance or pool-reserve cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpotLedgerCellOpeningV1 {
    kind: SpotLedgerCellKindV1,
    subject: SpotLedgerCellSubjectV1,
    asset_id: CommitmentV3,
    atoms: u128,
    cell_key: CommitmentV3,
    value_hash: ValueHashV2,
}

impl SpotLedgerCellOpeningV1 {
    fn account(
        account: [u8; PUBKEY_BYTES],
        asset_id: [u8; IDENTIFIER_BYTES],
        atoms: u128,
    ) -> Result<Self, SpotSettlementV7EffectBindingErrorV1> {
        Self::new(
            SpotLedgerCellKindV1::AccountBalance,
            SpotLedgerCellSubjectV1::Account(account),
            asset_id,
            atoms,
        )
    }

    fn pool(
        pool: [u8; IDENTIFIER_BYTES],
        asset_id: [u8; IDENTIFIER_BYTES],
        atoms: u128,
    ) -> Result<Self, SpotSettlementV7EffectBindingErrorV1> {
        Self::new(
            SpotLedgerCellKindV1::PoolReserve,
            SpotLedgerCellSubjectV1::Pool(pool),
            asset_id,
            atoms,
        )
    }

    fn new(
        kind: SpotLedgerCellKindV1,
        subject: SpotLedgerCellSubjectV1,
        asset_id: [u8; IDENTIFIER_BYTES],
        atoms: u128,
    ) -> Result<Self, SpotSettlementV7EffectBindingErrorV1> {
        let asset_id = CommitmentV3::new(asset_id)?;
        let cell_key = derive_cell_key(kind, subject, asset_id)?;
        let value_hash = derive_value_hash(cell_key, atoms)?;
        Ok(Self {
            kind,
            subject,
            asset_id,
            atoms,
            cell_key,
            value_hash,
        })
    }

    pub const fn kind(&self) -> SpotLedgerCellKindV1 {
        self.kind
    }

    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }

    pub const fn atoms(&self) -> u128 {
        self.atoms
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.cell_key
    }

    pub const fn value_hash(&self) -> ValueHashV2 {
        self.value_hash
    }

    pub const fn account_subject(&self) -> Option<[u8; PUBKEY_BYTES]> {
        match self.subject {
            SpotLedgerCellSubjectV1::Account(account) => Some(account),
            SpotLedgerCellSubjectV1::Pool(_) => None,
        }
    }

    pub const fn pool_subject(&self) -> Option<[u8; IDENTIFIER_BYTES]> {
        match self.subject {
            SpotLedgerCellSubjectV1::Account(_) => None,
            SpotLedgerCellSubjectV1::Pool(pool) => Some(pool),
        }
    }
}

/// One typed and direction-checked state change.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpotLedgerCellTransitionOpeningV1 {
    role: SpotLedgerCellRoleV1,
    pre: SpotLedgerCellOpeningV1,
    post: SpotLedgerCellOpeningV1,
    amount_atoms: u128,
    commitment: CommitmentV3,
}

impl SpotLedgerCellTransitionOpeningV1 {
    fn new(
        role: SpotLedgerCellRoleV1,
        pre: SpotLedgerCellOpeningV1,
        post: SpotLedgerCellOpeningV1,
    ) -> Result<Self, SpotSettlementV7EffectBindingErrorV1> {
        if pre.kind != post.kind
            || pre.subject != post.subject
            || pre.asset_id != post.asset_id
            || pre.cell_key != post.cell_key
        {
            return Err(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
                "cell identity changed",
            ));
        }
        let amount_atoms = match role {
            SpotLedgerCellRoleV1::Debit => pre.atoms.checked_sub(post.atoms),
            SpotLedgerCellRoleV1::Credit => post.atoms.checked_sub(pre.atoms),
        }
        .filter(|amount| *amount > 0)
        .ok_or(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
            "cell direction or zero amount",
        ))?;
        let commitment = derive_cell_change_commitment(role, pre, post, amount_atoms)?;
        Ok(Self {
            role,
            pre,
            post,
            amount_atoms,
            commitment,
        })
    }

    pub const fn role(&self) -> SpotLedgerCellRoleV1 {
        self.role
    }

    pub const fn pre(&self) -> &SpotLedgerCellOpeningV1 {
        &self.pre
    }

    pub const fn post(&self) -> &SpotLedgerCellOpeningV1 {
        &self.post
    }

    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }

    pub const fn commitment(&self) -> CommitmentV3 {
        self.commitment
    }

    fn ledger_write(
        &self,
        action_id: EconomicActionIdV1,
    ) -> Result<LedgerCellWriteV2, SpotSettlementV7EffectBindingErrorV1> {
        Ok(LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
            economic_action_id: action_id,
            cell_key: self.pre.cell_key,
            pre_value_hash: self.pre.value_hash,
            post_value_hash: self.post.value_hash,
        })?)
    }
}

/// Full-state opening for the restricted singleton Spot swap profile.
///
/// Construction recomputes the source app commitments and both state-root-v5
/// values. It then proves that the only economic state changes are exactly one
/// account-to-pool input transfer and one pool-to-account output transfer.
/// The value is proof-neutral because its V7 journal argument is not a receipt.
#[derive(Debug, PartialEq, Eq)]
pub struct SpotSettlementStateEffectOpeningV1 {
    compatibility_profile_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    source_journal_commitment: CommitmentV3,
    pre_state_root: CommitmentV3,
    post_state_root: CommitmentV3,
    sender_pubkey: [u8; PUBKEY_BYTES],
    ingress_nonce: u32,
    pool_id: CommitmentV3,
    input_asset_id: CommitmentV3,
    output_asset_id: CommitmentV3,
    input_amount_atoms: u128,
    output_amount_atoms: u128,
    recipient_pubkey: [u8; PUBKEY_BYTES],
    cell_transitions: Vec<SpotLedgerCellTransitionOpeningV1>,
    cell_transitions_root: CommitmentV3,
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
}

impl SpotSettlementStateEffectOpeningV1 {
    pub const fn compatibility_profile_id(&self) -> CommitmentV3 {
        self.compatibility_profile_id
    }

    pub const fn state_root_scheme_id(&self) -> CommitmentV3 {
        self.state_root_scheme_id
    }

    pub const fn source_journal_commitment(&self) -> CommitmentV3 {
        self.source_journal_commitment
    }

    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.pre_state_root
    }

    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.post_state_root
    }

    pub const fn sender_pubkey(&self) -> [u8; PUBKEY_BYTES] {
        self.sender_pubkey
    }

    pub const fn ingress_nonce(&self) -> u32 {
        self.ingress_nonce
    }

    pub const fn pool_id(&self) -> CommitmentV3 {
        self.pool_id
    }

    pub const fn input_asset_id(&self) -> CommitmentV3 {
        self.input_asset_id
    }

    pub const fn output_asset_id(&self) -> CommitmentV3 {
        self.output_asset_id
    }

    pub const fn input_amount_atoms(&self) -> u128 {
        self.input_amount_atoms
    }

    pub const fn output_amount_atoms(&self) -> u128 {
        self.output_amount_atoms
    }

    pub const fn recipient_pubkey(&self) -> [u8; PUBKEY_BYTES] {
        self.recipient_pubkey
    }

    pub fn cell_transitions(&self) -> &[SpotLedgerCellTransitionOpeningV1] {
        &self.cell_transitions
    }

    pub const fn cell_transitions_root(&self) -> CommitmentV3 {
        self.cell_transitions_root
    }

    pub const fn action_semantics_hash(&self) -> CommitmentV3 {
        self.action_semantics_hash
    }

    pub const fn effect_commitment(&self) -> CommitmentV3 {
        self.effect_commitment
    }

    pub fn expected_cell_writes(
        &self,
        action_id: EconomicActionIdV1,
    ) -> Result<Vec<LedgerCellWriteV2>, SpotSettlementV7EffectBindingErrorV1> {
        self.cell_transitions
            .iter()
            .map(|transition| transition.ledger_write(action_id))
            .collect()
    }

    pub fn expected_asset_effects(
        &self,
        action_id: EconomicActionIdV1,
    ) -> Result<Vec<AssetEffectV2>, SpotSettlementV7EffectBindingErrorV1> {
        let effects = vec![
            ordinary_effect(action_id, self.input_asset_id, self.input_amount_atoms)?,
            ordinary_effect(action_id, self.output_asset_id, self.output_amount_atoms)?,
        ];
        let mut identified = effects
            .into_iter()
            .map(|effect| Ok((effect.canonical_id()?, effect)))
            .collect::<Result<Vec<_>, SpotSettlementV7EffectBindingErrorV1>>()?;
        identified.sort_by_key(|(canonical_id, _)| *canonical_id);
        Ok(identified.into_iter().map(|(_, effect)| effect).collect())
    }
}

pub fn derive_spot_settlement_state_effect_opening_v1(
    journal: &SpotStateRootV7SemanticJournalV1,
    pre_state: &DexSnapshotV1,
    post_state: &DexSnapshotV1,
) -> Result<SpotSettlementStateEffectOpeningV1, SpotSettlementV7EffectBindingErrorV1> {
    verify_snapshots_against_journal(journal, pre_state, post_state)?;
    require_unchanged_non_swap_state(pre_state, post_state)?;
    let pool_delta = derive_pool_delta(pre_state, post_state)?;
    let account_delta = derive_account_delta(pre_state, post_state, &pool_delta, journal)?;
    let mut cell_transitions = derive_cell_transitions(&pool_delta, &account_delta)?;
    cell_transitions.sort_by_key(|transition| transition.pre.cell_key);
    require_unique_cell_keys(&cell_transitions)?;

    let cell_transitions_root = derive_cell_transitions_root(&cell_transitions)?;
    let action_semantics_hash = derive_action_semantics_hash(journal, &pool_delta, &account_delta)?;
    let pre_state_root = CommitmentV3::new(journal.pre_state_root_v5())?;
    let post_state_root = CommitmentV3::new(journal.post_state_root_v5())?;
    let effect_commitment = derive_effect_commitment(
        pre_state_root,
        post_state_root,
        action_semantics_hash,
        cell_transitions_root,
    )?;
    let source_journal_commitment = derive_source_journal_commitment(journal)?;
    Ok(SpotSettlementStateEffectOpeningV1 {
        compatibility_profile_id: CommitmentV3::new(journal.compatibility_profile_id())?,
        state_root_scheme_id: CommitmentV3::new(journal.state_root_scheme_id())?,
        source_journal_commitment,
        pre_state_root,
        post_state_root,
        sender_pubkey: journal.sender_pubkey(),
        ingress_nonce: journal.ingress_nonce(),
        pool_id: CommitmentV3::new(pool_delta.pool_id)?,
        input_asset_id: CommitmentV3::new(pool_delta.input_asset)?,
        output_asset_id: CommitmentV3::new(pool_delta.output_asset)?,
        input_amount_atoms: pool_delta.input_amount,
        output_amount_atoms: pool_delta.output_amount,
        recipient_pubkey: account_delta.recipient,
        cell_transitions,
        cell_transitions_root,
        action_semantics_hash,
        effect_commitment,
    })
}

#[derive(Clone, Copy)]
struct PoolRowV1 {
    pool_id: [u8; IDENTIFIER_BYTES],
    asset0: [u8; IDENTIFIER_BYTES],
    asset1: [u8; IDENTIFIER_BYTES],
    reserve0: u128,
    reserve1: u128,
    fee_bps: u32,
    lp_supply: u128,
    created_at: u64,
}

#[derive(Clone, Copy)]
struct PoolDeltaV1 {
    pool_id: [u8; IDENTIFIER_BYTES],
    input_asset: [u8; IDENTIFIER_BYTES],
    output_asset: [u8; IDENTIFIER_BYTES],
    input_pre: u128,
    input_post: u128,
    output_pre: u128,
    output_post: u128,
    input_amount: u128,
    output_amount: u128,
}

#[derive(Clone, Copy)]
struct AccountDeltaV1 {
    sender: [u8; PUBKEY_BYTES],
    recipient: [u8; PUBKEY_BYTES],
    input_pre: u128,
    input_post: u128,
    output_pre: u128,
    output_post: u128,
}

fn verify_snapshots_against_journal(
    journal: &SpotStateRootV7SemanticJournalV1,
    pre_state: &DexSnapshotV1,
    post_state: &DexSnapshotV1,
) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
    let sender = encode_hex(&journal.sender_pubkey());
    let nonce = u64::from(journal.ingress_nonce());
    let pre_nonces = [NonceEntryV1 {
        pubkey: sender.clone(),
        next_nonce: nonce,
    }];
    verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            pre_state,
            post_state,
            &pre_nonces,
            &sender,
            nonce,
            ExpectedLegacySpotCommitmentsV1::new(
                journal.source_pre_app_hash(),
                journal.source_post_app_hash(),
                journal.source_pre_nonce_root(),
                journal.source_post_nonce_root(),
            ),
            ExpectedSpotStateRootsV5::new(
                journal.pre_state_root_v5(),
                journal.post_state_root_v5(),
            ),
        ),
    )?;
    Ok(())
}

fn require_unchanged_non_swap_state(
    pre: &DexSnapshotV1,
    post: &DexSnapshotV1,
) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
    if pre.fee_accumulator.dust != post.fee_accumulator.dust {
        return Err(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
            "fee accumulator changed",
        ));
    }
    if lp_map(&pre.lp_balances)? != lp_map(&post.lp_balances)? {
        return Err(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
            "LP balances changed",
        ));
    }
    Ok(())
}

fn derive_pool_delta(
    pre: &DexSnapshotV1,
    post: &DexSnapshotV1,
) -> Result<PoolDeltaV1, SpotSettlementV7EffectBindingErrorV1> {
    let pre_pools = pool_map(&pre.pools)?;
    let post_pools = pool_map(&post.pools)?;
    if pre_pools.len() != post_pools.len() {
        return unsupported("pool set changed");
    }
    let mut changed = None;
    for (pool_id, before) in &pre_pools {
        let after = post_pools.get(pool_id).ok_or(
            SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta("pool set changed"),
        )?;
        if before.asset0 != after.asset0
            || before.asset1 != after.asset1
            || before.fee_bps != after.fee_bps
            || before.lp_supply != after.lp_supply
            || before.created_at != after.created_at
        {
            return unsupported("pool metadata changed");
        }
        if (before.reserve0 != after.reserve0 || before.reserve1 != after.reserve1)
            && changed.replace((*before, *after)).is_some()
        {
            return unsupported("multiple pools changed");
        }
    }
    let (before, after) = changed.ok_or(
        SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta("no pool changed"),
    )?;
    match (
        classify_delta(before.reserve0, after.reserve0)?,
        classify_delta(before.reserve1, after.reserve1)?,
    ) {
        (DeltaV1::Credit(input), DeltaV1::Debit(output)) => Ok(PoolDeltaV1 {
            pool_id: before.pool_id,
            input_asset: before.asset0,
            output_asset: before.asset1,
            input_pre: before.reserve0,
            input_post: after.reserve0,
            output_pre: before.reserve1,
            output_post: after.reserve1,
            input_amount: input,
            output_amount: output,
        }),
        (DeltaV1::Debit(output), DeltaV1::Credit(input)) => Ok(PoolDeltaV1 {
            pool_id: before.pool_id,
            input_asset: before.asset1,
            output_asset: before.asset0,
            input_pre: before.reserve1,
            input_post: after.reserve1,
            output_pre: before.reserve0,
            output_post: after.reserve0,
            input_amount: input,
            output_amount: output,
        }),
        _ => unsupported("pool reserves do not encode one exact swap"),
    }
}

fn derive_account_delta(
    pre: &DexSnapshotV1,
    post: &DexSnapshotV1,
    pool: &PoolDeltaV1,
    journal: &SpotStateRootV7SemanticJournalV1,
) -> Result<AccountDeltaV1, SpotSettlementV7EffectBindingErrorV1> {
    let pre_balances = balance_map(&pre.balances)?;
    let post_balances = balance_map(&post.balances)?;
    let keys = pre_balances
        .keys()
        .chain(post_balances.keys())
        .copied()
        .collect::<BTreeSet<_>>();
    let changes = keys
        .into_iter()
        .filter_map(|key| {
            let before = pre_balances.get(&key).copied().unwrap_or(0);
            let after = post_balances.get(&key).copied().unwrap_or(0);
            (before != after).then_some((key, before, after))
        })
        .collect::<Vec<_>>();
    if changes.len() != 2 {
        return unsupported("account balance change count is not two");
    }
    let ((debit_account, _), input_pre, input_post) = changes
        .iter()
        .find(|((_, asset), before, after)| {
            *asset == pool.input_asset && before.checked_sub(*after) == Some(pool.input_amount)
        })
        .ok_or(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
            "input account debit mismatch",
        ))?;
    let ((credit_account, _), output_pre, output_post) = changes
        .iter()
        .find(|((_, asset), before, after)| {
            *asset == pool.output_asset && after.checked_sub(*before) == Some(pool.output_amount)
        })
        .ok_or(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
            "output account credit mismatch",
        ))?;
    if *debit_account != journal.sender_pubkey() {
        return unsupported("input debit is not the journal sender");
    }
    Ok(AccountDeltaV1 {
        sender: *debit_account,
        recipient: *credit_account,
        input_pre: *input_pre,
        input_post: *input_post,
        output_pre: *output_pre,
        output_post: *output_post,
    })
}

fn derive_cell_transitions(
    pool: &PoolDeltaV1,
    account: &AccountDeltaV1,
) -> Result<Vec<SpotLedgerCellTransitionOpeningV1>, SpotSettlementV7EffectBindingErrorV1> {
    Ok(vec![
        SpotLedgerCellTransitionOpeningV1::new(
            SpotLedgerCellRoleV1::Debit,
            SpotLedgerCellOpeningV1::account(account.sender, pool.input_asset, account.input_pre)?,
            SpotLedgerCellOpeningV1::account(account.sender, pool.input_asset, account.input_post)?,
        )?,
        SpotLedgerCellTransitionOpeningV1::new(
            SpotLedgerCellRoleV1::Credit,
            SpotLedgerCellOpeningV1::pool(pool.pool_id, pool.input_asset, pool.input_pre)?,
            SpotLedgerCellOpeningV1::pool(pool.pool_id, pool.input_asset, pool.input_post)?,
        )?,
        SpotLedgerCellTransitionOpeningV1::new(
            SpotLedgerCellRoleV1::Debit,
            SpotLedgerCellOpeningV1::pool(pool.pool_id, pool.output_asset, pool.output_pre)?,
            SpotLedgerCellOpeningV1::pool(pool.pool_id, pool.output_asset, pool.output_post)?,
        )?,
        SpotLedgerCellTransitionOpeningV1::new(
            SpotLedgerCellRoleV1::Credit,
            SpotLedgerCellOpeningV1::account(
                account.recipient,
                pool.output_asset,
                account.output_pre,
            )?,
            SpotLedgerCellOpeningV1::account(
                account.recipient,
                pool.output_asset,
                account.output_post,
            )?,
        )?,
    ])
}

fn require_unique_cell_keys(
    changes: &[SpotLedgerCellTransitionOpeningV1],
) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
    if changes
        .windows(2)
        .any(|pair| pair[0].pre.cell_key >= pair[1].pre.cell_key)
    {
        return unsupported("typed cell keys are not unique");
    }
    Ok(())
}

fn derive_action_semantics_hash(
    journal: &SpotStateRootV7SemanticJournalV1,
    pool: &PoolDeltaV1,
    account: &AccountDeltaV1,
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    let mut hasher = domain_hasher(ACTION_SEMANTICS_DOMAIN_V1)?;
    hasher.update(journal.sender_pubkey());
    hasher.update(journal.ingress_nonce().to_be_bytes());
    hasher.update(pool.pool_id);
    hasher.update(pool.input_asset);
    hasher.update(pool.output_asset);
    hasher.update(pool.input_amount.to_be_bytes());
    hasher.update(pool.output_amount.to_be_bytes());
    hasher.update(account.recipient);
    finalize_commitment(hasher, "action_semantics")
}

fn derive_effect_commitment(
    pre_state_root: CommitmentV3,
    post_state_root: CommitmentV3,
    action_semantics_hash: CommitmentV3,
    cell_transitions_root: CommitmentV3,
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    let mut hasher = domain_hasher(EFFECT_COMMITMENT_DOMAIN_V1)?;
    hasher.update(pre_state_root.as_bytes());
    hasher.update(post_state_root.as_bytes());
    hasher.update(action_semantics_hash.as_bytes());
    hasher.update(cell_transitions_root.as_bytes());
    finalize_commitment(hasher, "effect_commitment")
}

fn derive_source_journal_commitment(
    journal: &SpotStateRootV7SemanticJournalV1,
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    let bytes = encode_spot_state_root_v7_semantic_journal_v1(journal);
    let mut hasher = domain_hasher(SOURCE_JOURNAL_DOMAIN_V1)?;
    let length = u32::try_from(bytes.len()).map_err(|_| {
        SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("source_journal_length")
    })?;
    hasher.update(length.to_be_bytes());
    hasher.update(bytes);
    finalize_commitment(hasher, "source_journal")
}

fn derive_cell_transitions_root(
    changes: &[SpotLedgerCellTransitionOpeningV1],
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    let mut hasher = domain_hasher(CELL_CHANGES_ROOT_DOMAIN_V1)?;
    let count = u32::try_from(changes.len()).map_err(|_| {
        SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("cell_change_count")
    })?;
    hasher.update(count.to_be_bytes());
    for change in changes {
        hasher.update(change.commitment.as_bytes());
    }
    finalize_commitment(hasher, "cell_transitions_root")
}

fn derive_cell_key(
    kind: SpotLedgerCellKindV1,
    subject: SpotLedgerCellSubjectV1,
    asset_id: CommitmentV3,
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    let mut hasher = domain_hasher(CELL_KEY_DOMAIN_V1)?;
    hasher.update([kind.code()]);
    match subject {
        SpotLedgerCellSubjectV1::Account(account) => hasher.update(account),
        SpotLedgerCellSubjectV1::Pool(pool) => hasher.update(pool),
    }
    hasher.update(asset_id.as_bytes());
    finalize_commitment(hasher, "cell_key")
}

fn derive_value_hash(
    cell_key: CommitmentV3,
    atoms: u128,
) -> Result<ValueHashV2, SpotSettlementV7EffectBindingErrorV1> {
    let mut hasher = domain_hasher(CELL_VALUE_DOMAIN_V1)?;
    hasher.update(cell_key.as_bytes());
    hasher.update(atoms.to_be_bytes());
    Ok(ValueHashV2::new(hasher.finalize().into()))
}

fn derive_cell_change_commitment(
    role: SpotLedgerCellRoleV1,
    pre: SpotLedgerCellOpeningV1,
    post: SpotLedgerCellOpeningV1,
    amount_atoms: u128,
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    let mut hasher = domain_hasher(CELL_CHANGE_DOMAIN_V1)?;
    hasher.update([pre.kind.code(), role.code()]);
    hasher.update(pre.cell_key.as_bytes());
    hasher.update(pre.asset_id.as_bytes());
    hasher.update(pre.value_hash.as_bytes());
    hasher.update(post.value_hash.as_bytes());
    hasher.update(amount_atoms.to_be_bytes());
    finalize_commitment(hasher, "cell_change")
}

fn ordinary_effect(
    action_id: EconomicActionIdV1,
    asset_id: CommitmentV3,
    amount_atoms: u128,
) -> Result<AssetEffectV2, SpotSettlementV7EffectBindingErrorV1> {
    Ok(AssetEffectV2::new(AssetEffectInputV2 {
        kind: AssetEffectKindV2::OrdinaryTransfer,
        economic_action_id: action_id,
        asset_id,
        debit_atoms: amount_atoms,
        credit_atoms: amount_atoms,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_scope_id: None,
        action_authorization_binding: None,
    })?)
}

fn pool_map(
    pools: &[DexPoolEntryV1],
) -> Result<BTreeMap<[u8; IDENTIFIER_BYTES], PoolRowV1>, SpotSettlementV7EffectBindingErrorV1> {
    pools
        .iter()
        .map(|pool| {
            let pool_id = decode_hex(&pool.pool_id, "pool.pool_id")?;
            Ok((
                pool_id,
                PoolRowV1 {
                    pool_id,
                    asset0: decode_hex(&pool.asset0, "pool.asset0")?,
                    asset1: decode_hex(&pool.asset1, "pool.asset1")?,
                    reserve0: pool.reserve0,
                    reserve1: pool.reserve1,
                    fee_bps: pool.fee_bps,
                    lp_supply: pool.lp_supply,
                    created_at: pool.created_at,
                },
            ))
        })
        .collect()
}

type BalanceKeyV1 = ([u8; PUBKEY_BYTES], [u8; IDENTIFIER_BYTES]);

fn balance_map(
    balances: &[DexBalanceEntryV1],
) -> Result<BTreeMap<BalanceKeyV1, u128>, SpotSettlementV7EffectBindingErrorV1> {
    balances
        .iter()
        .map(|entry| {
            Ok((
                (
                    decode_hex(&entry.pubkey, "balance.pubkey")?,
                    decode_hex(&entry.asset, "balance.asset")?,
                ),
                entry.amount,
            ))
        })
        .collect()
}

fn lp_map(
    balances: &[DexLpBalanceEntryV1],
) -> Result<BTreeMap<BalanceKeyV1, u128>, SpotSettlementV7EffectBindingErrorV1> {
    balances
        .iter()
        .map(|entry| {
            Ok((
                (
                    decode_hex(&entry.pubkey, "lp.pubkey")?,
                    decode_hex(&entry.pool_id, "lp.pool_id")?,
                ),
                entry.amount,
            ))
        })
        .collect()
}

enum DeltaV1 {
    Unchanged,
    Debit(u128),
    Credit(u128),
}

fn classify_delta(
    before: u128,
    after: u128,
) -> Result<DeltaV1, SpotSettlementV7EffectBindingErrorV1> {
    if before == after {
        return Ok(DeltaV1::Unchanged);
    }
    if before > after {
        return Ok(DeltaV1::Debit(before.checked_sub(after).ok_or(
            SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("debit_delta"),
        )?));
    }
    Ok(DeltaV1::Credit(after.checked_sub(before).ok_or(
        SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("credit_delta"),
    )?))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, SpotSettlementV7EffectBindingErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn finalize_commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| SpotSettlementV7EffectBindingErrorV1::DerivedCommitment(field))
}

fn decode_hex<const N: usize>(
    value: &str,
    field: &'static str,
) -> Result<[u8; N], SpotSettlementV7EffectBindingErrorV1> {
    let bytes = value.as_bytes();
    if bytes.len() != 2 + 2 * N
        || !value.starts_with("0x")
        || !bytes[2..]
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(SpotSettlementV7EffectBindingErrorV1::InvalidIdentifier(
            field,
        ));
    }
    let mut decoded = [0_u8; N];
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        decoded[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    Ok(decoded)
}

fn encode_hex<const N: usize>(value: &[u8; N]) -> String {
    let mut encoded = String::from("0x");
    for byte in value {
        encoded.push_str(&format!("{byte:02x}"));
    }
    encoded
}

const fn nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => 0,
    }
}

fn unsupported<T>(field: &'static str) -> Result<T, SpotSettlementV7EffectBindingErrorV1> {
    Err(SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(
        field,
    ))
}
