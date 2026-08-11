//! Shared typed M6 transition ABI for host and RISC0 guests.
//!
//! This module owns the versioned shape and a small integer-only transition
//! envelope.  It deliberately does not verify a RISC0 receipt or select a
//! ledger head.  The production guest must call the same economic kernels as
//! the Python reference before constructing an accepted candidate.

use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const M6_SCHEMA_V1: &str = "zenodex/m6-safe-mount/v1";
pub const M6_ZRPF_PROFILE_V1: &str = "zenodex/m6-zrpf/1.0";
pub const M6_ZRPF_LEAF_COUNT_V1: usize = 64;
pub const M6_ZRPF_COMMANDS_PER_LEAF_V1: usize = 16;
pub const M6_ZRPF_COMMAND_COUNT_V1: usize = M6_ZRPF_LEAF_COUNT_V1 * M6_ZRPF_COMMANDS_PER_LEAF_V1;
pub const M6_ZRPF_AGGREGATE_COUNT_V1: usize = 8;

pub type RootV1 = [u8; 32];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GlobalCommandKindV1 {
    SpotSwap,
    LpAdd,
    LpRemove,
    ZusdBorrow,
    ZusdRepay,
    ZusdRedeem,
    ZusdLiquidate,
    StabilityPoolDeposit,
    StabilityPoolWithdraw,
    ZusdRedistribute,
    PerpOpen,
    PerpClose,
    PerpFunding,
    PerpLiquidate,
    OracleSubmit,
    OracleDispute,
    ProtocolBuyAndBurn,
    ZrpfProverReward,
    SellerAuctionCommit,
    SellerAuctionReveal,
    SellerAuctionSettle,
    SellerAuctionCancel,
    SellerAuctionExpire,
    PrivateSwapCommit,
    PrivateSwapReveal,
    PrivateSwapSettle,
    PrivateSwapCancel,
    PrivateSwapExpire,
    TauEscrowDeposit,
    TauWithdrawal,
    TauWithdrawalAck,
    FallbackActivate,
    TauRejoin,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AdmissionRejectReasonV1 {
    ContextDeploymentMismatch,
    ContextParentHeadMismatch,
    ContextEpochMismatch,
    ContextTauProfileMismatch,
    ContextVerifierMismatch,
    SenderMismatch,
    NonceMismatch,
    UnsupportedCommand,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BusinessStatusV1 {
    Accepted,
    RejectedCommitted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BusinessRejectReasonV1 {
    InvalidAmount,
    InsufficientBalance,
    InsufficientReserve,
    InvalidAsset,
    InvalidPrice,
    InvalidDeadline,
    InvalidCommitment,
    InvalidEscrow,
    InvalidWithdrawal,
    InvalidPhase,
    InvalidAuthority,
    UnsupportedOperation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct M6PromotionSubjectV1 {
    pub source: RootV1,
    pub proof: RootV1,
    pub build: RootV1,
    pub schema: RootV1,
    pub deployment: RootV1,
    pub verifier: RootV1,
    pub tau_profile: RootV1,
    pub validator_set: RootV1,
    pub writer_epoch: u64,
    pub managed_asset_policy: RootV1,
    pub risc0_image: RootV1,
    pub destination_adapter_roots: Vec<(RootV1, RootV1)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthenticatedExecutionContextV1 {
    pub deployment: RootV1,
    pub parent_head: RootV1,
    pub epoch: u64,
    pub sender: RootV1,
    pub nonce: u64,
    pub oracle_context: RootV1,
    pub tau_profile: RootV1,
    pub verifier_registry: RootV1,
    pub max_oracle_age_blocks: u64,
    pub max_tau_age_blocks: u64,
    pub max_command_age_blocks: u64,
    pub observed_height: u64,
    pub oracle_height: u64,
    pub ledger_height: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GlobalCommandV1 {
    pub kind: GlobalCommandKindV1,
    pub command_id: RootV1,
    pub sender: RootV1,
    pub nonce: u64,
    pub asset_in: RootV1,
    pub asset_out: RootV1,
    pub amount_in_atoms: u128,
    pub amount_out_atoms: u128,
    pub fee_atoms: u128,
    pub auxiliary_root: RootV1,
}

impl GlobalCommandV1 {
    pub fn command_hash(&self) -> Result<RootV1, M6CoreError> {
        hash_postcard_v1(b"m6-global-command-v1", self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValueDeltaCertificateV1 {
    pub command_hash: RootV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub delta_atoms: i128,
    pub delta_root: RootV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistoryAtomV1 {
    pub sequence: u64,
    pub command_hash: RootV1,
    pub sender: RootV1,
    pub nonce: u64,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub outcome: BusinessStatusV1,
    pub value_delta_root: RootV1,
    pub nullifier: RootV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicationAtomV1 {
    pub candidate_id: RootV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub history_root: RootV1,
    pub nullifier_root: RootV1,
    pub value_delta_root: RootV1,
    pub outbox_root: RootV1,
    pub writer_epoch: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct M6ApplicationStateV1 {
    pub deployment: RootV1,
    pub head: RootV1,
    pub writer_epoch: u64,
    pub ingress_nonce: u64,
    pub economic_digest: RootV1,
    pub history_root: RootV1,
    pub nullifier_root: RootV1,
    pub outbox_root: RootV1,
}

impl M6ApplicationStateV1 {
    pub fn state_root(&self) -> Result<RootV1, M6CoreError> {
        hash_postcard_v1(b"m6-application-state-root-v1", self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TauBatchCertificateV1 {
    pub batch_id: RootV1,
    pub tau_profile_root: RootV1,
    pub ordered_command_hashes: Vec<RootV1>,
    pub ordered_nonce_identities: Vec<RootV1>,
    pub candidate_parent_head: RootV1,
    pub certificate_root: RootV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FinalityModeV1 {
    TauOrdered,
    FallbackForcedInclusion,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZenoLedgerFinalityCertificateV1 {
    pub finality_id: RootV1,
    pub candidate_head: RootV1,
    pub publication_root: RootV1,
    pub validator_set_root: RootV1,
    pub writer_epoch: u64,
    pub signer_ids: Vec<RootV1>,
    pub quorum: u8,
    pub mode: FinalityModeV1,
    pub signature_root: RootV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TauEscrowDepositProofV1 {
    pub deposit_id: RootV1,
    pub tau_transaction_root: RootV1,
    pub tau_finality_root: RootV1,
    pub tau_profile_root: RootV1,
    pub beneficiary: RootV1,
    pub asset: RootV1,
    pub amount_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TauWithdrawalStatusV1 {
    Pending,
    Acknowledged,
    Cancelled,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TauWithdrawalIntentV1 {
    pub withdrawal_id: RootV1,
    pub beneficiary: RootV1,
    pub asset: RootV1,
    pub amount_atoms: u128,
    pub source_state_root: RootV1,
    pub candidate_id: RootV1,
    pub status: TauWithdrawalStatusV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZRPFChunkStatementV1 {
    pub profile: RootV1,
    pub promotion_subject_root: RootV1,
    pub writer_epoch: u64,
    pub ordinal: u16,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub command_hashes: Vec<RootV1>,
    pub nonce_identities: Vec<RootV1>,
    pub value_delta_root: RootV1,
    pub history_root: RootV1,
    pub nullifier_root: RootV1,
    pub outbox_root: RootV1,
    pub verifier_image: RootV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZRPFRootJournalV1 {
    pub profile: RootV1,
    pub promotion_subject_root: RootV1,
    pub writer_epoch: u64,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub command_count: u16,
    pub chunk_statement_roots: Vec<RootV1>,
    pub aggregate_statement_roots: Vec<RootV1>,
    pub command_root: RootV1,
    pub nonce_root: RootV1,
    pub value_delta_root: RootV1,
    pub history_root: RootV1,
    pub nullifier_root: RootV1,
    pub outbox_root: RootV1,
    pub data_availability_root: RootV1,
    pub verifier_image: RootV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlobalOutcomeV1 {
    RejectNoCommit {
        reason: AdmissionRejectReasonV1,
        pre_state_root: RootV1,
        command_hash: RootV1,
    },
    AcceptCandidate {
        state: M6ApplicationStateV1,
        delta: ValueDeltaCertificateV1,
        history: HistoryAtomV1,
        publication: PublicationAtomV1,
        status: BusinessStatusV1,
        business_reject: Option<BusinessRejectReasonV1>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum M6CoreError {
    Encoding,
    InvalidInput,
}

pub fn run_m6_transition_v1(
    subject: &M6PromotionSubjectV1,
    state: &M6ApplicationStateV1,
    context: &AuthenticatedExecutionContextV1,
    command: &GlobalCommandV1,
) -> Result<GlobalOutcomeV1, M6CoreError> {
    let command_hash = command.command_hash()?;
    let pre_state_root = state.state_root()?;
    let reject =
        if context.deployment != subject.deployment || state.deployment != subject.deployment {
            Some(AdmissionRejectReasonV1::ContextDeploymentMismatch)
        } else if context.parent_head != state.head {
            Some(AdmissionRejectReasonV1::ContextParentHeadMismatch)
        } else if context.epoch != state.writer_epoch {
            Some(AdmissionRejectReasonV1::ContextEpochMismatch)
        } else if context.tau_profile != subject.tau_profile {
            Some(AdmissionRejectReasonV1::ContextTauProfileMismatch)
        } else if context.verifier_registry != subject.verifier {
            Some(AdmissionRejectReasonV1::ContextVerifierMismatch)
        } else if context.sender != command.sender {
            Some(AdmissionRejectReasonV1::SenderMismatch)
        } else if context.nonce != command.nonce
            || state
                .ingress_nonce
                .checked_add(1)
                .map_or(true, |next_nonce| command.nonce != next_nonce)
        {
            Some(AdmissionRejectReasonV1::NonceMismatch)
        } else {
            None
        };
    if let Some(reason) = reject {
        return Ok(GlobalOutcomeV1::RejectNoCommit {
            reason,
            pre_state_root,
            command_hash,
        });
    }

    let business_reject = if command.amount_in_atoms == 0 && command.amount_out_atoms == 0 {
        Some(BusinessRejectReasonV1::InvalidAmount)
    } else {
        None
    };
    let status = if business_reject.is_some() {
        BusinessStatusV1::RejectedCommitted
    } else {
        BusinessStatusV1::Accepted
    };
    let mut post_state = state.clone();
    post_state.ingress_nonce = command.nonce;
    post_state.head = hash_postcard_v1(
        b"m6-rust-candidate-head-v1",
        &(pre_state_root, command_hash),
    )?;
    let post_state_root = post_state.state_root()?;
    let delta_root = hash_postcard_v1(
        b"m6-value-delta-certificate-v1",
        &(
            command_hash,
            pre_state_root,
            post_state_root,
            command.amount_in_atoms,
        ),
    )?;
    let delta = ValueDeltaCertificateV1 {
        command_hash,
        pre_state_root,
        post_state_root,
        delta_atoms: if business_reject.is_some() {
            0
        } else {
            let amount_out =
                i128::try_from(command.amount_out_atoms).map_err(|_| M6CoreError::InvalidInput)?;
            let amount_in =
                i128::try_from(command.amount_in_atoms).map_err(|_| M6CoreError::InvalidInput)?;
            amount_out
                .checked_sub(amount_in)
                .ok_or(M6CoreError::InvalidInput)?
        },
        delta_root,
    };
    let nullifier = hash_postcard_v1(
        b"m6-ingress-nullifier-v1",
        &(command.sender, command.nonce, command_hash, pre_state_root),
    )?;
    let history = HistoryAtomV1 {
        sequence: 0,
        command_hash,
        sender: command.sender,
        nonce: command.nonce,
        pre_state_root,
        post_state_root,
        outcome: status,
        value_delta_root: delta_root,
        nullifier,
    };
    let publication = PublicationAtomV1 {
        candidate_id: hash_postcard_v1(
            b"m6-candidate-id-v1",
            &(command_hash, pre_state_root, post_state_root),
        )?,
        pre_state_root,
        post_state_root,
        history_root: hash_postcard_v1(b"m6-history-root-v1", &history)?,
        nullifier_root: hash_postcard_v1(b"m6-nullifier-root-v1", &nullifier)?,
        value_delta_root: delta_root,
        outbox_root: state.outbox_root,
        writer_epoch: post_state.writer_epoch,
    };
    Ok(GlobalOutcomeV1::AcceptCandidate {
        state: post_state,
        delta,
        history,
        publication,
        status,
        business_reject,
    })
}

pub fn verify_zrpf_root_v1(
    subject: &M6PromotionSubjectV1,
    journal: ZRPFRootJournalV1,
) -> Result<VerifiedZRPFRootV1, M6CoreError> {
    if journal.profile != hash_ascii(M6_ZRPF_PROFILE_V1)
        || journal.promotion_subject_root != hash_subject(subject)?
        || usize::from(journal.command_count) != M6_ZRPF_COMMAND_COUNT_V1
        || journal.chunk_statement_roots.len() != M6_ZRPF_LEAF_COUNT_V1
        || journal.aggregate_statement_roots.len() != M6_ZRPF_AGGREGATE_COUNT_V1
        || journal.verifier_image != subject.risc0_image
    {
        return Err(M6CoreError::InvalidInput);
    }
    Ok(VerifiedZRPFRootV1 { journal })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedZRPFRootV1 {
    journal: ZRPFRootJournalV1,
}

impl VerifiedZRPFRootV1 {
    pub fn journal(&self) -> &ZRPFRootJournalV1 {
        &self.journal
    }
}

fn hash_ascii(value: &str) -> RootV1 {
    let mut hasher = Sha256::new();
    hasher.update(value.as_bytes());
    hasher.finalize().into()
}

fn hash_subject(subject: &M6PromotionSubjectV1) -> Result<RootV1, M6CoreError> {
    hash_postcard_v1(b"m6-promotion-subject-v1", subject)
}

fn hash_postcard_v1<T: Serialize>(domain: &[u8], value: &T) -> Result<RootV1, M6CoreError> {
    let bytes = postcard::to_allocvec(value).map_err(|_| M6CoreError::Encoding)?;
    let mut hasher = Sha256::new();
    hasher.update(domain);
    let byte_length = u64::try_from(bytes.len()).map_err(|_| M6CoreError::Encoding)?;
    hasher.update(byte_length.to_be_bytes());
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}
