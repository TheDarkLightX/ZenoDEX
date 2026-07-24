use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, EconomicActionIdV1};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    compatibility_profile_id_v1, state_root_scheme_id_v5,
};

use crate::SpotSettlementV7EffectBindingErrorV1;

const BINDING_JOURNAL_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1";

pub const SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_VERSION_V1: u16 = 1;

/// Version followed by twelve exact 32-byte fields.
pub const SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1: usize = 2 + 12 * 32;

/// Fixed proof-neutral journal for a future receipt-bearing V7 guest.
///
/// Decode proves exact framing and governed profile identities only. It does
/// not establish that a guest derived the effect plan or state openings.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::SpotSettlementV7EffectBindingJournalV1;
/// let journal: SpotSettlementV7EffectBindingJournalV1 = unimplemented!();
/// let _ = journal.settlement_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpotSettlementV7EffectBindingJournalV1 {
    compatibility_profile_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    source_journal_commitment: CommitmentV3,
    source_settlement_plan_commitment: CommitmentV3,
    settlement_effect_plan_commitment: CommitmentV3,
    cell_transitions_root: CommitmentV3,
    pre_state_root: CommitmentV3,
    post_state_root: CommitmentV3,
    economic_action_id: EconomicActionIdV1,
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
    public_policy_hash: CommitmentV3,
}

pub(crate) struct SpotSettlementV7EffectBindingJournalInputV1 {
    pub compatibility_profile_id: CommitmentV3,
    pub state_root_scheme_id: CommitmentV3,
    pub source_journal_commitment: CommitmentV3,
    pub source_settlement_plan_commitment: CommitmentV3,
    pub settlement_effect_plan_commitment: CommitmentV3,
    pub cell_transitions_root: CommitmentV3,
    pub pre_state_root: CommitmentV3,
    pub post_state_root: CommitmentV3,
    pub economic_action_id: EconomicActionIdV1,
    pub action_semantics_hash: CommitmentV3,
    pub effect_commitment: CommitmentV3,
    pub public_policy_hash: CommitmentV3,
}

impl SpotSettlementV7EffectBindingJournalV1 {
    pub(crate) fn new(
        input: SpotSettlementV7EffectBindingJournalInputV1,
    ) -> Result<Self, SpotSettlementV7EffectBindingErrorV1> {
        let journal = Self {
            compatibility_profile_id: input.compatibility_profile_id,
            state_root_scheme_id: input.state_root_scheme_id,
            source_journal_commitment: input.source_journal_commitment,
            source_settlement_plan_commitment: input.source_settlement_plan_commitment,
            settlement_effect_plan_commitment: input.settlement_effect_plan_commitment,
            cell_transitions_root: input.cell_transitions_root,
            pre_state_root: input.pre_state_root,
            post_state_root: input.post_state_root,
            economic_action_id: input.economic_action_id,
            action_semantics_hash: input.action_semantics_hash,
            effect_commitment: input.effect_commitment,
            public_policy_hash: input.public_policy_hash,
        };
        journal.validate_profile()?;
        Ok(journal)
    }

    fn validate_profile(&self) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
        if self.compatibility_profile_id.as_bytes() != &compatibility_profile_id_v1() {
            return Err(SpotSettlementV7EffectBindingErrorV1::UnexpectedCompatibilityProfile);
        }
        if self.state_root_scheme_id.as_bytes() != &state_root_scheme_id_v5() {
            return Err(SpotSettlementV7EffectBindingErrorV1::UnexpectedStateRootScheme);
        }
        Ok(())
    }

    pub const fn compatibility_profile_id(&self) -> CommitmentV3 {
        self.compatibility_profile_id
    }

    pub const fn state_root_scheme_id(&self) -> CommitmentV3 {
        self.state_root_scheme_id
    }

    pub const fn source_journal_commitment(&self) -> CommitmentV3 {
        self.source_journal_commitment
    }

    pub const fn source_settlement_plan_commitment(&self) -> CommitmentV3 {
        self.source_settlement_plan_commitment
    }

    pub const fn settlement_effect_plan_commitment(&self) -> CommitmentV3 {
        self.settlement_effect_plan_commitment
    }

    pub const fn cell_transitions_root(&self) -> CommitmentV3 {
        self.cell_transitions_root
    }

    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.pre_state_root
    }

    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.post_state_root
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }

    pub const fn action_semantics_hash(&self) -> CommitmentV3 {
        self.action_semantics_hash
    }

    pub const fn effect_commitment(&self) -> CommitmentV3 {
        self.effect_commitment
    }

    pub const fn public_policy_hash(&self) -> CommitmentV3 {
        self.public_policy_hash
    }

    pub fn canonical_commitment(
        &self,
    ) -> Result<CommitmentV3, SpotSettlementV7EffectBindingErrorV1> {
        let bytes = encode_spot_settlement_v7_effect_binding_journal_v1(self);
        let mut hasher = Sha256::new();
        let length = u16::try_from(BINDING_JOURNAL_COMMITMENT_DOMAIN_V1.len()).map_err(|_| {
            SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("binding_journal_domain")
        })?;
        hasher.update(length.to_be_bytes());
        hasher.update(BINDING_JOURNAL_COMMITMENT_DOMAIN_V1);
        hasher.update(bytes);
        CommitmentV3::new(hasher.finalize().into())
            .map_err(|_| SpotSettlementV7EffectBindingErrorV1::DerivedCommitment("binding_journal"))
    }
}

pub fn encode_spot_settlement_v7_effect_binding_journal_v1(
    journal: &SpotSettlementV7EffectBindingJournalV1,
) -> Vec<u8> {
    let mut output = Vec::with_capacity(SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1);
    output.extend_from_slice(&SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_VERSION_V1.to_be_bytes());
    for field in [
        journal.compatibility_profile_id.into_bytes(),
        journal.state_root_scheme_id.into_bytes(),
        journal.source_journal_commitment.into_bytes(),
        journal.source_settlement_plan_commitment.into_bytes(),
        journal.settlement_effect_plan_commitment.into_bytes(),
        journal.cell_transitions_root.into_bytes(),
        journal.pre_state_root.into_bytes(),
        journal.post_state_root.into_bytes(),
        journal.economic_action_id.into_bytes(),
        journal.action_semantics_hash.into_bytes(),
        journal.effect_commitment.into_bytes(),
        journal.public_policy_hash.into_bytes(),
    ] {
        output.extend_from_slice(&field);
    }
    output
}

pub fn decode_exact_spot_settlement_v7_effect_binding_journal_v1(
    bytes: &[u8],
) -> Result<SpotSettlementV7EffectBindingJournalV1, SpotSettlementV7EffectBindingErrorV1> {
    if bytes.len() != SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1 {
        return Err(SpotSettlementV7EffectBindingErrorV1::JournalLength {
            actual: bytes.len(),
            expected: SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1,
        });
    }
    let mut cursor = CursorV1::new(bytes);
    let version = cursor.read_u16()?;
    if version != SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_VERSION_V1 {
        return Err(SpotSettlementV7EffectBindingErrorV1::InvalidJournalVersion(
            version,
        ));
    }
    SpotSettlementV7EffectBindingJournalV1::new(SpotSettlementV7EffectBindingJournalInputV1 {
        compatibility_profile_id: CommitmentV3::new(cursor.read_array()?)?,
        state_root_scheme_id: CommitmentV3::new(cursor.read_array()?)?,
        source_journal_commitment: CommitmentV3::new(cursor.read_array()?)?,
        source_settlement_plan_commitment: CommitmentV3::new(cursor.read_array()?)?,
        settlement_effect_plan_commitment: CommitmentV3::new(cursor.read_array()?)?,
        cell_transitions_root: CommitmentV3::new(cursor.read_array()?)?,
        pre_state_root: CommitmentV3::new(cursor.read_array()?)?,
        post_state_root: CommitmentV3::new(cursor.read_array()?)?,
        economic_action_id: EconomicActionIdV1::new(cursor.read_array()?)
            .map_err(|_| SpotSettlementV7EffectBindingErrorV1::DerivedCommitment("action"))?,
        action_semantics_hash: CommitmentV3::new(cursor.read_array()?)?,
        effect_commitment: CommitmentV3::new(cursor.read_array()?)?,
        public_policy_hash: CommitmentV3::new(cursor.read_array()?)?,
    })
}

struct CursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(&mut self) -> Result<u16, SpotSettlementV7EffectBindingErrorV1> {
        Ok(u16::from_be_bytes(self.read_array()?))
    }

    fn read_array<const N: usize>(
        &mut self,
    ) -> Result<[u8; N], SpotSettlementV7EffectBindingErrorV1> {
        let end = self.offset.checked_add(N).ok_or(
            SpotSettlementV7EffectBindingErrorV1::ArithmeticOverflow("journal_cursor"),
        )?;
        let value = self.bytes.get(self.offset..end).ok_or(
            SpotSettlementV7EffectBindingErrorV1::JournalLength {
                actual: self.bytes.len(),
                expected: SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1,
            },
        )?;
        self.offset = end;
        value
            .try_into()
            .map_err(|_| SpotSettlementV7EffectBindingErrorV1::JournalLength {
                actual: self.bytes.len(),
                expected: SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1,
            })
    }
}
