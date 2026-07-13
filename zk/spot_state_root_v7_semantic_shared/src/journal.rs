use alloc::vec::Vec;

use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    compatibility_profile_id_v1, state_root_scheme_id_v5, RestrictedSpotStateRootV5BridgeFactsV1,
};

use crate::SpotStateRootV7SemanticErrorV1;

pub const SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_VERSION_V1: u16 = 1;

/// Version + profile/scheme + six commitments + sender + ingress nonce.
pub const SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1: usize = 2 + 8 * 32 + 48 + 4;

/// Exact proof-neutral V7 journal surface.
///
/// The six transition commitments are the four legacy source commitments and
/// the two ZenoLedger state-root-v5 commitments. Program identity and every
/// authority claim remain outside this journal.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::SpotStateRootV7SemanticJournalV1;
/// let journal: SpotStateRootV7SemanticJournalV1 = unimplemented!();
/// let _ = journal.settlement_authority();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::SpotStateRootV7SemanticJournalV1;
/// let journal: SpotStateRootV7SemanticJournalV1 = unimplemented!();
/// let _ = journal.actual_program_id();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpotStateRootV7SemanticJournalV1 {
    compatibility_profile_id: [u8; 32],
    state_root_scheme_id: [u8; 32],
    source_pre_app_hash: [u8; 32],
    source_post_app_hash: [u8; 32],
    source_pre_nonce_root: [u8; 32],
    source_post_nonce_root: [u8; 32],
    pre_state_root_v5: [u8; 32],
    post_state_root_v5: [u8; 32],
    sender_pubkey: [u8; 48],
    ingress_nonce: u32,
}

impl SpotStateRootV7SemanticJournalV1 {
    pub(crate) fn from_bridge_facts(facts: RestrictedSpotStateRootV5BridgeFactsV1) -> Self {
        Self {
            compatibility_profile_id: facts.compatibility_profile_id(),
            state_root_scheme_id: facts.state_root_scheme_id(),
            source_pre_app_hash: facts.source_pre_app_hash(),
            source_post_app_hash: facts.source_post_app_hash(),
            source_pre_nonce_root: facts.source_pre_nonce_root(),
            source_post_nonce_root: facts.source_post_nonce_root(),
            pre_state_root_v5: facts.pre_state_root_v5(),
            post_state_root_v5: facts.post_state_root_v5(),
            sender_pubkey: facts.sender_pubkey(),
            ingress_nonce: facts.ingress_nonce(),
        }
    }

    pub const fn compatibility_profile_id(&self) -> [u8; 32] {
        self.compatibility_profile_id
    }

    pub const fn state_root_scheme_id(&self) -> [u8; 32] {
        self.state_root_scheme_id
    }

    pub const fn source_pre_app_hash(&self) -> [u8; 32] {
        self.source_pre_app_hash
    }

    pub const fn source_post_app_hash(&self) -> [u8; 32] {
        self.source_post_app_hash
    }

    pub const fn source_pre_nonce_root(&self) -> [u8; 32] {
        self.source_pre_nonce_root
    }

    pub const fn source_post_nonce_root(&self) -> [u8; 32] {
        self.source_post_nonce_root
    }

    pub const fn pre_state_root_v5(&self) -> [u8; 32] {
        self.pre_state_root_v5
    }

    pub const fn post_state_root_v5(&self) -> [u8; 32] {
        self.post_state_root_v5
    }

    pub const fn sender_pubkey(&self) -> [u8; 48] {
        self.sender_pubkey
    }

    pub const fn ingress_nonce(&self) -> u32 {
        self.ingress_nonce
    }
}

pub fn encode_spot_state_root_v7_semantic_journal_v1(
    journal: &SpotStateRootV7SemanticJournalV1,
) -> Vec<u8> {
    let mut output = Vec::with_capacity(SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1);
    output.extend_from_slice(&SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_VERSION_V1.to_be_bytes());
    for commitment in [
        journal.compatibility_profile_id,
        journal.state_root_scheme_id,
        journal.source_pre_app_hash,
        journal.source_post_app_hash,
        journal.source_pre_nonce_root,
        journal.source_post_nonce_root,
        journal.pre_state_root_v5,
        journal.post_state_root_v5,
    ] {
        output.extend_from_slice(&commitment);
    }
    output.extend_from_slice(&journal.sender_pubkey);
    output.extend_from_slice(&journal.ingress_nonce.to_be_bytes());
    output
}

pub fn decode_exact_spot_state_root_v7_semantic_journal_v1(
    bytes: &[u8],
) -> Result<SpotStateRootV7SemanticJournalV1, SpotStateRootV7SemanticErrorV1> {
    if bytes.len() < SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1 {
        return Err(SpotStateRootV7SemanticErrorV1::Truncated("journal"));
    }
    if bytes.len() > SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1 {
        return Err(SpotStateRootV7SemanticErrorV1::TrailingBytes);
    }
    let mut cursor = JournalCursorV1::new(bytes);
    let version = cursor.read_u16("journal version")?;
    if version != SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_VERSION_V1 {
        return Err(SpotStateRootV7SemanticErrorV1::InvalidVersion(version));
    }
    let compatibility_profile_id = cursor.read_array("compatibility profile id")?;
    if compatibility_profile_id != compatibility_profile_id_v1() {
        return Err(SpotStateRootV7SemanticErrorV1::UnexpectedProfileId);
    }
    let state_root_scheme_id = cursor.read_array("state root scheme id")?;
    if state_root_scheme_id != state_root_scheme_id_v5() {
        return Err(SpotStateRootV7SemanticErrorV1::UnexpectedStateRootSchemeId);
    }
    let journal = SpotStateRootV7SemanticJournalV1 {
        compatibility_profile_id,
        state_root_scheme_id,
        source_pre_app_hash: cursor.read_array("source pre app hash")?,
        source_post_app_hash: cursor.read_array("source post app hash")?,
        source_pre_nonce_root: cursor.read_array("source pre nonce root")?,
        source_post_nonce_root: cursor.read_array("source post nonce root")?,
        pre_state_root_v5: cursor.read_array("pre state root v5")?,
        post_state_root_v5: cursor.read_array("post state root v5")?,
        sender_pubkey: cursor.read_array("sender pubkey")?,
        ingress_nonce: cursor.read_u32("ingress nonce")?,
    };
    if journal.ingress_nonce == 0 {
        return Err(SpotStateRootV7SemanticErrorV1::IngressNonceZero);
    }
    Ok(journal)
}

struct JournalCursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> JournalCursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(&mut self, field: &'static str) -> Result<u16, SpotStateRootV7SemanticErrorV1> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    fn read_u32(&mut self, field: &'static str) -> Result<u32, SpotStateRootV7SemanticErrorV1> {
        Ok(u32::from_be_bytes(self.read_array(field)?))
    }

    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], SpotStateRootV7SemanticErrorV1> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(SpotStateRootV7SemanticErrorV1::LengthOverflow(field))?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or(SpotStateRootV7SemanticErrorV1::Truncated(field))?;
        self.offset = end;
        bytes
            .try_into()
            .map_err(|_| SpotStateRootV7SemanticErrorV1::Truncated(field))
    }
}
