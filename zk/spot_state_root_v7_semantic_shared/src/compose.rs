use alloc::string::String;

use tau_state_proof_risc0_shared::{DexSnapshotV1, NonceEntryV1};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    verify_restricted_spot_state_root_v5_transition_v1, ExpectedLegacySpotCommitmentsV1,
    ExpectedSpotStateRootsV5, RestrictedSpotStateRootV5ProfileV1,
    RestrictedSpotStateRootV5TransitionInputV1,
};

use crate::{
    BoundedSpotStateRootV7HostInputV1, SpotStateRootV7SemanticErrorV1,
    SpotStateRootV7SemanticJournalV1,
};

/// Source-side projection a future guest must derive only after verifying its
/// governed V6 child and authenticating the child's full-blob replay opening.
/// This proof-neutral type does not authenticate either step.
pub struct LegacySpotSourceProjectionV7<'a> {
    pre_state: &'a DexSnapshotV1,
    sender_pubkey: &'a str,
    ingress_nonce: u64,
    expected_commitments: ExpectedLegacySpotCommitmentsV1,
}

impl<'a> LegacySpotSourceProjectionV7<'a> {
    pub const fn new(
        pre_state: &'a DexSnapshotV1,
        sender_pubkey: &'a str,
        ingress_nonce: u64,
        expected_commitments: ExpectedLegacySpotCommitmentsV1,
    ) -> Self {
        Self {
            pre_state,
            sender_pubkey,
            ingress_nonce,
            expected_commitments,
        }
    }
}

/// Compose the exact proof-neutral V7 journal after the caller has obtained the
/// source projection from a verified child and its authenticated replay blob.
///
/// The function name documents a caller obligation. This kernel performs no
/// receipt verification and grants no source, receipt, or settlement authority.
pub fn compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
    source: &LegacySpotSourceProjectionV7<'_>,
    host: &BoundedSpotStateRootV7HostInputV1,
) -> Result<SpotStateRootV7SemanticJournalV1, SpotStateRootV7SemanticErrorV1> {
    let pre_nonces = [NonceEntryV1 {
        pubkey: String::from(source.sender_pubkey),
        next_nonce: source.ingress_nonce,
    }];
    let facts = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            source.pre_state,
            host.post_state(),
            &pre_nonces,
            source.sender_pubkey,
            source.ingress_nonce,
            source.expected_commitments,
            ExpectedSpotStateRootsV5::new(
                host.expected_pre_state_root_v5(),
                host.expected_post_state_root_v5(),
            ),
        ),
    )?;
    Ok(SpotStateRootV7SemanticJournalV1::from_bridge_facts(facts))
}
