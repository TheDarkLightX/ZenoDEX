use sha2::{Digest, Sha256};

use super::{
    LaneModuleTransitionJournalErrorV1, LaneModuleTransitionJournalV1,
    LaneModuleTransitionOutcomeV1,
};
use crate::CommitmentV3;

const JOURNAL_HASH_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.lane_module_transition_journal.v1";

pub(super) fn journal_hash_v1(
    journal: &LaneModuleTransitionJournalV1,
) -> Result<CommitmentV3, LaneModuleTransitionJournalErrorV1> {
    let mut hasher = domain_hasher(JOURNAL_HASH_DOMAIN_V1)?;
    hasher.update(journal.journal_version().to_be_bytes());
    hasher.update(journal.application_id().as_bytes());
    hasher.update(journal.chain_or_domain_id().as_bytes());
    hasher.update(journal.profile_id().as_bytes());
    hasher.update(journal.writer_epoch().to_be_bytes());
    hasher.update(journal.occurrence_id().as_bytes());
    hasher.update(journal.route_release_id().as_bytes());
    hasher.update(journal.economic_action_id().as_bytes());
    hasher.update([journal.lane_id().code()]);
    hasher.update(journal.module_release_id().as_bytes());
    hasher.update(journal.guest_image_id().as_bytes());
    for root in [
        journal.state_schema_root(),
        journal.command_schema_root(),
        journal.effect_schema_root(),
        journal.private_port_schema_root(),
        journal.command_variants_root(),
        journal.spec_root(),
        journal.source_root(),
        journal.toolchain_root(),
        journal.receipt_journal_schema_root(),
        journal.input_port_schema_root(),
        journal.output_port_schema_root(),
    ] {
        update_commitment(&mut hasher, root);
    }
    hasher.update(journal.global_pre_state_root().as_bytes());
    update_commitment(&mut hasher, journal.lane_pre_state_root());
    let outcome = journal.outcome();
    hasher.update([outcome.kind_code()]);
    match outcome {
        LaneModuleTransitionOutcomeV1::Accepted(accepted) => {
            hasher.update(accepted.global_post_state_root().as_bytes());
            for root in [
                accepted.global_effect_plan_commitment(),
                accepted.lane_post_state_root(),
                accepted.lane_effect_rows_root(),
                accepted.state_transition_root(),
                accepted.private_input_ports_root(),
                accepted.private_output_ports_root(),
                accepted.terminal_obligations_root(),
            ] {
                update_commitment(&mut hasher, root);
            }
        }
        LaneModuleTransitionOutcomeV1::Rejected(code) => {
            hasher.update(code.get().to_be_bytes());
        }
    }
    CommitmentV3::new(hasher.finalize().into()).map_err(|_| {
        LaneModuleTransitionJournalErrorV1::InvalidDerivedCommitment("lane_journal_hash")
    })
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, LaneModuleTransitionJournalErrorV1> {
    let length = u16::try_from(domain.len()).map_err(|_| {
        LaneModuleTransitionJournalErrorV1::ArithmeticOverflow("journal_hash_domain")
    })?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn update_commitment(hasher: &mut Sha256, value: CommitmentV3) {
    hasher.update(value.as_bytes());
}
