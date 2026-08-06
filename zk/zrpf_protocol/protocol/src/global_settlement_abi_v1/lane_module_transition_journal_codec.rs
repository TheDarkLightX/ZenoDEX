use alloc::vec::Vec;

use super::{
    LaneModuleTransitionJournalErrorV1, LaneModuleTransitionJournalV1,
    MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1,
};

pub fn encode_lane_module_transition_journal_v1(
    journal: &LaneModuleTransitionJournalV1,
) -> Result<Vec<u8>, LaneModuleTransitionJournalErrorV1> {
    journal.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(journal)
        .map_err(|_| LaneModuleTransitionJournalErrorV1::PostcardDecode)?;
    require_bounded(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_lane_module_transition_journal_v1(
    bytes: &[u8],
) -> Result<LaneModuleTransitionJournalV1, LaneModuleTransitionJournalErrorV1> {
    require_bounded(bytes.len())?;
    let (journal, remainder) = postcard::take_from_bytes::<LaneModuleTransitionJournalV1>(bytes)
        .map_err(|_| LaneModuleTransitionJournalErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(LaneModuleTransitionJournalErrorV1::TrailingBytes);
    }
    if encode_lane_module_transition_journal_v1(&journal)?.as_slice() != bytes {
        return Err(LaneModuleTransitionJournalErrorV1::NonCanonicalEncoding);
    }
    Ok(journal)
}

fn require_bounded(size: usize) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    if size == 0 {
        return Err(LaneModuleTransitionJournalErrorV1::EmptyInput);
    }
    if size > MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1 {
        return Err(LaneModuleTransitionJournalErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1,
        });
    }
    Ok(())
}
