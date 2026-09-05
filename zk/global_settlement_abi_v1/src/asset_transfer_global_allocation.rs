//! Restricted global snapshot relation. Snapshot authenticity and store adjacency
//! are shell premises; receipt admission separately binds the private port.

use crate::asset_transfer_lane_module::AssetTransferLaneModuleAcceptedV1;
use crate::canonical::AbiResultV1;
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::LaneIdV1;
use crate::state::{GlobalEconomicStateV1, ReplayStateV1};

/// Caller-owned complete relation inputs; construction confers no authority.
pub struct AssetTransferGlobalAllocationCandidateV1<'a> {
    pub accepted: &'a AssetTransferLaneModuleAcceptedV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub predecessor: &'a GlobalEconomicStateV1,
    pub current: &'a GlobalEconomicStateV1,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GlobalAllocationBindingRejectCodeV1 {
    GLOBAL_CONTEXT_DRIFT,
    GLOBAL_OCCURRENCE_DRIFT,
    GLOBAL_LANE_SCOPE_UNSUPPORTED,
    GLOBAL_LANE_ROOT_DRIFT,
    GLOBAL_PROJECTION_ROWS_DRIFT,
    GLOBAL_CLAIMANT_CONTINUITY_DRIFT,
    GLOBAL_UNSUPPORTED_STATE,
    GLOBAL_REPLAY_CONTINUITY_DRIFT,
}

impl GlobalAllocationBindingRejectCodeV1 {
    pub const ALL: [Self; 8] = [
        Self::GLOBAL_CONTEXT_DRIFT,
        Self::GLOBAL_OCCURRENCE_DRIFT,
        Self::GLOBAL_LANE_SCOPE_UNSUPPORTED,
        Self::GLOBAL_LANE_ROOT_DRIFT,
        Self::GLOBAL_PROJECTION_ROWS_DRIFT,
        Self::GLOBAL_CLAIMANT_CONTINUITY_DRIFT,
        Self::GLOBAL_UNSUPPORTED_STATE,
        Self::GLOBAL_REPLAY_CONTINUITY_DRIFT,
    ];
}

pub(crate) fn global_allocation_binding_reject_v1(
    accepted: &AssetTransferLaneModuleAcceptedV1,
    occurrence: &EconomicCommandOccurrenceV1,
    predecessor: &GlobalEconomicStateV1,
    current: &GlobalEconomicStateV1,
) -> AbiResultV1<Option<GlobalAllocationBindingRejectCodeV1>> {
    use GlobalAllocationBindingRejectCodeV1::*;
    let journal = &accepted.module_journal;
    for state in [predecessor, current] {
        if state.chain_id != journal.chain_id
            || state.deployment_root != journal.deployment_root
            || state.profile_root != journal.profile_root
            || state.writer_epoch != journal.writer_epoch
        {
            return Ok(Some(GLOBAL_CONTEXT_DRIFT));
        }
    }
    if occurrence.chain_id != journal.chain_id
        || occurrence.deployment_root != journal.deployment_root
        || occurrence.profile_root != journal.profile_root
    {
        return Ok(Some(GLOBAL_CONTEXT_DRIFT));
    }
    if occurrence.occurrence_id()? != journal.command_occurrence_id
        || occurrence.pre_state_root != predecessor.state_root()?
        || occurrence.height != current.height
        || predecessor.height.checked_add(1) != Some(current.height)
    {
        return Ok(Some(GLOBAL_OCCURRENCE_DRIFT));
    }
    for state in [predecessor, current] {
        if state
            .lane_roots
            .iter()
            .filter(|row| row.enabled)
            .map(|row| row.lane_id)
            .ne([LaneIdV1::ASSET_TRANSFER])
            || state.lane_roots[0].module_release_id != journal.module_release_id
        {
            return Ok(Some(GLOBAL_LANE_SCOPE_UNSUPPORTED));
        }
    }
    if predecessor.lane_roots[1..] != current.lane_roots[1..] {
        return Ok(Some(GLOBAL_LANE_SCOPE_UNSUPPORTED));
    }
    for (state, projection) in [
        (predecessor, &accepted.private_port.pre_state),
        (current, &accepted.private_port.post_state),
    ] {
        if state.lane_roots[0].state_root != projection.state_root()? {
            return Ok(Some(GLOBAL_LANE_ROOT_DRIFT));
        }
        if state.balances != projection.balances
            || state.custody != projection.custody
            || state.supplies != projection.supplies
        {
            return Ok(Some(GLOBAL_PROJECTION_ROWS_DRIFT));
        }
    }
    if predecessor.liabilities != current.liabilities {
        return Ok(Some(GLOBAL_CLAIMANT_CONTINUITY_DRIFT));
    }
    if predecessor.custody != current.custody
        || predecessor.oracle_occurrences != current.oracle_occurrences
        || [predecessor, current].iter().any(|state| {
            !state.reserves.is_empty()
                || !state.outbox.is_empty()
                || !state.terminal_obligations.is_empty()
        })
    {
        return Ok(Some(GLOBAL_UNSUPPORTED_STATE));
    }
    let added = ReplayStateV1 {
        replay_id: occurrence.replay_id()?.as_str().to_owned(),
        occurrence_id: occurrence.occurrence_id()?,
    };
    let mut expected = predecessor.replay_state.clone();
    expected.push(added.clone());
    expected.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    if predecessor
        .replay_state
        .iter()
        .any(|row| row.replay_id == added.replay_id || row.occurrence_id == added.occurrence_id)
        || current.replay_state != expected
    {
        return Ok(Some(GLOBAL_REPLAY_CONTINUITY_DRIFT));
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn global_allocation_relation_matches_python_fixed_vectors() {
        let fixture: serde_json::Value = serde_json::from_str(include_str!(
            "../../../tests/data/asset_transfer_global_allocation_v1_golden.json"
        ))
        .expect("fixture JSON");
        let accepted: AssetTransferLaneModuleAcceptedV1 =
            serde_json::from_value(fixture["accepted"].clone()).expect("accepted input");
        accepted.validate().expect("accepted invariants");
        for case in fixture["cases"].as_array().expect("cases") {
            let occurrence: EconomicCommandOccurrenceV1 =
                serde_json::from_value(case["occurrence"].clone()).expect("occurrence");
            let predecessor: GlobalEconomicStateV1 =
                serde_json::from_value(case["predecessor"].clone()).expect("predecessor");
            let current: GlobalEconomicStateV1 =
                serde_json::from_value(case["current"].clone()).expect("current");
            occurrence.validate().expect("occurrence boundary");
            predecessor.validate().expect("predecessor boundary");
            current.validate().expect("current boundary");
            let result =
                global_allocation_binding_reject_v1(&accepted, &occurrence, &predecessor, &current)
                    .expect("relation boundary");
            let actual = result.map(|code| format!("{code:?}"));
            assert_eq!(
                actual.as_deref(),
                case["expected_code"].as_str(),
                "{}",
                case["name"]
            );
        }
    }
}
