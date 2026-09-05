//! Restricted global snapshot relation. Snapshot authenticity and store adjacency
//! are shell premises; receipt admission separately binds the private port.

use crate::asset_transfer_lane_module::AssetTransferLaneModuleAcceptedV1;
use crate::canonical::{AbiErrorV1, AbiResultV1, MAX_EPOCH_COMMANDS_V1};
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

/// Data only. Source authenticity and previous-pair association belong to the
/// consuming epoch fold; an index is never an authority witness.
pub struct AssetTransferEpochPositionV1<'a> {
    pub epoch_source: &'a GlobalEconomicStateV1,
    pub occurrence_index: usize,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum GlobalAllocationHeightModeV1 {
    AdjacentState,
    EpochPosition,
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

/// Diagnose the complete restricted relation after validating all four inputs.
/// `Ok(None)` conveys no receipt, snapshot, claimant or publication authority.
/// Guests must separately verify every proof assumption they rely on.
pub fn check_asset_transfer_global_allocation_v1(
    candidate: AssetTransferGlobalAllocationCandidateV1<'_>,
) -> AbiResultV1<Option<GlobalAllocationBindingRejectCodeV1>> {
    let AssetTransferGlobalAllocationCandidateV1 {
        accepted,
        occurrence,
        predecessor,
        current,
    } = candidate;
    accepted.validate()?;
    occurrence.validate()?;
    predecessor.validate()?;
    current.validate()?;
    global_allocation_binding_reject_v1(
        accepted,
        occurrence,
        predecessor,
        current,
        GlobalAllocationHeightModeV1::AdjacentState,
    )
}

/// Check an explicit epoch position without changing either global state root.
/// The caller must associate every later predecessor with the checked prefix.
pub fn check_asset_transfer_epoch_allocation_v1(
    candidate: AssetTransferGlobalAllocationCandidateV1<'_>,
    position: AssetTransferEpochPositionV1<'_>,
) -> AbiResultV1<Option<GlobalAllocationBindingRejectCodeV1>> {
    use GlobalAllocationBindingRejectCodeV1::*;
    let AssetTransferGlobalAllocationCandidateV1 {
        accepted,
        occurrence,
        predecessor,
        current,
    } = candidate;
    accepted.validate()?;
    occurrence.validate()?;
    predecessor.validate()?;
    current.validate()?;
    let source = position.epoch_source;
    source.validate()?;
    if position.occurrence_index >= MAX_EPOCH_COMMANDS_V1 {
        return Err(AbiErrorV1::InvalidBinding("epoch position index"));
    }
    let journal = &accepted.module_journal;
    if source.chain_id != journal.chain_id
        || source.deployment_root != journal.deployment_root
        || source.profile_root != journal.profile_root
        || source.writer_epoch != journal.writer_epoch
        || occurrence.chain_id != journal.chain_id
        || occurrence.deployment_root != journal.deployment_root
        || occurrence.profile_root != journal.profile_root
    {
        return Ok(Some(GLOBAL_CONTEXT_DRIFT));
    }
    let Some(target_height) = source.height.checked_add(1) else {
        return Ok(Some(GLOBAL_OCCURRENCE_DRIFT));
    };
    let expected_prior = if position.occurrence_index == 0 {
        source.height
    } else {
        target_height
    };
    if occurrence.height != target_height
        || current.height != target_height
        || predecessor.height != expected_prior
        || (position.occurrence_index == 0 && predecessor != source)
    {
        return Ok(Some(GLOBAL_OCCURRENCE_DRIFT));
    }
    global_allocation_binding_reject_v1(
        accepted,
        occurrence,
        predecessor,
        current,
        GlobalAllocationHeightModeV1::EpochPosition,
    )
}

pub(crate) fn global_allocation_binding_reject_v1(
    accepted: &AssetTransferLaneModuleAcceptedV1,
    occurrence: &EconomicCommandOccurrenceV1,
    predecessor: &GlobalEconomicStateV1,
    current: &GlobalEconomicStateV1,
    height_mode: GlobalAllocationHeightModeV1,
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
        || (height_mode == GlobalAllocationHeightModeV1::AdjacentState
            && predecessor.height.checked_add(1) != Some(current.height))
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
        || predecessor.history_root != current.history_root
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
    use crate::canonical::{AbiErrorV1, MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1};

    fn fixture() -> serde_json::Value {
        serde_json::from_str(include_str!(
            "../../../tests/data/asset_transfer_global_allocation_v1_golden.json"
        ))
        .expect("fixture JSON")
    }

    fn valid_inputs() -> (
        AssetTransferLaneModuleAcceptedV1,
        EconomicCommandOccurrenceV1,
        GlobalEconomicStateV1,
        GlobalEconomicStateV1,
    ) {
        let fixture = fixture();
        let case = fixture["cases"]
            .as_array()
            .expect("cases")
            .iter()
            .find(|case| case["expected_code"].is_null())
            .expect("accepted relation case");
        (
            serde_json::from_value(fixture["accepted"].clone()).expect("accepted"),
            serde_json::from_value(case["occurrence"].clone()).expect("occurrence"),
            serde_json::from_value(case["predecessor"].clone()).expect("predecessor"),
            serde_json::from_value(case["current"].clone()).expect("current"),
        )
    }

    #[test]
    fn global_allocation_relation_matches_python_fixed_vectors() {
        let fixture = fixture();
        let accepted: AssetTransferLaneModuleAcceptedV1 =
            serde_json::from_value(fixture["accepted"].clone()).expect("accepted input");
        for case in fixture["cases"].as_array().expect("cases") {
            let occurrence: EconomicCommandOccurrenceV1 =
                serde_json::from_value(case["occurrence"].clone()).expect("occurrence");
            let predecessor: GlobalEconomicStateV1 =
                serde_json::from_value(case["predecessor"].clone()).expect("predecessor");
            let current: GlobalEconomicStateV1 =
                serde_json::from_value(case["current"].clone()).expect("current");
            let result = crate::check_asset_transfer_global_allocation_v1(
                AssetTransferGlobalAllocationCandidateV1 {
                    accepted: &accepted,
                    occurrence: &occurrence,
                    predecessor: &predecessor,
                    current: &current,
                },
            )
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

    #[test]
    fn global_allocation_relation_accepts_nonzero_history_bound_before_occurrence() {
        let fixture = fixture();
        let case = &fixture["nonzero_history"];
        let accepted: AssetTransferLaneModuleAcceptedV1 =
            serde_json::from_value(case["accepted"].clone()).expect("rebuilt accepted input");
        let occurrence: EconomicCommandOccurrenceV1 =
            serde_json::from_value(case["occurrence"].clone()).expect("rebuilt occurrence");
        let predecessor: GlobalEconomicStateV1 =
            serde_json::from_value(case["predecessor"].clone()).expect("nonzero predecessor");
        let current: GlobalEconomicStateV1 =
            serde_json::from_value(case["current"].clone()).expect("nonzero current");
        let (_, baseline_occurrence, _, _) = valid_inputs();
        assert_eq!(predecessor.history_root, current.history_root);
        assert_eq!(
            predecessor.history_root.as_str(),
            format!("0x{}", "de".repeat(32))
        );
        assert_eq!(occurrence.pre_state_root, predecessor.state_root().unwrap());
        assert_ne!(
            occurrence.occurrence_id(),
            baseline_occurrence.occurrence_id()
        );
        assert_eq!(
            accepted.module_journal.command_occurrence_id,
            occurrence.occurrence_id().unwrap()
        );
        assert_eq!(
            crate::check_asset_transfer_global_allocation_v1(
                AssetTransferGlobalAllocationCandidateV1 {
                    accepted: &accepted,
                    occurrence: &occurrence,
                    predecessor: &predecessor,
                    current: &current,
                },
            ),
            Ok(None),
        );
    }

    #[test]
    fn global_allocation_relation_validates_every_boundary_in_existing_order() {
        let (accepted, occurrence, predecessor, current) = valid_inputs();
        let mut changed_accepted = accepted.clone();
        let mut changed_occurrence = occurrence.clone();
        let mut changed_predecessor = predecessor.clone();
        let mut changed_current = current.clone();
        changed_accepted.post_state.schema.clear();
        changed_occurrence.chain_id.clear();
        changed_predecessor.lane_roots.clear();
        changed_current.chain_id.clear();
        let expected = [
            AbiErrorV1::InvalidSchema,
            AbiErrorV1::InvalidToken("occurrence chain id"),
            AbiErrorV1::InvalidOrder("global state lane roots"),
            AbiErrorV1::InvalidToken("global state chain id"),
        ];
        for (index, error) in expected.into_iter().enumerate() {
            assert_eq!(
                crate::check_asset_transfer_global_allocation_v1(
                    AssetTransferGlobalAllocationCandidateV1 {
                        accepted: &changed_accepted,
                        occurrence: &changed_occurrence,
                        predecessor: &changed_predecessor,
                        current: &changed_current,
                    },
                ),
                Err(error),
            );
            match index {
                0 => changed_accepted = accepted.clone(),
                1 => changed_occurrence = occurrence.clone(),
                2 => changed_predecessor = predecessor.clone(),
                3 => changed_current = current.clone(),
                _ => unreachable!("four boundary cases"),
            }
        }
        assert_eq!(
            crate::check_asset_transfer_global_allocation_v1(
                AssetTransferGlobalAllocationCandidateV1 {
                    accepted: &changed_accepted,
                    occurrence: &changed_occurrence,
                    predecessor: &changed_predecessor,
                    current: &changed_current,
                },
            ),
            Ok(None),
        );
    }

    #[test]
    fn global_allocation_relation_refuses_oversized_tables_before_partial_projection() {
        let (accepted, occurrence, predecessor, mut current) = valid_inputs();
        current.balances.resize(
            MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1 + 1,
            current.balances[0].clone(),
        );
        assert_eq!(
            crate::check_asset_transfer_global_allocation_v1(
                AssetTransferGlobalAllocationCandidateV1 {
                    accepted: &accepted,
                    occurrence: &occurrence,
                    predecessor: &predecessor,
                    current: &current,
                },
            ),
            Err(AbiErrorV1::InvalidBounds("global state balances")),
        );
        assert_eq!(
            current.balances.len(),
            MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1 + 1
        );
    }
}
