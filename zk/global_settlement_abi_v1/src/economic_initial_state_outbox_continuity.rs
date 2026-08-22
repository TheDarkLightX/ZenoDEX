//! Deterministic outbox preservation for genesis and migration admission.

use serde::Serialize;

use crate::canonical::{
    hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};
use crate::economic_initial_state::EconomicInitialStateKindV1;
use crate::state::{GlobalEconomicStateV1, OutboxStateV1};

pub const MAX_INITIAL_STATE_OUTBOX_ROWS_V1: usize = 4_096;

#[derive(Serialize)]
struct EconomicInitialStateOutboxContinuityV1<'a> {
    schema: &'static str,
    kind: EconomicInitialStateKindV1,
    source_state_root: RootV1,
    target_state_root: RootV1,
    source_outbox: &'a [OutboxStateV1],
    target_outbox: &'a [OutboxStateV1],
}

pub fn validate_economic_initial_state_outbox_row_count_v1(
    state: &GlobalEconomicStateV1,
) -> AbiResultV1<usize> {
    if state.outbox.len() > MAX_INITIAL_STATE_OUTBOX_ROWS_V1 {
        return Err(AbiErrorV1::InvalidBounds("initial state outbox rows"));
    }
    Ok(state.outbox.len())
}

pub fn derive_economic_initial_state_outbox_continuity_root_v1(
    kind: EconomicInitialStateKindV1,
    target_state: &GlobalEconomicStateV1,
    predecessor_state: Option<&GlobalEconomicStateV1>,
) -> AbiResultV1<RootV1> {
    validate_economic_initial_state_outbox_row_count_v1(target_state)?;
    if let Some(predecessor) = predecessor_state {
        validate_economic_initial_state_outbox_row_count_v1(predecessor)?;
    }
    let target_state_root = target_state.state_root()?;
    let (source_state_root, source_outbox) = match (kind, predecessor_state) {
        (EconomicInitialStateKindV1::GENESIS, None) => {
            if !target_state.outbox.is_empty() {
                return Err(AbiErrorV1::InvalidBinding(
                    "genesis outbox state must be empty",
                ));
            }
            (
                RootV1::parse(ZERO_ROOT_V1, "genesis outbox source state root", true)?,
                &[][..],
            )
        }
        (EconomicInitialStateKindV1::GENESIS, Some(_)) => {
            return Err(AbiErrorV1::InvalidBinding("genesis outbox predecessor"));
        }
        (EconomicInitialStateKindV1::MIGRATION, None) => {
            return Err(AbiErrorV1::InvalidBinding("migration outbox predecessor"));
        }
        (EconomicInitialStateKindV1::MIGRATION, Some(predecessor)) => {
            let source_state_root = predecessor.state_root()?;
            if target_state.outbox != predecessor.outbox {
                return Err(AbiErrorV1::InvalidBinding(
                    "migration outbox predecessor preservation",
                ));
            }
            (source_state_root, predecessor.outbox.as_slice())
        }
    };
    let projection = EconomicInitialStateOutboxContinuityV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1,
        kind,
        source_state_root,
        target_state_root,
        source_outbox,
        target_outbox: &target_state.outbox,
    };
    hash_global_v1("economic-initial-state-outbox-continuity-v1", &projection)
}

pub fn validate_economic_initial_state_outbox_continuity_binding_v1(
    kind: EconomicInitialStateKindV1,
    target_state: &GlobalEconomicStateV1,
    predecessor_state: Option<&GlobalEconomicStateV1>,
    expected_root: &RootV1,
) -> AbiResultV1<()> {
    let actual_root = derive_economic_initial_state_outbox_continuity_root_v1(
        kind,
        target_state,
        predecessor_state,
    )?;
    if actual_root != *expected_root {
        return Err(AbiErrorV1::InvalidBinding(
            "initial state outbox continuity root",
        ));
    }
    Ok(())
}
