//! Deterministic replay-row preservation for genesis and migration admission.

use serde::Serialize;

use crate::canonical::{
    hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};
use crate::economic_initial_state::EconomicInitialStateKindV1;
use crate::state::{GlobalEconomicStateV1, ReplayStateV1};

#[derive(Serialize)]
struct EconomicInitialStateReplayContinuityV1<'a> {
    schema: &'static str,
    kind: EconomicInitialStateKindV1,
    source_state_root: RootV1,
    target_state_root: RootV1,
    source_replay_state: &'a [ReplayStateV1],
    target_replay_state: &'a [ReplayStateV1],
}

pub fn derive_economic_initial_state_replay_continuity_root_v1(
    kind: EconomicInitialStateKindV1,
    target_state: &GlobalEconomicStateV1,
    predecessor_state: Option<&GlobalEconomicStateV1>,
) -> AbiResultV1<RootV1> {
    let target_state_root = target_state.state_root()?;
    let (source_state_root, source_replay_state) = match (kind, predecessor_state) {
        (EconomicInitialStateKindV1::GENESIS, None) => {
            if !target_state.replay_state.is_empty() {
                return Err(AbiErrorV1::InvalidBinding(
                    "genesis replay state must be empty",
                ));
            }
            (
                RootV1::parse(ZERO_ROOT_V1, "genesis replay source state root", true)?,
                &[][..],
            )
        }
        (EconomicInitialStateKindV1::GENESIS, Some(_)) => {
            return Err(AbiErrorV1::InvalidBinding("genesis replay predecessor"));
        }
        (EconomicInitialStateKindV1::MIGRATION, None) => {
            return Err(AbiErrorV1::InvalidBinding("migration replay predecessor"));
        }
        (EconomicInitialStateKindV1::MIGRATION, Some(predecessor)) => {
            let source_state_root = predecessor.state_root()?;
            if target_state.replay_state != predecessor.replay_state {
                return Err(AbiErrorV1::InvalidBinding(
                    "migration replay predecessor preservation",
                ));
            }
            (source_state_root, predecessor.replay_state.as_slice())
        }
    };
    let projection = EconomicInitialStateReplayContinuityV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1,
        kind,
        source_state_root,
        target_state_root,
        source_replay_state,
        target_replay_state: &target_state.replay_state,
    };
    hash_global_v1("economic-initial-state-replay-continuity-v1", &projection)
}

pub fn validate_economic_initial_state_replay_continuity_binding_v1(
    kind: EconomicInitialStateKindV1,
    target_state: &GlobalEconomicStateV1,
    predecessor_state: Option<&GlobalEconomicStateV1>,
    expected_root: &RootV1,
) -> AbiResultV1<()> {
    let actual_root = derive_economic_initial_state_replay_continuity_root_v1(
        kind,
        target_state,
        predecessor_state,
    )?;
    if actual_root != *expected_root {
        return Err(AbiErrorV1::InvalidBinding(
            "initial state replay continuity root",
        ));
    }
    Ok(())
}
