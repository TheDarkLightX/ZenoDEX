//! Deterministic terminal-obligation preservation for initial-state admission.

use serde::Serialize;

use crate::canonical::{
    hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};
use crate::economic_initial_state::EconomicInitialStateKindV1;
use crate::economic_initial_state_atom_coverage::validate_economic_initial_state_explicit_row_count_v1;
use crate::state::{GlobalEconomicStateV1, TerminalObligationV1};

#[derive(Serialize)]
struct EconomicInitialStateTerminalContinuityV1<'a> {
    schema: &'static str,
    kind: EconomicInitialStateKindV1,
    source_state_root: RootV1,
    target_state_root: RootV1,
    source_terminal_obligations: &'a [TerminalObligationV1],
    target_terminal_obligations: &'a [TerminalObligationV1],
}

pub fn derive_economic_initial_state_terminal_continuity_root_v1(
    kind: EconomicInitialStateKindV1,
    target_state: &GlobalEconomicStateV1,
    predecessor_state: Option<&GlobalEconomicStateV1>,
) -> AbiResultV1<RootV1> {
    validate_economic_initial_state_explicit_row_count_v1(target_state)?;
    if let Some(predecessor) = predecessor_state {
        validate_economic_initial_state_explicit_row_count_v1(predecessor)?;
    }
    let target_state_root = target_state.state_root()?;
    let (source_state_root, source_terminal_obligations) = match (kind, predecessor_state) {
        (EconomicInitialStateKindV1::GENESIS, None) => (
            RootV1::parse(ZERO_ROOT_V1, "genesis terminal source state root", true)?,
            &[][..],
        ),
        (EconomicInitialStateKindV1::GENESIS, Some(_)) => {
            return Err(AbiErrorV1::InvalidBinding("genesis terminal predecessor"));
        }
        (EconomicInitialStateKindV1::MIGRATION, None) => {
            return Err(AbiErrorV1::InvalidBinding("migration terminal predecessor"));
        }
        (EconomicInitialStateKindV1::MIGRATION, Some(predecessor)) => {
            let source_state_root = predecessor.state_root()?;
            if target_state.terminal_obligations != predecessor.terminal_obligations {
                return Err(AbiErrorV1::InvalidBinding(
                    "migration terminal predecessor preservation",
                ));
            }
            (
                source_state_root,
                predecessor.terminal_obligations.as_slice(),
            )
        }
    };
    let projection = EconomicInitialStateTerminalContinuityV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1,
        kind,
        source_state_root,
        target_state_root,
        source_terminal_obligations,
        target_terminal_obligations: &target_state.terminal_obligations,
    };
    hash_global_v1("economic-initial-state-terminal-continuity-v1", &projection)
}

pub fn validate_economic_initial_state_terminal_continuity_binding_v1(
    kind: EconomicInitialStateKindV1,
    target_state: &GlobalEconomicStateV1,
    predecessor_state: Option<&GlobalEconomicStateV1>,
    expected_root: &RootV1,
) -> AbiResultV1<()> {
    let actual_root = derive_economic_initial_state_terminal_continuity_root_v1(
        kind,
        target_state,
        predecessor_state,
    )?;
    if actual_root != *expected_root {
        return Err(AbiErrorV1::InvalidBinding(
            "initial state terminal continuity root",
        ));
    }
    Ok(())
}
