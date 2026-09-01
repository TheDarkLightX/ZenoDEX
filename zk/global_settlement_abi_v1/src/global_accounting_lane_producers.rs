//! Registered-empty lane fragment producers (wave A: EXTERNAL_CUSTODY, PROOF_REWARDS).
//!
//! Twin of `src/core/global_accounting_lane_producers_v1.py`: a pure function of the
//! committed `LaneStateRootV1` that certifies a registered-empty lane is disabled and
//! committed at its unique empty typed state root, and returns the exact-empty fragment.
//! Research-only; no writer, verifier, release, or publication authority.

use serde::{Deserialize, Serialize};

use crate::canonical::RootV1;
use crate::global_accounting_allocation_certificate::{
    registered_empty_lane_root_v1, registry_entry_v1, LaneAllocationFragmentV1, LaneProducerKindV1,
};
use crate::release::LaneIdV1;
use crate::state::LaneStateRootV1;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
#[allow(non_camel_case_types)]
pub enum LaneProducerRejectCodeV1 {
    LANE_NOT_REGISTERED_EMPTY,
    LANE_ENABLED,
    REGISTERED_EMPTY_ROOT_DRIFT,
}

impl LaneProducerRejectCodeV1 {
    pub const ALL: [Self; 3] = [
        Self::LANE_NOT_REGISTERED_EMPTY,
        Self::LANE_ENABLED,
        Self::REGISTERED_EMPTY_ROOT_DRIFT,
    ];

    pub const fn code(self) -> &'static str {
        match self {
            Self::LANE_NOT_REGISTERED_EMPTY => "LANE_NOT_REGISTERED_EMPTY",
            Self::LANE_ENABLED => "LANE_ENABLED",
            Self::REGISTERED_EMPTY_ROOT_DRIFT => "REGISTERED_EMPTY_ROOT_DRIFT",
        }
    }

    pub const fn message(self) -> &'static str {
        match self {
            Self::LANE_NOT_REGISTERED_EMPTY => "lane has no registered-empty producer",
            Self::LANE_ENABLED => "registered-empty lane is enabled",
            Self::REGISTERED_EMPTY_ROOT_DRIFT => {
                "committed lane root is not the empty lane state root"
            }
        }
    }
}

/// A producer refusal: nothing is produced and the committed lane root is echoed unchanged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LaneProducerRejectedV1 {
    pub code: LaneProducerRejectCodeV1,
    pub lane_id: LaneIdV1,
    pub committed_lane_root: RootV1,
}

/// Produce the exact-empty fragment of a registered-empty lane from its committed root.
pub fn produce_registered_empty_fragment_v1(
    lane_root: &LaneStateRootV1,
) -> Result<LaneAllocationFragmentV1, LaneProducerRejectedV1> {
    let reject = |code: LaneProducerRejectCodeV1| LaneProducerRejectedV1 {
        code,
        lane_id: lane_root.lane_id,
        committed_lane_root: lane_root.state_root.clone(),
    };
    let (registered_kind, _) = registry_entry_v1(lane_root.lane_id);
    let registered_empty = matches!(
        registered_kind,
        LaneProducerKindV1::REGISTERED_EMPTY_DISABLED
            | LaneProducerKindV1::REGISTERED_EMPTY_BLOCKED
    );
    let empty_root = registered_empty_lane_root_v1(lane_root.lane_id)
        .ok()
        .flatten();
    let Some(empty_root) = (if registered_empty { empty_root } else { None }) else {
        return Err(reject(LaneProducerRejectCodeV1::LANE_NOT_REGISTERED_EMPTY));
    };
    if lane_root.enabled {
        return Err(reject(LaneProducerRejectCodeV1::LANE_ENABLED));
    }
    if lane_root.state_root != empty_root {
        return Err(reject(
            LaneProducerRejectCodeV1::REGISTERED_EMPTY_ROOT_DRIFT,
        ));
    }
    Ok(LaneAllocationFragmentV1 {
        lane_id: lane_root.lane_id,
        module_release_id: lane_root.module_release_id.clone(),
        enabled: false,
        lane_state_root: lane_root.state_root.clone(),
        producer_kind: registered_kind,
        binding_root: lane_root.state_root.clone(),
        controlled_locations: Vec::new(),
        claimant_entitlements: Vec::new(),
        unencumbered_reserves: Vec::new(),
        pending_external_obligations: Vec::new(),
        terminal_bindings: Vec::new(),
    })
}
