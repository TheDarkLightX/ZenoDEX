//! Registered-empty lane fragment producers (wave A: EXTERNAL_CUSTODY, PROOF_REWARDS).
//!
//! Twin of `src/core/global_accounting_lane_producers_v1.py`: a pure function of the
//! committed `LaneStateRootV1` that certifies a registered-empty lane is disabled and
//! committed at its unique empty typed state root, and returns the exact-empty fragment.
//! Research-only; no writer, verifier, release, or publication authority.

use serde::{Deserialize, Serialize};

use crate::canonical::RootV1;
use crate::global_accounting_allocation_certificate::{
    registered_empty_lane_root_v1, registry_entry_v1, ClaimantEntitlementRowV1,
    ControlledLocationRowV1, LaneAllocationFragmentV1, LaneProducerKindV1,
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
    if !registered_empty {
        return Err(reject(LaneProducerRejectCodeV1::LANE_NOT_REGISTERED_EMPTY));
    }
    // Opus P15 P3-2: never swallow the root computation error into a different reject code.
    // Python's equivalent failure is an import-time error; here it maps to the root-drift
    // code, and a unit test pins that both registered-empty lanes compute their root.
    let empty_root = match registered_empty_lane_root_v1(lane_root.lane_id) {
        Ok(Some(root)) => root,
        Ok(None) | Err(_) => {
            return Err(reject(
                LaneProducerRejectCodeV1::REGISTERED_EMPTY_ROOT_DRIFT,
            ));
        }
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

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ReceiptBackedProducerRejectCodeV1 {
    ACCEPTED_INVALID,
    JOURNAL_LANE_DRIFT,
    LANE_DISABLED,
    MODULE_RELEASE_DRIFT,
    JOURNAL_ROOT_DRIFT,
    STALE_JOURNAL,
    TERMINAL_ROOT_NOT_EMPTY,
    ENTITLEMENT_ROWS_NOT_CANONICAL,
    CONTROLLED_FOLD_OVERFLOW,
    ENTITLEMENT_COVERAGE_DRIFT,
}

impl ReceiptBackedProducerRejectCodeV1 {
    pub const ALL: [Self; 10] = [
        Self::ACCEPTED_INVALID,
        Self::JOURNAL_LANE_DRIFT,
        Self::LANE_DISABLED,
        Self::MODULE_RELEASE_DRIFT,
        Self::JOURNAL_ROOT_DRIFT,
        Self::STALE_JOURNAL,
        Self::TERMINAL_ROOT_NOT_EMPTY,
        Self::ENTITLEMENT_ROWS_NOT_CANONICAL,
        Self::CONTROLLED_FOLD_OVERFLOW,
        Self::ENTITLEMENT_COVERAGE_DRIFT,
    ];

    pub const fn code(self) -> &'static str {
        match self {
            Self::ACCEPTED_INVALID => "ACCEPTED_INVALID",
            Self::JOURNAL_LANE_DRIFT => "JOURNAL_LANE_DRIFT",
            Self::LANE_DISABLED => "LANE_DISABLED",
            Self::MODULE_RELEASE_DRIFT => "MODULE_RELEASE_DRIFT",
            Self::JOURNAL_ROOT_DRIFT => "JOURNAL_ROOT_DRIFT",
            Self::STALE_JOURNAL => "STALE_JOURNAL",
            Self::TERMINAL_ROOT_NOT_EMPTY => "TERMINAL_ROOT_NOT_EMPTY",
            Self::ENTITLEMENT_ROWS_NOT_CANONICAL => "ENTITLEMENT_ROWS_NOT_CANONICAL",
            Self::ENTITLEMENT_COVERAGE_DRIFT => "ENTITLEMENT_COVERAGE_DRIFT",
            Self::CONTROLLED_FOLD_OVERFLOW => "CONTROLLED_FOLD_OVERFLOW",
        }
    }

    pub const fn message(self) -> &'static str {
        match self {
            Self::ACCEPTED_INVALID => "accepted transition value fails its own validation",
            Self::JOURNAL_LANE_DRIFT => "journal and committed root name different lanes",
            Self::LANE_DISABLED => "receipt-backed production requires an enabled lane",
            Self::MODULE_RELEASE_DRIFT => {
                "journal module release differs from the committed lane release"
            }
            Self::JOURNAL_ROOT_DRIFT => "journal post root differs from the committed lane root",
            Self::STALE_JOURNAL => "journal pre root does not continue the prior fragment",
            Self::TERMINAL_ROOT_NOT_EMPTY => {
                "asset transfer journal must commit no terminal obligations"
            }
            Self::ENTITLEMENT_ROWS_NOT_CANONICAL => {
                "entitlement rows are not canonically ordered, unique, and nonzero"
            }
            Self::ENTITLEMENT_COVERAGE_DRIFT => {
                "entitlement rows do not cover the controlled atoms exactly"
            }
            Self::CONTROLLED_FOLD_OVERFLOW => {
                "controlled or entitlement fold exceeds the u128 ceiling"
            }
        }
    }
}

/// A receipt-backed producer refusal: nothing is produced, every input left unchanged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReceiptBackedProducerRejectedV1 {
    pub code: ReceiptBackedProducerRejectCodeV1,
    pub lane_id: LaneIdV1,
    pub committed_lane_root: RootV1,
    pub detail: String,
}

fn reject_receipt_backed(
    code: ReceiptBackedProducerRejectCodeV1,
    lane_id: LaneIdV1,
    committed_lane_root: &RootV1,
    detail: &str,
) -> ReceiptBackedProducerRejectedV1 {
    ReceiptBackedProducerRejectedV1 {
        code,
        lane_id,
        committed_lane_root: committed_lane_root.clone(),
        detail: detail.to_owned(),
    }
}

/// Fold one accepted asset-transfer transition into a receipt-bound lane fragment (wave B).
///
/// The Python authority is `produce_asset_transfer_fragment_v1` in
/// `src/core/global_accounting_lane_producers_v1.py`; the check order and reject
/// codes mirror it exactly. The controlled-side fold overflow is unreachable for
/// well-formed accepted inputs (supply conservation bounds custody totals); the
/// reachable path is the caller-provided entitlement rows. NONCLAIM: no verifier
/// admits the journal yet (C9); the certificate registry keeps ASSET_TRANSFER at
/// NO_PRODUCER until receipt admission exists. Research-only; authority NONE.
pub fn produce_asset_transfer_fragment_v1(
    accepted: &crate::asset_transfer_lane_module::AssetTransferLaneModuleAcceptedV1,
    lane_root: &LaneStateRootV1,
    prior_fragment: &LaneAllocationFragmentV1,
    claimant_entitlements: &[ClaimantEntitlementRowV1],
) -> Result<LaneAllocationFragmentV1, ReceiptBackedProducerRejectedV1> {
    use std::collections::BTreeMap;

    let committed = &lane_root.state_root;
    // Opus P17 follow-through: the Rust accepted value is a plain struct with no
    // construction-time validation (Python's __post_init__ has no Rust twin), so the
    // producer validates it first; defensively unreachable in Python, reachable here.
    if accepted.validate().is_err() {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::ACCEPTED_INVALID,
            lane_root.lane_id,
            committed,
            "accepted validation",
        ));
    }
    let journal = &accepted.module_journal;
    if journal.lane_id != LaneIdV1::ASSET_TRANSFER || lane_root.lane_id != LaneIdV1::ASSET_TRANSFER
    {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::JOURNAL_LANE_DRIFT,
            lane_root.lane_id,
            committed,
            &format!(
                "journal {:?} vs committed {:?}",
                journal.lane_id, lane_root.lane_id
            ),
        ));
    }
    if !lane_root.enabled {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::LANE_DISABLED,
            lane_root.lane_id,
            committed,
            "lane disabled",
        ));
    }
    if journal.module_release_id != lane_root.module_release_id {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::MODULE_RELEASE_DRIFT,
            lane_root.lane_id,
            committed,
            "module release",
        ));
    }
    if journal.post_lane_root != *committed {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::JOURNAL_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "post root",
        ));
    }
    if prior_fragment.lane_id != LaneIdV1::ASSET_TRANSFER {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL,
            lane_root.lane_id,
            committed,
            "prior lane",
        ));
    }
    if prior_fragment.module_release_id != lane_root.module_release_id {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL,
            lane_root.lane_id,
            committed,
            "prior release",
        ));
    }
    if journal.pre_lane_root != prior_fragment.lane_state_root {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL,
            lane_root.lane_id,
            committed,
            "pre root",
        ));
    }
    if !journal.terminal_obligations_root.is_zero() {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::TERMINAL_ROOT_NOT_EMPTY,
            lane_root.lane_id,
            committed,
            "terminal root",
        ));
    }
    let entitlement_keys: Vec<(&str, &str, &str)> = claimant_entitlements
        .iter()
        .map(|row| {
            (
                row.asset.as_str(),
                row.claimant.as_str(),
                row.control_domain.as_str(),
            )
        })
        .collect();
    let mut sorted_unique = entitlement_keys.clone();
    sorted_unique.sort_unstable();
    sorted_unique.dedup();
    if entitlement_keys != sorted_unique {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "entitlement ordering",
        ));
    }
    if claimant_entitlements
        .iter()
        .any(|row| row.amount_atoms == 0)
    {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "zero amount",
        ));
    }
    let mut controlled: BTreeMap<(String, String), u128> = BTreeMap::new();
    for row in &accepted.private_port.post_state.custody {
        let key = (row.asset.clone(), row.custody_domain.clone());
        let entry = controlled.entry(key).or_insert(0);
        *entry = match entry.checked_add(row.amount_atoms) {
            Some(total) => total,
            None => {
                return Err(reject_receipt_backed(
                    ReceiptBackedProducerRejectCodeV1::CONTROLLED_FOLD_OVERFLOW,
                    lane_root.lane_id,
                    committed,
                    "controlled",
                ));
            }
        };
    }
    let mut assigned: BTreeMap<(String, String), u128> = BTreeMap::new();
    for row in claimant_entitlements {
        let key = (row.asset.clone(), row.control_domain.clone());
        let entry = assigned.entry(key).or_insert(0);
        *entry = match entry.checked_add(row.amount_atoms) {
            Some(total) => total,
            None => {
                return Err(reject_receipt_backed(
                    ReceiptBackedProducerRejectCodeV1::CONTROLLED_FOLD_OVERFLOW,
                    lane_root.lane_id,
                    committed,
                    "entitlements",
                ));
            }
        };
    }
    if controlled != assigned {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_COVERAGE_DRIFT,
            lane_root.lane_id,
            committed,
            "coverage",
        ));
    }
    let fragment = LaneAllocationFragmentV1 {
        lane_id: lane_root.lane_id,
        module_release_id: lane_root.module_release_id.clone(),
        enabled: true,
        lane_state_root: committed.clone(),
        producer_kind: LaneProducerKindV1::RECEIPT_BACKED,
        binding_root: journal.receipt_root.clone(),
        controlled_locations: accepted
            .private_port
            .post_state
            .custody
            .iter()
            .map(|row| ControlledLocationRowV1 {
                asset: row.asset.clone(),
                controlling_principal: row.owner.clone(),
                control_domain: row.custody_domain.clone(),
                amount_atoms: row.amount_atoms,
            })
            .collect(),
        claimant_entitlements: claimant_entitlements.to_vec(),
        unencumbered_reserves: Vec::new(),
        pending_external_obligations: Vec::new(),
        terminal_bindings: Vec::new(),
    };
    // Opus P17 P2-4: Rust has no __post_init__, so validate explicitly before returning;
    // the twins must agree on accept-vs-refuse for every input class.
    if fragment.validate().is_err() {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "fragment validation",
        ));
    }
    Ok(fragment)
}

#[cfg(test)]
mod tests {
    #[test]
    fn registered_empty_lane_roots_are_available() {
        use crate::global_accounting_allocation_certificate::registered_empty_lane_root_v1;
        use crate::release::LaneIdV1;
        // Pins Opus P15 P3-2's error path unreachable: both registered-empty lanes compute a root.
        for lane in [LaneIdV1::EXTERNAL_CUSTODY, LaneIdV1::PROOF_REWARDS] {
            let root = registered_empty_lane_root_v1(lane).expect("root computes");
            assert!(root.is_some(), "{lane:?} must have a registered-empty root");
        }
    }
}
