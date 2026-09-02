//! Lane fragment producers: registered-empty (wave A) and receipt-backed (wave B).
//!
//! Twin of `src/core/global_accounting_lane_producers_v1.py`. Wave A
//! (EXTERNAL_CUSTODY, PROOF_REWARDS): a pure function of the committed
//! `LaneStateRootV1` returning the exact-empty fragment or a closed reject. Wave B
//! (ASSET_TRANSFER): `produce_asset_transfer_fragment_v1` folds one accepted
//! lane-module transition into a receipt-bound fragment. The producer trusts its
//! caller for `accepted`; the Python authority admits fragments one layer up in
//! `asset_transfer_receipt_admission_v1` (C9a: module witness, exact-typed
//! snapshot, producer re-run), which has no Rust twin yet (an open gap for C9b),
//! and the certificate registry keeps ASSET_TRANSFER at NO_PRODUCER, so no
//! acceptance path uses these fragments until C9b.
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
    FRAGMENT_INVALID,
}

impl ReceiptBackedProducerRejectCodeV1 {
    pub const ALL: [Self; 11] = [
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
        Self::FRAGMENT_INVALID,
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
            Self::CONTROLLED_FOLD_OVERFLOW => "CONTROLLED_FOLD_OVERFLOW",
            Self::ENTITLEMENT_COVERAGE_DRIFT => "ENTITLEMENT_COVERAGE_DRIFT",
            Self::FRAGMENT_INVALID => "FRAGMENT_INVALID",
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
            Self::FRAGMENT_INVALID => "the assembled fragment fails its own validation",
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
/// `src/core/global_accounting_lane_producers_v1.py`. The shared check order and
/// reject codes are pinned across both languages by the gated family test; the
/// languages differ in where accepted-value invariants live (Python validates at
/// construction, Rust validates here at check 0), so the same malformed bytes can
/// fail construction in Python and `ACCEPTED_INVALID` here. The controlled-side
/// fold overflow is unreachable for well-formed accepted inputs (supply
/// conservation bounds custody totals); the reachable reject path is the
/// caller-provided entitlement rows. NONCLAIM: this producer trusts its caller for
/// `accepted` and covers claimant entitlements only per (asset, control_domain)
/// total; the Python admission (`asset_transfer_receipt_admission_v1`, C9a) takes
/// the module witness and re-runs the producer on an exact-typed snapshot, and has
/// no Rust twin yet; the certificate registry keeps ASSET_TRANSFER at NO_PRODUCER
/// until C9b. Research-only; authority NONE.
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
    // producer validates it first. In Python this is unreachable through construction
    // (__post_init__ validates; only object.__new__ forgery bypasses it); reachable here.
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
    if prior_fragment.producer_kind != LaneProducerKindV1::RECEIPT_BACKED {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL,
            lane_root.lane_id,
            committed,
            "prior kind",
        ));
    }
    if !prior_fragment.enabled {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::STALE_JOURNAL,
            lane_root.lane_id,
            committed,
            "prior disabled",
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
    if claimant_entitlements.len()
        > crate::global_accounting_allocation_certificate::MAX_FRAGMENT_ROWS_V1
    {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "row ceiling",
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
        controlled_locations: {
            let mut rows: Vec<ControlledLocationRowV1> = accepted
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
                .collect();
            // The module input's custody key (asset, owner, domain) equals the fragment's
            // controlled key (asset, principal, domain), so a validated input arrives in
            // fragment order already; the re-sort is defensive (order-independent fold).
            rows.sort_by(|a, b| {
                (&a.asset, &a.controlling_principal, &a.control_domain).cmp(&(
                    &b.asset,
                    &b.controlling_principal,
                    &b.control_domain,
                ))
            });
            rows
        },
        claimant_entitlements: claimant_entitlements.to_vec(),
        unencumbered_reserves: Vec::new(),
        pending_external_obligations: Vec::new(),
        terminal_bindings: Vec::new(),
    };
    // Opus P17 P2-4 + P18 P2-D: Rust has no __post_init__, so validate explicitly before
    // returning; with the ceilings and canonical checks above this is defensive totality,
    // and it carries its own code rather than mislabelling entitlement canonicality.
    if fragment.validate().is_err() {
        return Err(reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1::FRAGMENT_INVALID,
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
    fn terminal_root_check_is_reachable_with_a_fully_rebound_accepted_value() {
        // Opus P18 P2-C: the reachable TERMINAL_ROOT_NOT_EMPTY path, pinned exactly. Port and
        // journal both carry the nonzero terminal root, the private-port root is rebound, and
        // the receipt root is recomputed, so accepted.validate() passes and no earlier gate
        // can fire.
        use crate::asset_transfer_lane_module::{
            receipt_root, transition_asset_transfer_lane_module_v1, AssetTransferLaneModuleInputV1,
            AssetTransferLaneModuleResultV1, ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
        };
        use crate::asset_transfer_types::{
            AssetTransferCommandV1, AssetTransferContextV1, AssetTransferPolicyV1,
            AssetTransferStateV1, ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
        };
        use crate::canonical::RootV1;
        use crate::global_accounting_allocation_certificate::{
            ClaimantEntitlementRowV1, LaneAllocationFragmentV1, LaneProducerKindV1,
        };
        use crate::release::LaneIdV1;
        use crate::state::{AssetSupplyV1, EconomicAmountV1, LaneStateRootV1};

        let root =
            |v: u64| RootV1::parse(format!("0x{v:064x}"), "test root", false).expect("root parses");
        let input = AssetTransferLaneModuleInputV1 {
            schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
            context: AssetTransferContextV1 {
                chain_id: "zeno-asset-test".to_owned(),
                deployment_root: root(1),
                profile_root: root(2),
                writer_epoch: 7,
                module_release_id: root(3),
                command_occurrence_id: root(4),
                subject_id: "alice".to_owned(),
                grant_root: root(5),
            },
            pre_state: AssetTransferStateV1 {
                schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
                module_release_id: root(3),
                policies: vec![AssetTransferPolicyV1 {
                    asset: "USD".to_owned(),
                    fee_owner: "treasury".to_owned(),
                    transfer_fee_atoms: 2,
                    enabled: true,
                }],
                balances: vec![
                    EconomicAmountV1 {
                        owner: "alice".to_owned(),
                        asset: "USD".to_owned(),
                        custody_domain: "accounts".to_owned(),
                        amount_atoms: 100,
                    },
                    EconomicAmountV1 {
                        owner: "bob".to_owned(),
                        asset: "USD".to_owned(),
                        custody_domain: "accounts".to_owned(),
                        amount_atoms: 15,
                    },
                ],
                supplies: vec![AssetSupplyV1 {
                    asset: "USD".to_owned(),
                    amount_atoms: 120,
                }],
            },
            command: AssetTransferCommandV1 {
                command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
                asset: "USD".to_owned(),
                sender: "alice".to_owned(),
                recipient: "bob".to_owned(),
                amount_atoms: 30,
                max_fee_atoms: 2,
            },
            asset_policy_registry_root: root(11),
            fee_policy_registry_root: root(12),
            custody: vec![EconomicAmountV1 {
                owner: "pool-a".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "spot-pool".to_owned(),
                amount_atoms: 5,
            }],
        };
        let result =
            transition_asset_transfer_lane_module_v1(&input).expect("transition evaluates");
        let AssetTransferLaneModuleResultV1::Accepted(accepted) = result else {
            panic!("transition accepts")
        };
        let mut accepted = *accepted;
        accepted.private_port.terminal_obligations_root = root(7);
        accepted.module_journal.terminal_obligations_root = root(7);
        accepted.module_journal.private_port_root =
            accepted.private_port.port_root().expect("port root");
        accepted.module_journal.receipt_root = receipt_root(
            &accepted.statement_root,
            &accepted.module_journal,
            &accepted.private_port,
            &accepted.effects,
        )
        .expect("receipt root");
        assert!(
            accepted.validate().is_ok(),
            "rebound accepted must validate"
        );
        let lane_root = LaneStateRootV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            module_release_id: root(3),
            enabled: true,
            state_root: accepted.module_journal.post_lane_root.clone(),
        };
        let prior = LaneAllocationFragmentV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            module_release_id: root(3),
            enabled: true,
            lane_state_root: accepted.module_journal.pre_lane_root.clone(),
            producer_kind: LaneProducerKindV1::RECEIPT_BACKED,
            binding_root: accepted.module_journal.pre_lane_root.clone(),
            controlled_locations: Vec::new(),
            claimant_entitlements: Vec::new(),
            unencumbered_reserves: Vec::new(),
            pending_external_obligations: Vec::new(),
            terminal_bindings: Vec::new(),
        };
        let entitlements = vec![ClaimantEntitlementRowV1 {
            asset: "USD".to_owned(),
            claimant: "alice".to_owned(),
            control_domain: "spot-pool".to_owned(),
            amount_atoms: 5,
        }];
        let reject =
            super::produce_asset_transfer_fragment_v1(&accepted, &lane_root, &prior, &entitlements)
                .expect_err("nonzero terminal root rejects");
        assert_eq!(
            reject.code,
            super::ReceiptBackedProducerRejectCodeV1::TERMINAL_ROOT_NOT_EMPTY
        );
        assert_eq!(reject.detail, "terminal root");
    }

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
