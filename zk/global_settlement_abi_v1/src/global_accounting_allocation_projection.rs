//! Pure allocation projection of the currently registered V1 public surface.
//!
//! Mirrors `src/core/global_accounting_allocation_projection_v1.py`: at most one
//! enabled receipt-backed lane owns the custody and liability rows. All reserves,
//! pending external obligations and open terminals on that lane are refused before
//! row derivation. The Python private hypothetical external/terminal search helpers
//! are therefore outside this implementation; no search is truncated or guessed.
//! The shared fixture pins these producer assumptions and all reachable row refusals.
//!
//! Inputs are immutable borrowed values. A successful projection is caller-constructible
//! data, not verified authority: it authenticates neither a store snapshot nor a receipt,
//! and establishes neither claimant authorization nor predecessor continuity. No
//! publisher or guest is mounted here. Authority: NONE.

use std::collections::{BTreeMap, BTreeSet};

use crate::asset_transfer_receipt_admission::VerifiedLaneAllocationFragmentV1;
use crate::canonical::{AbiErrorV1, AbiResultV1, RootV1};
use crate::global_accounting_allocation_certificate::{
    derive_allocation_root_v1, derive_canonical_allocation_rows_v1, derive_field_ownership_root_v1,
    derive_terminal_binding_root_v1, registered_empty_lane_root_v1, registry_entry_v1,
    ChainContextV1, ClaimantEntitlementRowV1, ControlledLocationRowV1,
    GlobalAccountingAllocationCertificateV1, LaneAllocationFragmentV1, LaneProducerKindV1,
    ReserveInterpretationV1, GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1,
};
use crate::release::{LaneIdV1, ALL_LANE_IDS_V1};
use crate::state::{
    GlobalEconomicStateV1, LaneStateRootV1, OutboxStatusV1, TerminalObligationStatusV1,
};

pub const ALLOCATION_PROJECTION_SCHEMA_V1: &str =
    "zenodex/global-accounting-allocation-projection/v1";

/// The complete Python family, including private helper codes that the current
/// public producer gates make unreachable. Declaration order is not check order.
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationProjectionRejectCodeV1 {
    PROJECTION_MULTIPLE_ENABLED_LANES,
    PROJECTION_BINDING_ROOT_UNEXPECTED,
    PROJECTION_BINDING_ROOT_MISSING,
    PROJECTION_NO_LANE_FOR_ROWS,
    PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
    PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
    PROJECTION_NEGATIVE_RESIDUAL,
    PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
    PROJECTION_PENDING_WITHOUT_BACKING,
    PROJECTION_ROWS_BEYOND_PRODUCER,
    PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT,
    PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
    PROJECTION_ROW_TOTAL_OVERFLOW,
    PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER,
    PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT,
    PROJECTION_TERMINAL_WITHOUT_BACKING,
    PROJECTION_WITNESS_FRAGMENT_DRIFT,
    PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED,
    PROJECTION_TERMINAL_ASSIGNMENT_UNSEARCHED,
    PROJECTION_WITNESS_HEADER_DRIFT,
    PROJECTION_WITNESS_REQUIRED,
    PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW,
    PROJECTION_WITNESS_UNEXPECTED,
}

impl AllocationProjectionRejectCodeV1 {
    pub const ALL: [Self; 23] = [
        Self::PROJECTION_MULTIPLE_ENABLED_LANES,
        Self::PROJECTION_BINDING_ROOT_UNEXPECTED,
        Self::PROJECTION_BINDING_ROOT_MISSING,
        Self::PROJECTION_NO_LANE_FOR_ROWS,
        Self::PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
        Self::PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
        Self::PROJECTION_NEGATIVE_RESIDUAL,
        Self::PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
        Self::PROJECTION_PENDING_WITHOUT_BACKING,
        Self::PROJECTION_ROWS_BEYOND_PRODUCER,
        Self::PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT,
        Self::PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
        Self::PROJECTION_ROW_TOTAL_OVERFLOW,
        Self::PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER,
        Self::PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT,
        Self::PROJECTION_TERMINAL_WITHOUT_BACKING,
        Self::PROJECTION_WITNESS_FRAGMENT_DRIFT,
        Self::PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED,
        Self::PROJECTION_TERMINAL_ASSIGNMENT_UNSEARCHED,
        Self::PROJECTION_WITNESS_HEADER_DRIFT,
        Self::PROJECTION_WITNESS_REQUIRED,
        Self::PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW,
        Self::PROJECTION_WITNESS_UNEXPECTED,
    ];
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AllocationProjectionRejectedV1 {
    pub code: AllocationProjectionRejectCodeV1,
    pub detail: String,
    pub state_root: RootV1,
}

enum ProjectionError {
    Boundary(AbiErrorV1),
    Semantic(AllocationProjectionRejectCodeV1, String),
}

impl From<AbiErrorV1> for ProjectionError {
    fn from(value: AbiErrorV1) -> Self {
        Self::Boundary(value)
    }
}

type ProjectionResult<T> = Result<T, ProjectionError>;
use AllocationProjectionRejectCodeV1 as Code;

fn reject(code: Code, detail: impl Into<String>) -> ProjectionError {
    ProjectionError::Semantic(code, detail.into())
}

fn owning_lane(state: &GlobalEconomicStateV1) -> ProjectionResult<Option<&LaneStateRootV1>> {
    let enabled: Vec<_> = state
        .lane_roots
        .iter()
        .filter(|root| root.enabled)
        .collect();
    if enabled.len() > 1 {
        return Err(reject(
            Code::PROJECTION_MULTIPLE_ENABLED_LANES,
            enabled
                .iter()
                .map(|root| format!("{:?}", root.lane_id))
                .collect::<Vec<_>>()
                .join(","),
        ));
    }
    let owner = enabled.first().copied();
    if let Some(root) = owner {
        let (kind, blocked_on) = registry_entry_v1(root.lane_id);
        if kind != LaneProducerKindV1::RECEIPT_BACKED {
            return Err(reject(
                Code::PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER,
                format!("{:?} is enabled with {kind:?} ({blocked_on})", root.lane_id),
            ));
        }
    }
    for root in &state.lane_roots {
        if registered_empty_lane_root_v1(root.lane_id)?
            .is_some_and(|expected| root.state_root != expected)
        {
            return Err(reject(
                Code::PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT,
                format!("{:?}", root.lane_id),
            ));
        }
    }
    Ok(owner)
}

fn binding_roots(
    supplied: &[(LaneIdV1, RootV1)],
    owner: Option<&LaneStateRootV1>,
) -> ProjectionResult<BTreeMap<LaneIdV1, RootV1>> {
    let mut roots = BTreeMap::new();
    for (lane, root) in supplied {
        root.validate("lane binding root", false)?;
        if roots.insert(*lane, root.clone()).is_some() {
            return Err(AbiErrorV1::InvalidOrder(
                "lane binding roots must name each lane at most once",
            )
            .into());
        }
    }
    for (lane, _) in supplied {
        if owner.map(|root| root.lane_id) != Some(*lane) {
            return Err(reject(
                Code::PROJECTION_BINDING_ROOT_UNEXPECTED,
                format!("{lane:?}"),
            ));
        }
    }
    if let Some(root) = owner {
        if !roots.contains_key(&root.lane_id) {
            return Err(reject(
                Code::PROJECTION_BINDING_ROOT_MISSING,
                format!("{:?}", root.lane_id),
            ));
        }
    }
    Ok(roots)
}

fn check_row_families(
    state: &GlobalEconomicStateV1,
    owner: Option<&LaneStateRootV1>,
) -> ProjectionResult<()> {
    let pending = state
        .outbox
        .iter()
        .any(|row| row.status == OutboxStatusV1::PENDING);
    let open = state
        .terminal_obligations
        .iter()
        .any(|row| row.status == TerminalObligationStatusV1::OPEN);
    let Some(root) = owner else {
        if !state.custody.is_empty()
            || !state.liabilities.is_empty()
            || !state.reserves.is_empty()
            || pending
            || open
        {
            return Err(reject(
                Code::PROJECTION_NO_LANE_FOR_ROWS,
                "economic rows with every lane disabled",
            ));
        }
        return Ok(());
    };
    // Every enabled producer reaching this point is receipt-backed. This explicit
    // row-family gate must also hold for any future registry addition.
    let beyond: Vec<_> = [
        ("reserves", !state.reserves.is_empty()),
        ("pending external obligations", pending),
        ("open terminal obligations", open),
    ]
    .into_iter()
    .filter_map(|(name, present)| present.then_some(name))
    .collect();
    if !beyond.is_empty() {
        return Err(reject(
            Code::PROJECTION_ROWS_BEYOND_PRODUCER,
            format!("{:?} carries {}", root.lane_id, beyond.join(", ")),
        ));
    }
    Ok(())
}

fn check_partition(state: &GlobalEconomicStateV1) -> ProjectionResult<()> {
    let mut remaining = BTreeMap::new();
    for row in &state.custody {
        let key = (row.asset.as_str(), row.custody_domain.as_str());
        let total = remaining
            .get(&key)
            .copied()
            .unwrap_or(0u128)
            .checked_add(row.amount_atoms)
            .ok_or_else(|| {
                reject(
                    Code::PROJECTION_ROW_TOTAL_OVERFLOW,
                    format!("controlled totals for {}:{}", key.0, key.1),
                )
            })?;
        remaining.insert(key, total);
    }
    let controlled_keys: BTreeSet<_> = remaining.keys().copied().collect();
    let mut claim_keys = BTreeSet::new();
    let mut negative = BTreeSet::new();
    for row in &state.liabilities {
        let key = (row.asset.as_str(), row.custody_domain.as_str());
        claim_keys.insert(key);
        let residual = remaining.entry(key).or_insert(0);
        if let Some(value) = residual.checked_sub(row.amount_atoms) {
            *residual = value;
        } else {
            // Python uses arbitrary signed integers here. Once negative, later
            // subtractions cannot recover; retain the sign separately so a huge
            // liability fold yields NEGATIVE_RESIDUAL, without a false u128 overflow.
            negative.insert(key);
        }
    }
    for (key, amount) in &remaining {
        if *amount == 0
            && !negative.contains(key)
            && controlled_keys.contains(key) != claim_keys.contains(key)
        {
            return Err(reject(
                Code::PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW,
                format!("zero support for {}:{} on one side only", key.0, key.1),
            ));
        }
    }
    if let Some(key) = negative.first() {
        return Err(reject(
            Code::PROJECTION_NEGATIVE_RESIDUAL,
            format!(
                "entitlements and reserves exceed custody for {}:{}",
                key.0, key.1
            ),
        ));
    }
    let open_cells = remaining.values().filter(|amount| **amount > 0).count();
    if open_cells > 0 {
        return Err(reject(
            Code::PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
            format!("{open_cells} residual cells for 0 pending obligations"),
        ));
    }
    Ok(())
}

fn fragments(
    state: &GlobalEconomicStateV1,
    owner: Option<&LaneStateRootV1>,
    roots: &BTreeMap<LaneIdV1, RootV1>,
) -> Vec<LaneAllocationFragmentV1> {
    state
        .lane_roots
        .iter()
        .map(|root| {
            let owns_rows = owner.map(|item| item.lane_id) == Some(root.lane_id);
            LaneAllocationFragmentV1 {
                lane_id: root.lane_id,
                module_release_id: root.module_release_id.clone(),
                enabled: root.enabled,
                lane_state_root: root.state_root.clone(),
                producer_kind: registry_entry_v1(root.lane_id).0,
                binding_root: roots.get(&root.lane_id).unwrap_or(&root.state_root).clone(),
                controlled_locations: if owns_rows {
                    state
                        .custody
                        .iter()
                        .map(|row| ControlledLocationRowV1 {
                            asset: row.asset.clone(),
                            controlling_principal: row.owner.clone(),
                            control_domain: row.custody_domain.clone(),
                            amount_atoms: row.amount_atoms,
                        })
                        .collect()
                } else {
                    Vec::new()
                },
                claimant_entitlements: if owns_rows {
                    state
                        .liabilities
                        .iter()
                        .map(|row| ClaimantEntitlementRowV1 {
                            asset: row.asset.clone(),
                            claimant: row.owner.clone(),
                            control_domain: row.custody_domain.clone(),
                            amount_atoms: row.amount_atoms,
                        })
                        .collect()
                } else {
                    Vec::new()
                },
                unencumbered_reserves: Vec::new(),
                pending_external_obligations: Vec::new(),
                terminal_bindings: Vec::new(),
            }
        })
        .collect()
}

fn check_witnesses(
    state: &GlobalEconomicStateV1,
    fragments: &[LaneAllocationFragmentV1],
    witnesses: &[Option<&VerifiedLaneAllocationFragmentV1>],
) -> ProjectionResult<()> {
    for (index, fragment) in fragments.iter().enumerate() {
        let witness = witnesses.get(index).copied().flatten();
        let required = fragment.enabled
            && registry_entry_v1(fragment.lane_id).0 == LaneProducerKindV1::RECEIPT_BACKED;
        match witness {
            Some(_) if !required => {
                return Err(reject(
                    Code::PROJECTION_WITNESS_UNEXPECTED,
                    format!("{:?} carries a witness it must not", fragment.lane_id),
                ))
            }
            None if required => {
                return Err(reject(
                    Code::PROJECTION_WITNESS_REQUIRED,
                    format!(
                        "{:?} is enabled and receipt-backed with an empty slot",
                        fragment.lane_id
                    ),
                ))
            }
            None => continue,
            Some(witness) => {
                if witness.fragment() != fragment {
                    return Err(reject(
                        Code::PROJECTION_WITNESS_FRAGMENT_DRIFT,
                        format!("{:?} differs from its minted witness", fragment.lane_id),
                    ));
                }
                if witness.chain_id() != state.chain_id
                    || witness.deployment_root() != &state.deployment_root
                    || witness.profile_root() != &state.profile_root
                    || witness.writer_epoch() != state.writer_epoch
                {
                    return Err(reject(
                        Code::PROJECTION_WITNESS_HEADER_DRIFT,
                        format!(
                            "{:?} witness header differs from the state",
                            fragment.lane_id
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn project(
    state: &GlobalEconomicStateV1,
    state_root: &RootV1,
    supplied_roots: &[(LaneIdV1, RootV1)],
    witnesses: &[Option<&VerifiedLaneAllocationFragmentV1>],
) -> ProjectionResult<GlobalAccountingAllocationCertificateV1> {
    let owner = owning_lane(state)?;
    let roots = binding_roots(supplied_roots, owner)?;
    check_row_families(state, owner)?;
    if owner.is_some() {
        check_partition(state)?;
    }
    let fragments = fragments(state, owner, &roots);
    check_witnesses(state, &fragments, witnesses)?;
    let rows = derive_canonical_allocation_rows_v1(&fragments).map_err(|_| {
        reject(
            Code::PROJECTION_ROW_TOTAL_OVERFLOW,
            "canonical allocation rows",
        )
    })?;
    let certificate = GlobalAccountingAllocationCertificateV1 {
        schema: GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1.to_owned(),
        global_state_root: state_root.clone(),
        profile_root: state.profile_root.clone(),
        writer_epoch: state.writer_epoch,
        chain_context: ChainContextV1 {
            chain_id: state.chain_id.clone(),
            deployment_root: state.deployment_root.clone(),
        },
        field_ownership_root: derive_field_ownership_root_v1(&fragments)?,
        terminal_binding_root: derive_terminal_binding_root_v1(&fragments)?,
        allocation_root: derive_allocation_root_v1(&fragments, &rows)?,
        ordered_lane_fragments: fragments,
        canonical_allocation_rows: rows,
        reserve_interpretation: ReserveInterpretationV1::NAMED_UNENCUMBERED_NO_CLAIMANT,
    };
    certificate.validate()?;
    Ok(certificate)
}

/// Derive a certificate from one explicit state or return a typed refusal.
///
/// Malformed input yields `AbiErrorV1`, matching the Python type/constructor error
/// boundary. Well-formed input follows Python's public check order: lane ownership,
/// producer/empty roots, supplied binding roots, row families/partition, witness
/// presence/fragment/header, derived roots. Empty witness slices and twelve empty
/// slots have the same meaning. State validation bounds every table before folds.
/// A projection success gives no accounting authorization or publication capability.
pub fn project_allocation_certificate_v1(
    state: &GlobalEconomicStateV1,
    lane_binding_roots: &[(LaneIdV1, RootV1)],
    lane_witnesses: &[Option<&VerifiedLaneAllocationFragmentV1>],
) -> AbiResultV1<Result<GlobalAccountingAllocationCertificateV1, AllocationProjectionRejectedV1>> {
    if !lane_witnesses.is_empty() && lane_witnesses.len() != ALL_LANE_IDS_V1.len() {
        return Err(AbiErrorV1::InvalidBounds(
            "lane witnesses must carry twelve slots",
        ));
    }
    let state_root = state.state_root()?;
    match project(state, &state_root, lane_binding_roots, lane_witnesses) {
        Ok(certificate) => Ok(Ok(certificate)),
        Err(ProjectionError::Boundary(error)) => Err(error),
        Err(ProjectionError::Semantic(code, detail)) => Ok(Err(AllocationProjectionRejectedV1 {
            code,
            detail,
            state_root,
        })),
    }
}
