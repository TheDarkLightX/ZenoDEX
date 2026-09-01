//! GlobalAccountingAllocationCertificateV1: the sidecar contract of the O-008 formal cycle.
//!
//! Rust twin of `src/core/global_accounting_allocation_certificate_v1.py`. For one
//! exact `GlobalEconomicStateV1`, twelve ordered lane fragments classify every
//! controlled source atom exactly once under the normative partition
//! `controlled_atoms = claimant_entitlements + named_unencumbered_reserves +
//! pending_registered_external_obligations`, in the control-domain vocabulary. V1
//! wire names stay byte-stable.
//!
//! `check_global_accounting_allocation_certificate_v1` is a total function
//! `Accept | Reject(code)` with the same closed, ordered reject precedence as Python;
//! rejects carry the unchanged pre-state root. Every fold uses checked u128
//! arithmetic; every table is canonically ordered and unique. No lane has a
//! receipt-backed producer today, so an enabled lane rejects with
//! `BlockedLaneProducerMissing`. Authority: NONE.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::release::{LaneIdV1, ALL_LANE_IDS_V1};
use crate::state::{GlobalEconomicStateV1, OutboxStatusV1, TerminalObligationStatusV1};

pub const GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1: &str =
    "zenodex/global-accounting-allocation-certificate/v1";
pub const ALLOCATION_ROOT_DOMAIN_V1: &str = "global-accounting-allocation-certificate-v1";
pub const FIELD_OWNERSHIP_ROOT_DOMAIN_V1: &str = "global-accounting-field-ownership-v1";
pub const TERMINAL_BINDING_ROOT_DOMAIN_V1: &str = "global-accounting-terminal-binding-v1";
pub const LANE_FRAGMENT_ROOT_DOMAIN_V1: &str = "global-accounting-lane-fragment-v1";
pub const MAX_FRAGMENT_ROWS_V1: usize = 4_096;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum LaneProducerKindV1 {
    NO_PRODUCER,
    REGISTERED_EMPTY_DISABLED,
    REGISTERED_EMPTY_BLOCKED,
    RECEIPT_BACKED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ReserveInterpretationV1 {
    NAMED_UNENCUMBERED_NO_CLAIMANT,
}

/// Exhaustive over `LaneIdV1`, in canonical lane order: (producer kind, blocked-on).
pub const LANE_ALLOCATION_PRODUCER_REGISTRY_V1: [(LaneIdV1, LaneProducerKindV1, &str); 12] = [
    (
        LaneIdV1::ASSET_TRANSFER,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-04 wave B asset-transfer fragment producer",
    ),
    (
        LaneIdV1::SPOT_LIQUIDITY,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-04 wave C spot-liquidity producer; UP-01 UP-12 UP-14",
    ),
    (
        LaneIdV1::FARM_INCENTIVES,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-11 wave D no-writer proof; UP-03",
    ),
    (
        LaneIdV1::ZDEX_TOKENOMICS,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-04 wave C tokenomics producer; UP-01 UP-15",
    ),
    (
        LaneIdV1::ZUSD_MONETARY,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-11 wave E no-writer proof; UP-04",
    ),
    (
        LaneIdV1::PERPS_MARKET,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-05 wave B narrow perps producer; UP-05",
    ),
    (
        LaneIdV1::ORACLE_MARKET,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-11 wave D no-writer proof; UP-06",
    ),
    (
        LaneIdV1::SEALED_AUCTION,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-11 wave D no-writer proof; UP-07",
    ),
    (
        LaneIdV1::STRATEGY_ESCROW,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-11 wave E no-writer proof; UP-08",
    ),
    (
        LaneIdV1::PROOF_REWARDS,
        LaneProducerKindV1::REGISTERED_EMPTY_BLOCKED,
        "UP-09 proof-reward funding and claimant eligibility",
    ),
    (
        LaneIdV1::EXTERNAL_CUSTODY,
        LaneProducerKindV1::REGISTERED_EMPTY_DISABLED,
        "UP-11 external finality; registry empty by construction",
    ),
    (
        LaneIdV1::GOVERNANCE_MIGRATION,
        LaneProducerKindV1::NO_PRODUCER,
        "VM-11 wave E migration-journal predecessor rows; UP-10",
    ),
];

pub fn registry_entry_v1(lane: LaneIdV1) -> (LaneProducerKindV1, &'static str) {
    for (registered, kind, blocked_on) in LANE_ALLOCATION_PRODUCER_REGISTRY_V1 {
        if registered == lane {
            return (kind, blocked_on);
        }
    }
    // Unreachable by construction: the registry is exhaustive over LaneIdV1.
    (LaneProducerKindV1::NO_PRODUCER, "unregistered lane")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationCertificateRejectCodeV1 {
    HeaderBindingDrift,
    LaneOrderDrift,
    LaneStateRootDrift,
    ProducerKindDrift,
    BlockedLaneProducerMissing,
    DisabledLaneNotEmpty,
    AllocationTotalOverflow,
    SourceAtomNotAssignedExactlyOnce,
    EntitlementRowsDrift,
    ReserveRowsDrift,
    ExternalObligationBindingDrift,
    TerminalBindingDrift,
    LaneAggregateDrift,
    DerivedRootDrift,
}

impl AllocationCertificateRejectCodeV1 {
    pub const ALL: [Self; 14] = [
        Self::HeaderBindingDrift,
        Self::LaneOrderDrift,
        Self::LaneStateRootDrift,
        Self::ProducerKindDrift,
        Self::BlockedLaneProducerMissing,
        Self::DisabledLaneNotEmpty,
        Self::AllocationTotalOverflow,
        Self::SourceAtomNotAssignedExactlyOnce,
        Self::EntitlementRowsDrift,
        Self::ReserveRowsDrift,
        Self::ExternalObligationBindingDrift,
        Self::TerminalBindingDrift,
        Self::LaneAggregateDrift,
        Self::DerivedRootDrift,
    ];

    pub const fn code(self) -> &'static str {
        match self {
            Self::HeaderBindingDrift => "HEADER_BINDING_DRIFT",
            Self::LaneOrderDrift => "LANE_ORDER_DRIFT",
            Self::LaneStateRootDrift => "LANE_STATE_ROOT_DRIFT",
            Self::ProducerKindDrift => "PRODUCER_KIND_DRIFT",
            Self::BlockedLaneProducerMissing => "BLOCKED_LANE_PRODUCER_MISSING",
            Self::DisabledLaneNotEmpty => "DISABLED_LANE_NOT_EMPTY",
            Self::AllocationTotalOverflow => "ALLOCATION_TOTAL_OVERFLOW",
            Self::SourceAtomNotAssignedExactlyOnce => "SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE",
            Self::EntitlementRowsDrift => "ENTITLEMENT_ROWS_DRIFT",
            Self::ReserveRowsDrift => "RESERVE_ROWS_DRIFT",
            Self::ExternalObligationBindingDrift => "EXTERNAL_OBLIGATION_BINDING_DRIFT",
            Self::TerminalBindingDrift => "TERMINAL_BINDING_DRIFT",
            Self::LaneAggregateDrift => "LANE_AGGREGATE_DRIFT",
            Self::DerivedRootDrift => "DERIVED_ROOT_DRIFT",
        }
    }

    /// Byte-identical to the Python message table.
    pub const fn message(self) -> &'static str {
        match self {
            Self::HeaderBindingDrift => "allocation certificate header does not bind the exact global state",
            Self::LaneOrderDrift => "allocation certificate lane fragments are not the twelve ABI V1 lanes in canonical order",
            Self::LaneStateRootDrift => "allocation certificate lane fragment does not bind the committed lane state root",
            Self::ProducerKindDrift => "allocation certificate lane fragment producer kind differs from the registry",
            Self::BlockedLaneProducerMissing => "allocation certificate enabled lane has no receipt-backed fragment producer",
            Self::DisabledLaneNotEmpty => "allocation certificate disabled lane fragment carries rows",
            Self::AllocationTotalOverflow => "allocation certificate total overflows",
            Self::SourceAtomNotAssignedExactlyOnce => "allocation certificate controlled source atoms are not assigned exactly once",
            Self::EntitlementRowsDrift => "allocation certificate claimant entitlement rows differ from the V1 liabilities",
            Self::ReserveRowsDrift => "allocation certificate unencumbered reserve rows differ from the V1 reserve partition",
            Self::ExternalObligationBindingDrift => "allocation certificate pending external obligations do not bind the V1 outbox",
            Self::TerminalBindingDrift => "allocation certificate terminal binding rows do not bind the OPEN V1 terminal obligations",
            Self::LaneAggregateDrift => "allocation certificate lane aggregates differ from the global economic tables",
            Self::DerivedRootDrift => "allocation certificate derived roots differ from the recomputed roots",
        }
    }
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ControlledLocationRowV1 {
    pub asset: String,
    pub controlling_principal: String,
    pub control_domain: String,
    pub amount_atoms: u128,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ClaimantEntitlementRowV1 {
    pub asset: String,
    pub claimant: String,
    pub control_domain: String,
    pub amount_atoms: u128,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct UnencumberedReserveRowV1 {
    pub asset: String,
    pub reserve_principal: String,
    pub control_domain: String,
    pub amount_atoms: u128,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PendingExternalObligationRowV1 {
    pub effect_id: RootV1,
    pub asset: String,
    pub amount_atoms: u128,
    pub destination_id: String,
    pub commitment_root: RootV1,
    pub control_domain: String,
    pub source_principal: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TerminalBindingRowV1 {
    pub obligation_id: String,
    pub claimant: String,
    pub asset: String,
    pub amount_atoms: u128,
    pub control_domain: String,
    pub controlling_principal: String,
    pub lane_id: LaneIdV1,
    pub lane_state_root: RootV1,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneAllocationFragmentV1 {
    pub lane_id: LaneIdV1,
    pub module_release_id: RootV1,
    pub enabled: bool,
    pub lane_state_root: RootV1,
    pub producer_kind: LaneProducerKindV1,
    pub binding_root: RootV1,
    pub controlled_locations: Vec<ControlledLocationRowV1>,
    pub claimant_entitlements: Vec<ClaimantEntitlementRowV1>,
    pub unencumbered_reserves: Vec<UnencumberedReserveRowV1>,
    pub pending_external_obligations: Vec<PendingExternalObligationRowV1>,
    pub terminal_bindings: Vec<TerminalBindingRowV1>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ChainContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalAccountingAllocationCertificateV1 {
    pub schema: String,
    pub global_state_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub chain_context: ChainContextV1,
    pub ordered_lane_fragments: Vec<LaneAllocationFragmentV1>,
    pub canonical_allocation_rows: Vec<ClaimantEntitlementRowV1>,
    pub field_ownership_root: RootV1,
    pub terminal_binding_root: RootV1,
    pub allocation_root: RootV1,
    pub reserve_interpretation: ReserveInterpretationV1,
}

// ---------------------------------------------------------------------------
// Validation (canonical order, unique keys, token shape, root shape)
// ---------------------------------------------------------------------------

fn validate_ordered<T>(
    rows: &[T],
    field: &'static str,
    strictly_before: impl Fn(&T, &T) -> bool,
) -> AbiResultV1<()> {
    if rows.len() > MAX_FRAGMENT_ROWS_V1 {
        return Err(AbiErrorV1::InvalidBounds(field));
    }
    if rows
        .windows(2)
        .any(|pair| !strictly_before(&pair[0], &pair[1]))
    {
        return Err(AbiErrorV1::InvalidOrder(field));
    }
    Ok(())
}

impl ControlledLocationRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "controlled location asset")?;
        validate_token_v1(&self.controlling_principal, "controlled location principal")?;
        validate_token_v1(&self.control_domain, "controlled location control domain")
    }
    fn key(&self) -> (&str, &str, &str) {
        (
            &self.asset,
            &self.controlling_principal,
            &self.control_domain,
        )
    }
}

impl ClaimantEntitlementRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "claimant entitlement asset")?;
        validate_token_v1(&self.claimant, "claimant entitlement claimant")?;
        validate_token_v1(&self.control_domain, "claimant entitlement control domain")
    }
    fn key(&self) -> (&str, &str, &str) {
        (&self.asset, &self.claimant, &self.control_domain)
    }
}

impl UnencumberedReserveRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "unencumbered reserve asset")?;
        validate_token_v1(&self.reserve_principal, "unencumbered reserve principal")?;
        validate_token_v1(&self.control_domain, "unencumbered reserve control domain")
    }
    fn key(&self) -> (&str, &str, &str) {
        (&self.asset, &self.reserve_principal, &self.control_domain)
    }
}

impl PendingExternalObligationRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.effect_id
            .validate("pending external obligation effect id", false)?;
        validate_token_v1(&self.asset, "pending external obligation asset")?;
        validate_token_v1(
            &self.destination_id,
            "pending external obligation destination",
        )?;
        self.commitment_root
            .validate("pending external obligation commitment", false)?;
        validate_token_v1(
            &self.control_domain,
            "pending external obligation control domain",
        )?;
        validate_token_v1(
            &self.source_principal,
            "pending external obligation source principal",
        )
    }
}

impl TerminalBindingRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.obligation_id, "terminal binding obligation id")?;
        validate_token_v1(&self.claimant, "terminal binding claimant")?;
        validate_token_v1(&self.asset, "terminal binding asset")?;
        validate_token_v1(&self.control_domain, "terminal binding control domain")?;
        validate_token_v1(&self.controlling_principal, "terminal binding principal")?;
        self.lane_state_root
            .validate("terminal binding lane state root", true)
    }
}

impl LaneAllocationFragmentV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.module_release_id
            .validate("lane fragment module release id", false)?;
        self.lane_state_root
            .validate("lane fragment state root", true)?;
        self.binding_root
            .validate("lane fragment binding root", true)?;
        for row in &self.controlled_locations {
            row.validate()?;
        }
        validate_ordered(
            &self.controlled_locations,
            "lane fragment controlled locations",
            |a, b| a.key() < b.key(),
        )?;
        for row in &self.claimant_entitlements {
            row.validate()?;
        }
        validate_ordered(
            &self.claimant_entitlements,
            "lane fragment claimant entitlements",
            |a, b| a.key() < b.key(),
        )?;
        for row in &self.unencumbered_reserves {
            row.validate()?;
        }
        validate_ordered(
            &self.unencumbered_reserves,
            "lane fragment unencumbered reserves",
            |a, b| a.key() < b.key(),
        )?;
        for row in &self.pending_external_obligations {
            row.validate()?;
        }
        validate_ordered(
            &self.pending_external_obligations,
            "lane fragment pending external obligations",
            |a, b| a.effect_id.as_str() < b.effect_id.as_str(),
        )?;
        for row in &self.terminal_bindings {
            row.validate()?;
        }
        validate_ordered(
            &self.terminal_bindings,
            "lane fragment terminal bindings",
            |a, b| a.obligation_id.as_str() < b.obligation_id.as_str(),
        )
    }

    pub fn is_empty(&self) -> bool {
        self.controlled_locations.is_empty()
            && self.claimant_entitlements.is_empty()
            && self.unencumbered_reserves.is_empty()
            && self.pending_external_obligations.is_empty()
            && self.terminal_bindings.is_empty()
    }

    pub fn fragment_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(LANE_FRAGMENT_ROOT_DOMAIN_V1, self)
    }
}

impl ChainContextV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "chain context chain id")?;
        self.deployment_root
            .validate("chain context deployment root", false)
    }
}

impl GlobalAccountingAllocationCertificateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.global_state_root
            .validate("certificate global state root", false)?;
        self.profile_root
            .validate("certificate profile root", false)?;
        self.chain_context.validate()?;
        for fragment in &self.ordered_lane_fragments {
            fragment.validate()?;
        }
        for row in &self.canonical_allocation_rows {
            row.validate()?;
        }
        validate_ordered(
            &self.canonical_allocation_rows,
            "certificate canonical allocation rows",
            |a, b| a.key() < b.key(),
        )?;
        self.field_ownership_root
            .validate("certificate field ownership root", true)?;
        self.terminal_binding_root
            .validate("certificate terminal binding root", true)?;
        self.allocation_root
            .validate("certificate allocation root", true)
    }
}

// ---------------------------------------------------------------------------
// Derived roots (pure)
// ---------------------------------------------------------------------------

#[derive(Serialize)]
struct OwnershipRowV1<'a> {
    asset: &'a str,
    control_domain: &'a str,
    lane_id: LaneIdV1,
}

pub fn derive_field_ownership_root_v1(
    fragments: &[LaneAllocationFragmentV1],
) -> AbiResultV1<RootV1> {
    let mut rows: Vec<OwnershipRowV1<'_>> = fragments
        .iter()
        .flat_map(|fragment| {
            fragment
                .controlled_locations
                .iter()
                .map(move |row| OwnershipRowV1 {
                    asset: &row.asset,
                    control_domain: &row.control_domain,
                    lane_id: fragment.lane_id,
                })
        })
        .collect();
    rows.sort_by(|a, b| {
        (a.asset, a.control_domain, format!("{:?}", a.lane_id)).cmp(&(
            b.asset,
            b.control_domain,
            format!("{:?}", b.lane_id),
        ))
    });
    hash_global_v1(FIELD_OWNERSHIP_ROOT_DOMAIN_V1, &rows)
}

pub fn derive_terminal_binding_root_v1(
    fragments: &[LaneAllocationFragmentV1],
) -> AbiResultV1<RootV1> {
    let mut rows: Vec<&TerminalBindingRowV1> = fragments
        .iter()
        .flat_map(|fragment| fragment.terminal_bindings.iter())
        .collect();
    rows.sort_by(|a, b| a.obligation_id.cmp(&b.obligation_id));
    hash_global_v1(TERMINAL_BINDING_ROOT_DOMAIN_V1, &rows)
}

#[derive(Serialize)]
struct AllocationRootContentV1<'a> {
    fragment_roots: Vec<RootV1>,
    canonical_allocation_rows: &'a [ClaimantEntitlementRowV1],
}

pub fn derive_allocation_root_v1(
    fragments: &[LaneAllocationFragmentV1],
    canonical_rows: &[ClaimantEntitlementRowV1],
) -> AbiResultV1<RootV1> {
    let mut fragment_roots = Vec::with_capacity(fragments.len());
    for fragment in fragments {
        fragment_roots.push(fragment.fragment_root()?);
    }
    hash_global_v1(
        ALLOCATION_ROOT_DOMAIN_V1,
        &AllocationRootContentV1 {
            fragment_roots,
            canonical_allocation_rows: canonical_rows,
        },
    )
}

fn fold_u128<K: Ord + Clone>(
    rows: impl Iterator<Item = (K, u128)>,
    _label: &str,
) -> Result<BTreeMap<K, u128>, AllocationCertificateRejectCodeV1> {
    let mut totals = BTreeMap::new();
    for (key, amount) in rows {
        let total = totals
            .get(&key)
            .copied()
            .unwrap_or(0u128)
            .checked_add(amount)
            .ok_or(AllocationCertificateRejectCodeV1::AllocationTotalOverflow)?;
        totals.insert(key, total);
    }
    Ok(totals)
}

pub fn derive_canonical_allocation_rows_v1(
    fragments: &[LaneAllocationFragmentV1],
) -> Result<Vec<ClaimantEntitlementRowV1>, AllocationCertificateRejectCodeV1> {
    let totals = fold_u128(
        fragments.iter().flat_map(|fragment| {
            fragment.claimant_entitlements.iter().map(|row| {
                (
                    (
                        row.asset.clone(),
                        row.claimant.clone(),
                        row.control_domain.clone(),
                    ),
                    row.amount_atoms,
                )
            })
        }),
        "canonical allocation rows",
    )?;
    Ok(totals
        .into_iter()
        .map(
            |((asset, claimant, control_domain), amount_atoms)| ClaimantEntitlementRowV1 {
                asset,
                claimant,
                control_domain,
                amount_atoms,
            },
        )
        .collect())
}

// ---------------------------------------------------------------------------
// Outcome
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AllocationCertificateAcceptedV1 {
    pub global_state_root: RootV1,
    pub allocation_root: RootV1,
    pub field_ownership_root: RootV1,
    pub terminal_binding_root: RootV1,
    pub lane_fragment_roots: Vec<RootV1>,
    pub authority: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AllocationCertificateRejectedV1 {
    pub code: AllocationCertificateRejectCodeV1,
    pub detail: String,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AllocationCertificateOutcomeV1 {
    Accepted(AllocationCertificateAcceptedV1),
    Rejected(AllocationCertificateRejectedV1),
}

struct Reject(AllocationCertificateRejectCodeV1, String);

fn fail<T>(
    code: AllocationCertificateRejectCodeV1,
    detail: impl Into<String>,
) -> Result<T, Reject> {
    Err(Reject(code, detail.into()))
}

// ---------------------------------------------------------------------------
// Checks in fixed precedence
// ---------------------------------------------------------------------------

fn check_header(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
    state_root: &RootV1,
) -> Result<(), Reject> {
    if &certificate.global_state_root != state_root {
        return fail(
            AllocationCertificateRejectCodeV1::HeaderBindingDrift,
            "global_state_root",
        );
    }
    if certificate.profile_root != state.profile_root {
        return fail(
            AllocationCertificateRejectCodeV1::HeaderBindingDrift,
            "profile_root",
        );
    }
    if certificate.writer_epoch != state.writer_epoch {
        return fail(
            AllocationCertificateRejectCodeV1::HeaderBindingDrift,
            "writer_epoch",
        );
    }
    if certificate.chain_context.chain_id != state.chain_id
        || certificate.chain_context.deployment_root != state.deployment_root
    {
        return fail(
            AllocationCertificateRejectCodeV1::HeaderBindingDrift,
            "chain_context",
        );
    }
    Ok(())
}

fn check_lane_order(certificate: &GlobalAccountingAllocationCertificateV1) -> Result<(), Reject> {
    let lanes: Vec<LaneIdV1> = certificate
        .ordered_lane_fragments
        .iter()
        .map(|f| f.lane_id)
        .collect();
    if lanes != ALL_LANE_IDS_V1 {
        let listed: Vec<String> = lanes.iter().map(|lane| format!("{lane:?}")).collect();
        return fail(
            AllocationCertificateRejectCodeV1::LaneOrderDrift,
            listed.join(","),
        );
    }
    Ok(())
}

fn check_lane_bindings(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> Result<(), Reject> {
    for (fragment, lane_root) in certificate
        .ordered_lane_fragments
        .iter()
        .zip(state.lane_roots.iter())
    {
        let lane = format!("{:?}", fragment.lane_id);
        if fragment.module_release_id != lane_root.module_release_id
            || fragment.enabled != lane_root.enabled
            || fragment.lane_state_root != lane_root.state_root
        {
            return fail(AllocationCertificateRejectCodeV1::LaneStateRootDrift, lane);
        }
        let (registered_kind, blocked_on) = registry_entry_v1(fragment.lane_id);
        if fragment.producer_kind != registered_kind {
            return fail(
                AllocationCertificateRejectCodeV1::ProducerKindDrift,
                format!("{lane}:{:?}", fragment.producer_kind),
            );
        }
        if fragment.enabled && registered_kind != LaneProducerKindV1::RECEIPT_BACKED {
            return fail(
                AllocationCertificateRejectCodeV1::BlockedLaneProducerMissing,
                format!("{lane}:{blocked_on}"),
            );
        }
        if !fragment.enabled && !fragment.is_empty() {
            return fail(
                AllocationCertificateRejectCodeV1::DisabledLaneNotEmpty,
                lane,
            );
        }
    }
    Ok(())
}

fn fold_or_reject<K: Ord + Clone>(
    rows: impl Iterator<Item = (K, u128)>,
    label: &str,
) -> Result<BTreeMap<K, u128>, Reject> {
    fold_u128(rows, label).map_err(|code| Reject(code, label.to_owned()))
}

fn check_exactly_once(certificate: &GlobalAccountingAllocationCertificateV1) -> Result<(), Reject> {
    for fragment in &certificate.ordered_lane_fragments {
        let lane = format!("{:?}", fragment.lane_id);
        let controlled = fold_or_reject(
            fragment
                .controlled_locations
                .iter()
                .map(|r| ((r.asset.clone(), r.control_domain.clone()), r.amount_atoms)),
            &format!("{lane} controlled"),
        )?;
        let assigned = fold_or_reject(
            fragment
                .claimant_entitlements
                .iter()
                .map(|r| ((r.asset.clone(), r.control_domain.clone()), r.amount_atoms))
                .chain(
                    fragment
                        .unencumbered_reserves
                        .iter()
                        .map(|r| ((r.asset.clone(), r.control_domain.clone()), r.amount_atoms)),
                )
                .chain(
                    fragment
                        .pending_external_obligations
                        .iter()
                        .map(|r| ((r.asset.clone(), r.control_domain.clone()), r.amount_atoms)),
                ),
            &format!("{lane} assignments"),
        )?;
        if controlled != assigned {
            return fail(
                AllocationCertificateRejectCodeV1::SourceAtomNotAssignedExactlyOnce,
                lane,
            );
        }
    }
    Ok(())
}

fn check_entitlement_rows(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> Result<(), Reject> {
    let derived = derive_canonical_allocation_rows_v1(&certificate.ordered_lane_fragments)
        .map_err(|code| Reject(code, "canonical allocation rows".to_owned()))?;
    if derived != certificate.canonical_allocation_rows {
        return fail(
            AllocationCertificateRejectCodeV1::EntitlementRowsDrift,
            "canonical_allocation_rows",
        );
    }
    let liabilities: Vec<(&str, &str, &str, u128)> = state
        .liabilities
        .iter()
        .map(|row| {
            (
                row.asset.as_str(),
                row.owner.as_str(),
                row.custody_domain.as_str(),
                row.amount_atoms,
            )
        })
        .collect();
    let rows: Vec<(&str, &str, &str, u128)> = derived
        .iter()
        .map(|row| {
            (
                row.asset.as_str(),
                row.claimant.as_str(),
                row.control_domain.as_str(),
                row.amount_atoms,
            )
        })
        .collect();
    if rows != liabilities {
        return fail(
            AllocationCertificateRejectCodeV1::EntitlementRowsDrift,
            "liabilities",
        );
    }
    Ok(())
}

fn check_reserve_rows(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> Result<(), Reject> {
    let totals = fold_or_reject(
        certificate
            .ordered_lane_fragments
            .iter()
            .flat_map(|fragment| {
                fragment.unencumbered_reserves.iter().map(|r| {
                    (
                        (
                            r.asset.clone(),
                            r.reserve_principal.clone(),
                            r.control_domain.clone(),
                        ),
                        r.amount_atoms,
                    )
                })
            }),
        "reserves",
    )?;
    let reserves: Vec<(&str, &str, &str, u128)> = state
        .reserves
        .iter()
        .map(|row| {
            (
                row.asset.as_str(),
                row.owner.as_str(),
                row.custody_domain.as_str(),
                row.amount_atoms,
            )
        })
        .collect();
    let rows: Vec<(&str, &str, &str, u128)> = totals
        .iter()
        .map(|((asset, principal, domain), amount)| {
            (asset.as_str(), principal.as_str(), domain.as_str(), *amount)
        })
        .collect();
    if rows != reserves {
        return fail(
            AllocationCertificateRejectCodeV1::ReserveRowsDrift,
            "reserves",
        );
    }
    Ok(())
}

fn check_external_obligations(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> Result<(), Reject> {
    let pending: BTreeMap<&str, &PendingExternalObligationRowV1> = certificate
        .ordered_lane_fragments
        .iter()
        .flat_map(|fragment| fragment.pending_external_obligations.iter())
        .map(|row| (row.effect_id.as_str(), row))
        .collect();
    let outbox: BTreeMap<&str, &crate::state::OutboxStateV1> = state
        .outbox
        .iter()
        .filter(|row| row.status == OutboxStatusV1::PENDING)
        .map(|row| (row.effect_id.as_str(), row))
        .collect();
    let pending_ids: Vec<&str> = pending.keys().copied().collect();
    let outbox_ids: Vec<&str> = outbox.keys().copied().collect();
    if pending_ids != outbox_ids {
        return fail(
            AllocationCertificateRejectCodeV1::ExternalObligationBindingDrift,
            "effect_id set",
        );
    }
    for (effect_id, row) in &pending {
        let entry = outbox[effect_id];
        if row.destination_id != entry.destination_id || row.commitment_root != entry.payload_hash {
            return fail(
                AllocationCertificateRejectCodeV1::ExternalObligationBindingDrift,
                (*effect_id).to_owned(),
            );
        }
    }
    Ok(())
}

fn check_terminal_bindings(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> Result<(), Reject> {
    let mut bindings: BTreeMap<&str, (&TerminalBindingRowV1, &LaneAllocationFragmentV1)> =
        BTreeMap::new();
    for fragment in &certificate.ordered_lane_fragments {
        for row in &fragment.terminal_bindings {
            if bindings
                .insert(row.obligation_id.as_str(), (row, fragment))
                .is_some()
            {
                return fail(
                    AllocationCertificateRejectCodeV1::TerminalBindingDrift,
                    format!("duplicate {}", row.obligation_id),
                );
            }
        }
    }
    let open: BTreeMap<&str, &crate::state::TerminalObligationV1> = state
        .terminal_obligations
        .iter()
        .filter(|row| row.status == TerminalObligationStatusV1::OPEN)
        .map(|row| (row.obligation_id.as_str(), row))
        .collect();
    let binding_ids: Vec<&str> = bindings.keys().copied().collect();
    let open_ids: Vec<&str> = open.keys().copied().collect();
    if binding_ids != open_ids {
        return fail(
            AllocationCertificateRejectCodeV1::TerminalBindingDrift,
            "obligation_id set",
        );
    }
    for (obligation_id, (row, fragment)) in &bindings {
        let terminal = open[obligation_id];
        if row.claimant != terminal.claimant
            || row.asset != terminal.asset
            || row.amount_atoms != terminal.amount_atoms
            || row.lane_id != terminal.lane_id
        {
            return fail(
                AllocationCertificateRejectCodeV1::TerminalBindingDrift,
                (*obligation_id).to_owned(),
            );
        }
        if row.lane_id != fragment.lane_id || row.lane_state_root != fragment.lane_state_root {
            return fail(
                AllocationCertificateRejectCodeV1::TerminalBindingDrift,
                format!("{obligation_id} lane binding"),
            );
        }
        let entitled = fragment.claimant_entitlements.iter().any(|e| {
            e.asset == row.asset
                && e.claimant == row.claimant
                && e.control_domain == row.control_domain
                && e.amount_atoms >= row.amount_atoms
        });
        let controlled = fragment.controlled_locations.iter().any(|l| {
            l.asset == row.asset
                && l.controlling_principal == row.controlling_principal
                && l.control_domain == row.control_domain
        });
        if !entitled || !controlled {
            return fail(
                AllocationCertificateRejectCodeV1::TerminalBindingDrift,
                format!("{obligation_id} domain binding"),
            );
        }
    }
    Ok(())
}

fn check_lane_aggregates(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> Result<(), Reject> {
    let custody = fold_or_reject(
        certificate
            .ordered_lane_fragments
            .iter()
            .flat_map(|fragment| {
                fragment.controlled_locations.iter().map(|r| {
                    (
                        (
                            r.asset.clone(),
                            r.controlling_principal.clone(),
                            r.control_domain.clone(),
                        ),
                        r.amount_atoms,
                    )
                })
            }),
        "custody",
    )?;
    let expected: Vec<(&str, &str, &str, u128)> = state
        .custody
        .iter()
        .map(|row| {
            (
                row.asset.as_str(),
                row.owner.as_str(),
                row.custody_domain.as_str(),
                row.amount_atoms,
            )
        })
        .collect();
    let rows: Vec<(&str, &str, &str, u128)> = custody
        .iter()
        .map(|((asset, principal, domain), amount)| {
            (asset.as_str(), principal.as_str(), domain.as_str(), *amount)
        })
        .collect();
    if rows != expected {
        return fail(
            AllocationCertificateRejectCodeV1::LaneAggregateDrift,
            "custody",
        );
    }
    Ok(())
}

fn check_derived_roots(
    certificate: &GlobalAccountingAllocationCertificateV1,
) -> Result<(), Reject> {
    let fragments = &certificate.ordered_lane_fragments;
    let ownership = derive_field_ownership_root_v1(fragments).map_err(|_| {
        Reject(
            AllocationCertificateRejectCodeV1::DerivedRootDrift,
            "field_ownership_root".to_owned(),
        )
    })?;
    if certificate.field_ownership_root != ownership {
        return fail(
            AllocationCertificateRejectCodeV1::DerivedRootDrift,
            "field_ownership_root",
        );
    }
    let terminal = derive_terminal_binding_root_v1(fragments).map_err(|_| {
        Reject(
            AllocationCertificateRejectCodeV1::DerivedRootDrift,
            "terminal_binding_root".to_owned(),
        )
    })?;
    if certificate.terminal_binding_root != terminal {
        return fail(
            AllocationCertificateRejectCodeV1::DerivedRootDrift,
            "terminal_binding_root",
        );
    }
    let allocation = derive_allocation_root_v1(fragments, &certificate.canonical_allocation_rows)
        .map_err(|_| {
        Reject(
            AllocationCertificateRejectCodeV1::DerivedRootDrift,
            "allocation_root".to_owned(),
        )
    })?;
    if certificate.allocation_root != allocation {
        return fail(
            AllocationCertificateRejectCodeV1::DerivedRootDrift,
            "allocation_root",
        );
    }
    Ok(())
}

/// Total function: accept with the derived roots, or reject with the first failing closed code.
///
/// The certificate and state are validated first (`AbiErrorV1` on malformed input is
/// a parse-level failure, not a certificate reject). A reject never mutates and
/// carries the pre-state root twice.
pub fn check_global_accounting_allocation_certificate_v1(
    certificate: &GlobalAccountingAllocationCertificateV1,
    state: &GlobalEconomicStateV1,
) -> AbiResultV1<AllocationCertificateOutcomeV1> {
    certificate.validate()?;
    let pre_state_root = state.state_root()?;
    let run = || -> Result<(), Reject> {
        check_header(certificate, state, &pre_state_root)?;
        check_lane_order(certificate)?;
        check_lane_bindings(certificate, state)?;
        check_exactly_once(certificate)?;
        check_entitlement_rows(certificate, state)?;
        check_reserve_rows(certificate, state)?;
        check_external_obligations(certificate, state)?;
        check_terminal_bindings(certificate, state)?;
        check_lane_aggregates(certificate, state)?;
        check_derived_roots(certificate)
    };
    match run() {
        Err(Reject(code, detail)) => Ok(AllocationCertificateOutcomeV1::Rejected(
            AllocationCertificateRejectedV1 {
                code,
                detail,
                pre_state_root: pre_state_root.clone(),
                post_state_root: pre_state_root,
            },
        )),
        Ok(()) => {
            let mut lane_fragment_roots =
                Vec::with_capacity(certificate.ordered_lane_fragments.len());
            for fragment in &certificate.ordered_lane_fragments {
                lane_fragment_roots.push(fragment.fragment_root()?);
            }
            Ok(AllocationCertificateOutcomeV1::Accepted(
                AllocationCertificateAcceptedV1 {
                    global_state_root: certificate.global_state_root.clone(),
                    allocation_root: certificate.allocation_root.clone(),
                    field_ownership_root: certificate.field_ownership_root.clone(),
                    terminal_binding_root: certificate.terminal_binding_root.clone(),
                    lane_fragment_roots,
                    authority: "NONE",
                },
            ))
        }
    }
}

/// The only certificate the current profile can produce: twelve empty registered fragments.
pub fn build_registered_empty_certificate_v1(
    state: &GlobalEconomicStateV1,
) -> AbiResultV1<GlobalAccountingAllocationCertificateV1> {
    let fragments: Vec<LaneAllocationFragmentV1> = state
        .lane_roots
        .iter()
        .map(|lane_root| LaneAllocationFragmentV1 {
            lane_id: lane_root.lane_id,
            module_release_id: lane_root.module_release_id.clone(),
            enabled: lane_root.enabled,
            lane_state_root: lane_root.state_root.clone(),
            producer_kind: registry_entry_v1(lane_root.lane_id).0,
            binding_root: lane_root.state_root.clone(),
            controlled_locations: Vec::new(),
            claimant_entitlements: Vec::new(),
            unencumbered_reserves: Vec::new(),
            pending_external_obligations: Vec::new(),
            terminal_bindings: Vec::new(),
        })
        .collect();
    let rows = derive_canonical_allocation_rows_v1(&fragments)
        .map_err(|_| AbiErrorV1::Conservation("allocation certificate total overflows"))?;
    Ok(GlobalAccountingAllocationCertificateV1 {
        schema: GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1.to_owned(),
        global_state_root: state.state_root()?,
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
    })
}
