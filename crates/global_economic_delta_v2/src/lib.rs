#![forbid(unsafe_code)]

//! Event-level Global Economic Delta Algebra V2.
//!
//! This crate validates one defensively owned research plan. It proposes no
//! state transition and carries no proof, publication, release, or production
//! authority.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde_json::Value;
use sha2::{Digest, Sha256};

mod model;
mod source_history;
mod source_history_admission;

pub use source_history::{
    decode_source_history_statement_v2, CheckedSourceHistoryStatementV2, SourceHistoryRejectCodeV2,
    SourceHistoryRejectV2, MAX_SOURCE_HISTORY_INPUT_BYTES_V2, SOURCE_HISTORY_SCHEMA_V2,
};
pub use source_history_admission::{
    admit_source_history_v2, SourceHistoryBackendRejectV2, SourceHistoryProofBackendV2,
    VerifiedSourceHistoryDeltaPlanV2, MAX_SOURCE_HISTORY_RECEIPT_BYTES_V2,
};

use model::{
    CanonicalIdV2, EconomicDeltaV2, LiabilityDirectionV2, RawDeltaPlanV2, SourceBindingV2,
};

pub const SCHEMA_V2: &str = "zenodex/global-economic-delta-plan/v2";
pub const MAX_EVENTS_V2: usize = 64;
pub const MAX_SOURCE_BINDINGS_V2: usize = 64;
pub const MAX_INPUT_BYTES_V2: usize = 1_048_576;
const ROOT_DOMAIN_V2: &[u8] = b"zenodex:global-economic-delta-plan:v2\0";
const MAX_DELTA_ATOMS_V2: u128 = (1_u128 << 127) - 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeltaRejectCodeV2 {
    DecodeInvalid,
    SchemaMismatch,
    EmptyPlan,
    AmountOutOfRange,
    SourceEqualsDestination,
    LiabilityRelationInvalid,
    SlashPartitionMismatch,
    SelfReferentialEvent,
    DuplicateEvent,
    NoncanonicalEventOrder,
    SourceBindingCountOutOfRange,
    SourceReferenceInvalid,
    SourceReferenceReused,
    SourceBindingUnused,
    ReferenceRootConflict,
    NoncanonicalSourceOrder,
    EventCountOutOfRange,
    InputTooLarge,
    CanonicalEncodingFailed,
}

impl DeltaRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DecodeInvalid => "DECODE_INVALID",
            Self::SchemaMismatch => "SCHEMA_MISMATCH",
            Self::EmptyPlan => "EMPTY_PLAN",
            Self::AmountOutOfRange => "AMOUNT_OUT_OF_RANGE",
            Self::SourceEqualsDestination => "SOURCE_EQUALS_DESTINATION",
            Self::LiabilityRelationInvalid => "LIABILITY_RELATION_INVALID",
            Self::SlashPartitionMismatch => "SLASH_PARTITION_MISMATCH",
            Self::SelfReferentialEvent => "SELF_REFERENTIAL_EVENT",
            Self::DuplicateEvent => "DUPLICATE_EVENT",
            Self::NoncanonicalEventOrder => "NONCANONICAL_EVENT_ORDER",
            Self::SourceBindingCountOutOfRange => "SOURCE_BINDING_COUNT_OUT_OF_RANGE",
            Self::SourceReferenceInvalid => "SOURCE_REFERENCE_INVALID",
            Self::SourceReferenceReused => "SOURCE_REFERENCE_REUSED",
            Self::SourceBindingUnused => "SOURCE_BINDING_UNUSED",
            Self::ReferenceRootConflict => "REFERENCE_ROOT_CONFLICT",
            Self::NoncanonicalSourceOrder => "NONCANONICAL_SOURCE_ORDER",
            Self::EventCountOutOfRange => "EVENT_COUNT_OUT_OF_RANGE",
            Self::InputTooLarge => "INPUT_TOO_LARGE",
            Self::CanonicalEncodingFailed => "CANONICAL_ENCODING_FAILED",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeltaRejectV2 {
    pub code: DeltaRejectCodeV2,
    pub detail: String,
}

impl fmt::Display for DeltaRejectV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code.as_str(), self.detail)
    }
}

impl std::error::Error for DeltaRejectV2 {}

type DeltaResultV2<T> = Result<T, DeltaRejectV2>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructurallyValidDeltaPlanV2 {
    events: Vec<EconomicDeltaV2>,
    source_bindings: Vec<SourceBindingV2>,
    canonical_bytes: Vec<u8>,
    root: String,
}

impl StructurallyValidDeltaPlanV2 {
    pub fn event_count(&self) -> usize {
        self.events.len()
    }

    pub fn delta_classes(&self) -> Vec<&'static str> {
        self.events
            .iter()
            .map(EconomicDeltaV2::class_name)
            .collect()
    }

    pub fn source_binding_count(&self) -> usize {
        self.source_bindings.len()
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub fn root(&self) -> &str {
        &self.root
    }

    pub(crate) fn source_bindings(&self) -> &[SourceBindingV2] {
        &self.source_bindings
    }
}

fn reject_v2(code: DeltaRejectCodeV2, detail: impl Into<String>) -> DeltaRejectV2 {
    DeltaRejectV2 {
        code,
        detail: detail.into(),
    }
}

fn require_delta_atoms_v2(amount_atoms: u128) -> DeltaResultV2<()> {
    if amount_atoms == 0 || amount_atoms > MAX_DELTA_ATOMS_V2 {
        return Err(reject_v2(
            DeltaRejectCodeV2::AmountOutOfRange,
            "delta atoms must be in 1..=i128::MAX",
        ));
    }
    Ok(())
}

fn require_balance_atoms_v2(amount_atoms: u128) -> DeltaResultV2<()> {
    if amount_atoms > MAX_DELTA_ATOMS_V2 {
        return Err(reject_v2(
            DeltaRejectCodeV2::AmountOutOfRange,
            "balance atoms must be in 0..=i128::MAX",
        ));
    }
    Ok(())
}

fn require_distinct_locations_v2(
    source_owner: &CanonicalIdV2,
    source_allocation: &CanonicalIdV2,
    destination_owner: &CanonicalIdV2,
    destination_allocation: &CanonicalIdV2,
) -> DeltaResultV2<()> {
    if source_owner == destination_owner && source_allocation == destination_allocation {
        return Err(reject_v2(
            DeltaRejectCodeV2::SourceEqualsDestination,
            "source and destination locations must differ",
        ));
    }
    Ok(())
}

fn validate_liability_v2(
    amount_atoms: u128,
    direction: LiabilityDirectionV2,
    pre_atoms: u128,
    post_atoms: u128,
) -> DeltaResultV2<()> {
    require_balance_atoms_v2(pre_atoms)?;
    require_balance_atoms_v2(post_atoms)?;
    let relation_holds = match direction {
        LiabilityDirectionV2::Increase => post_atoms > pre_atoms,
        LiabilityDirectionV2::Decrease => pre_atoms > post_atoms,
    };
    if !relation_holds || post_atoms.abs_diff(pre_atoms) != amount_atoms {
        return Err(reject_v2(
            DeltaRejectCodeV2::LiabilityRelationInvalid,
            "liability before and after values must derive the exact directed amount",
        ));
    }
    Ok(())
}

fn validate_slash_v2(
    amount_atoms: u128,
    beneficiary_atoms: u128,
    residue_atoms: u128,
) -> DeltaResultV2<()> {
    require_balance_atoms_v2(beneficiary_atoms)?;
    require_balance_atoms_v2(residue_atoms)?;
    if beneficiary_atoms.checked_add(residue_atoms) != Some(amount_atoms) {
        return Err(reject_v2(
            DeltaRejectCodeV2::SlashPartitionMismatch,
            "slash beneficiary and residue must partition the exact amount",
        ));
    }
    Ok(())
}

pub(crate) fn sorted_json_v2(value: Value) -> Value {
    match value {
        Value::Array(items) => Value::Array(items.into_iter().map(sorted_json_v2).collect()),
        Value::Object(object) => {
            let sorted = object
                .into_iter()
                .map(|(key, item)| (key, sorted_json_v2(item)))
                .collect();
            Value::Object(sorted)
        }
        scalar => scalar,
    }
}

fn canonical_bytes_v2(plan: &RawDeltaPlanV2) -> DeltaResultV2<Vec<u8>> {
    let value = serde_json::to_value(plan).map_err(|_| {
        reject_v2(
            DeltaRejectCodeV2::CanonicalEncodingFailed,
            "plan cannot be projected to canonical JSON",
        )
    })?;
    let mut bytes = serde_json::to_vec(&sorted_json_v2(value)).map_err(|_| {
        reject_v2(
            DeltaRejectCodeV2::CanonicalEncodingFailed,
            "canonical JSON cannot be encoded",
        )
    })?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn validate_plan_v2(plan: RawDeltaPlanV2) -> DeltaResultV2<StructurallyValidDeltaPlanV2> {
    if plan.schema != SCHEMA_V2 {
        return Err(reject_v2(
            DeltaRejectCodeV2::SchemaMismatch,
            "plan schema is not V2",
        ));
    }
    if plan.events.is_empty() {
        return Err(reject_v2(
            DeltaRejectCodeV2::EmptyPlan,
            "a delta plan must contain at least one event",
        ));
    }
    if plan.events.len() > MAX_EVENTS_V2 {
        return Err(reject_v2(
            DeltaRejectCodeV2::EventCountOutOfRange,
            "a delta plan may contain at most 64 events",
        ));
    }
    if plan.source_bindings.len() > MAX_SOURCE_BINDINGS_V2 {
        return Err(reject_v2(
            DeltaRejectCodeV2::SourceBindingCountOutOfRange,
            "a delta plan may bind at most 64 source occurrences",
        ));
    }
    for binding in &plan.source_bindings {
        binding.validate()?;
    }
    for event in &plan.events {
        event.validate()?;
    }
    let event_ids: Vec<&str> = plan.events.iter().map(EconomicDeltaV2::event_id).collect();
    let unique: BTreeSet<&str> = event_ids.iter().copied().collect();
    if unique.len() != event_ids.len() {
        return Err(reject_v2(
            DeltaRejectCodeV2::DuplicateEvent,
            "economic event IDs must be unique",
        ));
    }
    if !event_ids.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(reject_v2(
            DeltaRejectCodeV2::NoncanonicalEventOrder,
            "economic events must be ordered by root",
        ));
    }
    validate_source_bindings_v2(&plan.source_bindings, &plan.events, &unique)?;
    let canonical_bytes = canonical_bytes_v2(&plan)?;
    let mut hasher = Sha256::new();
    hasher.update(ROOT_DOMAIN_V2);
    hasher.update(&canonical_bytes);
    let root = format!("sha256:{}", hex::encode(hasher.finalize()));
    Ok(StructurallyValidDeltaPlanV2 {
        source_bindings: plan.source_bindings,
        events: plan.events,
        canonical_bytes,
        root,
    })
}

fn validate_source_bindings_v2(
    bindings: &[SourceBindingV2],
    events: &[EconomicDeltaV2],
    event_ids: &BTreeSet<&str>,
) -> DeltaResultV2<()> {
    let binding_by_root = index_source_bindings_v2(bindings)?;
    validate_reference_domains_v2(events, event_ids, &binding_by_root)?;
    let consumed_count = consume_source_bindings_v2(events, event_ids, &binding_by_root)?;
    if consumed_count != binding_by_root.len() {
        return Err(reject_v2(
            DeltaRejectCodeV2::SourceBindingUnused,
            "every source binding must be consumed exactly once",
        ));
    }
    Ok(())
}

fn index_source_bindings_v2(
    bindings: &[SourceBindingV2],
) -> DeltaResultV2<BTreeMap<&str, &SourceBindingV2>> {
    let mut binding_by_root = BTreeMap::new();
    for binding in bindings {
        if binding_by_root.insert(binding.root(), binding).is_some() {
            return Err(reject_v2(
                DeltaRejectCodeV2::SourceReferenceReused,
                "source occurrence roots must be unique",
            ));
        }
    }
    if !bindings
        .windows(2)
        .all(|pair| pair[0].root() < pair[1].root())
    {
        return Err(reject_v2(
            DeltaRejectCodeV2::NoncanonicalSourceOrder,
            "source bindings must be ordered by root",
        ));
    }
    Ok(binding_by_root)
}

fn validate_reference_domains_v2(
    events: &[EconomicDeltaV2],
    event_ids: &BTreeSet<&str>,
    binding_by_root: &BTreeMap<&str, &SourceBindingV2>,
) -> DeltaResultV2<()> {
    let mut output_roots = BTreeSet::new();
    for output_root in events
        .iter()
        .filter_map(EconomicDeltaV2::destination_effect)
    {
        if event_ids.contains(output_root)
            || binding_by_root.contains_key(output_root)
            || !output_roots.insert(output_root)
        {
            return Err(reject_v2(
                DeltaRejectCodeV2::ReferenceRootConflict,
                "output effects, source occurrences, and economic events must be disjoint",
            ));
        }
    }
    if binding_by_root
        .keys()
        .any(|source_root| event_ids.contains(source_root))
    {
        return Err(reject_v2(
            DeltaRejectCodeV2::ReferenceRootConflict,
            "source occurrences cannot cite events from the candidate plan",
        ));
    }
    Ok(())
}

fn consume_source_bindings_v2(
    events: &[EconomicDeltaV2],
    event_ids: &BTreeSet<&str>,
    binding_by_root: &BTreeMap<&str, &SourceBindingV2>,
) -> DeltaResultV2<usize> {
    let mut consumed_roots = BTreeSet::new();
    for event in events {
        let Some((source_root, expected_kind, expected_asset)) = event.source_reference() else {
            continue;
        };
        if event_ids.contains(source_root) {
            return Err(reject_v2(
                DeltaRejectCodeV2::ReferenceRootConflict,
                "source references cannot cite events from the candidate plan",
            ));
        }
        let Some(binding) = binding_by_root.get(source_root) else {
            return Err(reject_v2(
                DeltaRejectCodeV2::SourceReferenceInvalid,
                "every referenced source must have an exact source binding",
            ));
        };
        if binding.kind() != expected_kind
            || binding.asset() != expected_asset
            || binding.amount_atoms()? != event.amount_atoms()?
        {
            return Err(reject_v2(
                DeltaRejectCodeV2::SourceReferenceInvalid,
                "source kind, asset, and amount must match the consuming event",
            ));
        }
        if !consumed_roots.insert(source_root) {
            return Err(reject_v2(
                DeltaRejectCodeV2::SourceReferenceReused,
                "one source occurrence cannot be consumed twice in a plan",
            ));
        }
    }
    Ok(consumed_roots.len())
}

/// Decode and structurally validate a complete owned V2 plan.
///
/// Rejection returns no candidate plan or effect projection. The result is
/// deterministic over the exact input bytes; whitespace and key order are
/// normalized only after strict closed-field decoding. Source bindings remain
/// declarative and require a separate proof-backed history verifier before an
/// authority layer may consume this result.
#[must_use = "delta validation must be inspected before any candidate use"]
pub fn decode_delta_plan_v2(input: &[u8]) -> DeltaResultV2<StructurallyValidDeltaPlanV2> {
    if input.len() > MAX_INPUT_BYTES_V2 {
        return Err(reject_v2(
            DeltaRejectCodeV2::InputTooLarge,
            "delta plan input exceeds the byte limit",
        ));
    }
    let plan: RawDeltaPlanV2 = serde_json::from_slice(input).map_err(|error| {
        reject_v2(
            DeltaRejectCodeV2::DecodeInvalid,
            format!("input is not one closed V2 JSON plan: {error}"),
        )
    })?;
    validate_plan_v2(plan)
}
