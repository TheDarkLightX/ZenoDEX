#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

mod aggregation;
mod preflight;

pub use aggregation::{
    preflight_aggregated_economic_epoch_guest_input_v1,
    preflight_command_aggregation_guest_input_v1, AggregatedEconomicEpochGuestInputV1,
    CommandAggregationGuestInputV1, CommandAggregationJournalV1, CommandAggregationReceiptClaimV1,
    GlobalEconomicRecursiveGuestInputV1, PreparedAggregatedEconomicEpochV1,
    PreparedCommandAggregationClaimV1, PreparedCommandAggregationV1,
    COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1,
};
pub use preflight::preflight_economic_epoch_guest_input_v1;

pub const GLOBAL_SETTLEMENT_ABI_V1: &str = "zenodex/global-settlement-abi/v1";
pub const ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1: &str = "zenodex/route-composition-assumption/v1";
pub const MAX_EPOCH_COMMANDS_V1: usize = 64;
pub const MAX_DIRECT_ROUTE_ASSUMPTIONS_V1: usize = 8;
pub const MAX_ROUTE_LANE_JOURNALS_V1: usize = 8;
pub const MAX_EPOCH_LEAF_OCCURRENCES_V1: u64 = 64;
pub const MAX_JOURNAL_BYTES_V1: usize = 1_048_576;
pub const MAX_EPOCH_GUEST_INPUT_BYTES_V1: u32 = 2 * 1_048_576;
pub const MAX_TOKEN_BYTES_V1: usize = 160;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EconomicEpochGuestErrorV1 {
    Decode(&'static str),
    Encode(&'static str),
    NonCanonical(&'static str),
    InvalidSchema(&'static str),
    InvalidToken(&'static str),
    InvalidRoot(&'static str),
    InvalidBounds(&'static str),
    InvalidOrder(&'static str),
    InvalidBinding(&'static str),
    Arithmetic(&'static str),
}

pub type EconomicEpochGuestResultV1<T> = Result<T, EconomicEpochGuestErrorV1>;

#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct RootV1(String);

impl RootV1 {
    pub fn parse(
        value: impl Into<String>,
        field: &'static str,
        allow_zero: bool,
    ) -> EconomicEpochGuestResultV1<Self> {
        let root = Self(value.into());
        root.validate(field, allow_zero)?;
        Ok(root)
    }

    pub fn from_digest(bytes: [u8; 32]) -> Self {
        Self(format!("0x{}", hex::encode(bytes)))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn is_zero(&self) -> bool {
        self.0 == "0x0000000000000000000000000000000000000000000000000000000000000000"
    }

    pub fn validate(
        &self,
        field: &'static str,
        allow_zero: bool,
    ) -> EconomicEpochGuestResultV1<()> {
        let bytes = self.0.as_bytes();
        let valid_hex = bytes.get(2..).is_some_and(|tail| {
            tail.iter()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
        });
        if bytes.len() != 66 || !self.0.starts_with("0x") || !valid_hex {
            return Err(EconomicEpochGuestErrorV1::InvalidRoot(field));
        }
        if !allow_zero && self.is_zero() {
            return Err(EconomicEpochGuestErrorV1::InvalidRoot(field));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RouteCompositionJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub ordered_lane_journal_roots: Vec<RootV1>,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl RouteCompositionJournalV1 {
    pub fn validate(&self) -> EconomicEpochGuestResultV1<()> {
        require_schema_v1(&self.schema, "route journal schema")?;
        require_token_v1(&self.chain_id, "route journal chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.pre_state_root,
            &self.post_state_root,
            &self.effect_plan_root,
        ] {
            root.validate("route journal required root", false)?;
        }
        self.terminal_obligations_root
            .validate("route journal terminal obligations root", true)?;
        if !(1..=MAX_ROUTE_LANE_JOURNALS_V1).contains(&self.ordered_lane_journal_roots.len()) {
            return Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "route lane journal roots",
            ));
        }
        require_unique_roots_v1(&self.ordered_lane_journal_roots, "route lane journal roots")
    }

    pub fn canonical_bytes(&self) -> EconomicEpochGuestResultV1<Vec<u8>> {
        self.validate()?;
        canonical_json_bytes_v1(self, "route journal")
    }

    pub fn journal_root(&self) -> EconomicEpochGuestResultV1<RootV1> {
        let bytes = self.canonical_bytes()?;
        hash_global_canonical_bytes_v1("route-composition-journal-v1", &bytes)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicEpochJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub height: u64,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub ordered_occurrence_ids: Vec<RootV1>,
    pub ordered_route_journal_roots: Vec<RootV1>,
    pub ordered_route_assumption_roots: Vec<RootV1>,
    pub module_leaf_occurrences: u64,
    pub aggregation_fanout: u64,
    pub aggregation_levels: u64,
    pub effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
    pub body_commitment: RootV1,
    pub data_availability_root: RootV1,
    pub finality_root: RootV1,
    pub source_manifest_root: RootV1,
    pub toolchain_manifest_root: RootV1,
    pub root_image_id: RootV1,
}

impl GlobalEconomicEpochJournalV1 {
    pub fn validate(&self) -> EconomicEpochGuestResultV1<()> {
        require_schema_v1(&self.schema, "epoch journal schema")?;
        require_token_v1(&self.chain_id, "epoch journal chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.pre_state_root,
            &self.post_state_root,
            &self.effect_plan_root,
            &self.body_commitment,
            &self.data_availability_root,
            &self.finality_root,
            &self.source_manifest_root,
            &self.toolchain_manifest_root,
            &self.root_image_id,
        ] {
            root.validate("epoch journal required root", false)?;
        }
        self.terminal_obligations_root
            .validate("epoch journal terminal obligations root", true)?;
        let count = self.ordered_occurrence_ids.len();
        if !(1..=MAX_EPOCH_COMMANDS_V1).contains(&count) {
            return Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "epoch command count",
            ));
        }
        if self.ordered_route_journal_roots.len() != count
            || self.ordered_route_assumption_roots.len() != count
        {
            return Err(EconomicEpochGuestErrorV1::InvalidBinding(
                "epoch route cardinality",
            ));
        }
        require_unique_roots_v1(&self.ordered_occurrence_ids, "epoch occurrences")?;
        require_unique_roots_v1(&self.ordered_route_journal_roots, "epoch route journals")?;
        require_unique_roots_v1(
            &self.ordered_route_assumption_roots,
            "epoch route assumptions",
        )?;
        let command_count = u64::try_from(count)
            .map_err(|_| EconomicEpochGuestErrorV1::InvalidBounds("epoch command count width"))?;
        if self.module_leaf_occurrences < command_count
            || self.module_leaf_occurrences > MAX_EPOCH_LEAF_OCCURRENCES_V1
        {
            return Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "epoch module leaf occurrences",
            ));
        }
        if self.aggregation_fanout != 8 || self.aggregation_levels > 2 {
            return Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "epoch aggregation shape",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RouteReceiptClaimV1 {
    pub image_id: [u32; 8],
    pub journal_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicEpochGuestInputV1 {
    pub certificate_journal_bytes: Vec<u8>,
    pub route_receipts: Vec<RouteReceiptClaimV1>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedRouteClaimV1 {
    pub image_id: [u32; 8],
    pub journal_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedEconomicEpochV1 {
    pub certificate_journal_bytes: Vec<u8>,
    pub root_image_id: RootV1,
    pub route_claims: Vec<PreparedRouteClaimV1>,
}

#[derive(Serialize)]
struct RouteCompositionAssumptionContentV1<'a> {
    schema: &'static str,
    profile_id: &'a RootV1,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    writer_epoch: u64,
    route_journal_root: &'a RootV1,
    route_journal_digest: &'a RootV1,
    expected_image_id: &'a RootV1,
}

pub struct RouteCompositionAssumptionInputV1<'a> {
    pub profile_id: &'a RootV1,
    pub route_release_id: &'a RootV1,
    pub command_occurrence_id: &'a RootV1,
    pub writer_epoch: u64,
    pub route_journal_root: &'a RootV1,
    pub route_journal_digest: &'a RootV1,
    pub expected_image_id: &'a RootV1,
}

pub fn derive_route_composition_assumption_root_v1(
    input: &RouteCompositionAssumptionInputV1<'_>,
) -> EconomicEpochGuestResultV1<RootV1> {
    for root in [
        input.profile_id,
        input.route_release_id,
        input.command_occurrence_id,
        input.route_journal_root,
        input.route_journal_digest,
        input.expected_image_id,
    ] {
        root.validate("route assumption root", false)?;
    }
    let content = RouteCompositionAssumptionContentV1 {
        schema: ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1,
        profile_id: input.profile_id,
        route_release_id: input.route_release_id,
        command_occurrence_id: input.command_occurrence_id,
        writer_epoch: input.writer_epoch,
        route_journal_root: input.route_journal_root,
        route_journal_digest: input.route_journal_digest,
        expected_image_id: input.expected_image_id,
    };
    let bytes = canonical_json_bytes_v1(&content, "route assumption")?;
    hash_global_canonical_bytes_v1("route-composition-assumption-v1", &bytes)
}

pub fn image_id_root_v1(image_id: [u32; 8]) -> EconomicEpochGuestResultV1<RootV1> {
    if image_id == [0; 8] {
        return Err(EconomicEpochGuestErrorV1::InvalidRoot(
            "route receipt image id",
        ));
    }
    let mut bytes = [0u8; 32];
    for (chunk, word) in bytes.chunks_exact_mut(4).zip(image_id) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    Ok(RootV1::from_digest(bytes))
}

pub fn canonical_json_bytes_v1<T: Serialize>(
    value: &T,
    label: &'static str,
) -> EconomicEpochGuestResultV1<Vec<u8>> {
    let canonical_value =
        serde_json::to_value(value).map_err(|_| EconomicEpochGuestErrorV1::Encode(label))?;
    serde_json::to_vec(&canonical_value).map_err(|_| EconomicEpochGuestErrorV1::Encode(label))
}

pub fn sha256_root_v1(bytes: &[u8]) -> RootV1 {
    RootV1::from_digest(Sha256::digest(bytes).into())
}

fn decode_canonical_json_v1<T: DeserializeOwned + Serialize>(
    bytes: &[u8],
    label: &'static str,
) -> EconomicEpochGuestResultV1<T> {
    let value =
        serde_json::from_slice(bytes).map_err(|_| EconomicEpochGuestErrorV1::Decode(label))?;
    let canonical = canonical_json_bytes_v1(&value, label)?;
    if canonical != bytes {
        return Err(EconomicEpochGuestErrorV1::NonCanonical(label));
    }
    Ok(value)
}

fn hash_global_canonical_bytes_v1(
    domain: &str,
    canonical_bytes: &[u8],
) -> EconomicEpochGuestResultV1<RootV1> {
    require_token_v1(domain, "hash domain")?;
    let mut digest = Sha256::new();
    digest.update(b"zenodex:");
    digest.update(domain.as_bytes());
    digest.update(b":v1\0");
    digest.update(canonical_bytes);
    Ok(RootV1::from_digest(digest.finalize().into()))
}

fn require_schema_v1(value: &str, field: &'static str) -> EconomicEpochGuestResultV1<()> {
    if value == GLOBAL_SETTLEMENT_ABI_V1 {
        Ok(())
    } else {
        Err(EconomicEpochGuestErrorV1::InvalidSchema(field))
    }
}

fn require_token_v1(value: &str, field: &'static str) -> EconomicEpochGuestResultV1<()> {
    let bytes = value.as_bytes();
    if bytes.is_empty()
        || bytes.len() > MAX_TOKEN_BYTES_V1
        || !bytes.iter().all(|byte| (0x21..=0x7e).contains(byte))
    {
        return Err(EconomicEpochGuestErrorV1::InvalidToken(field));
    }
    Ok(())
}

fn require_unique_roots_v1(
    roots: &[RootV1],
    field: &'static str,
) -> EconomicEpochGuestResultV1<()> {
    let mut seen = BTreeSet::new();
    for root in roots {
        root.validate(field, false)?;
        if !seen.insert(root.as_str()) {
            return Err(EconomicEpochGuestErrorV1::InvalidOrder(field));
        }
    }
    Ok(())
}
