use alloc::string::String;
use alloc::vec::Vec;

use serde::{Deserialize, Serialize};

use super::preflight::{
    checked_total_journal_bytes_v1, decode_epoch_certificate_v1, validate_route_claim_v1,
    RouteClaimExpectationV1,
};
use super::{
    canonical_json_bytes_v1, decode_canonical_json_v1, hash_global_canonical_bytes_v1,
    image_id_root_v1, require_schema_v1, require_token_v1, require_unique_roots_v1,
    EconomicEpochGuestErrorV1, EconomicEpochGuestInputV1, EconomicEpochGuestResultV1,
    GlobalEconomicEpochJournalV1, PreparedRouteClaimV1, RootV1, RouteReceiptClaimV1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_DIRECT_ROUTE_ASSUMPTIONS_V1, MAX_EPOCH_COMMANDS_V1,
    MAX_JOURNAL_BYTES_V1,
};

pub const COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1: &str = "zenodex/command-aggregation-journal/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CommandAggregationJournalV1 {
    pub schema: String,
    pub settlement_abi: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub epoch_height: u64,
    pub group_index: u64,
    pub first_command_index: u64,
    pub ordered_occurrence_ids: Vec<RootV1>,
    pub ordered_route_journal_roots: Vec<RootV1>,
    pub ordered_route_assumption_roots: Vec<RootV1>,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub module_leaf_occurrences: u64,
}

impl CommandAggregationJournalV1 {
    pub fn validate(&self) -> EconomicEpochGuestResultV1<()> {
        if self.schema != COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1 {
            return Err(EconomicEpochGuestErrorV1::InvalidSchema(
                "command aggregation journal schema",
            ));
        }
        require_schema_v1(&self.settlement_abi, "command aggregation settlement ABI")?;
        require_token_v1(&self.chain_id, "command aggregation chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.pre_state_root,
            &self.post_state_root,
        ] {
            root.validate("command aggregation required root", false)?;
        }
        let command_count = self.validate_route_vectors_v1()?;
        self.validate_position_and_leaf_bounds_v1(command_count)
    }

    fn validate_route_vectors_v1(&self) -> EconomicEpochGuestResultV1<usize> {
        let command_count = self.ordered_occurrence_ids.len();
        if !(1..=MAX_DIRECT_ROUTE_ASSUMPTIONS_V1).contains(&command_count)
            || self.ordered_route_journal_roots.len() != command_count
            || self.ordered_route_assumption_roots.len() != command_count
        {
            return Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "command aggregation route count",
            ));
        }
        require_unique_roots_v1(
            &self.ordered_occurrence_ids,
            "command aggregation occurrences",
        )?;
        require_unique_roots_v1(
            &self.ordered_route_journal_roots,
            "command aggregation route journals",
        )?;
        require_unique_roots_v1(
            &self.ordered_route_assumption_roots,
            "command aggregation route assumptions",
        )?;
        Ok(command_count)
    }

    fn validate_position_and_leaf_bounds_v1(
        &self,
        command_count: usize,
    ) -> EconomicEpochGuestResultV1<()> {
        if self.group_index >= 8
            || self.first_command_index
                != self
                    .group_index
                    .checked_mul(8)
                    .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
                        "command aggregation first index",
                    ))?
        {
            return Err(EconomicEpochGuestErrorV1::InvalidOrder(
                "command aggregation group position",
            ));
        }
        let command_count_u64 = u64::try_from(command_count).map_err(|_| {
            EconomicEpochGuestErrorV1::InvalidBounds("command aggregation route count width")
        })?;
        let command_end = self
            .first_command_index
            .checked_add(command_count_u64)
            .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
                "command aggregation command end",
            ))?;
        if command_end > MAX_EPOCH_COMMANDS_V1 as u64
            || self.module_leaf_occurrences < command_count_u64
            || self.module_leaf_occurrences > command_count_u64 * 8
        {
            return Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "command aggregation occurrence bounds",
            ));
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> EconomicEpochGuestResultV1<Vec<u8>> {
        self.validate()?;
        canonical_json_bytes_v1(self, "command aggregation journal")
    }

    pub fn journal_root(&self) -> EconomicEpochGuestResultV1<RootV1> {
        let bytes = self.canonical_bytes()?;
        hash_global_canonical_bytes_v1("command-aggregation-journal-v1", &bytes)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CommandAggregationGuestInputV1 {
    pub aggregation_journal_bytes: Vec<u8>,
    pub route_receipts: Vec<RouteReceiptClaimV1>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CommandAggregationReceiptClaimV1 {
    pub image_id: [u32; 8],
    pub journal_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AggregatedEconomicEpochGuestInputV1 {
    pub certificate_journal_bytes: Vec<u8>,
    pub command_aggregation_receipts: Vec<CommandAggregationReceiptClaimV1>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum GlobalEconomicRecursiveGuestInputV1 {
    DirectEpoch(EconomicEpochGuestInputV1),
    CommandAggregation(CommandAggregationGuestInputV1),
    AggregatedEpoch(AggregatedEconomicEpochGuestInputV1),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedCommandAggregationV1 {
    pub aggregation_journal_bytes: Vec<u8>,
    pub route_claims: Vec<PreparedRouteClaimV1>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedCommandAggregationClaimV1 {
    pub image_id: [u32; 8],
    pub journal_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedAggregatedEconomicEpochV1 {
    pub certificate_journal_bytes: Vec<u8>,
    pub root_image_id: RootV1,
    pub command_aggregation_claims: Vec<PreparedCommandAggregationClaimV1>,
}

pub fn preflight_command_aggregation_guest_input_v1(
    input: &CommandAggregationGuestInputV1,
) -> EconomicEpochGuestResultV1<PreparedCommandAggregationV1> {
    if input.aggregation_journal_bytes.is_empty()
        || input.aggregation_journal_bytes.len() > MAX_JOURNAL_BYTES_V1
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "command aggregation journal bytes",
        ));
    }
    let journal = decode_command_aggregation_journal_v1(
        &input.aggregation_journal_bytes,
        "command aggregation journal",
    )?;
    if input.route_receipts.len() != journal.ordered_occurrence_ids.len() {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "command aggregation route receipt count",
        ));
    }

    let mut current_root = journal.pre_state_root.clone();
    let mut total_journal_bytes = 0usize;
    let mut module_leaf_occurrences = 0u64;
    let mut route_claims = Vec::with_capacity(input.route_receipts.len());
    for (index, claim) in input.route_receipts.iter().enumerate() {
        total_journal_bytes =
            checked_total_journal_bytes_v1(total_journal_bytes, claim.journal_bytes.len())?;
        let validated = validate_route_claim_v1(
            claim,
            &RouteClaimExpectationV1 {
                chain_id: &journal.chain_id,
                deployment_root: &journal.deployment_root,
                profile_root: &journal.profile_root,
                writer_epoch: journal.writer_epoch,
                occurrence_id: &journal.ordered_occurrence_ids[index],
                route_journal_root: &journal.ordered_route_journal_roots[index],
                route_assumption_root: &journal.ordered_route_assumption_roots[index],
                pre_state_root: &current_root,
            },
        )?;
        module_leaf_occurrences = module_leaf_occurrences
            .checked_add(validated.module_leaf_occurrences)
            .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
                "command aggregation module leaves",
            ))?;
        current_root = validated.post_state_root;
        route_claims.push(validated.prepared);
    }
    if current_root != journal.post_state_root
        || module_leaf_occurrences != journal.module_leaf_occurrences
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "command aggregation terminal binding",
        ));
    }
    Ok(PreparedCommandAggregationV1 {
        aggregation_journal_bytes: input.aggregation_journal_bytes.clone(),
        route_claims,
    })
}

pub fn preflight_aggregated_economic_epoch_guest_input_v1(
    input: &AggregatedEconomicEpochGuestInputV1,
) -> EconomicEpochGuestResultV1<PreparedAggregatedEconomicEpochV1> {
    let certificate = decode_epoch_certificate_v1(&input.certificate_journal_bytes)?;
    let command_count = certificate.ordered_occurrence_ids.len();
    if !(9..=MAX_EPOCH_COMMANDS_V1).contains(&command_count) || certificate.aggregation_levels != 1
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "aggregated epoch shape",
        ));
    }
    let expected_group_count = command_count.div_ceil(MAX_DIRECT_ROUTE_ASSUMPTIONS_V1);
    if input.command_aggregation_receipts.len() != expected_group_count {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "aggregated epoch receipt count",
        ));
    }

    let expected_aggregation_image_id = certificate.root_image_id.clone();
    let mut current_root = certificate.pre_state_root.clone();
    let mut total_journal_bytes = 0usize;
    let mut module_leaf_occurrences = 0u64;
    let mut prepared_claims = Vec::with_capacity(expected_group_count);
    for (group_index, claim) in input.command_aggregation_receipts.iter().enumerate() {
        total_journal_bytes =
            checked_total_journal_bytes_v1(total_journal_bytes, claim.journal_bytes.len())?;
        if image_id_root_v1(claim.image_id)? != expected_aggregation_image_id {
            return Err(EconomicEpochGuestErrorV1::InvalidBinding(
                "command aggregation image id",
            ));
        }
        let journal = decode_command_aggregation_journal_v1(
            &claim.journal_bytes,
            "command aggregation receipt journal",
        )?;
        validate_group_partition_v1(group_index, &journal, &certificate, &current_root)?;
        module_leaf_occurrences = module_leaf_occurrences
            .checked_add(journal.module_leaf_occurrences)
            .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
                "aggregated epoch module leaves",
            ))?;
        current_root = journal.post_state_root;
        prepared_claims.push(PreparedCommandAggregationClaimV1 {
            image_id: claim.image_id,
            journal_bytes: claim.journal_bytes.clone(),
        });
    }
    if current_root != certificate.post_state_root
        || module_leaf_occurrences != certificate.module_leaf_occurrences
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "aggregated epoch terminal binding",
        ));
    }
    Ok(PreparedAggregatedEconomicEpochV1 {
        certificate_journal_bytes: input.certificate_journal_bytes.clone(),
        root_image_id: certificate.root_image_id,
        command_aggregation_claims: prepared_claims,
    })
}

fn decode_command_aggregation_journal_v1(
    bytes: &[u8],
    label: &'static str,
) -> EconomicEpochGuestResultV1<CommandAggregationJournalV1> {
    let journal: CommandAggregationJournalV1 = decode_canonical_json_v1(bytes, label)?;
    journal.validate()?;
    Ok(journal)
}

fn validate_group_partition_v1(
    group_index: usize,
    journal: &CommandAggregationJournalV1,
    certificate: &GlobalEconomicEpochJournalV1,
    current_root: &RootV1,
) -> EconomicEpochGuestResultV1<()> {
    let start = group_index
        .checked_mul(MAX_DIRECT_ROUTE_ASSUMPTIONS_V1)
        .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
            "aggregated epoch group start",
        ))?;
    let end = core::cmp::min(
        start + MAX_DIRECT_ROUTE_ASSUMPTIONS_V1,
        certificate.ordered_occurrence_ids.len(),
    );
    let expected_group_index = u64::try_from(group_index).map_err(|_| {
        EconomicEpochGuestErrorV1::InvalidBounds("aggregated epoch group index width")
    })?;
    let expected_start = u64::try_from(start).map_err(|_| {
        EconomicEpochGuestErrorV1::InvalidBounds("aggregated epoch command index width")
    })?;
    if journal.group_index != expected_group_index
        || journal.first_command_index != expected_start
        || journal.chain_id != certificate.chain_id
        || journal.settlement_abi != GLOBAL_SETTLEMENT_ABI_V1
        || journal.deployment_root != certificate.deployment_root
        || journal.profile_root != certificate.profile_root
        || journal.writer_epoch != certificate.writer_epoch
        || journal.epoch_height != certificate.height
        || journal.ordered_occurrence_ids.as_slice()
            != &certificate.ordered_occurrence_ids[start..end]
        || journal.ordered_route_journal_roots.as_slice()
            != &certificate.ordered_route_journal_roots[start..end]
        || journal.ordered_route_assumption_roots.as_slice()
            != &certificate.ordered_route_assumption_roots[start..end]
        || &journal.pre_state_root != current_root
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "aggregated epoch canonical partition",
        ));
    }
    Ok(())
}
