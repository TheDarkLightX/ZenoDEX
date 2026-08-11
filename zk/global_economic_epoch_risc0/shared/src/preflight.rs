use alloc::vec::Vec;

use super::{
    decode_canonical_json_v1, derive_route_composition_assumption_root_v1, image_id_root_v1,
    sha256_root_v1, EconomicEpochGuestErrorV1, EconomicEpochGuestInputV1,
    EconomicEpochGuestResultV1, GlobalEconomicEpochJournalV1, PreparedEconomicEpochV1,
    PreparedRouteClaimV1, RootV1, RouteCompositionAssumptionInputV1, RouteCompositionJournalV1,
    RouteReceiptClaimV1, MAX_DIRECT_ROUTE_ASSUMPTIONS_V1, MAX_JOURNAL_BYTES_V1,
};

pub(super) struct RouteClaimExpectationV1<'a> {
    pub chain_id: &'a str,
    pub deployment_root: &'a RootV1,
    pub profile_root: &'a RootV1,
    pub writer_epoch: u64,
    pub occurrence_id: &'a RootV1,
    pub route_journal_root: &'a RootV1,
    pub route_assumption_root: &'a RootV1,
    pub pre_state_root: &'a RootV1,
}

pub(super) struct ValidatedRouteClaimV1 {
    pub prepared: PreparedRouteClaimV1,
    pub post_state_root: RootV1,
    pub module_leaf_occurrences: u64,
}

struct PreflightAccumulatorV1 {
    current_root: RootV1,
    total_journal_bytes: usize,
    module_leaf_occurrences: u64,
    route_claims: Vec<PreparedRouteClaimV1>,
}

impl PreflightAccumulatorV1 {
    fn new(certificate: &GlobalEconomicEpochJournalV1, capacity: usize) -> Self {
        Self {
            current_root: certificate.pre_state_root.clone(),
            total_journal_bytes: 0,
            module_leaf_occurrences: 0,
            route_claims: Vec::with_capacity(capacity),
        }
    }

    fn advance(
        mut self,
        index: usize,
        claim: &RouteReceiptClaimV1,
        certificate: &GlobalEconomicEpochJournalV1,
    ) -> EconomicEpochGuestResultV1<Self> {
        self.total_journal_bytes =
            checked_total_journal_bytes_v1(self.total_journal_bytes, claim.journal_bytes.len())?;
        let validated = validate_route_claim_v1(
            claim,
            &RouteClaimExpectationV1 {
                chain_id: &certificate.chain_id,
                deployment_root: &certificate.deployment_root,
                profile_root: &certificate.profile_root,
                writer_epoch: certificate.writer_epoch,
                occurrence_id: &certificate.ordered_occurrence_ids[index],
                route_journal_root: &certificate.ordered_route_journal_roots[index],
                route_assumption_root: &certificate.ordered_route_assumption_roots[index],
                pre_state_root: &self.current_root,
            },
        )?;
        self.module_leaf_occurrences = self
            .module_leaf_occurrences
            .checked_add(validated.module_leaf_occurrences)
            .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
                "epoch module leaf occurrences",
            ))?;
        self.current_root = validated.post_state_root;
        self.route_claims.push(validated.prepared);
        Ok(self)
    }
}

pub fn preflight_economic_epoch_guest_input_v1(
    input: &EconomicEpochGuestInputV1,
) -> EconomicEpochGuestResultV1<PreparedEconomicEpochV1> {
    let certificate = decode_epoch_certificate_v1(&input.certificate_journal_bytes)?;
    validate_direct_shape_v1(input.route_receipts.len(), &certificate)?;
    let accumulator = input.route_receipts.iter().enumerate().try_fold(
        PreflightAccumulatorV1::new(&certificate, input.route_receipts.len()),
        |state, (index, claim)| state.advance(index, claim, &certificate),
    )?;
    if accumulator.current_root != certificate.post_state_root {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch post-state root",
        ));
    }
    if accumulator.module_leaf_occurrences != certificate.module_leaf_occurrences {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch module leaf occurrences",
        ));
    }
    Ok(PreparedEconomicEpochV1 {
        certificate_journal_bytes: input.certificate_journal_bytes.clone(),
        root_image_id: certificate.root_image_id,
        route_claims: accumulator.route_claims,
    })
}

pub(super) fn decode_epoch_certificate_v1(
    journal_bytes: &[u8],
) -> EconomicEpochGuestResultV1<GlobalEconomicEpochJournalV1> {
    if journal_bytes.is_empty() || journal_bytes.len() > MAX_JOURNAL_BYTES_V1 {
        return Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "epoch certificate journal bytes",
        ));
    }
    let certificate: GlobalEconomicEpochJournalV1 =
        decode_canonical_json_v1(journal_bytes, "epoch certificate journal")?;
    certificate.validate()?;
    Ok(certificate)
}

fn validate_direct_shape_v1(
    count: usize,
    certificate: &GlobalEconomicEpochJournalV1,
) -> EconomicEpochGuestResultV1<()> {
    if count != certificate.ordered_occurrence_ids.len() {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch route receipt count",
        ));
    }
    if !(1..=MAX_DIRECT_ROUTE_ASSUMPTIONS_V1).contains(&count)
        || certificate.aggregation_levels != 0
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "direct epoch aggregation shape",
        ));
    }
    Ok(())
}

pub(super) fn checked_total_journal_bytes_v1(
    current: usize,
    next: usize,
) -> EconomicEpochGuestResultV1<usize> {
    if next == 0 || next > MAX_JOURNAL_BYTES_V1 {
        return Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "route receipt journal bytes",
        ));
    }
    let total = current
        .checked_add(next)
        .ok_or(EconomicEpochGuestErrorV1::Arithmetic(
            "total route journal bytes",
        ))?;
    if total > MAX_JOURNAL_BYTES_V1 {
        return Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "total route journal bytes",
        ));
    }
    Ok(total)
}

pub(super) fn validate_route_claim_v1(
    claim: &RouteReceiptClaimV1,
    expected: &RouteClaimExpectationV1<'_>,
) -> EconomicEpochGuestResultV1<ValidatedRouteClaimV1> {
    let journal: RouteCompositionJournalV1 =
        decode_canonical_json_v1(&claim.journal_bytes, "route receipt journal")?;
    journal.validate()?;
    let route_journal_root = journal.journal_root()?;
    if &route_journal_root != expected.route_journal_root
        || &journal.command_occurrence_id != expected.occurrence_id
    {
        return Err(EconomicEpochGuestErrorV1::InvalidOrder(
            "epoch route receipt sequence",
        ));
    }
    if journal.chain_id != expected.chain_id
        || &journal.deployment_root != expected.deployment_root
        || &journal.profile_root != expected.profile_root
        || journal.writer_epoch != expected.writer_epoch
        || &journal.pre_state_root != expected.pre_state_root
    {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch route receipt context",
        ));
    }
    let route_journal_digest = sha256_root_v1(&claim.journal_bytes);
    let expected_image_id = image_id_root_v1(claim.image_id)?;
    let assumption_root =
        derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
            profile_id: expected.profile_root,
            route_release_id: &journal.route_release_id,
            command_occurrence_id: &journal.command_occurrence_id,
            writer_epoch: expected.writer_epoch,
            route_journal_root: &route_journal_root,
            route_journal_digest: &route_journal_digest,
            expected_image_id: &expected_image_id,
        })?;
    if &assumption_root != expected.route_assumption_root {
        return Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch route assumption root",
        ));
    }
    let module_leaf_occurrences = u64::try_from(journal.ordered_lane_journal_roots.len())
        .map_err(|_| EconomicEpochGuestErrorV1::InvalidBounds("route module leaf count width"))?;
    Ok(ValidatedRouteClaimV1 {
        prepared: PreparedRouteClaimV1 {
            image_id: claim.image_id,
            journal_bytes: claim.journal_bytes.clone(),
        },
        post_state_root: journal.post_state_root,
        module_leaf_occurrences,
    })
}
