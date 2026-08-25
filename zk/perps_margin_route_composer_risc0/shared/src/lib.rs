use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, RootV1, RouteCompositionJournalV1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_JOURNAL_BYTES_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    prepare_perps_margin_lane_coordinator_v1, PerpsMarginLaneCoordinatorGuestInputV1,
    PreparedPerpsMarginLaneCoordinatorV1,
};

pub const PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/perps-margin-route-composer-guest-input/v1";
pub const MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_V1: usize = 2 * 1_048_576;
pub const MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_U32_V1: u32 = 2 * 1_048_576;

/// Exact image words measured for the child lane coordinator at the source
/// revision that introduced this route guest. The host also compares this
/// value with the compiled child method before proving.
pub const PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1: [u32; 8] = [
    4_041_762_456,
    2_955_254_071,
    1_350_845_632,
    143_171_303,
    2_674_396_660,
    1_609_919_496,
    4_059_712_571,
    1_345_619_922,
];

const _: () = assert!(
    PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[0] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[1] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[2] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[3] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[4] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[5] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[6] != 0
        || PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1[7] != 0
);

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginRouteComposerGuestInputV1 {
    pub schema: String,
    pub lane_input: PerpsMarginLaneCoordinatorGuestInputV1,
    pub route_release_id: RootV1,
    /// Declared whole-economic roots are committed by this structural proof.
    /// Their state/effect refinement remains an outer verifier obligation.
    pub declared_pre_state_root: RootV1,
    pub declared_post_state_root: RootV1,
}

impl PerpsMarginRouteComposerGuestInputV1 {
    pub fn validate(&self) -> Result<(), PerpsMarginRouteComposerGuestErrorV1> {
        if self.schema != PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_SCHEMA_V1 {
            return Err(PerpsMarginRouteComposerGuestErrorV1::Schema);
        }
        self.lane_input
            .validate()
            .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Lane)?;
        for root in [
            &self.route_release_id,
            &self.declared_pre_state_root,
            &self.declared_post_state_root,
        ] {
            root.validate("perps margin structural route required root", false)
                .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Abi)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginRouteComposerGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    Lane,
    Abi,
    LaneJournalTooLarge,
    RouteJournalTooLarge,
}

impl PerpsMarginRouteComposerGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "perps margin route input is empty",
            Self::InputTooLarge => "perps margin route input exceeds release bound",
            Self::Decode => "perps margin route input decode failed",
            Self::NonCanonicalInput => "perps margin route input is noncanonical",
            Self::Schema => "perps margin route input schema rejected",
            Self::Lane => "perps margin route lane input rejected",
            Self::Abi => "perps margin route ABI validation failed",
            Self::LaneJournalTooLarge => "perps margin route child journal exceeds ABI bound",
            Self::RouteJournalTooLarge => "perps margin route journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for PerpsMarginRouteComposerGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "perps margin route guest rejected: {self:?}")
    }
}

impl std::error::Error for PerpsMarginRouteComposerGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedPerpsMarginRouteComposerV1 {
    pub input: PerpsMarginRouteComposerGuestInputV1,
    pub lane: PreparedPerpsMarginLaneCoordinatorV1,
    pub route_journal: RouteCompositionJournalV1,
    pub lane_journal_bytes: Vec<u8>,
    pub route_journal_bytes: Vec<u8>,
}

pub fn canonical_perps_margin_route_composer_guest_input_bytes_v1(
    input: &PerpsMarginRouteComposerGuestInputV1,
) -> Result<Vec<u8>, PerpsMarginRouteComposerGuestErrorV1> {
    input.validate()?;
    let bytes = canonical_bytes_v1(input).map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_perps_margin_route_composer_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedPerpsMarginRouteComposerV1, PerpsMarginRouteComposerGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: PerpsMarginRouteComposerGuestInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(PerpsMarginRouteComposerGuestErrorV1::NonCanonicalInput);
    }
    prepare_perps_margin_route_composer_v1(input)
}

pub fn prepare_perps_margin_route_composer_v1(
    input: PerpsMarginRouteComposerGuestInputV1,
) -> Result<PreparedPerpsMarginRouteComposerV1, PerpsMarginRouteComposerGuestErrorV1> {
    input.validate()?;
    let lane = prepare_perps_margin_lane_coordinator_v1(input.lane_input.clone())
        .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Lane)?;
    validate_journal_size_v1(
        &lane.lane_journal_bytes,
        PerpsMarginRouteComposerGuestErrorV1::LaneJournalTooLarge,
    )?;
    let lane_journal = &lane.lane_accepted.lane_journal;
    let route_journal = RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: lane_journal.chain_id.clone(),
        deployment_root: lane_journal.deployment_root.clone(),
        profile_root: lane_journal.profile_root.clone(),
        writer_epoch: lane_journal.writer_epoch,
        route_release_id: input.route_release_id.clone(),
        command_occurrence_id: lane_journal.command_occurrence_id.clone(),
        ordered_lane_journal_roots: vec![lane_journal
            .journal_root()
            .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Abi)?],
        pre_state_root: input.declared_pre_state_root.clone(),
        post_state_root: input.declared_post_state_root.clone(),
        effect_plan_root: lane_journal.effect_plan_root.clone(),
        terminal_obligations_root: lane_journal.terminal_obligations_root.clone(),
    };
    route_journal
        .validate()
        .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Abi)?;
    let route_journal_bytes = canonical_bytes_v1(&route_journal)
        .map_err(|_| PerpsMarginRouteComposerGuestErrorV1::Abi)?;
    validate_journal_size_v1(
        &route_journal_bytes,
        PerpsMarginRouteComposerGuestErrorV1::RouteJournalTooLarge,
    )?;
    Ok(PreparedPerpsMarginRouteComposerV1 {
        input,
        lane_journal_bytes: lane.lane_journal_bytes.clone(),
        lane,
        route_journal,
        route_journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), PerpsMarginRouteComposerGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(PerpsMarginRouteComposerGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_V1 {
        return Err(PerpsMarginRouteComposerGuestErrorV1::InputTooLarge);
    }
    Ok(())
}

fn validate_journal_size_v1(
    journal_bytes: &[u8],
    error: PerpsMarginRouteComposerGuestErrorV1,
) -> Result<(), PerpsMarginRouteComposerGuestErrorV1> {
    let journal_len = u64::try_from(journal_bytes.len()).map_err(|_| error)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(error);
    }
    Ok(())
}
