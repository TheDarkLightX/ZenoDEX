use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_zdex_tokenomics_burn_lane_v1, GlobalEconomicEffectPlanV1,
    LaneCompositionJournalV1, LaneIdV1, LaneModuleReleaseV1, LaneModuleTransitionJournalV1,
    ReleaseStatusV1, RootV1, ZDEXBurnJournalV1, ZDEXTokenomicsBurnCoordinatorContextV1,
    ZDEXTokenomicsBurnLaneCandidateV1, ZDEXTokenomicsBurnPrivatePortV1,
    ZDEXTokenomicsLaneCompositionAcceptedV1, ZDEXTokenomicsLaneCompositionResultV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1, ZDEXTokenomicsLaneStateV1, MAX_JOURNAL_BYTES_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
};

pub const ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-lane-coordinator-guest-input/v1";
pub const MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;
pub const MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_JOURNAL_BYTES_V1: u64 = 65_536;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsLaneCoordinatorGuestInputV1 {
    pub schema: String,
    pub module_release: LaneModuleReleaseV1,
    pub context: ZDEXTokenomicsBurnCoordinatorContextV1,
    pub module_journal: LaneModuleTransitionJournalV1,
    pub private_port: ZDEXTokenomicsBurnPrivatePortV1,
    pub pre_state: ZDEXTokenomicsLaneStateV1,
    pub post_state: ZDEXTokenomicsLaneStateV1,
    pub burn_journal: ZDEXBurnJournalV1,
    pub module_effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXTokenomicsLaneCoordinatorGuestInputV1 {
    pub fn validate(&self) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
        if self.schema != ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1 {
            return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Schema);
        }
        self.module_release
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.context
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.module_journal
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.private_port
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.pre_state
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.post_state
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.burn_journal
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.module_effects
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        validate_module_release_v1(self)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ZDEXTokenomicsLaneCoordinatorGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    Abi,
    ModuleRelease,
    ModuleReleaseBinding,
    Rejected(ZDEXTokenomicsLaneCoordinatorRejectCodeV1),
    BurnJournalTooLarge,
    LaneJournalTooLarge,
    ImageIdEncoding,
}

impl ZDEXTokenomicsLaneCoordinatorGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "ZDEX tokenomics coordinator guest input is empty",
            Self::InputTooLarge => "ZDEX tokenomics coordinator guest input exceeds release bound",
            Self::Decode => "ZDEX tokenomics coordinator guest input decode failed",
            Self::NonCanonicalInput => "ZDEX tokenomics coordinator guest input is noncanonical",
            Self::Schema => "ZDEX tokenomics coordinator guest input schema is unsupported",
            Self::Abi => "ZDEX tokenomics coordinator ABI validation failed",
            Self::ModuleRelease => "ZDEX tokenomics coordinator module release rejected",
            Self::ModuleReleaseBinding => {
                "ZDEX tokenomics coordinator module release binding rejected"
            }
            Self::Rejected(_) => "ZDEX tokenomics complete lane composition rejected",
            Self::BurnJournalTooLarge => "ZDEX tokenomics child burn journal exceeds release bound",
            Self::LaneJournalTooLarge => {
                "ZDEX tokenomics coordinator journal exceeds release bound"
            }
            Self::ImageIdEncoding => "ZDEX tokenomics module image ID encoding rejected",
        }
    }
}

impl fmt::Display for ZDEXTokenomicsLaneCoordinatorGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "ZDEX tokenomics lane coordinator guest rejected: {self:?}"
        )
    }
}

impl std::error::Error for ZDEXTokenomicsLaneCoordinatorGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedZDEXTokenomicsLaneCoordinatorV1 {
    pub input: ZDEXTokenomicsLaneCoordinatorGuestInputV1,
    pub accepted: ZDEXTokenomicsLaneCompositionAcceptedV1,
    pub burn_journal_bytes: Vec<u8>,
    pub lane_journal_bytes: Vec<u8>,
}

impl PreparedZDEXTokenomicsLaneCoordinatorV1 {
    pub fn lane_journal(&self) -> &LaneCompositionJournalV1 {
        &self.accepted.lane_journal
    }
}

pub fn canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1(
    input: &ZDEXTokenomicsLaneCoordinatorGuestInputV1,
) -> Result<Vec<u8>, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let bytes =
        canonical_bytes_v1(input).map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedZDEXTokenomicsLaneCoordinatorV1, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: ZDEXTokenomicsLaneCoordinatorGuestInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::NonCanonicalInput);
    }
    prepare_zdex_tokenomics_lane_coordinator_v1(input)
}

pub fn prepare_zdex_tokenomics_lane_coordinator_v1(
    input: ZDEXTokenomicsLaneCoordinatorGuestInputV1,
) -> Result<PreparedZDEXTokenomicsLaneCoordinatorV1, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let input_bytes =
        canonical_bytes_v1(&input).map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&input_bytes)?;

    let result = compose_zdex_tokenomics_burn_lane_v1(ZDEXTokenomicsBurnLaneCandidateV1 {
        context: &input.context,
        module_journal: &input.module_journal,
        private_port: &input.private_port,
        pre_state: &input.pre_state,
        post_state: &input.post_state,
        burn_journal: &input.burn_journal,
        module_effects: &input.module_effects,
    })
    .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    let accepted = match result {
        ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) => accepted,
        ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) => {
            return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Rejected(
                rejected.code,
            ));
        }
    };
    accepted
        .validate()
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;

    let burn_journal_bytes = canonical_bytes_v1(&input.burn_journal)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_burn_journal_size_v1(&input.module_release, &burn_journal_bytes)?;
    let lane_journal_bytes = canonical_bytes_v1(&accepted.lane_journal)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_lane_journal_size_v1(&lane_journal_bytes)?;

    Ok(PreparedZDEXTokenomicsLaneCoordinatorV1 {
        input,
        accepted: *accepted,
        burn_journal_bytes,
        lane_journal_bytes,
    })
}

pub fn risc0_digest_bytes_from_root_v1(
    root: &RootV1,
) -> Result<[u8; 32], ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    root.validate("ZDEX tokenomics module image ID", false)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ImageIdEncoding)?;
    let text = root
        .as_str()
        .strip_prefix("0x")
        .ok_or(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ImageIdEncoding)?;
    if text.len() != 64 {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ImageIdEncoding);
    }
    let mut bytes = [0_u8; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        let offset = index * 2;
        let high = decode_hex_nibble_v1(text.as_bytes()[offset])?;
        let low = decode_hex_nibble_v1(text.as_bytes()[offset + 1])?;
        *byte = (high << 4) | low;
    }
    Ok(bytes)
}

fn validate_module_release_v1(
    input: &ZDEXTokenomicsLaneCoordinatorGuestInputV1,
) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    let release = &input.module_release;
    let derived = release
        .derived_release_id()
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleRelease)?;
    if release.release_id != derived
        || release.status != ReleaseStatusV1::SHADOW
        || release.accepts_new_objects
        || release.lane_id != LaneIdV1::ZDEX_TOKENOMICS
        || !release
            .command_variants
            .iter()
            .any(|command| command == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
    {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleRelease);
    }
    if input.context.tokenomics_module_release_id != release.release_id
        || input.module_journal.module_release_id != release.release_id
        || input.private_port.module_release_id != release.release_id
        || input.burn_journal.tokenomics_module_release_id != release.release_id
    {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleReleaseBinding);
    }
    risc0_digest_bytes_from_root_v1(&release.guest_image_id)?;
    Ok(())
}

fn validate_input_size_v1(
    input_bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1 {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::InputTooLarge);
    }
    Ok(())
}

fn validate_burn_journal_size_v1(
    release: &LaneModuleReleaseV1,
    bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    let length = u64::try_from(bytes.len())
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::BurnJournalTooLarge)?;
    if length == 0 || length > release.max_journal_bytes.min(MAX_JOURNAL_BYTES_V1) {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::BurnJournalTooLarge);
    }
    Ok(())
}

fn validate_lane_journal_size_v1(
    bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    let length = u64::try_from(bytes.len())
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::LaneJournalTooLarge)?;
    if length == 0
        || length > MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_JOURNAL_BYTES_V1.min(MAX_JOURNAL_BYTES_V1)
    {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::LaneJournalTooLarge);
    }
    Ok(())
}

fn decode_hex_nibble_v1(value: u8) -> Result<u8, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        b'A'..=b'F' => Ok(value - b'A' + 10),
        _ => Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ImageIdEncoding),
    }
}
