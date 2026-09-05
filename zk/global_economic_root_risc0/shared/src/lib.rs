//! Tagged private dispatch over unchanged, closed initialization and epoch journals.
//! Successful preparation carries no publication authority or cryptographic receipt.

use core::fmt;
use zenodex_economic_initial_state_risc0_shared::{
    prepare_economic_initial_state_from_canonical_bytes_v1, EconomicInitialStateGuestErrorV1,
    MAX_ECONOMIC_INITIAL_STATE_GUEST_INPUT_BYTES_V1,
};
use zenodex_global_economic_epoch_risc0_shared::{
    preflight_aggregated_economic_epoch_guest_input_v1,
    preflight_command_aggregation_guest_input_v1, preflight_economic_epoch_guest_input_v1,
    EconomicEpochGuestErrorV1, GlobalEconomicRecursiveGuestInputV1, MAX_EPOCH_GUEST_INPUT_BYTES_V1,
};

pub const ROOT_INPUT_MAGIC_V1: &[u8; 8] = b"ZDXROOT1";
pub const ROOT_INPUT_HEADER_BYTES_V1: usize = 13;
pub const MAX_ROOT_GUEST_INPUT_BYTES_V1: usize =
    ROOT_INPUT_HEADER_BYTES_V1 + MAX_ECONOMIC_INITIAL_STATE_GUEST_INPUT_BYTES_V1;

#[derive(Clone, Debug)]
pub enum RootGuestInputV1 {
    InitialStateV1(Vec<u8>),
    RecursiveEpochV1(GlobalEconomicRecursiveGuestInputV1),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RootStatementKindV1 {
    Initialization,
    DirectEpoch,
    CommandAggregation,
    AggregatedEpoch,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RootChildClaimV1 {
    image_id: [u32; 8],
    journal_bytes: Vec<u8>,
}

impl RootChildClaimV1 {
    pub fn image_id(&self) -> [u32; 8] {
        self.image_id
    }
    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedRootV1 {
    kind: RootStatementKindV1,
    journal_bytes: Vec<u8>,
    root_image_id: Option<String>,
    child_claims: Vec<RootChildClaimV1>,
}

impl PreparedRootV1 {
    pub fn kind(&self) -> RootStatementKindV1 {
        self.kind
    }
    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }
    pub fn root_image_id(&self) -> Option<&str> {
        self.root_image_id.as_deref()
    }
    pub fn child_claims(&self) -> &[RootChildClaimV1] {
        &self.child_claims
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum RootGuestErrorV1 {
    Frame,
    Tag,
    Bounds,
    Decode,
    NonCanonical,
    InitialState(EconomicInitialStateGuestErrorV1),
    Epoch(EconomicEpochGuestErrorV1),
}

impl fmt::Display for RootGuestErrorV1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "economic root input rejected: {self:?}")
    }
}
impl std::error::Error for RootGuestErrorV1 {}

fn payload_bound(tag: u8) -> Result<usize, RootGuestErrorV1> {
    match tag {
        0 => Ok(MAX_ECONOMIC_INITIAL_STATE_GUEST_INPUT_BYTES_V1),
        1 => usize::try_from(MAX_EPOCH_GUEST_INPUT_BYTES_V1).map_err(|_| RootGuestErrorV1::Bounds),
        _ => Err(RootGuestErrorV1::Tag),
    }
}

pub fn canonical_root_input_bytes_v1(
    input: &RootGuestInputV1,
) -> Result<Vec<u8>, RootGuestErrorV1> {
    let (tag, payload) = match input {
        RootGuestInputV1::InitialStateV1(bytes) => (0, bytes.clone()),
        RootGuestInputV1::RecursiveEpochV1(value) => (
            1,
            postcard::to_allocvec(value).map_err(|_| RootGuestErrorV1::Decode)?,
        ),
    };
    if payload.is_empty() || payload.len() > payload_bound(tag)? {
        return Err(RootGuestErrorV1::Bounds);
    }
    let length = u32::try_from(payload.len()).map_err(|_| RootGuestErrorV1::Bounds)?;
    let mut bytes = Vec::with_capacity(ROOT_INPUT_HEADER_BYTES_V1 + payload.len());
    bytes.extend_from_slice(ROOT_INPUT_MAGIC_V1);
    bytes.push(tag);
    bytes.extend_from_slice(&length.to_le_bytes());
    bytes.extend_from_slice(&payload);
    // The encoder is also an admission boundary for typed but caller-created input.
    prepare_root_input_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_root_input_v1(bytes: &[u8]) -> Result<PreparedRootV1, RootGuestErrorV1> {
    if bytes.len() < ROOT_INPUT_HEADER_BYTES_V1 || &bytes[..8] != ROOT_INPUT_MAGIC_V1 {
        return Err(RootGuestErrorV1::Frame);
    }
    let bound = payload_bound(bytes[8])?;
    let length = u32::from_le_bytes(
        bytes[9..13]
            .try_into()
            .map_err(|_| RootGuestErrorV1::Frame)?,
    );
    let length = usize::try_from(length).map_err(|_| RootGuestErrorV1::Bounds)?;
    if length == 0 || length > bound {
        return Err(RootGuestErrorV1::Bounds);
    }
    if bytes.len() != ROOT_INPUT_HEADER_BYTES_V1 + length {
        return Err(RootGuestErrorV1::Frame);
    }
    let payload = &bytes[ROOT_INPUT_HEADER_BYTES_V1..];
    if bytes[8] == 0 {
        let prepared = prepare_economic_initial_state_from_canonical_bytes_v1(payload)
            .map_err(RootGuestErrorV1::InitialState)?;
        return Ok(PreparedRootV1 {
            kind: RootStatementKindV1::Initialization,
            journal_bytes: prepared.journal_bytes().to_vec(),
            root_image_id: Some(prepared.input().statement.root_image_id.as_str().to_owned()),
            child_claims: Vec::new(),
        });
    }
    let (input, trailing): (GlobalEconomicRecursiveGuestInputV1, &[u8]) =
        postcard::take_from_bytes(payload).map_err(|_| RootGuestErrorV1::Decode)?;
    if !trailing.is_empty()
        || postcard::to_allocvec(&input).map_err(|_| RootGuestErrorV1::Decode)? != payload
    {
        return Err(RootGuestErrorV1::NonCanonical);
    }
    prepare_epoch(input)
}

fn prepare_epoch(
    input: GlobalEconomicRecursiveGuestInputV1,
) -> Result<PreparedRootV1, RootGuestErrorV1> {
    match input {
        GlobalEconomicRecursiveGuestInputV1::DirectEpoch(input) => {
            let value =
                preflight_economic_epoch_guest_input_v1(&input).map_err(RootGuestErrorV1::Epoch)?;
            Ok(PreparedRootV1 {
                kind: RootStatementKindV1::DirectEpoch,
                journal_bytes: value.certificate_journal_bytes,
                root_image_id: Some(value.root_image_id.as_str().to_owned()),
                child_claims: value
                    .route_claims
                    .into_iter()
                    .map(|c| RootChildClaimV1 {
                        image_id: c.image_id,
                        journal_bytes: c.journal_bytes,
                    })
                    .collect(),
            })
        }
        GlobalEconomicRecursiveGuestInputV1::CommandAggregation(input) => {
            let value = preflight_command_aggregation_guest_input_v1(&input)
                .map_err(RootGuestErrorV1::Epoch)?;
            Ok(PreparedRootV1 {
                kind: RootStatementKindV1::CommandAggregation,
                journal_bytes: value.aggregation_journal_bytes,
                root_image_id: None,
                child_claims: value
                    .route_claims
                    .into_iter()
                    .map(|c| RootChildClaimV1 {
                        image_id: c.image_id,
                        journal_bytes: c.journal_bytes,
                    })
                    .collect(),
            })
        }
        GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(input) => {
            let value = preflight_aggregated_economic_epoch_guest_input_v1(&input)
                .map_err(RootGuestErrorV1::Epoch)?;
            // The reused preflight requires each aggregate child image to equal
            // this certificate's root image. The host binds that image to its ELF.
            Ok(PreparedRootV1 {
                kind: RootStatementKindV1::AggregatedEpoch,
                journal_bytes: value.certificate_journal_bytes,
                root_image_id: Some(value.root_image_id.as_str().to_owned()),
                child_claims: value
                    .command_aggregation_claims
                    .into_iter()
                    .map(|c| RootChildClaimV1 {
                        image_id: c.image_id,
                        journal_bytes: c.journal_bytes,
                    })
                    .collect(),
            })
        }
    }
}
