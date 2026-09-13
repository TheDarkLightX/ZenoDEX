//! Exact bounded replay frame for the margin/global V2 statement guest.
//!
//! This bridge owns only the `ZDPM2\0` frame boundary.  It reconstructs the
//! existing typed V2 values, runs the existing joint transition, and renders
//! the unchanged two-root statement journal.  It grants no route, profile,
//! receipt, or publication authority.

use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    PerpsMarginAccountV1, PerpsMarginCommandV1, PerpsMarginMarketStatusV1, PerpsMarginStateV1,
    RootV1, PERPS_MARGIN_MODULE_SCHEMA_V1,
};
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, AssetLaneCustodyStateV2, EconomicCommandOccurrenceV2,
    GlobalEconomicStateV2, RootV2, MAX_CANONICAL_INPUT_BYTES_V2,
};

use crate::{
    transition_perps_margin_global_v2, PerpsMarginClaimBindingV2, PerpsMarginGlobalRejectCodeV2,
    PerpsMarginGlobalResultV2, PerpsMarginOracleV2, PerpsMarginStateV2,
    MAX_PERPS_MARGIN_ACCOUNTS_V2, PERPS_MARGIN_MODULE_SCHEMA_V2,
};

pub const PERPS_MARGIN_FRAME_MAGIC_V2: &[u8; 6] = b"ZDPM2\0";
pub const PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2: &str =
    "zenodex/perps-margin-global-statement/v2";
pub const PERPS_MARGIN_REQUEST_SCHEMA_V2: &str = "zenodex/perps-margin-request/v2";
pub const MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2: usize = MAX_CANONICAL_INPUT_BYTES_V2;
pub const MAX_PERPS_MARGIN_FRAME_BYTES_V2: usize =
    PERPS_MARGIN_FRAME_MAGIC_V2.len() + 4 * (4 + MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginGlobalFrameErrorV2 {
    EmptyFrame,
    FrameTooLarge,
    FrameMagic,
    FrameStructure,
    FrameComponentBounds,
    FrameComponentTruncated,
    FrameTrailingBytes,
    Assets,
    Margin,
    GlobalState,
    Request,
    Transition,
    Rejected(PerpsMarginGlobalRejectCodeV2),
    SuccessorEncoding,
    SuccessorTooLarge,
    Journal,
}

impl fmt::Display for PerpsMarginGlobalFrameErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "perps margin global frame rejected: {self:?}")
    }
}

impl std::error::Error for PerpsMarginGlobalFrameErrorV2 {}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PerpsMarginClaimBindingWireV2 {
    account_id: String,
    obligation_id: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PerpsMarginStateWireV2 {
    schema: String,
    module_release_id: RootV1,
    market_id: String,
    collateral_asset: String,
    index_price_e8: u128,
    maintenance_margin_bps: u64,
    depeg_buffer_bps: u64,
    max_position_abs: u128,
    market_status: PerpsMarginMarketStatusV1,
    accounts: Vec<PerpsMarginAccountV1>,
    active_claims: Vec<PerpsMarginClaimBindingWireV2>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PerpsMarginOracleWireV2 {
    authority_root: RootV2,
    occurrence_root: RootV2,
    price_e8: u128,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PerpsMarginRequestWireV2 {
    schema: String,
    command: PerpsMarginCommandV1,
    occurrence: EconomicCommandOccurrenceV2,
    oracle: Option<PerpsMarginOracleWireV2>,
}

struct PerpsMarginRequestV2 {
    command: PerpsMarginCommandV1,
    occurrence: EconomicCommandOccurrenceV2,
    oracle: Option<PerpsMarginOracleV2>,
}

#[derive(Serialize)]
struct PerpsMarginRequestCanonicalV2<'a> {
    schema: &'static str,
    command: &'a PerpsMarginCommandV1,
    occurrence: &'a EconomicCommandOccurrenceV2,
    oracle: Option<&'a PerpsMarginOracleV2>,
}

#[derive(Serialize)]
struct PerpsMarginGlobalStatementV2<'a> {
    schema: &'static str,
    input_root: &'a RootV2,
    refinement_root: &'a RootV2,
}

/// Decodes one exact frame, reruns the native transition, and renders the only
/// statement journal a matching guest may commit.
pub fn prepare_perps_margin_global_from_frame_v2(
    frame: &[u8],
) -> Result<Vec<u8>, PerpsMarginGlobalFrameErrorV2> {
    let [assets_bytes, margin_bytes, state_bytes, request_bytes] = parse_frame_v2(frame)?;
    let assets = decode_canonical_v2::<AssetLaneCustodyStateV2>(assets_bytes)
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Assets)?;
    let margin = decode_margin_state_v2(margin_bytes)?;
    let state = decode_canonical_v2::<GlobalEconomicStateV2>(state_bytes)
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::GlobalState)?;
    let request = decode_request_v2(request_bytes)?;

    let accepted = match transition_perps_margin_global_v2(
        &assets,
        &margin,
        &state,
        &request.command,
        &request.occurrence,
        request.oracle.as_ref(),
    )
    .map_err(|_| PerpsMarginGlobalFrameErrorV2::Transition)?
    {
        PerpsMarginGlobalResultV2::Accepted(value) => value,
        PerpsMarginGlobalResultV2::Rejected(value) => {
            return Err(PerpsMarginGlobalFrameErrorV2::Rejected(value.code))
        }
    };

    for successor in [
        canonical_bytes_v2(accepted.post_assets()),
        accepted.post_margin().canonical_bytes(),
        canonical_bytes_v2(accepted.post_state()),
    ] {
        let successor = successor.map_err(|_| PerpsMarginGlobalFrameErrorV2::SuccessorEncoding)?;
        if successor.len() > MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2 {
            return Err(PerpsMarginGlobalFrameErrorV2::SuccessorTooLarge);
        }
    }

    let input_root = accepted.statement_root().clone();
    let refinement_root = accepted
        .refinement()
        .refinement_root()
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Journal)?;
    let journal_bytes = canonical_bytes_v2(&PerpsMarginGlobalStatementV2 {
        schema: PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2,
        input_root: &input_root,
        refinement_root: &refinement_root,
    })
    .map_err(|_| PerpsMarginGlobalFrameErrorV2::Journal)?;
    if journal_bytes.is_empty() || journal_bytes.len() > MAX_CANONICAL_INPUT_BYTES_V2 {
        return Err(PerpsMarginGlobalFrameErrorV2::Journal);
    }

    Ok(journal_bytes)
}

fn parse_frame_v2(frame: &[u8]) -> Result<[&[u8]; 4], PerpsMarginGlobalFrameErrorV2> {
    if frame.is_empty() {
        return Err(PerpsMarginGlobalFrameErrorV2::EmptyFrame);
    }
    if frame.len() > MAX_PERPS_MARGIN_FRAME_BYTES_V2 {
        return Err(PerpsMarginGlobalFrameErrorV2::FrameTooLarge);
    }
    if frame.get(..PERPS_MARGIN_FRAME_MAGIC_V2.len()) != Some(PERPS_MARGIN_FRAME_MAGIC_V2) {
        return Err(PerpsMarginGlobalFrameErrorV2::FrameMagic);
    }

    let mut cursor = PERPS_MARGIN_FRAME_MAGIC_V2.len();
    let mut components = [&frame[0..0]; 4];
    for component in &mut components {
        let length_end = cursor
            .checked_add(4)
            .ok_or(PerpsMarginGlobalFrameErrorV2::FrameStructure)?;
        let length_bytes = frame
            .get(cursor..length_end)
            .ok_or(PerpsMarginGlobalFrameErrorV2::FrameStructure)?;
        let mut width = [0_u8; 4];
        width.copy_from_slice(length_bytes);
        let length = usize::try_from(u32::from_le_bytes(width))
            .map_err(|_| PerpsMarginGlobalFrameErrorV2::FrameComponentBounds)?;
        if !(1..=MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2).contains(&length) {
            return Err(PerpsMarginGlobalFrameErrorV2::FrameComponentBounds);
        }
        cursor = length_end;
        let component_end = cursor
            .checked_add(length)
            .ok_or(PerpsMarginGlobalFrameErrorV2::FrameComponentTruncated)?;
        *component = frame
            .get(cursor..component_end)
            .ok_or(PerpsMarginGlobalFrameErrorV2::FrameComponentTruncated)?;
        cursor = component_end;
    }
    if cursor != frame.len() {
        return Err(PerpsMarginGlobalFrameErrorV2::FrameTrailingBytes);
    }
    Ok(components)
}

fn decode_margin_state_v2(
    bytes: &[u8],
) -> Result<PerpsMarginStateV2, PerpsMarginGlobalFrameErrorV2> {
    if !(1..=MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2).contains(&bytes.len()) {
        return Err(PerpsMarginGlobalFrameErrorV2::Margin);
    }
    let wire: PerpsMarginStateWireV2 =
        serde_json::from_slice(bytes).map_err(|_| PerpsMarginGlobalFrameErrorV2::Margin)?;
    if wire.schema != PERPS_MARGIN_MODULE_SCHEMA_V2
        || wire.accounts.len() > MAX_PERPS_MARGIN_ACCOUNTS_V2
        || wire.active_claims.len() > MAX_PERPS_MARGIN_ACCOUNTS_V2
    {
        return Err(PerpsMarginGlobalFrameErrorV2::Margin);
    }
    let active_claims = wire
        .active_claims
        .into_iter()
        .map(|claim| PerpsMarginClaimBindingV2::new(claim.account_id, claim.obligation_id))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Margin)?;
    let state = PerpsMarginStateV2::new(
        PerpsMarginStateV1 {
            schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: wire.module_release_id,
            market_id: wire.market_id,
            collateral_asset: wire.collateral_asset,
            index_price_e8: wire.index_price_e8,
            maintenance_margin_bps: wire.maintenance_margin_bps,
            depeg_buffer_bps: wire.depeg_buffer_bps,
            max_position_abs: wire.max_position_abs,
            market_status: wire.market_status,
            accounts: wire.accounts,
        },
        active_claims,
    )
    .map_err(|_| PerpsMarginGlobalFrameErrorV2::Margin)?;
    if state
        .canonical_bytes()
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Margin)?
        != bytes
    {
        return Err(PerpsMarginGlobalFrameErrorV2::Margin);
    }
    Ok(state)
}

fn decode_request_v2(bytes: &[u8]) -> Result<PerpsMarginRequestV2, PerpsMarginGlobalFrameErrorV2> {
    if !(1..=MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2).contains(&bytes.len()) {
        return Err(PerpsMarginGlobalFrameErrorV2::Request);
    }
    let wire: PerpsMarginRequestWireV2 =
        serde_json::from_slice(bytes).map_err(|_| PerpsMarginGlobalFrameErrorV2::Request)?;
    if wire.schema != PERPS_MARGIN_REQUEST_SCHEMA_V2 {
        return Err(PerpsMarginGlobalFrameErrorV2::Request);
    }
    wire.command
        .command_body_hash()
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Request)?;
    wire.occurrence
        .validate()
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Request)?;
    let oracle = wire
        .oracle
        .map(|value| {
            PerpsMarginOracleV2::new(value.authority_root, value.occurrence_root, value.price_e8)
        })
        .transpose()
        .map_err(|_| PerpsMarginGlobalFrameErrorV2::Request)?;
    let request = PerpsMarginRequestV2 {
        command: wire.command,
        occurrence: wire.occurrence,
        oracle,
    };
    let canonical = canonical_bytes_v2(&PerpsMarginRequestCanonicalV2 {
        schema: PERPS_MARGIN_REQUEST_SCHEMA_V2,
        command: &request.command,
        occurrence: &request.occurrence,
        oracle: request.oracle.as_ref(),
    })
    .map_err(|_| PerpsMarginGlobalFrameErrorV2::Request)?;
    if canonical != bytes {
        return Err(PerpsMarginGlobalFrameErrorV2::Request);
    }
    Ok(request)
}
