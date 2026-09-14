//! Candidate execution transport shared by native replay and the Spot guest.
//! No receipt, authentication, profile admission or publication authority.

use std::collections::BTreeMap;

use serde::{de::DeserializeOwned, Deserialize, Deserializer, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, AssetLaneCustodyStateV2, EconomicCommandOccurrenceV2,
    GlobalEconomicStateV2, RootV2, MAX_CANONICAL_INPUT_BYTES_V2,
};

use crate::{
    transition_spot_swap_global_v2, SpotSwapGlobalRejectCodeV2, SpotSwapGlobalResultV2,
    SpotSwapInputErrorV2, SpotSwapIntentPartsV2, SpotSwapIntentV2, SpotSwapKindV2, SpotSwapStateV2,
    SwapIntentFieldValueV2, SwapIntentIntegerV2,
};

pub const SPOT_SWAP_FRAME_MAGIC_V2: &[u8; 6] = b"ZDSS2\0";
pub const SPOT_SWAP_GLOBAL_JOURNAL_SCHEMA_V2: &str = "zenodex/spot-swap-global-statement/v2";
pub const MAX_SPOT_SWAP_FRAME_COMPONENT_BYTES_V2: usize = MAX_CANONICAL_INPUT_BYTES_V2;
pub const MAX_SPOT_SWAP_FRAME_BYTES_V2: usize =
    SPOT_SWAP_FRAME_MAGIC_V2.len() + 6 * (4 + MAX_SPOT_SWAP_FRAME_COMPONENT_BYTES_V2);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpotSwapGlobalFrameErrorV2 {
    Bounds,
    Magic,
    Truncated,
    TrailingBytes,
    Component(&'static str),
    Transition(SpotSwapInputErrorV2),
    Rejected(SpotSwapGlobalRejectCodeV2),
    SuccessorBounds,
    Journal,
}

impl core::fmt::Display for SpotSwapGlobalFrameErrorV2 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Spot execution frame rejected: {self:?}")
    }
}

impl std::error::Error for SpotSwapGlobalFrameErrorV2 {}

fn parse_frame(frame: &[u8]) -> Result<[&[u8]; 6], SpotSwapGlobalFrameErrorV2> {
    use SpotSwapGlobalFrameErrorV2 as Error;
    if frame.is_empty() || frame.len() > MAX_SPOT_SWAP_FRAME_BYTES_V2 {
        return Err(Error::Bounds);
    }
    if frame.get(..SPOT_SWAP_FRAME_MAGIC_V2.len()) != Some(SPOT_SWAP_FRAME_MAGIC_V2) {
        return Err(Error::Magic);
    }
    let mut cursor = SPOT_SWAP_FRAME_MAGIC_V2.len();
    let mut components = [&frame[0..0]; 6];
    for component in &mut components {
        let end = cursor.checked_add(4).ok_or(Error::Bounds)?;
        let bytes: [u8; 4] = frame
            .get(cursor..end)
            .ok_or(Error::Truncated)?
            .try_into()
            .map_err(|_| Error::Truncated)?;
        let size = usize::try_from(u32::from_le_bytes(bytes)).map_err(|_| Error::Bounds)?;
        if !(1..=MAX_SPOT_SWAP_FRAME_COMPONENT_BYTES_V2).contains(&size) {
            return Err(Error::Bounds);
        }
        cursor = end;
        let end = cursor.checked_add(size).ok_or(Error::Bounds)?;
        *component = frame.get(cursor..end).ok_or(Error::Truncated)?;
        cursor = end;
    }
    if cursor != frame.len() {
        return Err(Error::TrailingBytes);
    }
    Ok(components)
}

fn component<T: DeserializeOwned + Serialize>(
    bytes: &[u8],
    name: &'static str,
) -> Result<T, SpotSwapGlobalFrameErrorV2> {
    let error = || SpotSwapGlobalFrameErrorV2::Component(name);
    let value: T = serde_json::from_slice(bytes).map_err(|_| error())?;
    // Compare against the original bytes, before any normalization can hide a
    // duplicate key, missing optional field, private Number object or alias.
    if canonical_bytes_v2(&value).map_err(|_| error())? != bytes {
        return Err(error());
    }
    Ok(value)
}

fn required_option<'de, D: Deserializer<'de>>(d: D) -> Result<Option<String>, D::Error> {
    Option::<String>::deserialize(d)
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct IntentWire {
    module: String,
    version: String,
    kind: SpotSwapKindV2,
    intent_id: String,
    sender_pubkey: String,
    deadline: u64,
    #[serde(deserialize_with = "required_option")]
    salt: Option<String>,
    fields: BTreeMap<String, Value>,
}

fn intent(bytes: &[u8]) -> Result<SpotSwapIntentV2, SpotSwapGlobalFrameErrorV2> {
    let wire: IntentWire = component(bytes, "intent")?;
    let mut fields = BTreeMap::new();
    for (key, value) in wire.fields {
        let value = match value {
            Value::Number(number) => SwapIntentFieldValueV2::Integer(
                SwapIntentIntegerV2::parse_canonical_text(&number.to_string())
                    .map_err(|_| SpotSwapGlobalFrameErrorV2::Component("intent"))?,
            ),
            Value::String(value) => SwapIntentFieldValueV2::Text(value),
            _ => SwapIntentFieldValueV2::Nested,
        };
        fields.insert(key, value);
    }
    SpotSwapIntentV2::new(SpotSwapIntentPartsV2 {
        module: wire.module,
        version: wire.version,
        kind: wire.kind,
        intent_id: wire.intent_id,
        sender_pubkey: wire.sender_pubkey,
        deadline: wire.deadline,
        salt: wire.salt,
        fields,
    })
    .map_err(|_| SpotSwapGlobalFrameErrorV2::Component("intent"))
}

#[derive(Serialize)]
struct Journal<'a> {
    schema: &'static str,
    input_root: &'a RootV2,
    refinement_root: &'a RootV2,
}

/// Execute exactly one candidate frame. Only accepted transitions emit a
/// journal. The roots commit the complete command/context and state/effects;
/// their authenticity and the guest image are obligations of the verifier.
pub fn prepare_spot_swap_global_from_frame_v2(
    frame: &[u8],
) -> Result<Vec<u8>, SpotSwapGlobalFrameErrorV2> {
    let [assets, spot, state, command, occurrence, timestamp] = parse_frame(frame)?;
    let assets: AssetLaneCustodyStateV2 = component(assets, "assets")?;
    let spot: SpotSwapStateV2 = component(spot, "spot")?;
    let state: GlobalEconomicStateV2 = component(state, "state")?;
    let command = intent(command)?;
    let occurrence: EconomicCommandOccurrenceV2 = component(occurrence, "occurrence")?;
    let timestamp: u64 = component(timestamp, "timestamp")?;
    let accepted = match transition_spot_swap_global_v2(
        &assets,
        &spot,
        &state,
        &command,
        &occurrence,
        timestamp,
    )
    .map_err(SpotSwapGlobalFrameErrorV2::Transition)?
    {
        SpotSwapGlobalResultV2::Accepted(value) => value,
        SpotSwapGlobalResultV2::Rejected(value) => {
            return Err(SpotSwapGlobalFrameErrorV2::Rejected(value.code));
        }
    };
    // An admitted successor must be representable by this same transport.
    // Keep this additional transport ceiling separate from economic rejection.
    for bytes in [
        canonical_bytes_v2(accepted.post_assets()),
        canonical_bytes_v2(accepted.post_spot()),
        canonical_bytes_v2(accepted.post_state()),
    ] {
        let bytes = bytes.map_err(|_| SpotSwapGlobalFrameErrorV2::SuccessorBounds)?;
        if bytes.len() > MAX_SPOT_SWAP_FRAME_COMPONENT_BYTES_V2 {
            return Err(SpotSwapGlobalFrameErrorV2::SuccessorBounds);
        }
    }
    let refinement_root = accepted
        .refinement_root()
        .map_err(|_| SpotSwapGlobalFrameErrorV2::Journal)?;
    canonical_bytes_v2(&Journal {
        schema: SPOT_SWAP_GLOBAL_JOURNAL_SCHEMA_V2,
        input_root: accepted.statement_root(),
        refinement_root: &refinement_root,
    })
    .map_err(|_| SpotSwapGlobalFrameErrorV2::Journal)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_integer_has_no_boolean_float_object_or_duplicate_alias() {
        assert_eq!(component::<u64>(b"18446744073709551615", "n"), Ok(u64::MAX));
        for bytes in [
            b"true".as_slice(),
            b"1.0",
            b"01",
            b"1 ",
            b"-1",
            br#"{"$serde_json::private::Number":"1"}"#,
        ] {
            assert_eq!(
                component::<u64>(bytes, "n"),
                Err(SpotSwapGlobalFrameErrorV2::Component("n"))
            );
        }
        for bytes in [
            br#"{"n":1,"n":1}"#.as_slice(),
            br#"{"n":{"$serde_json::private::Number":"1"}}"#,
        ] {
            assert!(component::<Value>(bytes, "v").is_err());
        }
    }

    #[test]
    fn framing_checks_lengths_before_body_access_and_requires_exact_end() {
        let mut frame = SPOT_SWAP_FRAME_MAGIC_V2.to_vec();
        for byte in b"123456" {
            frame.extend_from_slice(&1_u32.to_le_bytes());
            frame.push(*byte);
        }
        assert_eq!(
            parse_frame(&frame).unwrap(),
            [b"1", b"2", b"3", b"4", b"5", b"6"]
        );
        for end in 0..frame.len() {
            assert!(parse_frame(&frame[..end]).is_err());
        }
        frame.push(0);
        assert_eq!(
            parse_frame(&frame),
            Err(SpotSwapGlobalFrameErrorV2::TrailingBytes)
        );
        for length in [
            0,
            u32::MAX,
            MAX_SPOT_SWAP_FRAME_COMPONENT_BYTES_V2 as u32 + 1,
        ] {
            let mut bad = SPOT_SWAP_FRAME_MAGIC_V2.to_vec();
            bad.extend_from_slice(&length.to_le_bytes());
            assert_eq!(parse_frame(&bad), Err(SpotSwapGlobalFrameErrorV2::Bounds));
        }
    }
}
