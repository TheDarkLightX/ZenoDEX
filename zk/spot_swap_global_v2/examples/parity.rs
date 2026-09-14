//! Bounded JSON-lines harness for Python/Rust parity tests.
//!
//! This example is test transport only. Each input line is one request object
//! with exactly the keys `assets`, `spot`, `state`, `intent`, `occurrence` and
//! `block_timestamp`, carrying the Python `to_canonical()` values and the
//! `spot_swap_command_body_v2` body. It returns the canonical successor
//! observation, the exact no-op rejection, or a typed input error. It is not a
//! production decoder, receipt verifier, wire successor or publication path.
//!
//! Bounds: one line is at most 16 MiB; assets and Spot components at most the
//! 1 MiB rootable ceiling; occurrence at most 64 KiB; intent at most 128 KiB.
//! The line is parsed with a strict visitor that rejects duplicate object keys
//! after JSON unescaping. Every typed component must then re-encode to the
//! same bytes as the parsed value (numbers keep their text through
//! `arbitrary_precision`); key order and whitespace of the raw line are
//! normalised by the parser before that check and are not observed here.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, BufRead};
use std::str::FromStr;

use serde::de::{self, MapAccess, SeqAccess, Visitor};
use serde::{de::DeserializeOwned, Deserialize, Deserializer, Serialize};
use serde_json::{json, Map, Value};
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, AssetLaneCustodyStateV2, EconomicCommandOccurrenceV2, GlobalEconomicStateV2,
};
use zenodex_spot_swap_global_v2::{
    transition_spot_swap_global_v2, SpotSwapGlobalResultV2, SpotSwapIntentPartsV2,
    SpotSwapIntentV2, SpotSwapKindV2, SpotSwapStateV2, SwapIntentFieldValueV2, SwapIntentIntegerV2,
};

const MAX_PARITY_LINE_BYTES: usize = 16 * 1024 * 1024;
const MAX_ASSETS_BYTES: usize = 1_048_576;
const MAX_SPOT_BYTES: usize = 1_048_576;
const MAX_STATE_BYTES: usize = MAX_PARITY_LINE_BYTES;
const MAX_OCCURRENCE_BYTES: usize = 65_536;
const MAX_INTENT_BYTES: usize = 131_072;
const MAX_TIMESTAMP_BYTES: usize = 32;
const REQUEST_KEYS: [&str; 6] = [
    "assets",
    "spot",
    "state",
    "intent",
    "occurrence",
    "block_timestamp",
];

/// The map key `serde_json` uses to hand an `arbitrary_precision` number to a
/// visitor as a one-entry map.
const NUMBER_TOKEN: &str = "$serde_json::private::Number";

/// `serde_json::Value` decoded with duplicate object keys rejected and the
/// private number token admitted only from `serde_json`'s own number path.
struct StrictValue(Value);

struct StrictValueVisitor;

/// Accepts the number text only as `serde_json` delivers it internally: an
/// owned `String` through `StringDeserializer::visit_string`. The JSON parser
/// never delivers owned strings for document values, so a document object
/// that spells the private token key reaches `visit_str` and is refused.
struct NumberTextVisitor;

impl Visitor<'_> for NumberTextVisitor {
    type Value = String;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("an internally delivered arbitrary-precision number text")
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<Self::Value, E> {
        Ok(value)
    }

    fn visit_str<E: de::Error>(self, _value: &str) -> Result<Self::Value, E> {
        Err(de::Error::custom(
            "private number token key spelled by a JSON object",
        ))
    }
}

struct NumberTextSeed;

impl<'de> de::DeserializeSeed<'de> for NumberTextSeed {
    type Value = String;

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        deserializer.deserialize_any(NumberTextVisitor)
    }
}

impl<'de> Visitor<'de> for StrictValueVisitor {
    type Value = StrictValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E: de::Error>(self, value: bool) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Bool(value)))
    }

    fn visit_i64<E: de::Error>(self, value: i64) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::from(value)))
    }

    fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::from(value)))
    }

    fn visit_f64<E: de::Error>(self, value: f64) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::from(value)))
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::String(value.to_owned())))
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::String(value)))
    }

    fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Null))
    }

    fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Null))
    }

    fn visit_some<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        deserializer.deserialize_any(StrictValueVisitor)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut items = Vec::new();
        while let Some(StrictValue(item)) = access.next_element::<StrictValue>()? {
            items.push(item);
        }
        Ok(StrictValue(Value::Array(items)))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut object = Map::new();
        while let Some(key) = access.next_key::<String>()? {
            if key == NUMBER_TOKEN && object.is_empty() {
                let text = access.next_value_seed(NumberTextSeed)?;
                let number = serde_json::Number::from_str(&text).map_err(de::Error::custom)?;
                if access.next_key::<String>()?.is_some() {
                    return Err(de::Error::custom("malformed number token"));
                }
                return Ok(StrictValue(Value::Number(number)));
            }
            let StrictValue(value) = access.next_value::<StrictValue>()?;
            if object.insert(key.clone(), value).is_some() {
                return Err(de::Error::custom(format!("duplicate object key: {key}")));
            }
        }
        Ok(StrictValue(Value::Object(object)))
    }
}

impl<'de> Deserialize<'de> for StrictValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(StrictValueVisitor)
    }
}

struct InputError {
    code: &'static str,
    detail: String,
}

impl InputError {
    fn new(code: &'static str, detail: impl Into<String>) -> Self {
        Self {
            code,
            detail: detail.into(),
        }
    }
}

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct IntentWire {
    module: String,
    version: String,
    kind: SpotSwapKindV2,
    intent_id: String,
    sender_pubkey: String,
    deadline: u64,
    #[serde(deserialize_with = "deserialize_required_option")]
    salt: Option<String>,
    fields: Map<String, Value>,
}

fn raw_bytes(
    value: &Value,
    code: &'static str,
    name: &str,
    max_bytes: usize,
) -> Result<Vec<u8>, InputError> {
    let raw =
        serde_json::to_vec(value).map_err(|error| InputError::new(code, error.to_string()))?;
    if raw.len() > max_bytes {
        return Err(InputError::new(
            code,
            format!("{name} exceeds {max_bytes} bytes"),
        ));
    }
    Ok(raw)
}

fn typed_component<T>(
    object: &Map<String, Value>,
    name: &str,
    code: &'static str,
    max_bytes: usize,
) -> Result<T, InputError>
where
    T: DeserializeOwned + Serialize,
{
    let value = object
        .get(name)
        .ok_or_else(|| InputError::new(code, format!("missing {name}")))?;
    let raw = raw_bytes(value, code, name, max_bytes)?;
    let typed: T = serde_json::from_value(value.clone())
        .map_err(|error| InputError::new(code, error.to_string()))?;
    let canonical =
        canonical_bytes_v2(&typed).map_err(|error| InputError::new(code, error.to_string()))?;
    if canonical != raw {
        return Err(InputError::new(code, format!("{name} is not canonical")));
    }
    Ok(typed)
}

fn field_value(item: &Value) -> Result<SwapIntentFieldValueV2, InputError> {
    match item {
        Value::Number(number) => SwapIntentIntegerV2::parse_canonical_text(&number.to_string())
            .map(SwapIntentFieldValueV2::Integer)
            .map_err(|error| InputError::new("INPUT_INTENT", error.to_string())),
        Value::String(text) => Ok(SwapIntentFieldValueV2::Text(text.clone())),
        _ => Ok(SwapIntentFieldValueV2::Nested),
    }
}

fn intent_component(object: &Map<String, Value>) -> Result<SpotSwapIntentV2, InputError> {
    const CODE: &str = "INPUT_INTENT";
    let value = object
        .get("intent")
        .ok_or_else(|| InputError::new(CODE, "missing intent"))?;
    let raw = raw_bytes(value, CODE, "intent", MAX_INTENT_BYTES)?;
    let wire: IntentWire = serde_json::from_value(value.clone())
        .map_err(|error| InputError::new(CODE, error.to_string()))?;
    let mut fields = BTreeMap::new();
    for (key, item) in wire.fields {
        fields.insert(key, field_value(&item)?);
    }
    let intent = SpotSwapIntentV2::new(SpotSwapIntentPartsV2 {
        module: wire.module,
        version: wire.version,
        kind: wire.kind,
        intent_id: wire.intent_id,
        sender_pubkey: wire.sender_pubkey,
        deadline: wire.deadline,
        salt: wire.salt,
        fields,
    })
    .map_err(|error| InputError::new(CODE, error.to_string()))?;
    if !intent.has_nested_fields() {
        let canonical = canonical_bytes_v2(&intent.command_body())
            .map_err(|error| InputError::new(CODE, error.to_string()))?;
        if canonical != raw {
            return Err(InputError::new(CODE, "intent is not canonical"));
        }
    }
    Ok(intent)
}

fn encoded<T: Serialize>(value: &T) -> Result<Value, InputError> {
    serde_json::to_value(value)
        .map_err(|error| InputError::new("INPUT_INTERNAL", error.to_string()))
}

fn handle(value: &Value) -> Result<Value, InputError> {
    let object = value
        .as_object()
        .ok_or_else(|| InputError::new("INPUT_REQUEST_SHAPE", "request must be a JSON object"))?;
    if object.len() != REQUEST_KEYS.len()
        || REQUEST_KEYS.iter().any(|key| !object.contains_key(*key))
    {
        return Err(InputError::new(
            "INPUT_REQUEST_SHAPE",
            "request must carry exactly assets, spot, state, intent, occurrence and block_timestamp",
        ));
    }
    let assets: AssetLaneCustodyStateV2 =
        typed_component(object, "assets", "INPUT_ASSETS", MAX_ASSETS_BYTES)?;
    let spot: SpotSwapStateV2 =
        typed_component(object, "spot", "INPUT_SPOT_STATE", MAX_SPOT_BYTES)?;
    let state: GlobalEconomicStateV2 =
        typed_component(object, "state", "INPUT_GLOBAL_STATE", MAX_STATE_BYTES)?;
    let occurrence: EconomicCommandOccurrenceV2 = typed_component(
        object,
        "occurrence",
        "INPUT_OCCURRENCE",
        MAX_OCCURRENCE_BYTES,
    )?;
    let block_timestamp: u64 = typed_component(
        object,
        "block_timestamp",
        "INPUT_BLOCK_TIMESTAMP",
        MAX_TIMESTAMP_BYTES,
    )?;
    let intent = intent_component(object)?;
    let result = transition_spot_swap_global_v2(
        &assets,
        &spot,
        &state,
        &intent,
        &occurrence,
        block_timestamp,
    )
    .map_err(|error| InputError::new(error.code(), error.to_string()))?;
    match result {
        SpotSwapGlobalResultV2::Accepted(accepted) => {
            let statement_root = accepted.statement_root().as_str().to_owned();
            let refinement_root = accepted
                .refinement_root()
                .map_err(|error| InputError::new("INPUT_INTERNAL", error.to_string()))?
                .as_str()
                .to_owned();
            Ok(json!({
                "status": "accepted",
                "post_assets": encoded(accepted.post_assets())?,
                "post_spot": encoded(accepted.post_spot())?,
                "post_state": encoded(accepted.post_state())?,
                "effects": encoded(accepted.effects())?,
                "statement_root": statement_root,
                "refinement_root": refinement_root,
            }))
        }
        SpotSwapGlobalResultV2::Rejected(rejected) => Ok(json!({
            "status": "rejected",
            "code": rejected.code.as_str(),
            "pre_state_root": rejected.pre_state_root.as_str(),
            "post_state_root": rejected.post_state_root().as_str(),
            "effects": encoded(&rejected.effects())?,
        })),
    }
}

fn read_bounded_line<R: BufRead>(reader: &mut R) -> io::Result<Option<String>> {
    let mut bytes = Vec::new();
    loop {
        let chunk = reader.fill_buf()?;
        if chunk.is_empty() {
            if bytes.is_empty() {
                return Ok(None);
            }
            break;
        }
        let newline = chunk.iter().position(|byte| *byte == b'\n');
        let take = newline.map_or(chunk.len(), |index| index + 1);
        if bytes.len().saturating_add(take) > MAX_PARITY_LINE_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "parity input line exceeds sixteen MiB",
            ));
        }
        bytes.extend_from_slice(&chunk[..take]);
        reader.consume(take);
        if newline.is_some() {
            break;
        }
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

fn input_error(code: &str, detail: &str) -> Value {
    eprintln!("{code}: {detail}");
    json!({"status": "input_error", "code": code})
}

fn main() {
    let stdin = io::stdin();
    let mut input = stdin.lock();
    loop {
        let line = match read_bounded_line(&mut input) {
            Ok(Some(line)) => line,
            Ok(None) => break,
            Err(error) => {
                println!("{}", input_error("INPUT_LINE", &error.to_string()));
                break;
            }
        };
        if line.trim().is_empty() {
            continue;
        }
        let output = match serde_json::from_str::<StrictValue>(&line) {
            Ok(StrictValue(value)) => match handle(&value) {
                Ok(output) => output,
                Err(error) => input_error(error.code, &error.detail),
            },
            Err(error) => input_error("INPUT_JSON", &error.to_string()),
        };
        println!("{output}");
    }
}
