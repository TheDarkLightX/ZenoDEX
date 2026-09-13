//! Bounded JSON-lines harness for Python/Rust parity tests.
//!
//! This example is test transport only.  It accepts complete, already typed
//! snapshots and returns canonical candidate observations; it is not a
//! production decoder, receipt verifier, or publication path.

use std::io::{self, BufRead};

use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::{json, Value};
use zenodex_global_settlement_abi_v1::{PerpsMarginCommandV1, PerpsMarginStateV1};
use zenodex_global_settlement_abi_v2::{
    derive_asset_lane_custody_global_post_v2, transition_asset_lane_custody_v2, AssetLaneCommandV2,
    AssetLaneContextV2, AssetLaneCustodyResultV2, AssetLaneCustodyStateV2, AssetTransferCommandV2,
    EconomicCommandOccurrenceV2, GlobalEconomicStateV2, GlobalOracleOccurrencePlanV2,
};
use zenodex_perps_margin_global_v2::{
    transition_perps_margin_global_v2, PerpsMarginClaimBindingV2, PerpsMarginGlobalResultV2,
    PerpsMarginOracleV2, PerpsMarginStateV2,
};

const MAX_PARITY_LINE_BYTES: usize = 4 * 1024 * 1024;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MarginWire {
    economic_state: PerpsMarginStateV1,
    active_claims: Vec<ClaimWire>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ClaimWire {
    account_id: String,
    obligation_id: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct OracleWire {
    authority_root: String,
    occurrence_root: String,
    price_e8: u128,
}

fn field<T: DeserializeOwned>(object: &Value, name: &str) -> Result<T, String> {
    let value = object
        .get(name)
        .ok_or_else(|| format!("missing parity field: {name}"))?;
    serde_json::from_value(value.clone()).map_err(|error| format!("invalid {name}: {error}"))
}

fn encoded<T: Serialize>(value: &T) -> Result<Value, String> {
    serde_json::to_value(value).map_err(|error| format!("canonical output: {error}"))
}

fn root_value(root: &zenodex_global_settlement_abi_v2::RootV2) -> Value {
    Value::String(root.as_str().to_owned())
}

fn abi<T>(result: zenodex_global_settlement_abi_v2::AbiResultV2<T>) -> Result<T, String> {
    result.map_err(|error| error.to_string())
}

fn refinement_value(
    refinement: &zenodex_global_settlement_abi_v2::GlobalEconomicStateEffectRefinementV2,
) -> Result<Value, String> {
    let refinement_root = abi(refinement.refinement_root())?;
    Ok(json!({
        "pre_state_root": root_value(refinement.pre_state_root()),
        "post_state_root": root_value(refinement.post_state_root()),
        "effect_plan_root": root_value(refinement.effect_plan_root()),
        "terminal_plan_root": root_value(refinement.terminal_plan_root()),
        "oracle_plan_root": root_value(refinement.oracle_plan_root()),
        "state_delta_root": root_value(refinement.state_delta_root()),
        "production_authority": refinement.production_authority(),
        "refinement_root": root_value(&refinement_root),
    }))
}

fn accepted_roots(
    refinement: &zenodex_global_settlement_abi_v2::GlobalEconomicStateEffectRefinementV2,
    effects: &zenodex_global_settlement_abi_v2::GlobalEconomicEffectPlanV2,
    terminal: &zenodex_global_settlement_abi_v2::GlobalTerminalObligationPlanV2,
    oracle: &GlobalOracleOccurrencePlanV2,
    statement: &zenodex_global_settlement_abi_v2::RootV2,
) -> Result<Value, String> {
    let effect_root = abi(effects.effect_plan_root())?;
    let terminal_root = abi(terminal.plan_root())?;
    let oracle_root = abi(oracle.plan_root())?;
    let refinement_root = abi(refinement.refinement_root())?;
    Ok(json!({
        "pre_state_root": root_value(refinement.pre_state_root()),
        "post_state_root": root_value(refinement.post_state_root()),
        "effect_plan_root": root_value(&effect_root),
        "terminal_plan_root": root_value(&terminal_root),
        "oracle_plan_root": root_value(&oracle_root),
        "state_delta_root": root_value(refinement.state_delta_root()),
        "refinement_root": root_value(&refinement_root),
        "statement_root": root_value(statement),
    }))
}

fn rejected_roots(
    pre_state_root: &zenodex_global_settlement_abi_v2::RootV2,
    post_state_root: &zenodex_global_settlement_abi_v2::RootV2,
    effects: &zenodex_global_settlement_abi_v2::GlobalEconomicEffectPlanV2,
    terminal: &zenodex_global_settlement_abi_v2::GlobalTerminalObligationPlanV2,
    oracle: &GlobalOracleOccurrencePlanV2,
) -> Result<Value, String> {
    let effect_root = abi(effects.effect_plan_root())?;
    let terminal_root = abi(terminal.plan_root())?;
    let oracle_root = abi(oracle.plan_root())?;
    Ok(json!({
        "pre_state_root": root_value(pre_state_root),
        "post_state_root": root_value(post_state_root),
        "effect_plan_root": root_value(&effect_root),
        "terminal_plan_root": root_value(&terminal_root),
        "oracle_plan_root": root_value(&oracle_root),
        "state_delta_root": Value::Null,
        "refinement_root": Value::Null,
        "statement_root": Value::Null,
    }))
}

fn parse_oracle(object: &Value) -> Result<Option<PerpsMarginOracleV2>, String> {
    let Some(value) = object.get("oracle") else {
        return Ok(None);
    };
    if value.is_null() {
        return Ok(None);
    }
    let wire: OracleWire = serde_json::from_value(value.clone())
        .map_err(|error| format!("invalid oracle: {error}"))?;
    let authority = abi(zenodex_global_settlement_abi_v2::RootV2::parse(
        wire.authority_root,
        "parity oracle authority root",
        false,
    ))?;
    let occurrence = abi(zenodex_global_settlement_abi_v2::RootV2::parse(
        wire.occurrence_root,
        "parity oracle occurrence root",
        false,
    ))?;
    Ok(Some(abi(PerpsMarginOracleV2::new(
        authority,
        occurrence,
        wire.price_e8,
    ))?))
}

fn margin_input(object: &Value) -> Result<PerpsMarginStateV2, String> {
    let wire: MarginWire = field(object, "margin")?;
    let claims = wire
        .active_claims
        .into_iter()
        .map(|binding| {
            abi(PerpsMarginClaimBindingV2::new(
                binding.account_id,
                binding.obligation_id,
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    abi(PerpsMarginStateV2::new(wire.economic_state, claims))
}

fn handle_perps(object: &Value) -> Result<Value, String> {
    let assets: AssetLaneCustodyStateV2 = field(object, "assets")?;
    let margin = margin_input(object)?;
    let state: GlobalEconomicStateV2 = field(object, "state")?;
    let command: PerpsMarginCommandV1 = field(object, "command")?;
    let occurrence: EconomicCommandOccurrenceV2 = field(object, "occurrence")?;
    let oracle = parse_oracle(object)?;
    let result = abi(transition_perps_margin_global_v2(
        &assets,
        &margin,
        &state,
        &command,
        &occurrence,
        oracle.as_ref(),
    ))?;
    match result {
        PerpsMarginGlobalResultV2::Accepted(accepted) => {
            let oracle_plan = GlobalOracleOccurrencePlanV2::empty();
            let refinement = refinement_value(accepted.refinement())?;
            let roots = accepted_roots(
                accepted.refinement(),
                accepted.effects(),
                accepted.terminal_plan(),
                &oracle_plan,
                accepted.statement_root(),
            )?;
            Ok(json!({
                "kind": "accepted",
                "assets": encoded(accepted.post_assets())?,
                "margin": encoded(&accepted.post_margin().to_canonical())?,
                "state": encoded(accepted.post_state())?,
                "effects": encoded(accepted.effects())?,
                "terminal_plan": encoded(accepted.terminal_plan())?,
                "oracle_plan": encoded(&oracle_plan)?,
                "refinement": refinement,
                "statement_root": root_value(accepted.statement_root()),
                "roots": roots,
            }))
        }
        PerpsMarginGlobalResultV2::Rejected(rejected) => {
            let effects = rejected.effects();
            let terminal = rejected.terminal_plan();
            let oracle = rejected.oracle_plan();
            Ok(json!({
                "kind": "rejected",
                "code": rejected.code.as_str(),
                "effects": encoded(&effects)?,
                "terminal_plan": encoded(&terminal)?,
                "oracle_plan": encoded(&oracle)?,
                "refinement": Value::Null,
                "statement_root": Value::Null,
                "roots": rejected_roots(
                    &rejected.pre_state_root,
                    &rejected.post_state_root,
                    &effects,
                    &terminal,
                    &oracle,
                )?,
            }))
        }
    }
}

fn handle_transfer(object: &Value) -> Result<Value, String> {
    let assets: AssetLaneCustodyStateV2 = field(object, "assets")?;
    let state: GlobalEconomicStateV2 = field(object, "state")?;
    let context: AssetLaneContextV2 = field(object, "context")?;
    let command: AssetTransferCommandV2 = field(object, "command")?;
    let occurrence: EconomicCommandOccurrenceV2 = field(object, "occurrence")?;
    let lane_command = AssetLaneCommandV2::Transfer(command);
    let result = abi(transition_asset_lane_custody_v2(
        &context,
        &assets,
        &lane_command,
    ))?;
    match result {
        AssetLaneCustodyResultV2::Accepted(accepted) => {
            let post_state = abi(derive_asset_lane_custody_global_post_v2(
                &assets,
                &accepted,
                &state,
                &occurrence,
            ))?;
            Ok(json!({
                "kind": "accepted",
                "assets": encoded(accepted.post_state())?,
                "state": encoded(&post_state)?,
                "effects": encoded(accepted.effects())?,
                "roots": {
                    "asset_state_root": root_value(&abi(accepted.post_state().state_root())?),
                    "state_root": root_value(&abi(post_state.state_root())?),
                    "effect_plan_root": root_value(&abi(accepted.effects().effect_plan_root())?),
                },
            }))
        }
        AssetLaneCustodyResultV2::Rejected(rejected) => Ok(json!({
            "kind": "rejected",
            "code": rejected.code().as_str(),
            "effects": encoded(rejected.effects())?,
            "roots": {
                "pre_state_root": root_value(rejected.pre_state_root()),
                "post_state_root": root_value(rejected.post_state_root()),
            },
        })),
    }
}

fn require_outer_keys(object: &Value, allowed: &[&str]) -> Result<(), String> {
    let fields = object
        .as_object()
        .ok_or_else(|| "parity input must be a JSON object".to_owned())?;
    if let Some(unknown) = fields.keys().find(|key| !allowed.contains(&key.as_str())) {
        return Err(format!("unknown parity input field: {unknown}"));
    }
    Ok(())
}

fn handle(value: Value) -> Result<Value, String> {
    match value.get("op").and_then(Value::as_str) {
        Some("perps") => {
            require_outer_keys(
                &value,
                &[
                    "op",
                    "assets",
                    "margin",
                    "state",
                    "command",
                    "occurrence",
                    "oracle",
                ],
            )?;
            handle_perps(&value)
        }
        Some("transfer") => {
            require_outer_keys(
                &value,
                &["op", "assets", "state", "context", "command", "occurrence"],
            )?;
            handle_transfer(&value)
        }
        Some(other) => Err(format!("unsupported parity operation: {other}")),
        None => Err("parity operation is missing".to_owned()),
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
                "parity input line exceeds four MiB",
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

fn main() {
    let stdin = io::stdin();
    let mut input = stdin.lock();
    loop {
        let output = match read_bounded_line(&mut input) {
            Ok(Some(line)) => match serde_json::from_str::<Value>(&line) {
                Ok(value) => match handle(value) {
                    Ok(output) => output,
                    Err(error) => json!({"kind": "error", "error": error}),
                },
                Err(error) => json!({"kind": "error", "error": format!("invalid JSON: {error}")}),
            },
            Ok(None) => break,
            Err(error) => {
                println!(
                    "{}",
                    json!({"kind": "error", "error": format!("input: {error}")})
                );
                break;
            }
        };
        println!("{}", output);
    }
}
