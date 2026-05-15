use serde::Serialize;
use serde_json::{Map, Value};
use std::io::{self, Read, Write};

const MAX_EPOCH: u64 = 0xFFFF_FFFF;

#[derive(Debug, PartialEq, Eq, Serialize)]
struct VerifiedAttestation {
    measurement: String,
    policy_digest: String,
    attestation_epoch: u32,
}

fn main() {
    let exit_code = match run() {
        Ok(()) => 0,
        Err(err) => {
            let _ = writeln!(io::stderr(), "{err}");
            1
        }
    };
    std::process::exit(exit_code);
}

fn run() -> Result<(), String> {
    let payload = read_payload()?;
    let response = match verify_payload(&payload) {
        Ok(result) => serde_json::json!({"ok": true, "result": result}),
        Err(err) => serde_json::json!({"ok": false, "error": err}),
    };
    write_response(&response)
}

fn read_payload() -> Result<Map<String, Value>, String> {
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .map_err(|err| format!("failed to read stdin: {err}"))?;
    let value: Value =
        serde_json::from_str(&input).map_err(|err| format!("invalid input json: {err}"))?;
    require_object(&value, "payload").cloned()
}

fn write_response(response: &Value) -> Result<(), String> {
    let bytes = serde_json::to_vec(response)
        .map_err(|err| format!("failed to encode output json: {err}"))?;
    io::stdout()
        .write_all(&bytes)
        .map_err(|err| format!("failed to write stdout: {err}"))
}

fn verify_payload(payload: &Map<String, Value>) -> Result<VerifiedAttestation, String> {
    let provider = require_string_field(payload, "provider")?.to_lowercase();
    let policy_digest = canonical_policy_digest(&require_string_field(payload, "policy_digest")?)?;
    let issued_at_s = require_u64_field(payload, "issued_at_s")?;
    let epoch_length_s = require_positive_u64_field(payload, "epoch_length_s")?;
    let attestation_epoch = compute_attestation_epoch(issued_at_s, epoch_length_s)?;
    if provider == "nitro" {
        let summary = require_object_field(payload, "summary")?;
        let measurement = nitro_measurement(summary)?;
        return Ok(VerifiedAttestation {
            measurement,
            policy_digest,
            attestation_epoch,
        });
    }
    if provider == "azure-sevsnp" {
        let claims = require_object_field(payload, "claims")?;
        let (measurement, bound_policy_digest) = azure_measurement_and_policy_digest(claims)?;
        if policy_digest != bound_policy_digest {
            return Err("policy_digest must match azure hostdata".to_string());
        }
        return Ok(VerifiedAttestation {
            measurement,
            policy_digest,
            attestation_epoch,
        });
    }
    Err("provider must be nitro or azure-sevsnp".to_string())
}

fn require_object<'a>(value: &'a Value, name: &str) -> Result<&'a Map<String, Value>, String> {
    if let Value::Object(obj) = value {
        return Ok(obj);
    }
    Err(format!("{name} must be an object"))
}

fn require_object_field<'a>(
    mapping: &'a Map<String, Value>,
    key: &str,
) -> Result<&'a Map<String, Value>, String> {
    let value = mapping
        .get(key)
        .ok_or_else(|| format!("{key} must be an object"))?;
    require_object(value, key)
}

fn require_string_field(mapping: &Map<String, Value>, key: &str) -> Result<String, String> {
    let value = mapping
        .get(key)
        .ok_or_else(|| format!("{key} must be a non-empty string"))?;
    let text = value
        .as_str()
        .ok_or_else(|| format!("{key} must be a non-empty string"))?
        .trim();
    if text.is_empty() {
        return Err(format!("{key} must be a non-empty string"));
    }
    Ok(text.to_string())
}

fn require_u64_field(mapping: &Map<String, Value>, key: &str) -> Result<u64, String> {
    let value = mapping
        .get(key)
        .ok_or_else(|| format!("{key} must be a non-negative int"))?;
    value
        .as_u64()
        .ok_or_else(|| format!("{key} must be a non-negative int"))
}

fn require_positive_u64_field(mapping: &Map<String, Value>, key: &str) -> Result<u64, String> {
    let value = require_u64_field(mapping, key)?;
    if value == 0 {
        return Err(format!("{key} must be a positive int"));
    }
    Ok(value)
}

fn canonical_policy_digest(value: &str) -> Result<String, String> {
    let hex = canonical_lower_hex(value, "policy_digest", 64)?;
    Ok(format!("0x{hex}"))
}

fn canonical_lower_hex(value: &str, name: &str, exact_length: usize) -> Result<String, String> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Err(format!("{name} must be a non-empty string"));
    }
    let lower = trimmed.to_lowercase();
    let hex = lower.strip_prefix("0x").unwrap_or(&lower);
    if hex.len() != exact_length {
        return Err(format!("{name} must be {exact_length}-char hex"));
    }
    if !hex.as_bytes().iter().all(u8::is_ascii_hexdigit) {
        return Err(format!("{name} must be hex"));
    }
    Ok(hex.to_string())
}

fn compute_attestation_epoch(issued_at_s: u64, epoch_length_s: u64) -> Result<u32, String> {
    let epoch = issued_at_s / epoch_length_s;
    if epoch > MAX_EPOCH {
        return Err("attestation_epoch must fit in u32".to_string());
    }
    u32::try_from(epoch).map_err(|_| "attestation_epoch must fit in u32".to_string())
}

fn nitro_measurement(summary: &Map<String, Value>) -> Result<String, String> {
    let pcrs = require_object_field(summary, "pcrs")?;
    let pcr0 = canonical_lower_hex(&require_string_field(pcrs, "0")?, "pcr0", 96)?;
    let pcr8 = canonical_lower_hex(&require_string_field(pcrs, "8")?, "pcr8", 96)?;
    Ok(format!("nitro:pcr0:{pcr0}:pcr8:{pcr8}"))
}

fn azure_measurement_and_policy_digest(
    claims: &Map<String, Value>,
) -> Result<(String, String), String> {
    let attestation_type = require_string_field(claims, "x-ms-attestation-type")?.to_lowercase();
    if attestation_type != "sevsnpvm" {
        return Err("x-ms-attestation-type must be sevsnpvm".to_string());
    }
    let debuggable = claims
        .get("x-ms-sevsnpvm-is-debuggable")
        .ok_or_else(|| "azure confidential container must not be debuggable".to_string())?;
    if !is_false_like(debuggable) {
        return Err("azure confidential container must not be debuggable".to_string());
    }
    let hostdata = canonical_lower_hex(
        &require_string_field(claims, "x-ms-sevsnpvm-hostdata")?,
        "x-ms-sevsnpvm-hostdata",
        64,
    )?;
    Ok((
        format!("azure-sevsnp:hostdata:{hostdata}"),
        format!("0x{hostdata}"),
    ))
}

fn is_false_like(value: &Value) -> bool {
    if let Some(flag) = value.as_bool() {
        return !flag;
    }
    if let Some(number) = value.as_u64() {
        return number == 0;
    }
    if let Some(text) = value.as_str() {
        return text == "false" || text == "False";
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn nitro_payload_normalizes_measurement_and_epoch() {
        let payload = json!({
            "provider": "nitro",
            "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 120,
            "epoch_length_s": 60,
            "summary": {"pcrs": {"0": "AA".repeat(48), "8": "BB".repeat(48)}}
        });
        let obj = match payload.as_object() {
            Some(value) => value,
            None => panic!("payload must be object"),
        };
        let verified = match verify_payload(obj) {
            Ok(value) => value,
            Err(err) => panic!("unexpected error: {err}"),
        };
        assert_eq!(
            verified,
            VerifiedAttestation {
                measurement: format!("nitro:pcr0:{}:pcr8:{}", "aa".repeat(48), "bb".repeat(48)),
                policy_digest: format!("0x{}", "d".repeat(64)),
                attestation_epoch: 2,
            }
        );
    }

    #[test]
    fn azure_payload_requires_hostdata_policy_binding() {
        let payload = json!({
            "provider": "azure-sevsnp",
            "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 60,
            "epoch_length_s": 60,
            "claims": {
                "x-ms-attestation-type": "sevsnpvm",
                "x-ms-sevsnpvm-is-debuggable": false,
                "x-ms-sevsnpvm-hostdata": "c".repeat(64)
            }
        });
        let obj = match payload.as_object() {
            Some(value) => value,
            None => panic!("payload must be object"),
        };
        let err = match verify_payload(obj) {
            Ok(_) => panic!("expected error"),
            Err(value) => value,
        };
        assert_eq!(err, "policy_digest must match azure hostdata");
    }

    #[test]
    fn epoch_must_fit_u32() {
        let payload = json!({
            "provider": "nitro",
            "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": (MAX_EPOCH + 1) * 60,
            "epoch_length_s": 1,
            "summary": {"pcrs": {"0": "aa".repeat(48), "8": "bb".repeat(48)}}
        });
        let obj = match payload.as_object() {
            Some(value) => value,
            None => panic!("payload must be object"),
        };
        let err = match verify_payload(obj) {
            Ok(_) => panic!("expected error"),
            Err(value) => value,
        };
        assert_eq!(err, "attestation_epoch must fit in u32");
    }
}
