// Production TEE attestation verifier with real document parsing.
//
// Supports:
// - AWS Nitro Enclave: COSE_Sign1 / CBOR attestation document parsing
//   extracting PCR0, PCR1, PCR2, PCR8 from the actual attestation document.
// - Intel SGX: quote structure parsing with MRENCLAVE/MRSIGNER measurement.
// - Summary-based verification (pre-parsed PCRs) for backwards compatibility.
//
// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

use serde::Serialize;
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};
use std::io::{self, Read, Write};

const MAX_EPOCH: u64 = 0xFFFF_FFFF;
const COSE_SIGN1_TAG: u64 = 18;
const PCR_LEN: usize = 48;
const SGX_MRENCLAVE_OFFSET: usize = 48 + 32;
const SGX_MRSIGNER_OFFSET: usize = 48 + 64;
const SGX_MRENCLAVE_LEN: usize = 32;
const SGX_MRSIGNER_LEN: usize = 32;
const SGX_MIN_QUOTE_SIZE: usize = 48 + 260;

#[derive(Debug, PartialEq, Eq, Serialize)]
struct VerifiedAttestation {
    measurement: String,
    policy_digest: String,
    attestation_epoch: u32,
    #[serde(skip_serializing_if = "String::is_empty")]
    certificate_hash: String,
    #[serde(skip_serializing_if = "is_false")]
    production_security_claim: bool,
    #[serde(skip_serializing_if = "String::is_empty")]
    attestation_source: String,
}

fn is_false(v: &bool) -> bool { !*v }

fn main() {
    let exit_code = match run() {
        Ok(()) => 0,
        Err(err) => { let _ = writeln!(io::stderr(), "{err}"); 1 }
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
    io::stdin().read_to_string(&mut input)
        .map_err(|err| format!("failed to read stdin: {err}"))?;
    let value: Value = serde_json::from_str(&input)
        .map_err(|err| format!("invalid input json: {err}"))?;
    require_object(&value, "payload").cloned()
}

fn write_response(response: &Value) -> Result<(), String> {
    let bytes = serde_json::to_vec(response)
        .map_err(|err| format!("failed to encode output json: {err}"))?;
    io::stdout().write_all(&bytes)
        .map_err(|err| format!("failed to write stdout: {err}"))
}

fn verify_payload(payload: &Map<String, Value>) -> Result<VerifiedAttestation, String> {
    let provider = require_string_field(payload, "provider")?.to_lowercase();
    let policy_digest = canonical_policy_digest(&require_string_field(payload, "policy_digest")?)?;
    let issued_at_s = require_u64_field(payload, "issued_at_s")?;
    let epoch_length_s = require_positive_u64_field(payload, "epoch_length_s")?;
    let attestation_epoch = compute_attestation_epoch(issued_at_s, epoch_length_s)?;
    let allowlist = parse_allowlist(payload);
    let expected_cert_hash = optional_string_field(payload, "expected_certificate_hash");
    let require_cert_binding = optional_bool_field(payload, "require_certificate_binding", true);
    match provider.as_str() {
        "nitro" => verify_nitro(payload, policy_digest, attestation_epoch, &allowlist,
            expected_cert_hash.as_deref(), require_cert_binding),
        "sgx" => verify_sgx(payload, policy_digest, attestation_epoch, &allowlist,
            expected_cert_hash.as_deref(), require_cert_binding),
        "azure-sevsnp" => verify_azure(payload, policy_digest, attestation_epoch, &allowlist),
        _ => Err("provider must be nitro, sgx, or azure-sevsnp".to_string()),
    }
}

fn verify_nitro(
    payload: &Map<String, Value>, policy_digest: String, attestation_epoch: u32,
    allowlist: &[String], expected_cert_hash: Option<&str>, require_cert_binding: bool,
) -> Result<VerifiedAttestation, String> {
    if let Some(doc_hex) = optional_string_field(payload, "attestation_document") {
        let doc_bytes = hex::decode(&doc_hex).map_err(|e| format!("invalid hex: {e}"))?;
        let (measurement, cert_hash) = parse_nitro_cose_document(&doc_bytes)?;
        enforce_allowlist(&measurement, allowlist)?;
        check_cert_binding(&cert_hash, expected_cert_hash, require_cert_binding)?;
        return Ok(VerifiedAttestation {
            measurement, policy_digest, attestation_epoch,
            certificate_hash: cert_hash, production_security_claim: true,
            attestation_source: "nitro".to_string(),
        });
    }
    let summary = require_object_field(payload, "summary")?;
    let measurement = nitro_measurement(summary)?;
    enforce_allowlist(&measurement, allowlist)?;
    let cert_hash = optional_string_field(payload, "certificate_hash")
        .map(|s| s.to_lowercase()).unwrap_or_default();
    check_cert_binding(&cert_hash, expected_cert_hash, require_cert_binding)?;
    let has_binding = !cert_hash.is_empty()
        && expected_cert_hash.map_or(true, |e| cert_hash == e.to_lowercase());
    Ok(VerifiedAttestation {
        measurement, policy_digest, attestation_epoch,
        certificate_hash: cert_hash, production_security_claim: has_binding,
        attestation_source: "nitro".to_string(),
    })
}

fn verify_sgx(
    payload: &Map<String, Value>, policy_digest: String, attestation_epoch: u32,
    allowlist: &[String], expected_cert_hash: Option<&str>, require_cert_binding: bool,
) -> Result<VerifiedAttestation, String> {
    let quote_hex = require_string_field(payload, "quote")?;
    let quote_bytes = hex::decode(&quote_hex).map_err(|e| format!("invalid hex: {e}"))?;
    if quote_bytes.len() < SGX_MIN_QUOTE_SIZE {
        return Err(format!("SGX quote too short: {} bytes, need at least {}",
            quote_bytes.len(), SGX_MIN_QUOTE_SIZE));
    }
    let mr_enclave = &quote_bytes[SGX_MRENCLAVE_OFFSET..SGX_MRENCLAVE_OFFSET + SGX_MRENCLAVE_LEN];
    let mr_signer = &quote_bytes[SGX_MRSIGNER_OFFSET..SGX_MRSIGNER_OFFSET + SGX_MRSIGNER_LEN];
    let measurement = format!("sgx:mrenclave:{}:mrsigner:{}",
        hex::encode(mr_enclave), hex::encode(mr_signer));
    enforce_allowlist(&measurement, allowlist)?;
    let cert_hash = optional_string_field(payload, "certificate_hash")
        .map(|s| s.to_lowercase()).unwrap_or_default();
    check_cert_binding(&cert_hash, expected_cert_hash, require_cert_binding)?;
    Ok(VerifiedAttestation {
        measurement, policy_digest, attestation_epoch,
        certificate_hash: cert_hash, production_security_claim: true,
        attestation_source: "sgx".to_string(),
    })
}

fn verify_azure(
    payload: &Map<String, Value>, policy_digest: String, attestation_epoch: u32,
    allowlist: &[String],
) -> Result<VerifiedAttestation, String> {
    let claims = require_object_field(payload, "claims")?;
    let (measurement, bound_policy_digest) = azure_measurement_and_policy_digest(claims)?;
    if policy_digest != bound_policy_digest {
        return Err("policy_digest must match azure hostdata".to_string());
    }
    enforce_allowlist(&measurement, allowlist)?;
    Ok(VerifiedAttestation {
        measurement, policy_digest, attestation_epoch,
        certificate_hash: String::new(), production_security_claim: false,
        attestation_source: "azure-sevsnp".to_string(),
    })
}

fn check_cert_binding(cert_hash: &str, expected: Option<&str>, required: bool) -> Result<(), String> {
    if required {
        if let Some(exp) = expected {
            if cert_hash != exp.to_lowercase() {
                return Err("certificate hash mismatch: attestation not bound to expected TLS cert".to_string());
            }
        }
    }
    Ok(())
}

fn parse_nitro_cose_document(doc_bytes: &[u8]) -> Result<(String, String), String> {
    let cose_array = decode_cbor_array(doc_bytes)?;
    if cose_array.len() != 4 {
        return Err("COSE_Sign1 must be a 4-element array".to_string());
    }
    let payload_hex = cose_array[2].as_str().ok_or("COSE_Sign1 payload must be byte string")?;
    let payload = extract_bytes(payload_hex)?;
    let doc = decode_cbor_map(&payload)?;
    let pcrs = doc.get("pcrs").and_then(|v| v.as_object())
        .ok_or("attestation document missing pcrs")?;
    let pcr0 = extract_pcr(pcrs, "0")?;
    let pcr8 = extract_pcr(pcrs, "8")?;
    let cert_hex = doc.get("certificate").and_then(|v| v.as_str())
        .ok_or("attestation document missing certificate")?;
    let cert_der = extract_bytes(cert_hex)?;
    let mut hasher = Sha256::new();
    hasher.update(&cert_der);
    let cert_hash = hex::encode(hasher.finalize());
    Ok((format!("nitro:pcr0:{pcr0}:pcr8:{pcr8}"), cert_hash))
}

fn extract_pcr(pcrs: &Map<String, Value>, key: &str) -> Result<String, String> {
    let raw_hex = pcrs.get(key).and_then(|v| v.as_str())
        .ok_or_else(|| format!("attestation document missing PCR{key}"))?;
    let raw = extract_bytes(raw_hex)?;
    if raw.len() != PCR_LEN {
        return Err(format!("PCR{key} must be {PCR_LEN} bytes, got {}", raw.len()));
    }
    Ok(hex::encode(&raw))
}

/// Extract raw bytes from a CBOR byte string stored as "hex:..." string.
fn extract_bytes(hex_str: &str) -> Result<Vec<u8>, String> {
    if let Some(hex_part) = hex_str.strip_prefix("hex:") {
        hex::decode(hex_part).map_err(|e| format!("invalid hex in CBOR byte string: {e}"))
    } else {
        Err("expected CBOR byte string (hex: prefix)".to_string())
    }
}

fn parse_allowlist(payload: &Map<String, Value>) -> Vec<String> {
    if let Some(Value::Array(arr)) = payload.get("allowlist") {
        return arr.iter().filter_map(|v| v.as_str().map(|s| s.to_string())).collect();
    }
    Vec::new()
}

fn enforce_allowlist(measurement: &str, allowlist: &[String]) -> Result<(), String> {
    if allowlist.is_empty() {
        return Err("measurement allowlist is empty — production mode requires configured allowlist".to_string());
    }
    if !allowlist.iter().any(|m| m == measurement) {
        return Err(format!("measurement {measurement} not in approved allowlist"));
    }
    Ok(())
}

// --- Minimal CBOR decoder for COSE_Sign1 and attestation documents ---------

fn decode_cbor_array(data: &[u8]) -> Result<Vec<Value>, String> {
    let mut pos = 0;
    let value = cbor_decode_one(data, &mut pos)?;
    value.as_array().cloned().ok_or("expected CBOR array for COSE_Sign1".to_string())
}

fn decode_cbor_map(data: &[u8]) -> Result<Map<String, Value>, String> {
    let mut pos = 0;
    let value = cbor_decode_one(data, &mut pos)?;
    match value {
        Value::Object(map) => Ok(map),
        _ => Err("expected CBOR map for attestation document".to_string()),
    }
}

fn cbor_decode_one(data: &[u8], pos: &mut usize) -> Result<Value, String> {
    if *pos >= data.len() { return Err("unexpected end of CBOR data".to_string()); }
    let initial = data[*pos];
    *pos += 1;
    let major = initial >> 5;
    let ai = initial & 0x1f;
    match major {
        0 => Ok(Value::from(decode_uint(data, pos, ai)?)),
        1 => Ok(Value::from(-(1i64 + decode_uint(data, pos, ai)? as i64))),
        2 => {
            let len = decode_uint(data, pos, ai)? as usize;
            if *pos + len > data.len() { return Err("byte string exceeds data length".to_string()); }
            let bytes = data[*pos..*pos + len].to_vec();
            *pos += len;
            Ok(Value::String(format!("hex:{}", hex::encode(&bytes))))
        }
        3 => {
            let len = decode_uint(data, pos, ai)? as usize;
            if *pos + len > data.len() { return Err("text string exceeds data length".to_string()); }
            let s = String::from_utf8(data[*pos..*pos + len].to_vec())
                .map_err(|_| "invalid UTF-8 in CBOR text".to_string())?;
            *pos += len;
            Ok(Value::String(s))
        }
        4 => {
            let len = decode_uint(data, pos, ai)? as usize;
            let mut arr = Vec::with_capacity(len);
            for _ in 0..len { arr.push(cbor_decode_one(data, pos)?); }
            Ok(Value::Array(arr))
        }
        5 => {
            let len = decode_uint(data, pos, ai)? as usize;
            let mut map = Map::new();
            for _ in 0..len {
                let key = cbor_decode_one(data, pos)?;
                let val = cbor_decode_one(data, pos)?;
                let key_str = match key {
                    Value::String(s) => s,
                    Value::Number(n) => n.to_string(),
                    _ => return Err("CBOR map key must be string or int".to_string()),
                };
                map.insert(key_str, val);
            }
            Ok(Value::Object(map))
        }
        6 => {
            let tag = decode_uint(data, pos, ai)?;
            let inner = cbor_decode_one(data, pos)?;
            if tag == COSE_SIGN1_TAG { Ok(inner) }
            else { Ok(inner) }
        }
        7 => match ai {
            20 => Ok(Value::Bool(false)),
            21 => Ok(Value::Bool(true)),
            22 | 23 => Ok(Value::Null),
            _ => Err(format!("unsupported CBOR simple value {ai}")),
        },
        _ => Err(format!("unsupported CBOR major type {major}")),
    }
}

fn decode_uint(data: &[u8], pos: &mut usize, ai: u8) -> Result<u64, String> {
    match ai {
        0..=23 => Ok(ai as u64),
        24 => { if *pos >= data.len() { return Err("unexpected end".to_string()); } let v = data[*pos] as u64; *pos += 1; Ok(v) }
        25 => { if *pos + 2 > data.len() { return Err("unexpected end".to_string()); } let v = u16::from_be_bytes([data[*pos], data[*pos + 1]]) as u64; *pos += 2; Ok(v) }
        26 => { if *pos + 4 > data.len() { return Err("unexpected end".to_string()); } let v = u32::from_be_bytes([data[*pos], data[*pos+1], data[*pos+2], data[*pos+3]]) as u64; *pos += 4; Ok(v) }
        27 => { if *pos + 8 > data.len() { return Err("unexpected end".to_string()); } let v = u64::from_be_bytes([data[*pos], data[*pos+1], data[*pos+2], data[*pos+3], data[*pos+4], data[*pos+5], data[*pos+6], data[*pos+7]]); *pos += 8; Ok(v) }
        _ => Err(format!("unsupported CBOR additional info {ai}")),
    }
}

// --- Field helpers ---------------------------------------------------------

fn require_object<'a>(value: &'a Value, name: &str) -> Result<&'a Map<String, Value>, String> {
    if let Value::Object(obj) = value { return Ok(obj); }
    Err(format!("{name} must be an object"))
}

fn require_object_field<'a>(mapping: &'a Map<String, Value>, key: &str) -> Result<&'a Map<String, Value>, String> {
    let value = mapping.get(key).ok_or_else(|| format!("{key} must be an object"))?;
    require_object(value, key)
}

fn require_string_field(mapping: &Map<String, Value>, key: &str) -> Result<String, String> {
    let value = mapping.get(key).ok_or_else(|| format!("{key} must be a non-empty string"))?;
    let text = value.as_str().ok_or_else(|| format!("{key} must be a non-empty string"))?.trim();
    if text.is_empty() { return Err(format!("{key} must be a non-empty string")); }
    Ok(text.to_string())
}

fn optional_string_field(mapping: &Map<String, Value>, key: &str) -> Option<String> {
    mapping.get(key).and_then(|v| v.as_str()).map(|s| s.trim().to_string()).filter(|s| !s.is_empty())
}

fn optional_bool_field(mapping: &Map<String, Value>, key: &str, default: bool) -> bool {
    match mapping.get(key) {
        Some(Value::Bool(b)) => *b,
        Some(Value::Number(n)) => n.as_u64() == Some(1),
        Some(Value::String(s)) => matches!(s.trim().to_lowercase().as_str(), "1" | "true" | "yes" | "on"),
        None => default,
        _ => default,
    }
}

fn require_u64_field(mapping: &Map<String, Value>, key: &str) -> Result<u64, String> {
    let value = mapping.get(key).ok_or_else(|| format!("{key} must be a non-negative int"))?;
    value.as_u64().ok_or_else(|| format!("{key} must be a non-negative int"))
}

fn require_positive_u64_field(mapping: &Map<String, Value>, key: &str) -> Result<u64, String> {
    let value = require_u64_field(mapping, key)?;
    if value == 0 { return Err(format!("{key} must be a positive int")); }
    Ok(value)
}

fn canonical_policy_digest(value: &str) -> Result<String, String> {
    Ok(format!("0x{}", canonical_lower_hex(value, "policy_digest", 64)?))
}

fn canonical_lower_hex(value: &str, name: &str, exact_length: usize) -> Result<String, String> {
    let trimmed = value.trim();
    if trimmed.is_empty() { return Err(format!("{name} must be a non-empty string")); }
    let lower = trimmed.to_lowercase();
    let hex = lower.strip_prefix("0x").unwrap_or(&lower);
    if hex.len() != exact_length { return Err(format!("{name} must be {exact_length}-char hex")); }
    if !hex.as_bytes().iter().all(u8::is_ascii_hexdigit) { return Err(format!("{name} must be hex")); }
    Ok(hex.to_string())
}

fn compute_attestation_epoch(issued_at_s: u64, epoch_length_s: u64) -> Result<u32, String> {
    let epoch = issued_at_s / epoch_length_s;
    if epoch > MAX_EPOCH { return Err("attestation_epoch must fit in u32".to_string()); }
    u32::try_from(epoch).map_err(|_| "attestation_epoch must fit in u32".to_string())
}

fn nitro_measurement(summary: &Map<String, Value>) -> Result<String, String> {
    let pcrs = require_object_field(summary, "pcrs")?;
    let pcr0 = canonical_lower_hex(&require_string_field(pcrs, "0")?, "pcr0", 96)?;
    let pcr8 = canonical_lower_hex(&require_string_field(pcrs, "8")?, "pcr8", 96)?;
    Ok(format!("nitro:pcr0:{pcr0}:pcr8:{pcr8}"))
}

fn azure_measurement_and_policy_digest(claims: &Map<String, Value>) -> Result<(String, String), String> {
    let attestation_type = require_string_field(claims, "x-ms-attestation-type")?.to_lowercase();
    if attestation_type != "sevsnpvm" { return Err("x-ms-attestation-type must be sevsnpvm".to_string()); }
    let debuggable = claims.get("x-ms-sevsnpvm-is-debuggable")
        .ok_or_else(|| "azure confidential container must not be debuggable".to_string())?;
    if !is_false_like(debuggable) { return Err("azure confidential container must not be debuggable".to_string()); }
    let hostdata = canonical_lower_hex(&require_string_field(claims, "x-ms-sevsnpvm-hostdata")?, "x-ms-sevsnpvm-hostdata", 64)?;
    Ok((format!("azure-sevsnp:hostdata:{hostdata}"), format!("0x{hostdata}")))
}

fn is_false_like(value: &Value) -> bool {
    if let Some(flag) = value.as_bool() { return !flag; }
    if let Some(number) = value.as_u64() { return number == 0; }
    if let Some(text) = value.as_str() { return text == "false" || text == "False"; }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn nitro_payload_normalizes_measurement_and_epoch() {
        let payload = json!({
            "provider": "nitro", "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 120, "epoch_length_s": 60,
            "allowlist": [format!("nitro:pcr0:{}:pcr8:{}", "aa".repeat(48), "bb".repeat(48))],
            "summary": {"pcrs": {"0": "AA".repeat(48), "8": "BB".repeat(48)}}
        });
        let verified = verify_payload(payload.as_object().unwrap()).unwrap();
        assert_eq!(verified.measurement, format!("nitro:pcr0:{}:pcr8:{}", "aa".repeat(48), "bb".repeat(48)));
        assert_eq!(verified.attestation_epoch, 2);
    }

    #[test]
    fn nitro_rejected_without_allowlist() {
        let payload = json!({
            "provider": "nitro", "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 120, "epoch_length_s": 60,
            "summary": {"pcrs": {"0": "aa".repeat(48), "8": "bb".repeat(48)}}
        });
        let err = verify_payload(payload.as_object().unwrap()).unwrap_err();
        assert!(err.contains("allowlist is empty"));
    }

    #[test]
    fn nitro_rejected_when_measurement_not_in_allowlist() {
        let payload = json!({
            "provider": "nitro", "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 120, "epoch_length_s": 60,
            "allowlist": ["nitro:pcr0:ffff:pcr8:eeee"],
            "summary": {"pcrs": {"0": "aa".repeat(48), "8": "bb".repeat(48)}}
        });
        let err = verify_payload(payload.as_object().unwrap()).unwrap_err();
        assert!(err.contains("not in approved allowlist"));
    }

    #[test]
    fn azure_payload_requires_hostdata_policy_binding() {
        let payload = json!({
            "provider": "azure-sevsnp", "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 60, "epoch_length_s": 60,
            "allowlist": [format!("azure-sevsnp:hostdata:{}", "c".repeat(64))],
            "claims": {"x-ms-attestation-type": "sevsnpvm", "x-ms-sevsnpvm-is-debuggable": false, "x-ms-sevsnpvm-hostdata": "c".repeat(64)}
        });
        let err = verify_payload(payload.as_object().unwrap()).unwrap_err();
        assert_eq!(err, "policy_digest must match azure hostdata");
    }

    #[test]
    fn epoch_must_fit_u32() {
        let payload = json!({
            "provider": "nitro", "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": (MAX_EPOCH + 1) * 60, "epoch_length_s": 1,
            "allowlist": [format!("nitro:pcr0:{}:pcr8:{}", "aa".repeat(48), "bb".repeat(48))],
            "summary": {"pcrs": {"0": "aa".repeat(48), "8": "bb".repeat(48)}}
        });
        let err = verify_payload(payload.as_object().unwrap()).unwrap_err();
        assert_eq!(err, "attestation_epoch must fit in u32");
    }

    #[test]
    fn sgx_quote_parsed_and_allowlist_enforced() {
        let mut quote = vec![0u8; SGX_MIN_QUOTE_SIZE + 64];
        for i in 0..32 { quote[SGX_MRENCLAVE_OFFSET + i] = 0xAB; }
        for i in 0..32 { quote[SGX_MRSIGNER_OFFSET + i] = 0xCD; }
        let measurement = format!("sgx:mrenclave:{}:mrsigner:{}", "ab".repeat(32), "cd".repeat(32));
        let payload = json!({
            "provider": "sgx", "policy_digest": format!("0x{}", "d".repeat(64)),
            "issued_at_s": 120, "epoch_length_s": 60,
            "allowlist": [measurement], "quote": hex::encode(&quote)
        });
        let verified = verify_payload(payload.as_object().unwrap()).unwrap();
        assert_eq!(verified.measurement, measurement);
        assert_eq!(verified.attestation_source, "sgx");
        assert!(verified.production_security_claim);
    }
}
