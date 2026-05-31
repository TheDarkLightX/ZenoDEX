//! Deterministic canonical encoding primitives.
//!
//! These mirror, byte-for-byte, the authoritative Python encoder in
//! `src/state/canonical.py`. Cross-language agreement on these primitives is
//! what makes Python/Rust state-root and receipt-hash equality possible.
//!
//! Conventions:
//! * `encode_uvarint` — unsigned LEB128 (little-endian base-128).
//! * `encode_bytes` — `uvarint(len)` length prefix, then the raw bytes.
//! * `domain_sep_bytes` — `b"zenodex:" + label + b":v" + version + b"\x00"`,
//!   an ASCII, NUL-terminated domain-separation prefix.
//! * `sha256_bytes` / `sha256_hex` — raw or lowercase `0x`-prefixed SHA-256.
//! * `hex_to_bytes_fixed` — `0x`-prefixed fixed-width hex → bytes.
//! * `canonical_json_bytes` — `sort_keys`, compact, `ensure_ascii=False`,
//!   floats rejected (over the core-owned [`JsonValue`] tree).

use num_bigint::BigInt;
use sha2::{Digest, Sha256};

/// Errors raised by the fallible canonical primitives (`hex_to_bytes_fixed` and
/// the serde→[`JsonValue`] bridge). Each carries a stable `code()` string so the
/// CLI and the Python differential can compare rejections deterministically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CanonicalError {
    /// Hex string is not `0x`-prefixed, or has the wrong length for `nbytes`.
    BadHexFormat,
    /// Hex body contains a non-`[0-9a-fA-F]` character.
    BadHexChars,
    /// Domain-separation label is empty, non-ASCII, or contains NUL.
    BadDomainLabel,
    /// Domain-separation version is zero.
    BadDomainVersion,
    /// A JSON number is not an integer (floats are rejected, matching Python).
    FloatNotAllowed,
}

impl CanonicalError {
    /// Stable machine code for this rejection.
    pub fn code(&self) -> &'static str {
        match self {
            CanonicalError::BadHexFormat => "bad_hex_format",
            CanonicalError::BadHexChars => "bad_hex_chars",
            CanonicalError::BadDomainLabel => "bad_domain_label",
            CanonicalError::BadDomainVersion => "bad_domain_version",
            CanonicalError::FloatNotAllowed => "float_not_allowed",
        }
    }
}

impl std::fmt::Display for CanonicalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

impl std::error::Error for CanonicalError {}

/// Unsigned LEB128 encoding of `value`.
pub fn encode_uvarint(mut value: u128) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            out.push(byte | 0x80);
        } else {
            out.push(byte);
            break;
        }
    }
    out
}

/// Length-prefixed byte string: `uvarint(len)` followed by `value`.
pub fn encode_bytes(value: &[u8]) -> Vec<u8> {
    let mut out = encode_uvarint(value.len() as u128);
    out.extend_from_slice(value);
    out
}

/// Fallible domain-separation prefix constructor.
pub fn try_domain_sep_bytes(label: &str, version: u32) -> Result<Vec<u8>, CanonicalError> {
    if label.is_empty() || !label.is_ascii() || label.contains('\u{0}') {
        return Err(CanonicalError::BadDomainLabel);
    }
    if version == 0 {
        return Err(CanonicalError::BadDomainVersion);
    }
    let mut out = Vec::new();
    out.extend_from_slice(b"zenodex:");
    out.extend_from_slice(label.as_bytes());
    out.extend_from_slice(b":v");
    out.extend_from_slice(version.to_string().as_bytes());
    out.push(0x00);
    Ok(out)
}

/// Domain-separation prefix: `b"zenodex:" + label + b":v" + version + b"\x00"`.
///
/// Core call sites pass compile-time constants. Dynamic labels should use
/// [`try_domain_sep_bytes`] and propagate the typed rejection.
pub fn domain_sep_bytes(label: &str, version: u32) -> Vec<u8> {
    try_domain_sep_bytes(label, version).expect("static domain separator is valid")
}

/// Raw SHA-256 digest of `data`.
pub fn sha256_bytes(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// Lowercase SHA-256 of `data`, `0x`-prefixed.
pub fn sha256_hex(data: &[u8]) -> String {
    format!("0x{}", hex::encode(sha256_bytes(data)))
}

/// Decode a `0x`-prefixed, fixed-width hex string into exactly `nbytes` bytes.
///
/// Mirrors `hex_to_bytes_fixed` in `src/state/canonical.py`: the input must be
/// `0x`-prefixed, exactly `2 + 2*nbytes` characters long, and the body must be
/// `[0-9a-fA-F]` (mixed case accepted, like Python's `bytes.fromhex`). Anything
/// else is a typed rejection — never a panic.
pub fn hex_to_bytes_fixed(hex_str: &str, nbytes: usize) -> Result<Vec<u8>, CanonicalError> {
    let expected_len = 2 + 2 * nbytes;
    let body = match hex_str.strip_prefix("0x") {
        Some(b) if hex_str.len() == expected_len => b,
        _ => return Err(CanonicalError::BadHexFormat),
    };
    if !body.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err(CanonicalError::BadHexChars);
    }
    // Length already pins this to exactly `nbytes` bytes; `hex::decode` cannot fail
    // here, but propagate defensively rather than unwrap.
    hex::decode(body).map_err(|_| CanonicalError::BadHexChars)
}

/// A canonical-JSON value tree.
///
/// This is the core crate's own JSON model (the core has no `serde` dependency).
/// It deliberately has **no float variant**: floats are rejected at the
/// serde→`JsonValue` boundary in the CLI, exactly as `canonical_json_bytes`
/// rejects them in Python. `Int` is an arbitrary-precision [`BigInt`] so the
/// encoding matches Python's unbounded `int`. Strings are Rust `String`s, which
/// are valid UTF-8 by construction — so the Python "surrogate code point"
/// rejection is satisfied structurally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Int(BigInt),
    Str(String),
    Array(Vec<JsonValue>),
    /// Object entries; serialization sorts keys by Unicode code point, so input
    /// order is irrelevant (matches Python `json.dumps(sort_keys=True)`).
    Object(Vec<(String, JsonValue)>),
}

impl JsonValue {
    /// Build an `Int` node from a decimal string (the serde→`JsonValue` bridge
    /// in the CLI uses this so it needs no `num-bigint` dependency of its own).
    /// Returns `None` if `s` is not a valid base-10 integer literal.
    pub fn int_from_decimal_str(s: &str) -> Option<JsonValue> {
        s.parse::<BigInt>().ok().map(JsonValue::Int)
    }
}

/// Append the canonical JSON escaping of `s` (the quoted form, including the
/// surrounding `"`) to `out`, matching CPython `json.encoder` with
/// `ensure_ascii=False`: escape `"`, `\`, and control chars `0x00..=0x1f`
/// (short escapes for `\b \t \n \f \r`, `\u00xx` otherwise); everything else
/// (including all non-ASCII) is emitted as raw UTF-8.
fn escape_json_string(s: &str, out: &mut String) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\u{09}' => out.push_str("\\t"),
            '\u{0a}' => out.push_str("\\n"),
            '\u{0c}' => out.push_str("\\f"),
            '\u{0d}' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn write_canonical_json(value: &JsonValue, out: &mut String) {
    match value {
        JsonValue::Null => out.push_str("null"),
        JsonValue::Bool(true) => out.push_str("true"),
        JsonValue::Bool(false) => out.push_str("false"),
        JsonValue::Int(n) => out.push_str(&n.to_string()),
        JsonValue::Str(s) => escape_json_string(s, out),
        JsonValue::Array(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i != 0 {
                    out.push(',');
                }
                write_canonical_json(item, out);
            }
            out.push(']');
        }
        JsonValue::Object(entries) => {
            // Sort by key code point. Rust `str` ordering is byte-lexicographic
            // over UTF-8, which equals Unicode code-point order — identical to
            // Python's `sorted()` on `str` keys.
            let mut sorted: Vec<&(String, JsonValue)> = entries.iter().collect();
            sorted.sort_by(|a, b| a.0.cmp(&b.0));
            out.push('{');
            for (i, (k, v)) in sorted.iter().enumerate() {
                if i != 0 {
                    out.push(',');
                }
                escape_json_string(k, out);
                out.push(':');
                write_canonical_json(v, out);
            }
            out.push('}');
        }
    }
}

/// Canonical JSON encoding (UTF-8 bytes) of `value`, byte-for-byte equal to
/// `canonical_json_bytes` in `src/state/canonical.py`:
/// `sort_keys=True`, `separators=(",", ":")`, `ensure_ascii=False`,
/// `allow_nan=False`, floats rejected. Infallible here because [`JsonValue`]
/// cannot represent a float or a non-string key (those are rejected when an
/// external value is lowered into `JsonValue`).
pub fn canonical_json_bytes(value: &JsonValue) -> Vec<u8> {
    let mut out = String::new();
    write_canonical_json(value, &mut out);
    out.into_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uvarint_known_vectors() {
        assert_eq!(encode_uvarint(0), vec![0x00]);
        assert_eq!(encode_uvarint(1), vec![0x01]);
        assert_eq!(encode_uvarint(127), vec![0x7f]);
        assert_eq!(encode_uvarint(128), vec![0x80, 0x01]);
        assert_eq!(encode_uvarint(300), vec![0xac, 0x02]);
        assert_eq!(encode_uvarint(16_384), vec![0x80, 0x80, 0x01]);
    }

    #[test]
    fn encode_bytes_prefixes_length() {
        assert_eq!(encode_bytes(b""), vec![0x00]);
        assert_eq!(encode_bytes(b"ab"), vec![0x02, b'a', b'b']);
    }

    #[test]
    fn domain_sep_matches_python() {
        assert_eq!(
            domain_sep_bytes("fee_receipt", 1),
            b"zenodex:fee_receipt:v1\x00".to_vec()
        );
        assert_eq!(
            domain_sep_bytes("fee_accumulator", 1),
            b"zenodex:fee_accumulator:v1\x00".to_vec()
        );
    }

    #[test]
    fn try_domain_sep_rejects_bad_labels_and_versions() {
        assert_eq!(
            try_domain_sep_bytes("", 1),
            Err(CanonicalError::BadDomainLabel)
        );
        assert_eq!(
            try_domain_sep_bytes("bad\u{0}label", 1),
            Err(CanonicalError::BadDomainLabel)
        );
        assert_eq!(
            try_domain_sep_bytes("nonasciié", 1),
            Err(CanonicalError::BadDomainLabel)
        );
        assert_eq!(
            try_domain_sep_bytes("fee_receipt", 0),
            Err(CanonicalError::BadDomainVersion)
        );
    }

    #[test]
    fn sha256_hex_empty_vector() {
        // Matches hashlib.sha256(b"").hexdigest() with the 0x prefix.
        assert_eq!(
            sha256_bytes(b""),
            [
                0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f,
                0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b,
                0x78, 0x52, 0xb8, 0x55,
            ]
        );
        assert_eq!(
            sha256_hex(b""),
            "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn hex_to_bytes_fixed_roundtrip_and_case() {
        assert_eq!(hex_to_bytes_fixed("0x00", 1).unwrap(), vec![0x00]);
        assert_eq!(hex_to_bytes_fixed("0xff", 1).unwrap(), vec![0xff]);
        // Mixed case accepted (matches Python bytes.fromhex).
        assert_eq!(
            hex_to_bytes_fixed("0xDeAdBeEf", 4).unwrap(),
            vec![0xde, 0xad, 0xbe, 0xef]
        );
        assert_eq!(hex_to_bytes_fixed("0x0102", 2).unwrap(), vec![0x01, 0x02]);
    }

    #[test]
    fn hex_to_bytes_fixed_rejections() {
        // Missing 0x prefix.
        assert_eq!(
            hex_to_bytes_fixed("00", 1),
            Err(CanonicalError::BadHexFormat)
        );
        // Wrong length for nbytes.
        assert_eq!(
            hex_to_bytes_fixed("0x0102", 1),
            Err(CanonicalError::BadHexFormat)
        );
        assert_eq!(
            hex_to_bytes_fixed("0x01", 2),
            Err(CanonicalError::BadHexFormat)
        );
        // Right length, non-hex body.
        assert_eq!(
            hex_to_bytes_fixed("0xzz", 1),
            Err(CanonicalError::BadHexChars)
        );
        // Prefix only.
        assert_eq!(
            hex_to_bytes_fixed("0x", 1),
            Err(CanonicalError::BadHexFormat)
        );
    }

    fn int(n: i64) -> JsonValue {
        JsonValue::Int(BigInt::from(n))
    }

    #[test]
    fn canonical_json_scalars() {
        assert_eq!(canonical_json_bytes(&JsonValue::Null), b"null");
        assert_eq!(canonical_json_bytes(&JsonValue::Bool(true)), b"true");
        assert_eq!(canonical_json_bytes(&JsonValue::Bool(false)), b"false");
        assert_eq!(canonical_json_bytes(&int(0)), b"0");
        assert_eq!(canonical_json_bytes(&int(-123)), b"-123");
        assert_eq!(
            canonical_json_bytes(&JsonValue::Str("ab".to_string())),
            b"\"ab\""
        );
    }

    #[test]
    fn canonical_json_big_integer() {
        // 10^30 — beyond u128 digit domain checks, but BigInt is exact.
        let big: BigInt = "1000000000000000000000000000000".parse().unwrap();
        assert_eq!(
            canonical_json_bytes(&JsonValue::Int(big)),
            b"1000000000000000000000000000000"
        );
    }

    #[test]
    fn canonical_json_sorts_keys_and_compacts() {
        // Insertion order b, a → emitted a, b; no whitespace.
        let obj = JsonValue::Object(vec![("b".to_string(), int(2)), ("a".to_string(), int(1))]);
        assert_eq!(canonical_json_bytes(&obj), b"{\"a\":1,\"b\":2}");
    }

    #[test]
    fn canonical_json_nested_and_arrays() {
        let v = JsonValue::Object(vec![
            (
                "fields".to_string(),
                JsonValue::Array(vec![int(1), JsonValue::Str("x".to_string())]),
            ),
            ("k".to_string(), JsonValue::Bool(true)),
        ]);
        assert_eq!(
            canonical_json_bytes(&v),
            b"{\"fields\":[1,\"x\"],\"k\":true}"
        );
    }

    #[test]
    fn canonical_json_escaping_matches_python() {
        // Quote, backslash, and short control escapes (\b \t \n \f \r).
        // Input: a " b \ c <newline> <tab>
        let s = JsonValue::Str("a\"b\\c\n\t".to_string());
        // Expected body: a \" b \\ c \n \t  (each escape is two chars), quoted.
        let expected = b"\"a\\\"b\\\\c\\n\\t\"".to_vec();
        assert_eq!(canonical_json_bytes(&s), expected);
        // A non-short control char (0x01) escapes as  (lowercase, 4 digits).
        assert_eq!(
            canonical_json_bytes(&JsonValue::Str("\u{01}".to_string())),
            b"\"\\u0001\""
        );
        // Non-ASCII stays raw UTF-8 (ensure_ascii=False), not \uXXXX.
        let u = JsonValue::Str("é".to_string());
        assert_eq!(canonical_json_bytes(&u), "\"é\"".as_bytes());
    }
}
