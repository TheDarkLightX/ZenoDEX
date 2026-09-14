//! Owned swap intent in the legacy `SwapIntent` signing-codec shape.
//!
//! The intent is ordinary data. It carries the complete wire body (module,
//! version, kind, id, sender, deadline, salt and flat fields) so the command
//! body hash and the statement root bind every original field. Field scalars
//! keep the exact integer text or text the codec admits; a non-scalar value is
//! carried as `Nested` so the transition can classify it in Python order.
//! Nothing here authenticates a signature or a subject.

use std::collections::BTreeMap;
use std::str::FromStr;

use serde::{Deserialize, Serialize, Serializer};
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, hash_economic_command_body_v2, AbiErrorV2, AbiResultV2, RootV2,
};

pub const SWAP_INTENT_MODULE_V2: &str = "TauSwap";
pub const SWAP_INTENT_VERSION_V2: &str = "0.1";
pub const MAX_SWAP_INTENT_TEXT_CHARS_V2: usize = 512;
pub const MAX_SWAP_INTENT_SALT_CHARS_V2: usize = 4_096;
pub const MAX_SWAP_INTENT_FIELD_TEXT_CHARS_V2: usize = 32_000;
/// Largest key count the legacy freezer admits (`5 * len + 1 <= 32_000`).
pub const MAX_SWAP_INTENT_FIELD_COUNT_V2: usize = 6_399;
pub const MAX_SWAP_INTENT_FIELDS_CANONICAL_BYTES_V2: usize = 32_000;
/// Decimal digits of `2^256 - 1`, the legacy `MAX_UVARINT_BITS` magnitude.
pub const MAX_SWAP_INTENT_INTEGER_DIGITS_V2: usize = 78;
pub const MAX_SWAP_INTENT_NONCE_V2: u64 = 4_294_967_295;
pub const SWAP_INTENT_TRANSPORT_RESERVED_FIELDS_V2: [&str; 10] = [
    "module",
    "version",
    "kind",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "salt",
    "fields",
    "signature",
    "quote_receipt",
];
const MAX_SWAP_INTENT_INTEGER_MAGNITUDE_TEXT_V2: &str =
    "115792089237316195423570985008687907853269984665640564039457584007913129639935";
const _: () =
    assert!(MAX_SWAP_INTENT_INTEGER_MAGNITUDE_TEXT_V2.len() == MAX_SWAP_INTENT_INTEGER_DIGITS_V2);

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum SpotSwapKindV2 {
    SWAP_EXACT_IN,
    SWAP_EXACT_OUT,
}

impl SpotSwapKindV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SWAP_EXACT_IN => "SWAP_EXACT_IN",
            Self::SWAP_EXACT_OUT => "SWAP_EXACT_OUT",
        }
    }

    /// The closed field set of `_snapshot_swap_fields` for this kind.
    pub const fn supported_fields(self) -> [&'static str; 7] {
        match self {
            Self::SWAP_EXACT_IN => [
                "pool_id",
                "asset_in",
                "asset_out",
                "nonce",
                "recipient",
                "amount_in",
                "min_amount_out",
            ],
            Self::SWAP_EXACT_OUT => [
                "pool_id",
                "asset_in",
                "asset_out",
                "nonce",
                "recipient",
                "amount_out",
                "max_amount_in",
            ],
        }
    }

    const fn amount_fields(self) -> (&'static str, &'static str) {
        match self {
            Self::SWAP_EXACT_IN => ("amount_in", "min_amount_out"),
            Self::SWAP_EXACT_OUT => ("amount_out", "max_amount_in"),
        }
    }
}

/// Canonical decimal integer text admitted by the legacy intent codec
/// (magnitude at most `2^256 - 1`, optional leading minus, no leading zeros).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SwapIntentIntegerV2 {
    text: String,
}

impl SwapIntentIntegerV2 {
    pub fn parse_canonical_text(text: &str) -> AbiResultV2<Self> {
        let digits = text.strip_prefix('-').unwrap_or(text);
        let negative = digits.len() != text.len();
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(AbiErrorV2::InvalidBounds("swap intent integer text"));
        }
        if (digits.len() > 1 && digits.starts_with('0')) || (negative && digits == "0") {
            return Err(AbiErrorV2::InvalidBounds(
                "swap intent integer text is not canonical",
            ));
        }
        if digits.len() > MAX_SWAP_INTENT_INTEGER_DIGITS_V2
            || (digits.len() == MAX_SWAP_INTENT_INTEGER_DIGITS_V2
                && digits > MAX_SWAP_INTENT_INTEGER_MAGNITUDE_TEXT_V2)
        {
            return Err(AbiErrorV2::InvalidBounds(
                "swap intent integer exceeds 256 bits",
            ));
        }
        Ok(Self {
            text: text.to_owned(),
        })
    }

    pub fn from_u128(value: u128) -> Self {
        Self {
            text: value.to_string(),
        }
    }

    pub fn from_i128(value: i128) -> Self {
        Self {
            text: value.to_string(),
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn is_negative(&self) -> bool {
        self.text.starts_with('-')
    }

    pub fn is_zero(&self) -> bool {
        self.text == "0"
    }

    /// The value when it is nonnegative and fits `u128`.
    pub fn as_u128(&self) -> Option<u128> {
        if self.is_negative() {
            return None;
        }
        u128::from_str(&self.text).ok()
    }

    /// The value when it is nonnegative and fits `u64`.
    pub fn as_u64(&self) -> Option<u64> {
        if self.is_negative() {
            return None;
        }
        u64::from_str(&self.text).ok()
    }
}

/// One flat intent field value as the legacy codec stores it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SwapIntentFieldValueV2 {
    Integer(SwapIntentIntegerV2),
    Text(String),
    /// A JSON value outside the flat scalar profile (null, bool, array or
    /// object). It is carried only so the transition can classify it; it is
    /// never hashed and never admitted.
    Nested,
}

impl Serialize for SwapIntentFieldValueV2 {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Integer(value) => {
                let number = serde_json::Number::from_str(value.text())
                    .map_err(<S::Error as serde::ser::Error>::custom)?;
                number.serialize(serializer)
            }
            Self::Text(text) => serializer.serialize_str(text),
            Self::Nested => Err(<S::Error as serde::ser::Error>::custom(
                "nested swap intent field values are not flat scalars",
            )),
        }
    }
}

/// A slippage bound as the Python comparison sees it: integers beyond `u128`
/// compare above every reachable amount.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SwapAmountBoundV2 {
    Atoms(u128),
    BeyondU128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SwapIntentFieldProfileV2 {
    Supported,
    Unsupported,
}

/// The complete legacy `SwapIntent` value set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpotSwapIntentPartsV2 {
    pub module: String,
    pub version: String,
    pub kind: SpotSwapKindV2,
    pub intent_id: String,
    pub sender_pubkey: String,
    pub deadline: u64,
    pub salt: Option<String>,
    pub fields: BTreeMap<String, SwapIntentFieldValueV2>,
}

/// Validated owned swap intent. Construction mirrors `SwapIntent.__post_init__`
/// plus the structural checks of `_snapshot_intent`; field classification for
/// the swap profile happens in [`SpotSwapIntentV2::field_profile`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpotSwapIntentV2 {
    parts: SpotSwapIntentPartsV2,
}

/// Canonical command body: every original wire field including the flat fields.
#[derive(Serialize)]
pub struct SpotSwapCommandBodyV2<'a> {
    pub module: &'a str,
    pub version: &'a str,
    pub kind: SpotSwapKindV2,
    pub intent_id: &'a str,
    pub sender_pubkey: &'a str,
    pub deadline: u64,
    pub salt: Option<&'a str>,
    pub fields: &'a BTreeMap<String, SwapIntentFieldValueV2>,
}

fn require_text(value: &str, maximum: usize, field: &'static str) -> AbiResultV2<()> {
    let chars = value.chars().count();
    if chars == 0 || chars > maximum {
        return Err(AbiErrorV2::InvalidBounds(field));
    }
    Ok(())
}

fn amount_bound(value: Option<&SwapIntentIntegerV2>) -> SwapAmountBoundV2 {
    match value.and_then(SwapIntentIntegerV2::as_u128) {
        Some(atoms) => SwapAmountBoundV2::Atoms(atoms),
        None => SwapAmountBoundV2::BeyondU128,
    }
}

impl SpotSwapIntentV2 {
    pub fn new(parts: SpotSwapIntentPartsV2) -> AbiResultV2<Self> {
        let intent = Self { parts };
        intent.validate()?;
        Ok(intent)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        let parts = &self.parts;
        if parts.module != SWAP_INTENT_MODULE_V2 {
            return Err(AbiErrorV2::InvalidBinding("swap intent module"));
        }
        if parts.version != SWAP_INTENT_VERSION_V2 {
            return Err(AbiErrorV2::InvalidBinding("swap intent version"));
        }
        RootV2::parse(parts.intent_id.clone(), "swap intent id", true)?;
        require_text(
            &parts.sender_pubkey,
            MAX_SWAP_INTENT_TEXT_CHARS_V2,
            "swap intent sender",
        )?;
        if let Some(salt) = &parts.salt {
            require_text(salt, MAX_SWAP_INTENT_SALT_CHARS_V2, "swap intent salt")?;
        }
        if parts.fields.len() > MAX_SWAP_INTENT_FIELD_COUNT_V2 {
            return Err(AbiErrorV2::InvalidBounds("swap intent field count"));
        }
        for (key, value) in &parts.fields {
            if key.chars().count() > MAX_SWAP_INTENT_FIELD_TEXT_CHARS_V2 {
                return Err(AbiErrorV2::InvalidBounds("swap intent field key"));
            }
            if SWAP_INTENT_TRANSPORT_RESERVED_FIELDS_V2.contains(&key.as_str()) {
                return Err(AbiErrorV2::InvalidBinding(
                    "swap intent reserved transport key",
                ));
            }
            if let SwapIntentFieldValueV2::Text(text) = value {
                if text.chars().count() > MAX_SWAP_INTENT_FIELD_TEXT_CHARS_V2 {
                    return Err(AbiErrorV2::InvalidBounds("swap intent field text"));
                }
            }
        }
        self.require_swap_fields()?;
        if !self.has_nested_fields()
            && canonical_bytes_v2(&parts.fields)?.len() > MAX_SWAP_INTENT_FIELDS_CANONICAL_BYTES_V2
        {
            return Err(AbiErrorV2::InvalidBounds(
                "swap intent fields canonical bytes",
            ));
        }
        Ok(())
    }

    fn require_swap_fields(&self) -> AbiResultV2<()> {
        let fields = &self.parts.fields;
        for name in ["pool_id", "asset_in", "asset_out"] {
            match fields.get(name) {
                Some(SwapIntentFieldValueV2::Text(text)) if !text.is_empty() => {}
                _ => {
                    return Err(AbiErrorV2::InvalidBinding(
                        "swap intent required text field",
                    ))
                }
            }
        }
        if let Some(value) = fields.get("recipient") {
            match value {
                SwapIntentFieldValueV2::Text(text) if !text.is_empty() => {}
                _ => return Err(AbiErrorV2::InvalidBinding("swap intent recipient")),
            }
        }
        let (positive, nonnegative) = self.parts.kind.amount_fields();
        match fields.get(positive) {
            Some(SwapIntentFieldValueV2::Integer(value))
                if !value.is_negative() && !value.is_zero() => {}
            _ => return Err(AbiErrorV2::InvalidBinding("swap intent positive amount")),
        }
        match fields.get(nonnegative) {
            Some(SwapIntentFieldValueV2::Integer(value)) if !value.is_negative() => {}
            _ => return Err(AbiErrorV2::InvalidBinding("swap intent nonnegative amount")),
        }
        Ok(())
    }

    pub fn parts(&self) -> &SpotSwapIntentPartsV2 {
        &self.parts
    }

    pub fn kind(&self) -> SpotSwapKindV2 {
        self.parts.kind
    }

    pub fn command_kind(&self) -> &'static str {
        self.parts.kind.as_str()
    }

    pub fn intent_id(&self) -> &str {
        &self.parts.intent_id
    }

    pub fn sender_pubkey(&self) -> &str {
        &self.parts.sender_pubkey
    }

    pub fn deadline(&self) -> u64 {
        self.parts.deadline
    }

    pub fn salt(&self) -> Option<&str> {
        self.parts.salt.as_deref()
    }

    pub fn fields(&self) -> &BTreeMap<String, SwapIntentFieldValueV2> {
        &self.parts.fields
    }

    fn text_field(&self, name: &str) -> &str {
        match self.parts.fields.get(name) {
            Some(SwapIntentFieldValueV2::Text(text)) => text.as_str(),
            _ => "",
        }
    }

    fn integer_field(&self, name: &str) -> Option<&SwapIntentIntegerV2> {
        match self.parts.fields.get(name) {
            Some(SwapIntentFieldValueV2::Integer(value)) => Some(value),
            _ => None,
        }
    }

    pub fn pool_id(&self) -> &str {
        self.text_field("pool_id")
    }

    pub fn asset_in(&self) -> &str {
        self.text_field("asset_in")
    }

    pub fn asset_out(&self) -> &str {
        self.text_field("asset_out")
    }

    /// The optional recipient field, defaulting to the sender exactly as
    /// `intent.get_field("recipient", sender_pubkey)` does.
    pub fn recipient(&self) -> &str {
        match self.parts.fields.get("recipient") {
            Some(SwapIntentFieldValueV2::Text(text)) => text.as_str(),
            _ => self.parts.sender_pubkey.as_str(),
        }
    }

    /// The inner nonce when it is an exact integer in `1..=u32::MAX`; any other
    /// value (text, zero, negative, oversized) is `None` and rejects as
    /// `INVALID_NONCE` in the planner.
    pub fn nonce(&self) -> Option<u32> {
        let nonce = self.integer_field("nonce")?.as_u64()?;
        if nonce == 0 || nonce > MAX_SWAP_INTENT_NONCE_V2 {
            return None;
        }
        u32::try_from(nonce).ok()
    }

    pub fn amount_in(&self) -> Option<u128> {
        self.integer_field("amount_in")
            .and_then(SwapIntentIntegerV2::as_u128)
    }

    pub fn amount_out(&self) -> Option<u128> {
        self.integer_field("amount_out")
            .and_then(SwapIntentIntegerV2::as_u128)
    }

    pub fn min_amount_out(&self) -> SwapAmountBoundV2 {
        amount_bound(self.integer_field("min_amount_out"))
    }

    pub fn max_amount_in(&self) -> SwapAmountBoundV2 {
        amount_bound(self.integer_field("max_amount_in"))
    }

    pub fn has_nested_fields(&self) -> bool {
        self.parts
            .fields
            .values()
            .any(|value| matches!(value, SwapIntentFieldValueV2::Nested))
    }

    /// Mirrors `_snapshot_swap_fields`: too many keys or a foreign key is the
    /// economic `UNSUPPORTED_FIELDS` outcome; a non-scalar value under a
    /// supported key is a structural error, checked in sorted key order. An
    /// empty key fails the legacy `key <= previous` ordering check against its
    /// empty sentinel and is therefore structural as well.
    pub fn field_profile(&self) -> AbiResultV2<SwapIntentFieldProfileV2> {
        let supported = self.parts.kind.supported_fields();
        if self.parts.fields.len() > supported.len() {
            return Ok(SwapIntentFieldProfileV2::Unsupported);
        }
        for (key, value) in &self.parts.fields {
            if key.is_empty() {
                return Err(AbiErrorV2::InvalidBinding(
                    "swap intent fields must have unique, ordered keys",
                ));
            }
            if !supported.contains(&key.as_str()) {
                return Ok(SwapIntentFieldProfileV2::Unsupported);
            }
            if matches!(value, SwapIntentFieldValueV2::Nested) {
                return Err(AbiErrorV2::InvalidBinding(
                    "swap intent fields must contain exact flat scalars",
                ));
            }
        }
        Ok(SwapIntentFieldProfileV2::Supported)
    }

    pub fn command_body(&self) -> SpotSwapCommandBodyV2<'_> {
        SpotSwapCommandBodyV2 {
            module: &self.parts.module,
            version: &self.parts.version,
            kind: self.parts.kind,
            intent_id: &self.parts.intent_id,
            sender_pubkey: &self.parts.sender_pubkey,
            deadline: self.parts.deadline,
            salt: self.parts.salt.as_deref(),
            fields: &self.parts.fields,
        }
    }

    /// `hash_economic_command_body_v2(kind.value, _intent_body(intent))`.
    pub fn command_body_hash(&self) -> AbiResultV2<RootV2> {
        hash_economic_command_body_v2(self.command_kind(), &self.command_body())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zenodex_global_settlement_abi_v2::canonical_economic_command_body_bytes_v2;

    fn integer(value: i128) -> SwapIntentFieldValueV2 {
        SwapIntentFieldValueV2::Integer(SwapIntentIntegerV2::from_i128(value))
    }

    fn text(value: &str) -> SwapIntentFieldValueV2 {
        SwapIntentFieldValueV2::Text(value.to_owned())
    }

    fn parts(kind: SpotSwapKindV2) -> SpotSwapIntentPartsV2 {
        let mut fields = BTreeMap::new();
        fields.insert("pool_id".to_owned(), text("pool"));
        fields.insert("asset_in".to_owned(), text("A"));
        fields.insert("asset_out".to_owned(), text("B"));
        fields.insert("nonce".to_owned(), integer(1));
        match kind {
            SpotSwapKindV2::SWAP_EXACT_IN => {
                fields.insert("amount_in".to_owned(), integer(10));
                fields.insert("min_amount_out".to_owned(), integer(7));
            }
            SpotSwapKindV2::SWAP_EXACT_OUT => {
                fields.insert("amount_out".to_owned(), integer(7));
                fields.insert("max_amount_in".to_owned(), integer(10));
            }
        }
        SpotSwapIntentPartsV2 {
            module: SWAP_INTENT_MODULE_V2.to_owned(),
            version: SWAP_INTENT_VERSION_V2.to_owned(),
            kind,
            intent_id: format!("0x{}", "11".repeat(32)),
            sender_pubkey: "alice".to_owned(),
            deadline: 100,
            salt: None,
            fields,
        }
    }

    #[test]
    fn command_body_bytes_match_the_python_canonical_json_layout() {
        let intent = SpotSwapIntentV2::new(parts(SpotSwapKindV2::SWAP_EXACT_OUT)).expect("intent");
        let bytes =
            canonical_economic_command_body_bytes_v2(intent.command_kind(), &intent.command_body())
                .expect("canonical body");
        let expected = format!(
            "{{\"command\":{{\"deadline\":100,\"fields\":{{\"amount_out\":7,\"asset_in\":\"A\",\"asset_out\":\"B\",\"max_amount_in\":10,\"nonce\":1,\"pool_id\":\"pool\"}},\"intent_id\":\"0x{}\",\"kind\":\"SWAP_EXACT_OUT\",\"module\":\"TauSwap\",\"salt\":null,\"sender_pubkey\":\"alice\",\"version\":\"0.1\"}},\"command_kind\":\"SWAP_EXACT_OUT\"}}",
            "11".repeat(32)
        );
        assert_eq!(String::from_utf8(bytes).expect("utf8"), expected);
        assert!(intent.command_body_hash().is_ok());
    }

    #[test]
    fn big_integer_text_round_trips_exactly_and_bounds_at_256_bits() {
        let max =
            SwapIntentIntegerV2::parse_canonical_text(MAX_SWAP_INTENT_INTEGER_MAGNITUDE_TEXT_V2)
                .expect("2^256 - 1 is admitted");
        assert_eq!(max.as_u128(), None);
        let mut fields = parts(SpotSwapKindV2::SWAP_EXACT_IN).fields;
        fields.insert(
            "min_amount_out".to_owned(),
            SwapIntentFieldValueV2::Integer(max),
        );
        let bytes = canonical_bytes_v2(&fields).expect("fields bytes");
        assert!(String::from_utf8(bytes).expect("utf8").contains(&format!(
            "\"min_amount_out\":{MAX_SWAP_INTENT_INTEGER_MAGNITUDE_TEXT_V2}"
        )));
        for rejected in [
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000",
            "-0",
            "007",
            "",
            "-",
            "1.0",
            "1e3",
            "+1",
        ] {
            assert!(
                SwapIntentIntegerV2::parse_canonical_text(rejected).is_err(),
                "{rejected} must reject"
            );
        }
        let negative = SwapIntentIntegerV2::parse_canonical_text("-5").expect("negative text");
        assert!(negative.is_negative());
        assert_eq!(negative.as_u64(), None);
    }

    #[test]
    fn reserved_transport_keys_and_missing_required_fields_are_structural_errors() {
        for reserved in SWAP_INTENT_TRANSPORT_RESERVED_FIELDS_V2 {
            let mut candidate = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
            candidate.fields.insert(reserved.to_owned(), text("x"));
            assert!(SpotSwapIntentV2::new(candidate).is_err(), "{reserved}");
        }
        for missing in [
            "pool_id",
            "asset_in",
            "asset_out",
            "amount_out",
            "max_amount_in",
        ] {
            let mut candidate = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
            candidate.fields.remove(missing);
            assert!(SpotSwapIntentV2::new(candidate).is_err(), "{missing}");
        }
        let mut zero_amount = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        zero_amount
            .fields
            .insert("amount_in".to_owned(), integer(0));
        assert!(SpotSwapIntentV2::new(zero_amount).is_err());
        let mut negative_bound = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        negative_bound
            .fields
            .insert("min_amount_out".to_owned(), integer(-1));
        assert!(SpotSwapIntentV2::new(negative_bound).is_err());
        let mut empty_recipient = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        empty_recipient
            .fields
            .insert("recipient".to_owned(), text(""));
        assert!(SpotSwapIntentV2::new(empty_recipient).is_err());
        let mut foreign_module = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        foreign_module.module = "Other".to_owned();
        assert!(SpotSwapIntentV2::new(foreign_module).is_err());
        let mut foreign_version = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        foreign_version.version = "0.2".to_owned();
        assert!(SpotSwapIntentV2::new(foreign_version).is_err());
        let mut bad_id = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        bad_id.intent_id = "0x11".to_owned();
        assert!(SpotSwapIntentV2::new(bad_id).is_err());
        let mut long_salt = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        long_salt.salt = Some("s".repeat(MAX_SWAP_INTENT_SALT_CHARS_V2 + 1));
        assert!(SpotSwapIntentV2::new(long_salt).is_err());
        let mut max_salt = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        max_salt.salt = Some("s".repeat(MAX_SWAP_INTENT_SALT_CHARS_V2));
        assert!(SpotSwapIntentV2::new(max_salt).is_ok());
    }

    #[test]
    fn nonce_text_zero_and_overflow_are_not_nonces_while_max_u32_is() {
        for (value, expected) in [
            (integer(1), Some(1)),
            (integer(0), None),
            (integer(-1), None),
            (integer(4_294_967_295), Some(u32::MAX)),
            (integer(4_294_967_296), None),
            (text("1"), None),
        ] {
            let mut candidate = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
            candidate.fields.insert("nonce".to_owned(), value);
            let intent =
                SpotSwapIntentV2::new(candidate).expect("nonce is unchecked at construction");
            assert_eq!(intent.nonce(), expected);
        }
    }

    #[test]
    fn field_profile_follows_python_count_then_sorted_key_classification() {
        let intent = SpotSwapIntentV2::new(parts(SpotSwapKindV2::SWAP_EXACT_OUT)).expect("intent");
        assert_eq!(
            intent.field_profile().expect("profile"),
            SwapIntentFieldProfileV2::Supported
        );
        assert_eq!(intent.recipient(), "alice");

        let mut foreign = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
        foreign
            .fields
            .insert("quote_receipt_hash".to_owned(), text("foreign"));
        foreign.fields.insert("recipient".to_owned(), text("bob"));
        let foreign = SpotSwapIntentV2::new(foreign).expect("eight flat fields construct");
        assert_eq!(
            foreign.field_profile().expect("profile"),
            SwapIntentFieldProfileV2::Unsupported
        );
        assert_eq!(foreign.recipient(), "bob");

        let mut nested_foreign = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
        nested_foreign
            .fields
            .insert("route".to_owned(), SwapIntentFieldValueV2::Nested);
        let nested_foreign =
            SpotSwapIntentV2::new(nested_foreign).expect("nested foreign constructs");
        assert_eq!(
            nested_foreign.field_profile().expect("profile"),
            SwapIntentFieldProfileV2::Unsupported
        );
        assert!(nested_foreign.command_body_hash().is_err());

        let mut nested_supported = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
        nested_supported
            .fields
            .insert("recipient".to_owned(), SwapIntentFieldValueV2::Nested);
        assert!(SpotSwapIntentV2::new(nested_supported).is_err());

        let mut nested_nonce = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
        nested_nonce
            .fields
            .insert("nonce".to_owned(), SwapIntentFieldValueV2::Nested);
        let nested_nonce =
            SpotSwapIntentV2::new(nested_nonce).expect("nonce is unchecked at construction");
        assert!(nested_nonce.field_profile().is_err());

        // Seven fields including the empty key: the legacy ordering check
        // raises on "" before the foreign-key classification can run.
        let mut empty_key = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
        empty_key.fields.insert(String::new(), integer(1));
        let empty_key = SpotSwapIntentV2::new(empty_key).expect("empty key constructs");
        assert!(empty_key.field_profile().is_err());
        let mut empty_key_over = parts(SpotSwapKindV2::SWAP_EXACT_OUT);
        empty_key_over.fields.insert(String::new(), integer(1));
        empty_key_over.fields.insert("z".to_owned(), integer(1));
        let empty_key_over = SpotSwapIntentV2::new(empty_key_over).expect("eight fields construct");
        assert_eq!(
            empty_key_over
                .field_profile()
                .expect("count check precedes the loop"),
            SwapIntentFieldProfileV2::Unsupported
        );
    }

    #[test]
    fn amount_bounds_beyond_u128_follow_python_comparisons() {
        let mut candidate = parts(SpotSwapKindV2::SWAP_EXACT_IN);
        candidate.fields.insert(
            "min_amount_out".to_owned(),
            SwapIntentFieldValueV2::Integer(
                SwapIntentIntegerV2::parse_canonical_text(
                    "340282366920938463463374607431768211456",
                )
                .expect("2^128"),
            ),
        );
        let intent = SpotSwapIntentV2::new(candidate).expect("intent");
        assert_eq!(intent.min_amount_out(), SwapAmountBoundV2::BeyondU128);
        assert_eq!(intent.amount_in(), Some(10));
        let plain = SpotSwapIntentV2::new(parts(SpotSwapKindV2::SWAP_EXACT_OUT)).expect("intent");
        assert_eq!(plain.max_amount_in(), SwapAmountBoundV2::Atoms(10));
        assert_eq!(plain.amount_out(), Some(7));
    }
}
