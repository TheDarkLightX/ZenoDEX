use core::fmt;
use std::collections::BTreeMap;

use risc0_zkvm::{
    sha::Digestible, InnerReceipt, Receipt, SuccinctReceiptVerifierParameters, VerifierContext,
};
use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v3, encode_node_journal_v3, CommitmentV3, NodeJournalV3, ProgramIdV3,
    ProjectedChildDescriptorV3,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
};

pub const ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1: &str = "risc0_succinct_poseidon2_3_0_5_v1";

const RECEIPT_KIND_SUCCINCT_V1: &str = "succinct";
const RECEIPT_VERIFIER_PARAMETERS_V1: &str =
    "ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013";
const RECEIPT_HASHFN_POSEIDON2_V1: &str = "poseidon2";
const RECEIPT_CONTROL_ID_V1: &str =
    "53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExpectedReceiptProfileV3 {
    profile_id: &'static str,
    receipt_kind: &'static str,
    verifier_parameters: &'static str,
    hashfn: &'static str,
    control_id: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedReceiptProfileV3 {
    profile_id: &'static str,
    receipt_kind: &'static str,
    verifier_parameters: String,
    hashfn: String,
    control_id: String,
}

impl VerifiedReceiptProfileV3 {
    pub const fn profile_id(&self) -> &'static str {
        self.profile_id
    }

    pub const fn receipt_kind(&self) -> &'static str {
        self.receipt_kind
    }

    pub fn verifier_parameters(&self) -> &str {
        &self.verifier_parameters
    }

    pub fn hashfn(&self) -> &str {
        &self.hashfn
    }

    pub fn control_id(&self) -> &str {
        &self.control_id
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedNodeReceiptErrorV3 {
    NonSuccinctReceipt,
    InvalidCompiledReceiptProfile(&'static str),
    ReceiptProfileMismatch(&'static str),
    ReceiptMetadataMismatch,
    ReceiptVerificationFailed,
    ExpectedJournalEncodingFailed,
    JournalBytesMismatch,
    JournalDecodeFailed,
    ProgramIdMismatch,
    ClaimBindingFailed,
    ChildProjectionFailed,
}

impl VerifiedNodeReceiptErrorV3 {
    /// Stable machine-readable reject code for evidence transcripts and
    /// admission adapters. Human-readable error text remains diagnostic.
    pub const fn code(self) -> &'static str {
        match self {
            Self::NonSuccinctReceipt => "non_succinct_receipt",
            Self::InvalidCompiledReceiptProfile(_) => "invalid_compiled_receipt_profile",
            Self::ReceiptProfileMismatch(_) => "receipt_profile_mismatch",
            Self::ReceiptMetadataMismatch => "receipt_metadata_mismatch",
            Self::ReceiptVerificationFailed => "receipt_verification_failed",
            Self::ExpectedJournalEncodingFailed => "expected_journal_encoding_failed",
            Self::JournalBytesMismatch => "journal_bytes_mismatch",
            Self::JournalDecodeFailed => "journal_decode_failed",
            Self::ProgramIdMismatch => "program_id_mismatch",
            Self::ClaimBindingFailed => "claim_binding_failed",
            Self::ChildProjectionFailed => "child_projection_failed",
        }
    }
}

impl fmt::Display for VerifiedNodeReceiptErrorV3 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::NonSuccinctReceipt => "node receipt is not Succinct",
            Self::InvalidCompiledReceiptProfile(field) => {
                return write!(
                    formatter,
                    "compiled node receipt profile {field} is invalid"
                );
            }
            Self::ReceiptProfileMismatch(field) => {
                return write!(formatter, "node receipt profile {field} mismatch");
            }
            Self::ReceiptMetadataMismatch => "node receipt metadata verifier parameters mismatch",
            Self::ReceiptVerificationFailed => "node receipt verification failed",
            Self::ExpectedJournalEncodingFailed => "expected node journal encoding failed",
            Self::JournalBytesMismatch => "node journal differs from the expected journal",
            Self::JournalDecodeFailed => "verified node journal strict decoding failed",
            Self::ProgramIdMismatch => {
                "node journal program ID differs from the image used to verify the receipt"
            }
            Self::ClaimBindingFailed => "verified RISC0 claim binding derivation failed",
            Self::ChildProjectionFailed => "verified child descriptor projection failed",
        })
    }
}

/// A receipt and V3 journal that have crossed the complete host verification
/// boundary. Fields are private so callers cannot construct this type from an
/// unverified receipt or from journal bytes alone.
pub struct VerifiedNodeReceiptV3 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    journal: NodeJournalV3,
    claim_binding: CommitmentV3,
    child_descriptor: ProjectedChildDescriptorV3,
}

impl VerifiedNodeReceiptV3 {
    pub fn verify_canonical_succinct(
        receipt: Receipt,
        expected_image_id: [u32; 8],
    ) -> Result<Self, VerifiedNodeReceiptErrorV3> {
        let receipt_profile = verify_pinned_succinct_profile(&receipt)?;
        let verifier_context = explicit_succinct_verifier_context()?;
        receipt
            .verify_with_context(&verifier_context, expected_image_id)
            .map_err(|_| VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed)?;
        let journal = decode_exact_node_journal_v3(&receipt.journal.bytes)
            .map_err(|_| VerifiedNodeReceiptErrorV3::JournalDecodeFailed)?;
        let verified_program_id = ProgramIdV3::new(risc0_image_words_to_bytes(expected_image_id))
            .map_err(|_| VerifiedNodeReceiptErrorV3::ProgramIdMismatch)?;
        if journal.actual_program_id() != verified_program_id {
            return Err(VerifiedNodeReceiptErrorV3::ProgramIdMismatch);
        }
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedNodeReceiptErrorV3::ClaimBindingFailed)?;
        let child_descriptor = ProjectedChildDescriptorV3::project_canonical_journal(
            claim_binding,
            &receipt.journal.bytes,
        )
        .map_err(|_| VerifiedNodeReceiptErrorV3::ChildProjectionFailed)?;
        Ok(Self {
            receipt,
            receipt_profile,
            journal,
            claim_binding,
            child_descriptor,
        })
    }

    pub fn verify_exact_succinct(
        receipt: Receipt,
        expected_image_id: [u32; 8],
        expected_journal: &NodeJournalV3,
    ) -> Result<Self, VerifiedNodeReceiptErrorV3> {
        let verified = Self::verify_canonical_succinct(receipt, expected_image_id)?;
        let expected_bytes = encode_node_journal_v3(expected_journal)
            .map_err(|_| VerifiedNodeReceiptErrorV3::ExpectedJournalEncodingFailed)?;
        if verified.receipt.journal.bytes != expected_bytes {
            return Err(VerifiedNodeReceiptErrorV3::JournalBytesMismatch);
        }
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn journal(&self) -> &NodeJournalV3 {
        &self.journal
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub const fn child_descriptor(&self) -> &ProjectedChildDescriptorV3 {
        &self.child_descriptor
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

const fn expected_receipt_profile() -> ExpectedReceiptProfileV3 {
    ExpectedReceiptProfileV3 {
        profile_id: ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
        receipt_kind: RECEIPT_KIND_SUCCINCT_V1,
        verifier_parameters: RECEIPT_VERIFIER_PARAMETERS_V1,
        hashfn: RECEIPT_HASHFN_POSEIDON2_V1,
        control_id: RECEIPT_CONTROL_ID_V1,
    }
}

fn verify_pinned_succinct_profile(
    receipt: &Receipt,
) -> Result<VerifiedReceiptProfileV3, VerifiedNodeReceiptErrorV3> {
    let expected = expected_receipt_profile();
    validate_compiled_receipt_profile(expected)?;
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err(VerifiedNodeReceiptErrorV3::NonSuccinctReceipt);
    };
    if receipt.metadata.verifier_parameters != inner.verifier_parameters {
        return Err(VerifiedNodeReceiptErrorV3::ReceiptMetadataMismatch);
    }
    let actual = VerifiedReceiptProfileV3 {
        profile_id: expected.profile_id,
        receipt_kind: RECEIPT_KIND_SUCCINCT_V1,
        verifier_parameters: inner.verifier_parameters.to_string(),
        hashfn: inner.hashfn.clone(),
        control_id: inner.control_id.to_string(),
    };
    require_receipt_profile_match(&actual, expected)?;
    Ok(actual)
}

fn validate_compiled_receipt_profile(
    profile: ExpectedReceiptProfileV3,
) -> Result<(), VerifiedNodeReceiptErrorV3> {
    if profile.profile_id.is_empty() {
        return Err(VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile(
            "profile ID",
        ));
    }
    if profile.receipt_kind != RECEIPT_KIND_SUCCINCT_V1 {
        return Err(VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile(
            "receipt kind",
        ));
    }
    if profile.hashfn != RECEIPT_HASHFN_POSEIDON2_V1 {
        return Err(VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile(
            "hash function",
        ));
    }
    if profile.verifier_parameters
        != SuccinctReceiptVerifierParameters::default()
            .digest()
            .to_string()
    {
        return Err(VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile(
            "verifier parameters",
        ));
    }
    for (value, field) in [
        (profile.verifier_parameters, "verifier parameters"),
        (profile.control_id, "control ID"),
    ] {
        if !is_lower_hex32(value) {
            return Err(VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile(
                field,
            ));
        }
    }
    Ok(())
}

fn require_receipt_profile_match(
    actual: &VerifiedReceiptProfileV3,
    expected: ExpectedReceiptProfileV3,
) -> Result<(), VerifiedNodeReceiptErrorV3> {
    for (matches, field) in [
        (actual.profile_id == expected.profile_id, "profile ID"),
        (actual.receipt_kind == expected.receipt_kind, "receipt kind"),
        (
            actual.verifier_parameters == expected.verifier_parameters,
            "verifier parameters",
        ),
        (actual.hashfn == expected.hashfn, "hash function"),
        (actual.control_id == expected.control_id, "control ID"),
    ] {
        if !matches {
            return Err(VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch(field));
        }
    }
    Ok(())
}

fn explicit_succinct_verifier_context() -> Result<VerifierContext, VerifiedNodeReceiptErrorV3> {
    let mut default_suites = VerifierContext::default_hash_suites();
    let poseidon2 = default_suites.remove(RECEIPT_HASHFN_POSEIDON2_V1).ok_or(
        VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile("compiled hash suite"),
    )?;
    Ok(VerifierContext::empty()
        .with_suites(BTreeMap::from([(
            RECEIPT_HASHFN_POSEIDON2_V1.to_owned(),
            poseidon2,
        )]))
        .with_succinct_verifier_parameters(SuccinctReceiptVerifierParameters::default()))
}

fn is_lower_hex32(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::process::Command;

    use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
    use serde_json::{json, Value};

    use super::{
        expected_receipt_profile, explicit_succinct_verifier_context, is_lower_hex32,
        require_receipt_profile_match, validate_compiled_receipt_profile,
        VerifiedNodeReceiptErrorV3, VerifiedNodeReceiptV3, VerifiedReceiptProfileV3,
        ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
    };
    use zenodex_zrpf_risc0_shared::{
        derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
    };

    const IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    const VERIFIER_WORDS: [u32; 8] = [
        3_102_336_492,
        3_939_904_686,
        3_022_461_035,
        1_208_221_540,
        3_740_575_737,
        10_233_549,
        1_979_579_783,
        329_288_969,
    ];
    const CONTROL_WORDS: [u32; 8] = [
        1_035_118_419,
        1_570_699_527,
        1_491_633_494,
        504_952_180,
        648_709_764,
        132_516_474,
        1_203_431_935,
        1_255_849_416,
    ];

    fn invalid_exact_profile_succinct_receipt() -> Receipt {
        let fake = FakeReceipt::new(ReceiptClaim::ok(IMAGE_ID, b"journal".to_vec()));
        let fake_receipt = Receipt::try_from(fake).expect("fake receipt conversion");
        let mut value = serde_json::to_value(fake_receipt).expect("fake receipt JSON");
        let inner = value
            .get_mut("inner")
            .and_then(Value::as_object_mut)
            .expect("inner object");
        let fake = inner.remove("Fake").expect("fake inner");
        let claim = fake.get("claim").expect("fake claim").clone();
        *inner = serde_json::from_value(json!({
            "Succinct": {
                "seal": [],
                "control_id": CONTROL_WORDS,
                "claim": claim,
                "hashfn": "poseidon2",
                "verifier_parameters": VERIFIER_WORDS,
                "control_inclusion_proof": {"index": 0, "digests": []}
            }
        }))
        .expect("succinct inner object");
        value["metadata"]["verifier_parameters"] = json!(VERIFIER_WORDS);
        serde_json::from_value(value).expect("invalid succinct receipt")
    }

    #[test]
    fn verifier_reject_codes_are_stable_and_unique() {
        let errors = [
            VerifiedNodeReceiptErrorV3::NonSuccinctReceipt,
            VerifiedNodeReceiptErrorV3::InvalidCompiledReceiptProfile("test"),
            VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch("test"),
            VerifiedNodeReceiptErrorV3::ReceiptMetadataMismatch,
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
            VerifiedNodeReceiptErrorV3::ExpectedJournalEncodingFailed,
            VerifiedNodeReceiptErrorV3::JournalBytesMismatch,
            VerifiedNodeReceiptErrorV3::JournalDecodeFailed,
            VerifiedNodeReceiptErrorV3::ProgramIdMismatch,
            VerifiedNodeReceiptErrorV3::ClaimBindingFailed,
            VerifiedNodeReceiptErrorV3::ChildProjectionFailed,
        ];
        let codes: BTreeSet<&str> = errors.iter().map(|error| error.code()).collect();
        assert_eq!(codes.len(), errors.len());
        assert!(codes.contains("receipt_verification_failed"));
        assert!(codes.contains("receipt_profile_mismatch"));
    }

    #[test]
    fn compiled_succinct_profile_is_exact_and_context_is_explicit() {
        let profile = expected_receipt_profile();
        validate_compiled_receipt_profile(profile).expect("compiled profile");
        explicit_succinct_verifier_context().expect("explicit verifier context");
        assert_eq!(
            profile.profile_id,
            ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1
        );
        assert_eq!(profile.receipt_kind, "succinct");
        assert_eq!(profile.hashfn, "poseidon2");
        assert!(is_lower_hex32(profile.verifier_parameters));
        assert!(is_lower_hex32(profile.control_id));
    }

    #[test]
    fn every_succinct_profile_field_is_fail_closed() {
        let expected = expected_receipt_profile();
        let baseline = VerifiedReceiptProfileV3 {
            profile_id: expected.profile_id,
            receipt_kind: expected.receipt_kind,
            verifier_parameters: expected.verifier_parameters.to_owned(),
            hashfn: expected.hashfn.to_owned(),
            control_id: expected.control_id.to_owned(),
        };
        require_receipt_profile_match(&baseline, expected).expect("exact profile");

        let cases = [
            (
                VerifiedReceiptProfileV3 {
                    profile_id: "wrong",
                    ..baseline.clone()
                },
                "profile ID",
            ),
            (
                VerifiedReceiptProfileV3 {
                    receipt_kind: "composite",
                    ..baseline.clone()
                },
                "receipt kind",
            ),
            (
                VerifiedReceiptProfileV3 {
                    verifier_parameters: "00".repeat(32),
                    ..baseline.clone()
                },
                "verifier parameters",
            ),
            (
                VerifiedReceiptProfileV3 {
                    hashfn: "sha-256".to_owned(),
                    ..baseline.clone()
                },
                "hash function",
            ),
            (
                VerifiedReceiptProfileV3 {
                    control_id: "00".repeat(32),
                    ..baseline
                },
                "control ID",
            ),
        ];
        for (actual, field) in cases {
            assert_eq!(
                require_receipt_profile_match(&actual, expected),
                Err(VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch(field))
            );
        }
    }

    #[test]
    fn typed_receipt_profile_mutations_reject_before_invalid_seal() {
        let baseline = invalid_exact_profile_succinct_receipt();
        assert_eq!(
            VerifiedNodeReceiptV3::verify_canonical_succinct(baseline.clone(), IMAGE_ID)
                .err()
                .expect("invalid seal must reject"),
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed
        );

        let mut hashfn = serde_json::to_value(&baseline).expect("receipt JSON");
        hashfn["inner"]["Succinct"]["hashfn"] = json!("sha-256");
        assert_eq!(
            VerifiedNodeReceiptV3::verify_canonical_succinct(
                serde_json::from_value(hashfn).expect("hashfn mutation"),
                IMAGE_ID,
            )
            .err()
            .expect("hashfn mutation must reject"),
            VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch("hash function")
        );

        let mut control = serde_json::to_value(&baseline).expect("receipt JSON");
        control["inner"]["Succinct"]["control_id"][0] = json!(CONTROL_WORDS[0] ^ 1);
        assert_eq!(
            VerifiedNodeReceiptV3::verify_canonical_succinct(
                serde_json::from_value(control).expect("control mutation"),
                IMAGE_ID,
            )
            .err()
            .expect("control mutation must reject"),
            VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch("control ID")
        );

        let mut parameters = serde_json::to_value(&baseline).expect("receipt JSON");
        let changed_parameters = {
            let mut words = VERIFIER_WORDS;
            words[0] ^= 1;
            words
        };
        parameters["inner"]["Succinct"]["verifier_parameters"] = json!(changed_parameters);
        parameters["metadata"]["verifier_parameters"] = json!(changed_parameters);
        assert_eq!(
            VerifiedNodeReceiptV3::verify_canonical_succinct(
                serde_json::from_value(parameters).expect("parameters mutation"),
                IMAGE_ID,
            )
            .err()
            .expect("parameters mutation must reject"),
            VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch("verifier parameters")
        );

        let mut metadata = serde_json::to_value(baseline).expect("receipt JSON");
        metadata["metadata"]["verifier_parameters"][0] = json!(VERIFIER_WORDS[0] ^ 1);
        assert_eq!(
            VerifiedNodeReceiptV3::verify_canonical_succinct(
                serde_json::from_value(metadata).expect("metadata mutation"),
                IMAGE_ID,
            )
            .err()
            .expect("metadata mutation must reject"),
            VerifiedNodeReceiptErrorV3::ReceiptMetadataMismatch
        );
    }

    #[test]
    fn explicit_context_does_not_read_risc0_dev_mode_environment() {
        let output = Command::new(std::env::current_exe().expect("current test executable"))
            .env("RISC0_DEV_MODE", "1")
            .args([
                "--ignored",
                "--exact",
                "tests::risc0_dev_mode_environment_child",
            ])
            .output()
            .expect("run environment-isolation child");
        assert!(
            output.status.success(),
            "child stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    #[ignore = "subprocess-only environment isolation check"]
    fn risc0_dev_mode_environment_child() {
        assert_eq!(
            VerifiedNodeReceiptV3::verify_canonical_succinct(
                invalid_exact_profile_succinct_receipt(),
                IMAGE_ID,
            )
            .err()
            .expect("invalid seal must reject"),
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed
        );
    }

    #[test]
    fn image_words_use_risc0_digest_byte_order() {
        assert_eq!(
            risc0_image_words_to_bytes([
                0x0302_0100,
                0x0706_0504,
                0x0b0a_0908,
                0x0f0e_0d0c,
                0x1312_1110,
                0x1716_1514,
                0x1b1a_1918,
                0x1f1e_1d1c,
            ]),
            core::array::from_fn(|index| index as u8),
        );
    }

    #[test]
    fn verified_claim_binding_binds_program_and_exact_journal() {
        let image = [1u32; 8];
        let baseline = derive_risc0_verified_claim_binding_v1(image, b"journal").expect("binding");
        assert_ne!(
            baseline,
            derive_risc0_verified_claim_binding_v1([2u32; 8], b"journal").expect("binding")
        );
        assert_ne!(
            baseline,
            derive_risc0_verified_claim_binding_v1(image, b"journal\0").expect("binding")
        );
    }
}
