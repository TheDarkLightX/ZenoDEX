use std::fs;
use std::path::PathBuf;

use serde::Deserialize;
use sha2::{Digest, Sha256};
use zenodex_proof_market_key_parity_v2::{
    canonical_economic_work_key_bytes_v2, canonical_economic_work_key_v2, EconomicWorkDescriptorV2,
    WorkKeyErrorV2, CANONICAL_WORK_KEY_DOMAIN_V2,
};

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    schema: String,
    status: String,
    descriptor: DescriptorFixture,
    encoding: EncodingFixture,
    expected: ExpectedFixture,
    nonclaims: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct DescriptorFixture {
    product_kind: String,
    claim: String,
    assumptions: String,
    public_inputs: String,
    requested_output: String,
    verifier_profile: String,
    release: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct EncodingFixture {
    domain: String,
    field_order: Vec<String>,
    length_bytes: u8,
    length_endian: String,
    value_encoding: String,
    rust_parity_subset: String,
    digest: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ExpectedFixture {
    key: String,
    framed_bytes_sha256: String,
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("docs/research/PROOF_MARKET_WORK_KEY_GOLDEN_V2.json")
}

fn load_fixture() -> Fixture {
    let bytes = fs::read(fixture_path()).expect("golden vector must be readable");
    serde_json::from_slice(&bytes).expect("golden vector must be typed JSON")
}

fn descriptor(fixture: &DescriptorFixture) -> EconomicWorkDescriptorV2 {
    EconomicWorkDescriptorV2 {
        product_kind: fixture.product_kind.clone(),
        claim: fixture.claim.clone(),
        assumptions: fixture.assumptions.clone(),
        public_inputs: fixture.public_inputs.clone(),
        requested_output: fixture.requested_output.clone(),
        verifier_profile: fixture.verifier_profile.clone(),
        release: fixture.release.clone(),
    }
}

#[test]
fn rust_matches_python_golden_key_and_framed_bytes() {
    let fixture = load_fixture();
    assert_eq!(fixture.schema, "zenodex/proof-market-work-key-golden/v2");
    assert_eq!(fixture.status, "RESEARCH_ONLY_GOLDEN_VECTOR");
    assert_eq!(fixture.nonclaims.len(), 3);
    assert_eq!(
        fixture.encoding.domain.as_bytes(),
        CANONICAL_WORK_KEY_DOMAIN_V2
    );
    assert_eq!(fixture.encoding.length_bytes, 4);
    assert_eq!(fixture.encoding.length_endian, "big");
    assert_eq!(fixture.encoding.value_encoding, "UTF-8_NFC");
    assert_eq!(fixture.encoding.rust_parity_subset, "ASCII_ONLY");
    assert_eq!(fixture.encoding.digest, "SHA-256");
    assert_eq!(
        fixture.encoding.field_order,
        [
            "product_kind",
            "claim",
            "assumptions",
            "public_inputs",
            "requested_output",
            "verifier_profile",
            "release"
        ]
    );

    let work = descriptor(&fixture.descriptor);
    let bytes = canonical_economic_work_key_bytes_v2(&work).unwrap();
    assert_eq!(
        hex::encode(Sha256::digest(&bytes)),
        fixture.expected.framed_bytes_sha256
    );
    assert_eq!(
        canonical_economic_work_key_v2(&work).unwrap(),
        fixture.expected.key
    );

    let mut changed = work.clone();
    changed.requested_output.push_str("_V2");
    assert_ne!(
        canonical_economic_work_key_v2(&changed).unwrap(),
        fixture.expected.key
    );
}

#[test]
fn rust_rejects_non_ascii_work_fields() {
    let work = EconomicWorkDescriptorV2 {
        product_kind: "ZENO_PROOF".to_owned(),
        claim: "e\u{301}".to_owned(),
        assumptions: "ASSUMPTIONS".to_owned(),
        public_inputs: "INPUTS".to_owned(),
        requested_output: "OUTPUT".to_owned(),
        verifier_profile: "PROFILE".to_owned(),
        release: "RELEASE".to_owned(),
    };
    assert_eq!(
        canonical_economic_work_key_v2(&work),
        Err(WorkKeyErrorV2::NonAsciiField("claim"))
    );
}
