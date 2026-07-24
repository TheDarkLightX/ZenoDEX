use super::cli::{parse_options, Mode};
use super::source::require_exact_json_encoding;

use serde::Serialize;

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

#[derive(Serialize)]
struct CanonicalFixture {
    first: u8,
    second: u8,
}

#[test]
fn source_wrapper_canonicality_rejects_reordering_and_trailing_newline() {
    let fixture = CanonicalFixture {
        first: 1,
        second: 2,
    };
    assert!(require_exact_json_encoding(&fixture, br#"{"first":1,"second":2}"#, "fixture").is_ok());
    assert!(
        require_exact_json_encoding(&fixture, br#"{"second":2,"first":1}"#, "fixture").is_err()
    );
    assert!(
        require_exact_json_encoding(&fixture, b"{\"first\":1,\"second\":2}\n", "fixture").is_err()
    );
}

#[test]
fn cli_accepts_exact_positive_and_verify_forms() {
    let positive = parse_options(strings(&[
        "--source-proof",
        "source.json",
        "--receipt-out",
        "adapter.json",
        "--ordinal",
        "7",
    ]))
    .expect("exact positive CLI");
    assert_eq!(positive.mode, Mode::Prove);
    assert_eq!(positive.assigned_leaf_ordinal, 7);

    let verify = parse_options(strings(&[
        "--source-proof",
        "source.json",
        "--verify-receipt",
        "adapter.json",
    ]))
    .expect("exact verify CLI");
    assert_eq!(verify.mode, Mode::VerifyReceipt);
    assert_eq!(verify.assigned_leaf_ordinal, 0);
}

#[test]
fn cli_accepts_bounded_assumption_negative_controls() {
    let missing = parse_options(strings(&[
        "--source-proof",
        "source.json",
        "--missing-assumption",
    ]))
    .expect("missing-assumption CLI");
    assert_eq!(missing.mode, Mode::MissingAssumption);

    let substituted = parse_options(strings(&[
        "--source-proof",
        "source.json",
        "--substituted-source-journal",
        "--ordinal",
        "1",
    ]))
    .expect("substituted-journal CLI");
    assert_eq!(substituted.mode, Mode::SubstitutedSourceJournal);
}

#[test]
fn cli_rejects_ambiguous_paths_noncanonical_ordinals_and_extra_arguments() {
    assert!(parse_options(strings(&[
        "--source-proof",
        "same.json",
        "--receipt-out",
        "same.json",
    ]))
    .is_err());
    assert!(parse_options(strings(&[
        "--source-proof",
        "source.json",
        "--receipt-out",
        "adapter.json",
        "--ordinal",
        "07",
    ]))
    .is_err());
    assert!(parse_options(strings(&[
        "--source-proof",
        "source.json",
        "--missing-assumption",
        "--receipt-out",
        "adapter.json",
    ]))
    .is_err());
    assert!(parse_options(strings(&[
        "--receipt-out",
        "adapter.json",
        "--source-proof",
        "source.json",
    ]))
    .is_err());
}
