//! Cross-language CLOB matching-LAW parity (Stage 2 I6, proof-carrying orderbook).
//!
//! The shared crate's `clob::check_no_skip_law` must reproduce the verdict of the
//! LIVE Python law checker (`tools/clob_matching_law.py::verify_no_priority_skip`,
//! classified by `law_violation_code`) for every fixture case: lawful matcher
//! fills accepted, every FORGED fill list (priority skip, partial-fill skip,
//! wrong fill order, over-fill, absent maker) rejected with the same class code.
//! Also pins `clob_matching_law_rule_hash` -- the law identity the guest commits
//! into its journal -- against the Python `MATCHING_LAW_RULE_HASH`, and asserts
//! the checker accepts the canonical matcher's output for the whole match-fixture
//! corpus. Fixture: `shared/src/clob_law_cases_v1.json` (regenerate via
//! `tools/gen_clob_law_fixture.py`; kept current by
//! `tests/core/test_clob_law_fixture.py`). Does NOT touch `main.rs`.

use tau_state_proof_risc0_shared::clob::{
    apply_clob_order, check_no_skip_law, clob_matching_law_rule_hash, ClobBookV1,
    ClobFillV1, ClobMatchResultV1, ClobOrderV1,
};

fn order_from(o: &serde_json::Value) -> ClobOrderV1 {
    ClobOrderV1 {
        side_code: o["side_code"].as_u64().unwrap() as u8,
        price_q_per_base: o["price_q_per_base"].as_u64().unwrap(),
        base_qty: o["base_qty"].as_u64().unwrap(),
        sequence: o["sequence"].as_u64().unwrap(),
        order_id: o["order_id"].as_str().unwrap().to_string(),
        owner: o["owner"].as_str().unwrap().to_string(),
    }
}

fn fill_from(f: &serde_json::Value) -> ClobFillV1 {
    ClobFillV1 {
        base: f["base"].as_u64().unwrap(),
        quote: f["quote"].as_i64().unwrap() as i128,
        maker_price: f["maker_price"].as_u64().unwrap(),
        buyer: f["buyer"].as_str().unwrap().to_string(),
        seller: f["seller"].as_str().unwrap().to_string(),
        taker_order_id: f["taker_order_id"].as_str().unwrap().to_string(),
        maker_order_id: f["maker_order_id"].as_str().unwrap().to_string(),
        maker_side_code: f["maker_side_code"].as_u64().unwrap() as u8,
    }
}

fn book_from(case: &serde_json::Value) -> ClobBookV1 {
    ClobBookV1::new(
        case["base_asset"].as_str().unwrap().to_string(),
        case["quote_asset"].as_str().unwrap().to_string(),
        case["orders"]
            .as_array()
            .unwrap()
            .iter()
            .map(order_from)
            .collect(),
    )
}

fn hexstr(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// The guest's journal-committed law identity MUST equal the Python ledger's
/// MATCHING_LAW_RULE_HASH -- else the client pins a law hash the guest never
/// emits and rejects every proof (the rule-hash drift-bug class).
#[test]
fn clob_law_rule_hash_matches_python_ledger() {
    let fixture = include_str!("../../shared/src/clob_law_cases_v1.json");
    let v: serde_json::Value = serde_json::from_str(fixture).expect("valid JSON");
    assert_eq!(
        hexstr(&clob_matching_law_rule_hash()),
        v["matching_law_rule_hash"].as_str().expect("law rule hash"),
        "matching_law_rule_hash must byte-match the Python ledger"
    );
}

#[test]
fn clob_law_verdicts_match_python_class_for_class() {
    let fixture = include_str!("../../shared/src/clob_law_cases_v1.json");
    let v: serde_json::Value = serde_json::from_str(fixture).expect("valid JSON");
    let cases = v["cases"].as_array().expect("cases");
    assert!(cases.len() >= 10, "law corpus too small");
    let mut violations = 0usize;

    for case in cases {
        let name = case["name"].as_str().unwrap();
        let book = book_from(case);
        let taker = order_from(&case["taker"]);
        let fills: Vec<ClobFillV1> = case["fills"]
            .as_array()
            .unwrap()
            .iter()
            .map(fill_from)
            .collect();

        let verdict = check_no_skip_law(&book, &taker, &fills);
        match case["violation"].as_str() {
            None => assert!(verdict.is_ok(), "{name}: expected lawful, got {verdict:?}"),
            Some(code) => {
                violations += 1;
                assert_eq!(
                    verdict.expect_err(&format!("{name}: forged fills must be rejected")),
                    code,
                    "violation class for {name}"
                );
            }
        }
    }
    assert!(violations >= 5, "law corpus must keep its forged-violation teeth");
}

/// The law checker must accept the canonical matcher's own output for EVERY
/// accepted case of the matcher-parity corpus (the dual-checker control: the
/// independent law re-derivation agrees with the production matcher).
#[test]
fn clob_law_accepts_all_canonical_matcher_outputs() {
    let fixture = include_str!("../../shared/src/clob_match_cases_v1.json");
    let v: serde_json::Value = serde_json::from_str(fixture).expect("valid JSON");
    let mut accepted = 0usize;

    for case in v["cases"].as_array().expect("cases") {
        let name = case["name"].as_str().unwrap();
        if !case["result"]["accepted"].as_bool().unwrap() {
            continue;
        }
        let book = book_from(case);
        let taker = order_from(&case["taker"]);
        match apply_clob_order(&book, &taker).expect("matcher returns ok") {
            ClobMatchResultV1::Accepted { fills, .. } => {
                accepted += 1;
                assert!(
                    check_no_skip_law(&book, &taker, &fills).is_ok(),
                    "law rejected canonical matcher output for {name}"
                );
            }
            ClobMatchResultV1::Rejected { reason } => {
                panic!("{name}: fixture says accept, matcher rejected with {reason}")
            }
        }
    }
    assert!(accepted >= 7, "matcher corpus accepted-case coverage too small");
}
