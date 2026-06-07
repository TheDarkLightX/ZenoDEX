//! Cross-language CLOB matcher parity (Stage 2 I2, proof-carrying orderbook).
//!
//! The shared crate's `clob::apply_clob_order` must reproduce the LIVE Python
//! `clob_matching.apply_order` for every fixture case: same accept/reject (and
//! reason), same fills (field-by-field), same post-book root, same
//! resting_taker_qty. Fixture: `shared/src/clob_match_cases_v1.json` (regenerate
//! via `tools/gen_clob_match_fixture.py`; kept current by
//! `tests/core/test_clob_match_fixture.py`). Does NOT touch `main.rs`.

use tau_state_proof_risc0_shared::clob::{
    apply_clob_order, clob_fee_rule_hash, clob_matching_rule_hash, ClobBookV1, ClobMatchResultV1,
    ClobOrderV1,
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

fn hexstr(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// The guest's rule-hash identities MUST equal the Python ledger's
/// (orderbook_api.MATCHING_RULE_HASH / FEE_RULE_HASH, emitted into the fixture) --
/// else the guest's journal carries a rulebook hash the client never accepts.
/// (Adversarial review 2026-06-07, finding #5: the Rust labels had drifted.)
#[test]
fn clob_rule_hashes_match_python_ledger() {
    let fixture = include_str!("../../shared/src/clob_match_cases_v1.json");
    let v: serde_json::Value = serde_json::from_str(fixture).expect("valid JSON");
    let rh = &v["rule_hashes"];
    assert_eq!(
        hexstr(&clob_matching_rule_hash()),
        rh["matching"].as_str().expect("matching rule hash"),
        "matching_rule_hash must byte-match the Python ledger"
    );
    assert_eq!(
        hexstr(&clob_fee_rule_hash()),
        rh["fee"].as_str().expect("fee rule hash"),
        "fee_rule_hash must byte-match the Python ledger"
    );
}

#[test]
fn clob_matcher_matches_python_byte_for_byte() {
    let fixture = include_str!("../../shared/src/clob_match_cases_v1.json");
    let v: serde_json::Value = serde_json::from_str(fixture).expect("valid JSON");
    let cases = v["cases"].as_array().expect("cases");
    assert!(cases.len() >= 9, "matcher corpus too small");

    for case in cases {
        let name = case["name"].as_str().unwrap();
        let orders: Vec<ClobOrderV1> =
            case["orders"].as_array().unwrap().iter().map(order_from).collect();
        let book = ClobBookV1::new(
            case["base_asset"].as_str().unwrap().to_string(),
            case["quote_asset"].as_str().unwrap().to_string(),
            orders,
        );
        let taker = order_from(&case["taker"]);
        let result = apply_clob_order(&book, &taker).expect("matcher returns ok");
        let expect = &case["result"];

        if expect["accepted"].as_bool().unwrap() {
            match result {
                ClobMatchResultV1::Accepted { post_book, fills, resting_taker_qty } => {
                    assert_eq!(
                        resting_taker_qty,
                        expect["resting_taker_qty"].as_u64().unwrap(),
                        "resting_taker_qty for {name}"
                    );
                    assert_eq!(
                        hexstr(&post_book.state_root().unwrap()),
                        expect["post_book_root"].as_str().unwrap(),
                        "post-book root for {name}"
                    );
                    let exp_fills = expect["fills"].as_array().unwrap();
                    assert_eq!(fills.len(), exp_fills.len(), "fill count for {name}");
                    for (f, ef) in fills.iter().zip(exp_fills) {
                        assert_eq!(f.base, ef["base"].as_u64().unwrap(), "base for {name}");
                        assert_eq!(f.quote, ef["quote"].as_i64().unwrap() as i128, "quote for {name}");
                        assert_eq!(f.maker_price, ef["maker_price"].as_u64().unwrap(), "maker_price for {name}");
                        assert_eq!(f.buyer, ef["buyer"].as_str().unwrap(), "buyer for {name}");
                        assert_eq!(f.seller, ef["seller"].as_str().unwrap(), "seller for {name}");
                        assert_eq!(f.taker_order_id, ef["taker_order_id"].as_str().unwrap(), "taker_oid for {name}");
                        assert_eq!(f.maker_order_id, ef["maker_order_id"].as_str().unwrap(), "maker_oid for {name}");
                        assert_eq!(
                            f.maker_side_code,
                            ef["maker_side_code"].as_u64().unwrap() as u8,
                            "maker_side_code for {name}"
                        );
                    }
                }
                ClobMatchResultV1::Rejected { reason } => {
                    panic!("{name}: expected accept, got reject {reason}")
                }
            }
        } else {
            match result {
                ClobMatchResultV1::Rejected { reason } => {
                    assert_eq!(reason, expect["reason"].as_str().unwrap(), "reject reason for {name}")
                }
                ClobMatchResultV1::Accepted { .. } => panic!("{name}: expected reject, got accept"),
            }
        }
    }
}
