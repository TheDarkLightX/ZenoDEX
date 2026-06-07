//! Cross-language CLOB matcher parity (Stage 2 I2, proof-carrying orderbook).
//!
//! The shared crate's `clob::apply_clob_order` must reproduce the LIVE Python
//! `clob_matching.apply_order` for every fixture case: same accept/reject (and
//! reason), same fills (field-by-field), same post-book root, same
//! resting_taker_qty. Fixture: `shared/src/clob_match_cases_v1.json` (regenerate
//! via `tools/gen_clob_match_fixture.py`; kept current by
//! `tests/core/test_clob_match_fixture.py`). Does NOT touch `main.rs`.

use tau_state_proof_risc0_shared::clob::{
    apply_clob_order, clob_event_log_root, clob_fee_rule_hash, clob_matching_rule_hash,
    execute_clob_transition_v1_unchecked_with_journal, ClobBookV1, ClobMatchResultV1, ClobOrderV1,
    ClobTransitionInputV1, ClobTransitionJournalV1, PROOF_TYPE_CLOB,
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

fn asset(byte: &str) -> String {
    "0x".to_string() + &byte.repeat(32)
}

fn owner(byte: &str) -> String {
    "0x".to_string() + &byte.repeat(48)
}

fn oid(n: u64) -> String {
    format!("0x{:064x}", n)
}

fn order(side_code: u8, price: u64, qty: u64, seq: u64, id: u64, owner_byte: &str) -> ClobOrderV1 {
    ClobOrderV1 {
        side_code,
        price_q_per_base: price,
        base_qty: qty,
        sequence: seq,
        order_id: oid(id),
        owner: owner(owner_byte),
    }
}

const IMAGE_ID: [u32; 8] = [
    0x1111_1111,
    0x2222_2222,
    0x3333_3333,
    0x4444_4444,
    0x5555_5555,
    0x6666_6666,
    0x7777_7777,
    0x8888_8888,
];

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
fn clob_transition_journal_round_trips_through_guest_postcard_channel() {
    // REVIEW(Codex 2026-06-07, grade B+ -> A-): I2b called this a
    // journal-bound transition, but the CLOB input/journal structs were not
    // serde/postcard types. This regression pins compatibility with the same
    // byte channel used by the RISC0 guest's commit_journal helper.
    let input = ClobTransitionInputV1 {
        state_hash: [7u8; 32],
        chain_id: "devnet".to_string(),
        pre_book: ClobBookV1::new(
            asset("11"),
            asset("22"),
            vec![order(1, 100_000_000, 5, 1, 1, "bb")],
        ),
        taker: order(0, 100_000_000, 5, 10, 99, "aa"),
        pre_app_hash_present: false,
        pre_app_hash: [0u8; 32],
        expected_post_app_hash: [0u8; 32],
        risc0_image_id: IMAGE_ID,
    };
    let (journal, _) = execute_clob_transition_v1_unchecked_with_journal(input).unwrap();

    let bytes = postcard::to_allocvec(&journal).expect("journal serializes");
    let decoded: ClobTransitionJournalV1 =
        postcard::from_bytes(&bytes).expect("journal deserializes");

    assert_eq!(decoded.journal_version, journal.journal_version);
    assert_eq!(decoded.proof_type, PROOF_TYPE_CLOB);
    assert_eq!(decoded.state_hash, [7u8; 32]);
    assert_eq!(decoded.chain_id, "devnet");
    assert_eq!(decoded.pre_app_hash_present, journal.pre_app_hash_present);
    assert_eq!(decoded.pre_app_hash, journal.pre_app_hash);
    assert_eq!(decoded.pre_book_root, journal.pre_book_root);
    assert_eq!(decoded.post_book_root, journal.post_book_root);
    assert_eq!(decoded.post_app_hash, journal.post_book_root);
    assert_eq!(decoded.operation_hash, journal.event_log_root);
    assert_eq!(decoded.state_delta_hash, journal.state_delta_hash);
    assert_eq!(decoded.event_log_root, journal.event_log_root);
    assert_eq!(decoded.matching_rule_hash, journal.matching_rule_hash);
    assert_eq!(decoded.fee_rule_hash, journal.fee_rule_hash);
    assert_eq!(decoded.risc0_image_id, IMAGE_ID);
    assert_eq!(decoded.fee_total, 0);
    assert_eq!(decoded.fills, journal.fills);
    assert_eq!(decoded.resting_taker_qty, journal.resting_taker_qty);
}

#[test]
fn clob_matcher_matches_python_byte_for_byte() {
    let fixture = include_str!("../../shared/src/clob_match_cases_v1.json");
    let v: serde_json::Value = serde_json::from_str(fixture).expect("valid JSON");
    let cases = v["cases"].as_array().expect("cases");
    assert!(cases.len() >= 9, "matcher corpus too small");

    for case in cases {
        let name = case["name"].as_str().unwrap();
        let orders: Vec<ClobOrderV1> = case["orders"]
            .as_array()
            .unwrap()
            .iter()
            .map(order_from)
            .collect();
        let book = ClobBookV1::new(
            case["base_asset"].as_str().unwrap().to_string(),
            case["quote_asset"].as_str().unwrap().to_string(),
            orders,
        );
        let taker = order_from(&case["taker"]);

        // event-log root (a NEW guest-defined encoding) must match the Python
        // mirror (src/core/clob_journal.clob_event_log_root) -- same drift-bug
        // class as the rule hashes.
        assert_eq!(
            hexstr(&clob_event_log_root(&[&taker]).unwrap()),
            case["event_log_root"].as_str().unwrap(),
            "event_log_root for {name}"
        );

        let result = apply_clob_order(&book, &taker).expect("matcher returns ok");
        let expect = &case["result"];

        if expect["accepted"].as_bool().unwrap() {
            match result {
                ClobMatchResultV1::Accepted {
                    post_book,
                    fills,
                    resting_taker_qty,
                } => {
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
                        assert_eq!(
                            f.quote,
                            ef["quote"].as_i64().unwrap() as i128,
                            "quote for {name}"
                        );
                        assert_eq!(
                            f.maker_price,
                            ef["maker_price"].as_u64().unwrap(),
                            "maker_price for {name}"
                        );
                        assert_eq!(f.buyer, ef["buyer"].as_str().unwrap(), "buyer for {name}");
                        assert_eq!(
                            f.seller,
                            ef["seller"].as_str().unwrap(),
                            "seller for {name}"
                        );
                        assert_eq!(
                            f.taker_order_id,
                            ef["taker_order_id"].as_str().unwrap(),
                            "taker_oid for {name}"
                        );
                        assert_eq!(
                            f.maker_order_id,
                            ef["maker_order_id"].as_str().unwrap(),
                            "maker_oid for {name}"
                        );
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
                    assert_eq!(
                        reason,
                        expect["reason"].as_str().unwrap(),
                        "reject reason for {name}"
                    )
                }
                ClobMatchResultV1::Accepted { .. } => panic!("{name}: expected reject, got accept"),
            }
        }
    }
}
