use zenodex_global_economic_delta_v2::{
    decode_delta_plan_v2, DeltaRejectCodeV2, MAX_EVENTS_V2, MAX_INPUT_BYTES_V2, SCHEMA_V2,
};

const PYTHON_CANONICAL_VECTOR: &str =
    include_str!("../../../tests/data/global_economic_delta_v2_plan.json");

fn replace_once(input: &str, from: &str, to: &str) -> String {
    assert_eq!(input.matches(from).count(), 1);
    input.replacen(from, to, 1)
}

#[test]
fn python_rust_vector_has_identical_canonical_bytes_and_root() {
    // Arrange / Act
    let validated = decode_delta_plan_v2(PYTHON_CANONICAL_VECTOR.as_bytes()).unwrap();

    // Assert
    assert_eq!(validated.event_count(), 8);
    assert_eq!(validated.source_binding_count(), 3);
    assert_eq!(
        validated.delta_classes(),
        vec![
            "internal_transfer",
            "mint",
            "burn",
            "liability",
            "external_in",
            "external_out",
            "refund",
            "slash",
        ]
    );
    assert_eq!(
        validated.canonical_bytes(),
        PYTHON_CANONICAL_VECTOR.as_bytes()
    );
    assert_eq!(
        validated.root(),
        "sha256:0a7e960b474fd446a834a590ecf2abe6c208adabb704c794a702f9d41894f18a"
    );
}

#[test]
fn amount_bva_accepts_one_and_i128_max_then_rejects_neighbors() {
    // Arrange
    let one_event = format!(
        r#"{{"events":[{{"amount_atoms":{{AMOUNT}},"asset":"zdex","delta_class":"internal_transfer","destination_ledger_allocation":"account:bob","destination_owner":"bob","economic_event":"sha256:0101010101010101010101010101010101010101010101010101010101010101","source_ledger_allocation":"account:alice","source_owner":"alice"}}],"schema":"{SCHEMA_V2}","source_bindings":[]}}"#
    );
    let max = i128::MAX.to_string();
    let above = (i128::MAX as u128 + 1).to_string();

    // Act / Assert
    assert!(decode_delta_plan_v2(one_event.replace("{AMOUNT}", "1").as_bytes()).is_ok());
    let max_plan = decode_delta_plan_v2(one_event.replace("{AMOUNT}", &max).as_bytes()).unwrap();
    assert_eq!(
        max_plan.root(),
        "sha256:68a13c2c92e55244dc3cae9b4f13114dbf85977a9b18a29f32b5f3819f8d6f4f"
    );
    for amount in ["0", above.as_str()] {
        let rejected =
            decode_delta_plan_v2(one_event.replace("{AMOUNT}", amount).as_bytes()).unwrap_err();
        assert_eq!(rejected.code, DeltaRejectCodeV2::AmountOutOfRange);
    }
}

#[test]
fn unknown_field_and_trailing_document_reject_during_closed_decode() {
    // Arrange
    let unknown = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""source_ledger_allocation":"account:alice","source_owner":"alice"}"#,
        r#""source_ledger_allocation":"account:alice","source_owner":"alice","hidden_authority":"mallory"}"#,
    );
    let trailing = format!("{PYTHON_CANONICAL_VECTOR}{{}}");

    // Act / Assert
    for input in [unknown.as_bytes(), trailing.as_bytes()] {
        let rejected = decode_delta_plan_v2(input).unwrap_err();
        assert_eq!(rejected.code, DeltaRejectCodeV2::DecodeInvalid);
    }
}

#[test]
fn liability_no_change_and_wrong_direction_reject() {
    // Arrange
    let no_change = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""post_atoms":11,"pre_atoms":7"#,
        r#""post_atoms":7,"pre_atoms":7"#,
    );
    let wrong_direction = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""direction":"increase""#,
        r#""direction":"decrease""#,
    );

    // Act / Assert
    for input in [no_change, wrong_direction] {
        let rejected = decode_delta_plan_v2(input.as_bytes()).unwrap_err();
        assert_eq!(rejected.code, DeltaRejectCodeV2::LiabilityRelationInvalid);
    }
}

#[test]
fn slash_partition_mismatch_rejects() {
    // Arrange -- kills a mutant that omits exact slash partitioning.
    let input = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""residue_atoms":3"#,
        r#""residue_atoms":2"#,
    );

    // Act
    let rejected = decode_delta_plan_v2(input.as_bytes()).unwrap_err();

    // Assert
    assert_eq!(rejected.code, DeltaRejectCodeV2::SlashPartitionMismatch);
}

#[test]
fn duplicate_and_reordered_event_ids_reject() {
    // Arrange
    let duplicate = replace_once(
        PYTHON_CANONICAL_VECTOR,
        "sha256:0202020202020202020202020202020202020202020202020202020202020202",
        "sha256:0101010101010101010101010101010101010101010101010101010101010101",
    );
    let reordered = replace_once(
        PYTHON_CANONICAL_VECTOR,
        "sha256:0202020202020202020202020202020202020202020202020202020202020202",
        "sha256:0000000000000000000000000000000000000000000000000000000000000001",
    );

    // Act / Assert
    assert_eq!(
        decode_delta_plan_v2(duplicate.as_bytes()).unwrap_err().code,
        DeltaRejectCodeV2::DuplicateEvent
    );
    assert_eq!(
        decode_delta_plan_v2(reordered.as_bytes()).unwrap_err().code,
        DeltaRejectCodeV2::NoncanonicalEventOrder
    );
}

#[test]
fn event_count_and_input_bytes_are_bounded_before_candidate_use() {
    // Arrange
    let template: serde_json::Value = serde_json::from_str(PYTHON_CANONICAL_VECTOR).unwrap();
    let first = template["events"][0].clone();
    let build = |count: usize| {
        let mut events = Vec::new();
        for index in 0..count {
            let mut event = first.clone();
            event["economic_event"] =
                serde_json::Value::String(format!("sha256:{:064x}", index + 1));
            events.push(event);
        }
        serde_json::to_vec(
            &serde_json::json!({"schema": SCHEMA_V2, "events": events, "source_bindings": []}),
        )
        .unwrap()
    };

    // Act / Assert
    assert_eq!(
        decode_delta_plan_v2(&build(MAX_EVENTS_V2))
            .unwrap()
            .event_count(),
        MAX_EVENTS_V2
    );
    assert_eq!(
        decode_delta_plan_v2(&build(MAX_EVENTS_V2 + 1))
            .unwrap_err()
            .code,
        DeltaRejectCodeV2::EventCountOutOfRange
    );
    assert_eq!(
        decode_delta_plan_v2(&vec![b' '; MAX_INPUT_BYTES_V2 + 1])
            .unwrap_err()
            .code,
        DeltaRejectCodeV2::InputTooLarge
    );

    let mut exact = build(1);
    exact.resize(MAX_INPUT_BYTES_V2, b' ');
    assert!(decode_delta_plan_v2(&exact).is_ok());
}

#[test]
fn event_ancestry_and_effect_roots_cannot_self_reference() {
    // Arrange
    let cases = [
        (
            "\"source_effect\":\"sha256:1111111111111111111111111111111111111111111111111111111111111111\"",
            "\"source_effect\":\"sha256:0505050505050505050505050505050505050505050505050505050505050505\"",
        ),
        (
            "\"ancestor_claim_event\":\"sha256:2222222222222222222222222222222222222222222222222222222222222222\"",
            "\"ancestor_claim_event\":\"sha256:0606060606060606060606060606060606060606060606060606060606060606\"",
        ),
        (
            "\"source_event\":\"sha256:4444444444444444444444444444444444444444444444444444444444444444\"",
            "\"source_event\":\"sha256:0707070707070707070707070707070707070707070707070707070707070707\"",
        ),
        (
            "\"destination_effect\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\"",
            "\"destination_effect\":\"sha256:2222222222222222222222222222222222222222222222222222222222222222\"",
        ),
    ];

    // Act / Assert
    for (from, to) in cases {
        let input = replace_once(PYTHON_CANONICAL_VECTOR, from, to);
        assert_eq!(
            decode_delta_plan_v2(input.as_bytes()).unwrap_err().code,
            DeltaRejectCodeV2::SelfReferentialEvent
        );
    }
}

#[test]
fn source_references_are_exact_single_use_and_acyclic() {
    // Arrange
    let template: serde_json::Value = serde_json::from_str(PYTHON_CANONICAL_VECTOR).unwrap();
    let mut missing = template.clone();
    missing["source_bindings"] = serde_json::json!([]);

    let mut mismatch = template.clone();
    mismatch["source_bindings"][2]["amount_atoms"] = serde_json::json!(8);

    let refund = template["events"][6].clone();
    let mut repeated_refund = refund.clone();
    repeated_refund["economic_event"] = serde_json::json!(
        "sha256:0909090909090909090909090909090909090909090909090909090909090909"
    );
    let repeated = serde_json::json!({
        "events": [refund.clone(), repeated_refund],
        "schema": SCHEMA_V2,
        "source_bindings": [template["source_bindings"][2].clone()],
    });

    let mut first = refund.clone();
    first["source_event"] = serde_json::json!(
        "sha256:0808080808080808080808080808080808080808080808080808080808080808"
    );
    let mut second = refund;
    second["economic_event"] = serde_json::json!(
        "sha256:0808080808080808080808080808080808080808080808080808080808080808"
    );
    second["source_event"] = serde_json::json!(
        "sha256:0707070707070707070707070707070707070707070707070707070707070707"
    );
    let cycle = serde_json::json!({
        "events": [first, second],
        "schema": SCHEMA_V2,
        "source_bindings": [],
    });

    // Act / Assert
    let cases = [
        (missing, DeltaRejectCodeV2::SourceReferenceInvalid),
        (mismatch, DeltaRejectCodeV2::SourceReferenceInvalid),
        (cycle, DeltaRejectCodeV2::ReferenceRootConflict),
    ];
    for (value, expected) in cases {
        let bytes = serde_json::to_vec(&value).unwrap();
        assert_eq!(decode_delta_plan_v2(&bytes).unwrap_err().code, expected);
    }
    assert_eq!(
        decode_delta_plan_v2(&serde_json::to_vec(&repeated).unwrap())
            .unwrap_err()
            .code,
        DeltaRejectCodeV2::SourceReferenceReused
    );
}

#[test]
fn malformed_boolean_amount_uses_shared_decode_reject() {
    // Arrange
    let input = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""amount_atoms":1"#,
        r#""amount_atoms":true"#,
    );
    let mut deep = vec![b'['; 2_000];
    deep.push(b'0');
    deep.extend(vec![b']'; 2_000]);

    // Act / Assert
    assert_eq!(
        decode_delta_plan_v2(input.as_bytes()).unwrap_err().code,
        DeltaRejectCodeV2::DecodeInvalid
    );
    assert_eq!(
        decode_delta_plan_v2(&deep).unwrap_err().code,
        DeltaRejectCodeV2::DecodeInvalid
    );
}

#[test]
fn liability_balance_bva_rejects_above_i128_max() {
    // Arrange
    let above = (1_u128 << 127).to_string();
    let input = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""pre_atoms":7"#,
        &format!(r#""pre_atoms":{above}"#),
    );

    // Act / Assert
    assert_eq!(
        decode_delta_plan_v2(input.as_bytes()).unwrap_err().code,
        DeltaRejectCodeV2::AmountOutOfRange
    );
}

#[test]
fn identifier_root_and_source_binding_bva_are_closed() {
    // Arrange
    let template: serde_json::Value = serde_json::from_str(PYTHON_CANONICAL_VECTOR).unwrap();
    let single_event = |asset: String, event_root: String| {
        let mut plan = template.clone();
        let mut event = template["events"][0].clone();
        event["asset"] = serde_json::Value::String(asset);
        event["economic_event"] = serde_json::Value::String(event_root);
        plan["events"] = serde_json::json!([event]);
        plan["source_bindings"] = serde_json::json!([]);
        serde_json::to_vec(&plan).unwrap()
    };
    let canonical_root = format!("sha256:{}", "1".repeat(64));

    // Act / Assert
    assert!(decode_delta_plan_v2(&single_event("a".repeat(128), canonical_root.clone())).is_ok());
    for candidate in [
        single_event("a".repeat(129), canonical_root),
        single_event("zdex".to_owned(), format!("sha256:{}", "1".repeat(63))),
        single_event("zdex".to_owned(), format!("sha256:{}", "0".repeat(64))),
    ] {
        assert_eq!(
            decode_delta_plan_v2(&candidate).unwrap_err().code,
            DeltaRejectCodeV2::DecodeInvalid
        );
    }

    for amount in [serde_json::json!(0), serde_json::json!(1_u128 << 127)] {
        let mut plan = template.clone();
        plan["source_bindings"][0]["amount_atoms"] = amount;
        assert_eq!(
            decode_delta_plan_v2(&serde_json::to_vec(&plan).unwrap())
                .unwrap_err()
                .code,
            DeltaRejectCodeV2::AmountOutOfRange
        );
    }
}

#[test]
fn zero_is_allowed_only_for_balance_side_atoms() {
    // Arrange
    let mut plan: serde_json::Value = serde_json::from_str(PYTHON_CANONICAL_VECTOR).unwrap();
    plan["events"][3]["pre_atoms"] = serde_json::json!(0);
    plan["events"][3]["post_atoms"] = serde_json::json!(4);
    plan["events"][7]["beneficiary_atoms"] = serde_json::json!(0);
    plan["events"][7]["residue_atoms"] = serde_json::json!(8);

    // Act / Assert
    assert!(decode_delta_plan_v2(&serde_json::to_vec(&plan).unwrap()).is_ok());
}

#[test]
fn malformed_byte_corpus_matches_python_rejection_abi() {
    // Arrange
    let mut bom = vec![0xef, 0xbb, 0xbf];
    bom.extend_from_slice(PYTHON_CANONICAL_VECTOR.as_bytes());
    let mut utf16 = vec![0xff, 0xfe];
    for unit in PYTHON_CANONICAL_VECTOR.encode_utf16() {
        utf16.extend_from_slice(&unit.to_le_bytes());
    }
    let float_amount = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""amount_atoms":1"#,
        r#""amount_atoms":1.5"#,
    );
    let numeric_schema = replace_once(
        PYTHON_CANONICAL_VECTOR,
        r#""schema":"zenodex/global-economic-delta-plan/v2""#,
        r#""schema":7"#,
    );

    // Act / Assert
    for candidate in [
        bom,
        utf16,
        float_amount.into_bytes(),
        numeric_schema.into_bytes(),
    ] {
        assert_eq!(
            decode_delta_plan_v2(&candidate).unwrap_err().code,
            DeltaRejectCodeV2::DecodeInvalid
        );
    }
    let wrong_schema = replace_once(
        PYTHON_CANONICAL_VECTOR,
        "zenodex/global-economic-delta-plan/v2",
        "zenodex/global-economic-delta-plan/v3",
    );
    assert_eq!(
        decode_delta_plan_v2(wrong_schema.as_bytes())
            .unwrap_err()
            .code,
        DeltaRejectCodeV2::SchemaMismatch
    );
}
