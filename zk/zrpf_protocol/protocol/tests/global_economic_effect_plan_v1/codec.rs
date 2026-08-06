use super::support::*;

fn dummy_plan(
    body: GlobalEconomicEffectBodyV1,
    local_domain: DomainIdV3,
) -> Result<GlobalEconomicEffectPlanV1, GlobalEconomicEffectPlanErrorV1> {
    GlobalEconomicEffectPlanV1::new(plan_input(
        body,
        application_id(1),
        local_domain,
        EconomicProfileIdV1::new(root(3).into_bytes()).unwrap(),
        9,
        EconomicCommandOccurrenceIdV1::new(root(4).into_bytes()).unwrap(),
        RouteReleaseIdV1::new(root(5).into_bytes()).unwrap(),
        state_root(201),
    ))
}

#[test]
fn constructor_canonicalizes_rows_and_codec_round_trips_exactly() {
    // Arrange
    let first_asset = root(10);
    let second_asset = root(11);
    let first_row = transfer_row(first_asset, 3);
    let second_row = transfer_row(second_asset, 4);
    let first_reconciliation = reconciliation(first_asset, 3, 3, 3, 3, 0, 0, 0, 0);
    let second_reconciliation = reconciliation(second_asset, 4, 4, 4, 4, 0, 0, 0, 0);
    let body_a = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(202),
        effects: vec![first_row.clone(), second_row.clone()],
        reconciliations: vec![first_reconciliation, second_reconciliation],
    })
    .unwrap();
    let body_b = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(202),
        effects: vec![second_row, first_row],
        reconciliations: vec![second_reconciliation, first_reconciliation],
    })
    .unwrap();
    let plan_a = dummy_plan(body_a, domain_id(2)).unwrap();
    let plan_b = dummy_plan(body_b, domain_id(2)).unwrap();

    // Act
    let encoded = encode_global_economic_effect_plan_v1(&plan_a).unwrap();
    let decoded = decode_exact_global_economic_effect_plan_v1(&encoded).unwrap();

    // Assert
    assert_eq!(plan_a, plan_b);
    assert_eq!(decoded, plan_a);
    assert_eq!(
        decoded.canonical_commitment().unwrap(),
        plan_b.canonical_commitment().unwrap()
    );
}

#[test]
fn exact_codec_rejects_empty_trailing_and_mutated_version_bytes() {
    // Arrange
    let plan = dummy_plan(transfer_body(1, vec![]), domain_id(2)).unwrap();
    let encoded = encode_global_economic_effect_plan_v1(&plan).unwrap();
    let mut trailing = encoded.clone();
    trailing.push(0);
    let mut version = encoded;
    version[0] = 2;

    // Act / Assert
    assert_eq!(
        decode_exact_global_economic_effect_plan_v1(&[]),
        Err(GlobalEconomicEffectPlanErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_global_economic_effect_plan_v1(&trailing),
        Err(GlobalEconomicEffectPlanErrorV1::TrailingBytes)
    );
    assert!(decode_exact_global_economic_effect_plan_v1(&version).is_err());
}

#[test]
fn external_outbox_requires_one_exact_value_effect_and_external_destination() {
    // Arrange
    let asset = root(10);
    let transfer = transfer_row(asset, 5);
    let value_effect_id = transfer.canonical_id().unwrap();
    let outbox = |outbox_seed, destination, value_id| {
        GlobalEconomicEffectRowV1::external_outbox_enqueue(GlobalExternalOutboxInputV1 {
            outbox_id: root(outbox_seed),
            destination_domain_id: destination,
            asset_id: asset,
            amount_atoms: 5,
            value_effect_id: value_id,
            payload_commitment: root(outbox_seed + 1),
        })
        .unwrap()
    };
    let make_body = |rows| {
        GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
            post_state_root: state_root(202),
            effects: rows,
            reconciliations: vec![reconciliation(asset, 5, 5, 5, 5, 0, 0, 0, 0)],
        })
    };

    // Act
    let exact_body = make_body(vec![
        transfer.clone(),
        outbox(30, domain_id(3), value_effect_id),
    ])
    .unwrap();
    let external = dummy_plan(exact_body.clone(), domain_id(2));
    let internal = dummy_plan(
        make_body(vec![
            transfer.clone(),
            outbox(32, domain_id(2), value_effect_id),
        ])
        .unwrap(),
        domain_id(2),
    );
    let missing = make_body(vec![transfer.clone(), outbox(34, domain_id(3), root(99))]);
    let duplicate = make_body(vec![
        transfer,
        outbox(36, domain_id(3), value_effect_id),
        outbox(38, domain_id(4), value_effect_id),
    ]);

    // Assert
    assert!(external.is_ok());
    assert_eq!(
        rejection(internal),
        GlobalEconomicEffectPlanErrorV1::InternalOutboxDestination
    );
    assert_eq!(
        rejection(missing),
        GlobalEconomicEffectPlanErrorV1::OutboxValueEffectMismatch
    );
    assert_eq!(
        rejection(duplicate),
        GlobalEconomicEffectPlanErrorV1::DuplicateOutboxValueEffect
    );
}

#[test]
fn plan_rejects_a_nonchanging_global_root_even_with_nonempty_rows() {
    // Arrange
    let body = GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(201),
        effects: vec![transfer_row(root(10), 1)],
        reconciliations: vec![reconciliation(root(10), 1, 1, 1, 1, 0, 0, 0, 0)],
    })
    .unwrap();

    // Act
    let result = dummy_plan(body, domain_id(2));

    // Assert
    assert_eq!(
        rejection(result),
        GlobalEconomicEffectPlanErrorV1::PreAndPostStateMatch
    );
}
