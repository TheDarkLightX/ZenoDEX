use zenodex_global_settlement_abi_v1::zdex_atomic_buyback_quote_port_v2::{
    ZDEXAtomicBuybackQuotePortV2, ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
};
use zenodex_global_settlement_abi_v1::{
    zdex_pool_reserve_principal_v1, RootV1, FEE_BUYBACK_PRINCIPAL_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed test root")
}

fn port() -> ZDEXAtomicBuybackQuotePortV2 {
    ZDEXAtomicBuybackQuotePortV2 {
        schema: ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2.to_owned(),
        profile_root: root(1),
        route_release_id: root(2),
        command_occurrence_id: root(3),
        global_pre_state_root: root(4),
        producer_module_release_id: root(5),
        consumer_module_release_id: root(6),
        producer_quote_pre_state_root: root(7),
        producer_quote_post_state_root: root(8),
        producer_quote_effect_plan_root: root(9),
        selected_pool_id: root(10),
        quote_asset_id: root(11),
        amount_atoms: 12,
    }
}

#[test]
fn root_and_derived_principals_match_python() {
    let port = port();
    assert_eq!(
        port.port_root().expect("port root").to_string(),
        "0xeabb1e68ae0540628753e32982bee5dc635bf41a70293185d6f3b1b3dffd4af4"
    );
    assert_eq!(port.source_principal(), FEE_BUYBACK_PRINCIPAL_V1);
    assert_eq!(
        port.destination_principal().expect("destination"),
        zdex_pool_reserve_principal_v1(&port.selected_pool_id, &port.quote_asset_id)
            .expect("destination")
    );
}

#[test]
fn boundaries_and_malformed_values_fail_closed() {
    let mut one = port();
    one.amount_atoms = 1;
    one.validate().expect("one atom");

    let mut maximum = port();
    maximum.amount_atoms = i128::MAX.unsigned_abs();
    maximum.validate().expect("maximum signed effect");

    let mut zero = port();
    zero.amount_atoms = 0;
    assert!(zero.validate().is_err());

    let mut excess = port();
    excess.amount_atoms = i128::MAX.unsigned_abs() + 1;
    assert!(excess.validate().is_err());

    let mut zero_root = port();
    zero_root.producer_quote_effect_plan_root =
        RootV1::parse(ZERO_ROOT_V1, "zero root", true).expect("zero root");
    assert!(zero_root.validate().is_err());

    let mut same_release = port();
    same_release.consumer_module_release_id = same_release.producer_module_release_id.clone();
    assert!(same_release.validate().is_err());

    let mut same_state = port();
    same_state.producer_quote_post_state_root = same_state.producer_quote_pre_state_root.clone();
    assert!(same_state.validate().is_err());
}

#[test]
fn unknown_or_derived_fields_cannot_enter_the_wire_value() {
    let mut value = serde_json::to_value(port()).expect("port value");
    value
        .as_object_mut()
        .expect("port object")
        .insert("source_principal".to_owned(), serde_json::json!("mallory"));
    assert!(serde_json::from_value::<ZDEXAtomicBuybackQuotePortV2>(value).is_err());
}
