use zenodex_global_settlement_abi_v1::{
    PerpsMarginCommandV1, PerpsMarginContextV1, PerpsMarginLaneModuleInputV1,
    PerpsMarginMarketStatusV1, PerpsMarginStateV1, RootV1, PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1, PERPS_MARGIN_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};

pub fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "perps module host test root",
        false,
    )
    .unwrap()
}

pub fn module_input(amount_atoms: u128) -> PerpsMarginLaneModuleInputV1 {
    let zero = RootV1::parse(ZERO_ROOT_V1, "perps module host zero root", true).unwrap();
    PerpsMarginLaneModuleInputV1 {
        schema: PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: PerpsMarginContextV1 {
            chain_id: "zeno-perps-module-risc0-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: "alice".to_owned(),
            grant_root: root(5),
            oracle_authority_root: zero.clone(),
            oracle_occurrence_root: zero,
            oracle_price_e8: 0,
        },
        pre_state: PerpsMarginStateV1 {
            schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root(3),
            market_id: "BTC-ZUSD-PERP".to_owned(),
            collateral_asset: "zUSD".to_owned(),
            index_price_e8: 6_500_000_000_000,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            max_position_abs: 10,
            market_status: PerpsMarginMarketStatusV1::ACTIVE,
            accounts: vec![],
        },
        command: PerpsMarginCommandV1 {
            command_kind: PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1.to_owned(),
            account_id: "alice-margin".to_owned(),
            market_id: "BTC-ZUSD-PERP".to_owned(),
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            amount_atoms,
            nonce: 1,
        },
    }
}
