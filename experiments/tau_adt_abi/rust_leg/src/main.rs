//! Rust leg of the Tau ADT ABI parity oracle: replays the frozen vector set
//! through the real Rust transition and reports per-vector agreement with the
//! Python-oracle expectation. Research-only.

use std::io::Read;

use zenodex_global_settlement_abi_v1::{
    transition_asset_transfer_v1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferPolicyV1, AssetTransferResultV1, AssetTransferStateV1, EconomicAmountV1, RootV1,
    ACCOUNT_CUSTODY_DOMAIN_V1, ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

#[derive(serde::Deserialize)]
struct VectorV1 {
    vector_id: String,
    s_bal: u128,
    r_bal: u128,
    t_bal: u128,
    fee_flat: u128,
    enabled: bool,
    amount: u128,
    max_fee: u128,
    recipient: String,
    expected: String,
}

#[derive(serde::Deserialize)]
struct FileV1 {
    vectors: Vec<VectorV1>,
}

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "abi leg root", false).expect("root parses")
}

fn amount(owner: &str, atoms: u128) -> EconomicAmountV1 {
    EconomicAmountV1 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
        amount_atoms: atoms,
    }
}

fn main() {
    let mut raw = String::new();
    std::io::stdin().read_to_string(&mut raw).expect("stdin");
    let file: FileV1 = serde_json::from_str(&raw).expect("vector json");
    let mut ok = true;
    let mut rows = Vec::new();
    for vector in &file.vectors {
        let mut balances: Vec<EconomicAmountV1> = [
            ("recv", vector.r_bal),
            ("sender", vector.s_bal),
            ("treasury", vector.t_bal),
        ]
        .iter()
        .filter(|(_, atoms)| *atoms > 0)
        .map(|(owner, atoms)| amount(owner, *atoms))
        .collect();
        balances.sort_by(|a, b| (&a.asset, &a.owner).cmp(&(&b.asset, &b.owner)));
        let state = AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root(3),
            policies: vec![AssetTransferPolicyV1 {
                asset: "USD".to_owned(),
                fee_owner: "treasury".to_owned(),
                transfer_fee_atoms: vector.fee_flat,
                enabled: vector.enabled,
            }],
            balances,
            supplies: vec![AssetSupplyV1 {
                asset: "USD".to_owned(),
                amount_atoms: vector.s_bal + vector.r_bal + vector.t_bal,
            }],
        };
        let context = AssetTransferContextV1 {
            chain_id: "zenodex".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 1,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: "sender".to_owned(),
            grant_root: root(5),
        };
        let command = AssetTransferCommandV1 {
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            asset: "USD".to_owned(),
            sender: "sender".to_owned(),
            recipient: vector.recipient.clone(),
            amount_atoms: vector.amount,
            max_fee_atoms: vector.max_fee,
        };
        let outcome = match transition_asset_transfer_v1(&context, &state, &command) {
            Ok(AssetTransferResultV1::Accepted(_)) => "ACCEPT".to_owned(),
            Ok(AssetTransferResultV1::Rejected(rejected)) => {
                assert_eq!(rejected.pre_state_root, rejected.post_state_root);
                assert!(rejected.effects.is_empty());
                format!("{:?}", rejected.code)
            }
            Err(error) => format!("ABI_ERROR({error:?})"),
        };
        let agree = outcome == vector.expected;
        ok &= agree;
        rows.push(format!(
            "{{\"vector\":\"{}\",\"rust\":\"{}\",\"expected\":\"{}\",\"parity\":{}}}",
            vector.vector_id, outcome, vector.expected, agree
        ));
        eprintln!("{}: rust={} expected={}", vector.vector_id, outcome, vector.expected);
    }
    println!(
        "{{\"ok\":{},\"schema\":\"zenodex/tau-adt-abi-rust-leg/v1\",\"vectors\":[{}]}}",
        ok,
        rows.join(",")
    );
    std::process::exit(if ok { 0 } else { 1 });
}
