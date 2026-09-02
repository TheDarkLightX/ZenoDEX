//! Rust leg of the Tau ADT ABI parity oracle (v2 vectors): replays the frozen
//! vector set through the real Rust transition and reports per-vector
//! agreement with the Python-oracle expectation. Research-only.

use std::io::Read;

use zenodex_global_settlement_abi_v1::{
    transition_asset_transfer_v1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferPolicyV1, AssetTransferResultV1, AssetTransferStateV1, EconomicAmountV1, RootV1,
    ACCOUNT_CUSTODY_DOMAIN_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

#[derive(serde::Deserialize)]
struct VectorV2 {
    vector_id: String,
    tier: String,
    release_tag: u64,
    subject: String,
    kind: String,
    asset: String,
    sender: String,
    recipient: String,
    amount: String,
    max_fee: String,
    state_release_tag: u64,
    policy_asset: String,
    fee: String,
    enabled: bool,
    s_bal: String,
    r_bal: String,
    t_bal: String,
    extra_rows: u32,
    expected: String,
}

#[derive(serde::Deserialize)]
struct FileV2 {
    schema: String,
    vectors: Vec<VectorV2>,
}

fn root(tag: u64) -> RootV1 {
    // Tag 1 == the Python harness ROOT (0x11..11), tag 2 == OTHER_ROOT (0x22..22).
    let byte = match tag {
        1 => "11",
        2 => "22",
        other => panic!("unknown root tag {other}"),
    };
    RootV1::parse(format!("0x{}", byte.repeat(32)), "abi leg root", false).expect("root parses")
}

fn atoms(value: &str) -> u128 {
    value.parse::<u128>().expect("u128 literal")
}

fn amount(owner: &str, asset: &str, atoms: u128) -> EconomicAmountV1 {
    EconomicAmountV1 {
        owner: owner.to_owned(),
        asset: asset.to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
        amount_atoms: atoms,
    }
}

fn main() {
    let mut raw = String::new();
    std::io::stdin().read_to_string(&mut raw).expect("stdin");
    let file: FileV2 = serde_json::from_str(&raw).expect("vector json");
    assert_eq!(file.schema, "zenodex/tau-adt-abi-vectors/v2");
    let mut ok = true;
    let mut rows = Vec::new();
    for vector in &file.vectors {
        let mut balances: Vec<EconomicAmountV1> = Vec::new();
        for (owner, value) in [
            ("sender", &vector.s_bal),
            ("recv", &vector.r_bal),
            ("treasury", &vector.t_bal),
        ] {
            let value = atoms(value);
            if value > 0 {
                balances.push(amount(owner, &vector.policy_asset, value));
            }
        }
        for index in 0..vector.extra_rows {
            balances.push(amount(&format!("acct-{index:04}"), &vector.policy_asset, 1));
        }
        balances.sort_by(|a, b| (&a.asset, &a.owner).cmp(&(&b.asset, &b.owner)));
        let supply: u128 = balances.iter().map(|row| row.amount_atoms).sum();
        let state = AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root(vector.state_release_tag),
            policies: vec![AssetTransferPolicyV1 {
                asset: vector.policy_asset.clone(),
                fee_owner: "treasury".to_owned(),
                transfer_fee_atoms: atoms(&vector.fee),
                enabled: vector.enabled,
            }],
            balances,
            supplies: vec![AssetSupplyV1 {
                asset: vector.policy_asset.clone(),
                amount_atoms: supply,
            }],
        };
        let context = AssetTransferContextV1 {
            chain_id: "zenodex".to_owned(),
            deployment_root: root(1),
            profile_root: root(1),
            writer_epoch: 1,
            module_release_id: root(vector.release_tag),
            command_occurrence_id: root(1),
            subject_id: vector.subject.clone(),
            grant_root: root(1),
        };
        let command = AssetTransferCommandV1 {
            command_kind: vector.kind.clone(),
            asset: vector.asset.clone(),
            sender: vector.sender.clone(),
            recipient: vector.recipient.clone(),
            amount_atoms: atoms(&vector.amount),
            max_fee_atoms: atoms(&vector.max_fee),
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
            "{{\"vector\":\"{}\",\"tier\":\"{}\",\"rust\":\"{}\",\"expected\":\"{}\",\"parity\":{}}}",
            vector.vector_id, vector.tier, outcome, vector.expected, agree
        ));
        eprintln!(
            "{}: rust={} expected={}",
            vector.vector_id, outcome, vector.expected
        );
    }
    println!(
        "{{\"ok\":{},\"schema\":\"zenodex/tau-adt-abi-rust-leg/v2\",\"vectors\":[{}]}}",
        ok,
        rows.join(",")
    );
    std::process::exit(if ok { 0 } else { 1 });
}
