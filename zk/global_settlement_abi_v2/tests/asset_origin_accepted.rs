use serde::{de::DeserializeOwned, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    decode_canonical_v2, transition_asset_origin_registration_v2, AbiErrorV2,
    AssetOriginRegistrationAcceptedV2, AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2, AssetOriginRegistrationResultV2, AssetOriginRegistryStateV2,
    ExternalOutboxEnqueueV2, RootV2, ValidateCanonicalV2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_asset_origin_golden.json");

fn fixture() -> Value {
    serde_json::from_str(GOLDEN).expect("committed asset-origin fixture must parse")
}

fn typed_vector<T>(fixture: &Value, name: &str) -> T
where
    T: DeserializeOwned + Serialize + ValidateCanonicalV2,
{
    let canonical = &fixture["accepted"]["vectors"][name]["canonical"];
    decode_canonical_v2(&serde_json::to_vec(canonical).expect("golden vector bytes"))
        .expect("golden vector must decode")
}

fn vector_root(fixture: &Value, name: &str) -> RootV2 {
    serde_json::from_value(fixture["accepted"]["vectors"][name]["expected_root"].clone())
        .expect("golden vector root")
}

fn accepted_registration(fixture: &Value) -> Box<AssetOriginRegistrationAcceptedV2> {
    let context: AssetOriginRegistrationContextV2 = typed_vector(fixture, "context");
    let state: AssetOriginRegistryStateV2 = typed_vector(fixture, "pre_state");
    let command: AssetOriginRegistrationCommandV2 = typed_vector(fixture, "command");
    let result = transition_asset_origin_registration_v2(&context, &state, &command)
        .expect("golden transition");
    let AssetOriginRegistrationResultV2::Accepted(accepted) = result else {
        panic!("golden transition unexpectedly rejected");
    };
    accepted
}

#[test]
fn accepted_rejects_outbox_before_journal_bindings_without_mutation() {
    let fixture = fixture();
    let honest = accepted_registration(&fixture);
    let honest_before = (*honest).clone();
    let mut forged = (*honest).clone();
    forged
        .effects
        .external_outbox_enqueue
        .push(ExternalOutboxEnqueueV2 {
            effect_id: vector_root(&fixture, "command"),
            destination_id: "external:adapter".to_owned(),
            payload_hash: vector_root(&fixture, "context"),
            adapter_profile_root: vector_root(&fixture, "pre_state"),
        });
    forged.module_journal.private_port_root = vector_root(&fixture, "record");

    assert_eq!(
        forged.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset origin registration created an external outbox effect"
        ))
    );
    assert_eq!(*honest, honest_before);
    assert!(honest.effects.external_outbox_enqueue.is_empty());
}

#[test]
fn accepted_rejects_each_external_commitment_root() {
    let fixture = fixture();
    let honest = accepted_registration(&fixture);
    let forged_root = vector_root(&fixture, "record");

    for field in ["private", "terminal", "oracle"] {
        let mut forged = (*honest).clone();
        match field {
            "private" => forged.module_journal.private_port_root = forged_root.clone(),
            "terminal" => {
                forged.module_journal.terminal_obligations_root = forged_root.clone();
            }
            "oracle" => forged.module_journal.oracle_occurrence_plan_root = forged_root.clone(),
            _ => unreachable!("closed root field"),
        }
        assert_eq!(
            forged.validate(),
            Err(AbiErrorV2::InvalidBinding(
                "asset origin registration created an unrelated plan"
            )),
            "{field}"
        );
    }
    assert!(honest.module_journal.private_port_root.is_zero());
    assert!(honest.module_journal.terminal_obligations_root.is_zero());
    assert!(honest.module_journal.oracle_occurrence_plan_root.is_zero());
}
