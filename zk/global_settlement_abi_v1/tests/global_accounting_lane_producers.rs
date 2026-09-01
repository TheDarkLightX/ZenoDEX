//! Rust side of the registered-empty lane producers (wave A) against the shared fixture.
//!
//! The producer applied to the accepted fixture state's lane roots must yield exactly the
//! fragments the accepted certificate carries for EXTERNAL_CUSTODY and PROOF_REWARDS; an
//! enabled lane, a foreign root, and an unregistered lane reject with the closed codes.
//! Authority: NONE.

use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, produce_registered_empty_fragment_v1, registered_empty_lane_root_v1,
    GlobalEconomicStateV1, LaneIdV1, LaneProducerRejectCodeV1, LaneStateRootV1, RootV1,
};

fn fixture() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_accounting_allocation_certificate_v1_golden.json");
    serde_json::from_slice(&fs::read(path).expect("fixture readable")).expect("fixture JSON")
}

fn accepted_state_and_certificate() -> (GlobalEconomicStateV1, Value) {
    let fixture = fixture();
    let vector = &fixture["vectors"]["accepts_registered_empty_certificate_over_empty_state"];
    let state: GlobalEconomicStateV1 =
        serde_json::from_value(vector["state"].clone()).expect("state decodes");
    (state, vector["certificate"].clone())
}

fn lane_root(state: &GlobalEconomicStateV1, lane: LaneIdV1) -> LaneStateRootV1 {
    state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == lane)
        .expect("lane root present")
        .clone()
}

#[test]
fn producer_reproduces_the_accepted_fixture_fragments() {
    let (state, certificate) = accepted_state_and_certificate();
    for lane in [LaneIdV1::EXTERNAL_CUSTODY, LaneIdV1::PROOF_REWARDS] {
        let produced =
            produce_registered_empty_fragment_v1(&lane_root(&state, lane)).expect("produces");
        let bytes = canonical_bytes_v1(&produced).expect("fragment encodes");
        let produced_json: Value = serde_json::from_slice(&bytes).expect("JSON");
        let expected = certificate["ordered_lane_fragments"]
            .as_array()
            .expect("fragments")
            .iter()
            .find(|f| f["lane_id"] == Value::String(format!("{lane:?}")))
            .expect("fixture fragment")
            .clone();
        assert_eq!(produced_json, expected, "{lane:?}");
        let empty_root = registered_empty_lane_root_v1(lane)
            .expect("root")
            .expect("registered");
        assert_eq!(produced.lane_state_root, empty_root);
    }
    assert_eq!(
        registered_empty_lane_root_v1(LaneIdV1::ASSET_TRANSFER).expect("root"),
        None
    );
}

#[test]
fn producer_rejects_enabled_foreign_root_and_unregistered_lanes() {
    let (state, _) = accepted_state_and_certificate();
    let mut enabled = lane_root(&state, LaneIdV1::EXTERNAL_CUSTODY);
    enabled.enabled = true;
    let reject = produce_registered_empty_fragment_v1(&enabled).expect_err("enabled rejects");
    assert_eq!(reject.code, LaneProducerRejectCodeV1::LANE_ENABLED);
    let mut foreign = lane_root(&state, LaneIdV1::PROOF_REWARDS);
    foreign.state_root =
        RootV1::parse(format!("0x{:064x}", 4242u64), "foreign root", false).expect("root");
    let reject = produce_registered_empty_fragment_v1(&foreign).expect_err("foreign root rejects");
    assert_eq!(
        reject.code,
        LaneProducerRejectCodeV1::REGISTERED_EMPTY_ROOT_DRIFT
    );
    assert_eq!(reject.committed_lane_root, foreign.state_root);
    let reject = produce_registered_empty_fragment_v1(&lane_root(&state, LaneIdV1::ASSET_TRANSFER))
        .expect_err("unregistered rejects");
    assert_eq!(
        reject.code,
        LaneProducerRejectCodeV1::LANE_NOT_REGISTERED_EMPTY
    );
    assert_eq!(LaneProducerRejectCodeV1::ALL.len(), 3);
    assert_eq!(
        LaneProducerRejectCodeV1::LANE_ENABLED.message(),
        "registered-empty lane is enabled"
    );
}
