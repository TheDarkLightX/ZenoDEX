//! Independent CPU replay of the exact final proof input; no receipt authority.

use zenodex_asset_lane_coordinator_risc0_shared::prepare_asset_lane_coordinator_v1;
use zenodex_asset_transfer_route_composer_risc0_shared::prepare_asset_transfer_route_from_bytes_v1;

#[test]
#[ignore = "export the supplied final proof input's existing Rust economic relations"]
fn final_input_economic_reference() {
    let input = std::fs::read(std::env::var_os("ZENODEX_FINAL_ROUTE_INPUT").unwrap()).unwrap();
    let prepared = prepare_asset_transfer_route_from_bytes_v1(&input).unwrap();
    let lane = prepare_asset_lane_coordinator_v1(prepared.input().lane_input.clone()).unwrap();
    let value = serde_json::json!({
        "input": prepared.input(),
        "lane_journal": serde_json::from_slice::<serde_json::Value>(prepared.lane_journal_bytes()).unwrap(),
        "route_journal": serde_json::from_slice::<serde_json::Value>(prepared.route_journal_bytes()).unwrap(),
        "effect_plan": lane.lane_accepted.effects,
        "projection_root": prepared.projection_root(),
        "refinement_root": prepared.refinement_root(),
    });
    std::fs::write(
        std::env::var_os("ZENODEX_FINAL_ROUTE_REFERENCE").unwrap(),
        serde_json::to_vec_pretty(&value).unwrap(),
    )
    .unwrap();
}
