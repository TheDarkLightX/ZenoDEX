#![no_main]
//! libFuzzer target: fee_router::route_fee must never panic, and on accept must
//! conserve value for the (source, asset) stream.

use libfuzzer_sys::fuzz_target;
use zenodex_runtime_core::fee_router::{route_fee, FeeAccumulator, FeeSplitTable};

#[derive(arbitrary::Arbitrary, Debug)]
struct Input {
    source: String,
    asset: String,
    steps: Vec<(u128, i64, i64, i64, i64)>,
}

fuzz_target!(|input: Input| {
    let mut acc = FeeAccumulator::default();
    for (amount, b, s, r, h) in input.steps.into_iter().take(64) {
        let table = FeeSplitTable { buyburn_bps: b, stakers_bps: s, reserve_bps: r, hosts_bps: h };
        let dust_in = acc.dust_for(&input.source, &input.asset);
        if let Ok(a) = route_fee(&input.source, &input.asset, amount, &table, &acc) {
            let rc = &a.receipt;
            assert_eq!(amount + dust_in, rc.buyburn + rc.stakers + rc.reserve + rc.hosts + rc.dust);
            let _ = a.receipt.receipt_hash();
            let _ = a.accumulator.state_root();
            acc = a.accumulator;
        }
    }
});
