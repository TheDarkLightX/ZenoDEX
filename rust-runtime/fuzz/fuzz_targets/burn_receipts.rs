#![no_main]
//! libFuzzer target: burn rails must never panic; on accept, supply is
//! conserved and the accumulator grows by exactly the burned amount.

use libfuzzer_sys::fuzz_target;
use zenodex_runtime_core::burn_receipts::{verify_rails, RailInputs};

#[derive(arbitrary::Arbitrary, Debug)]
struct Rails {
    do_burn: i64,
    receipt_bound: i64,
    nullifier_unused: i64,
    policy_ok: i64,
    burn_amount: i64,
    receipt_amount: i64,
    burn_budget: i64,
    supply_before: i64,
    supply_after: i64,
    batch_burn_sum_before: i64,
    batch_burn_sum_after: i64,
}

fuzz_target!(|r: Rails| {
    let inputs = RailInputs {
        do_burn: r.do_burn,
        receipt_bound: r.receipt_bound,
        nullifier_unused: r.nullifier_unused,
        policy_ok: r.policy_ok,
        burn_amount: r.burn_amount,
        receipt_amount: r.receipt_amount,
        burn_budget: r.burn_budget,
        supply_before: r.supply_before,
        supply_after: r.supply_after,
        batch_burn_sum_before: r.batch_burn_sum_before,
        batch_burn_sum_after: r.batch_burn_sum_after,
    };
    if verify_rails(&inputs).is_ok() {
        assert_eq!(inputs.supply_after, inputs.supply_before - inputs.burn_amount);
        assert_eq!(
            inputs.batch_burn_sum_after,
            inputs.batch_burn_sum_before + inputs.burn_amount
        );
        assert!(inputs.burn_budget >= inputs.burn_amount);
    }
});
