use zenodex_global_settlement_abi_v1::*;

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX buyback price-safety test root",
        false,
    )
    .unwrap()
}

fn policy() -> ZDEXBuybackPriceSafetyPolicyV1 {
    ZDEXBuybackPriceSafetyPolicyV1 {
        schema: ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1.to_owned(),
        oracle_id: "zdex-buyback-oracle".to_owned(),
        maximum_oracle_age_blocks: 3,
        minimum_quote_reserve_atoms: 500,
        minimum_zdex_reserve_atoms: 200,
        maximum_pool_oracle_deviation_bps: 500,
        maximum_execution_impact_bps: 500,
        maximum_oracle_execution_deviation_bps: 1_000,
        maximum_quote_reserve_spend_bps: 2_000,
    }
}

fn observation() -> ZDEXBuybackPriceSafetyObservationV1 {
    ZDEXBuybackPriceSafetyObservationV1 {
        schema: ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1.to_owned(),
        oracle_occurrence_root: root(1),
        current_height: 77,
        oracle_observed_height: 76,
        oracle_quote_numerator_atoms: 4,
        oracle_zdex_denominator_atoms: 1,
        quote_reserve_atoms: 1_000,
        zdex_reserve_atoms: 250,
        quote_amount_in_atoms: 100,
        purchased_zdex_atoms: 24,
        claimed_route_safe_quote_limit_atoms: 200,
        claimed_minimum_output_atoms: 23,
    }
}

fn reject_code(
    observation: &ZDEXBuybackPriceSafetyObservationV1,
) -> ZDEXBuybackPriceSafetyRejectCodeV1 {
    match verify_zdex_buyback_price_safety_v1(&policy(), observation).unwrap() {
        ZDEXBuybackPriceSafetyResultV1::Rejected(code) => code,
        ZDEXBuybackPriceSafetyResultV1::Accepted(_) => panic!("expected rejection"),
    }
}

#[test]
fn exact_integer_price_envelope_accepts_and_matches_python_roots() {
    // Arrange / Act.
    let policy = policy();
    let observation = observation();
    let ZDEXBuybackPriceSafetyResultV1::Accepted(verified) =
        verify_zdex_buyback_price_safety_v1(&policy, &observation).unwrap()
    else {
        panic!("valid envelope must accept")
    };

    // Assert.
    assert_eq!(verified.route_safe_quote_limit_atoms(), 200);
    assert_eq!(verified.minimum_output_atoms(), 23);
    assert_eq!(
        policy.policy_root().unwrap().as_str(),
        "0xa0bad2275012b07b60962ef5fc75cf0c02c46e95772062c9b8c3c98a95b95d69"
    );
    assert_eq!(
        observation.observation_root().unwrap().as_str(),
        "0xcaee810d431a967702c20a76df988014dde2b063c7fab375a1ae972f80b8b915"
    );
}

#[test]
fn boundaries_and_one_defect_mutations_fail_closed() {
    let mut candidate = observation();
    candidate.oracle_observed_height = 78;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::HEIGHT_REGRESSION
    );

    candidate = observation();
    candidate.oracle_observed_height = 73;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::STALE_ORACLE
    );

    candidate = observation();
    candidate.zdex_reserve_atoms = 300;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::POOL_ORACLE_DEVIATION
    );

    candidate = observation();
    candidate.purchased_zdex_atoms = 22;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::MINIMUM_OUTPUT_NOT_MET
    );

    candidate = observation();
    candidate.quote_amount_in_atoms = 201;
    candidate.purchased_zdex_atoms = 49;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::QUOTE_LIMIT_EXCEEDED
    );

    candidate = observation();
    candidate.claimed_minimum_output_atoms = 24;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::DERIVED_MINIMUM_OUTPUT_MISMATCH
    );
}

#[test]
fn execution_impact_is_independently_enforced() {
    let mut restrictive = policy();
    restrictive.maximum_execution_impact_bps = 100;

    let result = verify_zdex_buyback_price_safety_v1(&restrictive, &observation()).unwrap();

    assert_eq!(
        result,
        ZDEXBuybackPriceSafetyResultV1::Rejected(
            ZDEXBuybackPriceSafetyRejectCodeV1::EXECUTION_IMPACT
        )
    );
}

#[test]
fn checked_cross_multiplication_rejects_overflow() {
    let mut candidate = observation();
    candidate.oracle_quote_numerator_atoms = MAX_ATOMS_V1;
    assert_eq!(
        reject_code(&candidate),
        ZDEXBuybackPriceSafetyRejectCodeV1::ARITHMETIC_OVERFLOW
    );
}
