use zenodex_global_settlement_abi_v1::{
    g1_testnet_asset_authority_candidate_v1, AbiErrorV1, AssetAuthorityPolicyV1,
    AssetProfileAvailabilityV1, AutomaticGovernanceRoleV1, G1AssetAuthorityCandidateV1,
    LocalSupplyAuthorityV1, RootV1, G1_ASSET_AUTHORITY_CANDIDATE_SCHEMA_V1,
    GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};

fn root(byte: u8) -> RootV1 {
    RootV1::parse(
        format!("0x{}", format!("{byte:02x}").repeat(32)),
        "test root",
        false,
    )
    .unwrap()
}

fn policy_mut<'a>(
    profile: &'a mut G1AssetAuthorityCandidateV1,
    asset: &str,
) -> &'a mut AssetAuthorityPolicyV1 {
    profile
        .policies
        .iter_mut()
        .find(|policy| policy.asset == asset)
        .unwrap()
}

#[test]
fn exact_four_asset_candidate_is_closed_and_rooted() {
    // Arrange
    let profile = g1_testnet_asset_authority_candidate_v1(root(1));

    // Act
    profile.validate().unwrap();
    let profile_root = profile.profile_root().unwrap();

    // Assert
    assert_eq!(profile.schema, G1_ASSET_AUTHORITY_CANDIDATE_SCHEMA_V1);
    assert_eq!(profile.policies.len(), 4);
    assert_eq!(
        profile.automatic_governance_role,
        AutomaticGovernanceRoleV1::REGISTERED_PROPOSAL_ORIGINATOR
    );
    assert!(!profile_root.is_zero());

    let tau = profile.policy_for("TAU").unwrap();
    assert_eq!(
        tau.issue_authority,
        LocalSupplyAuthorityV1::NO_LOCAL_AUTHORITY
    );
    assert_eq!(
        tau.burn_authority,
        LocalSupplyAuthorityV1::NO_LOCAL_AUTHORITY
    );
    assert_eq!(
        tau.availability,
        AssetProfileAvailabilityV1::TAU_INTEGRATION_HOLD
    );

    let zdex = profile.policy_for("ZDEX").unwrap();
    assert_eq!(
        zdex.issue_authority,
        LocalSupplyAuthorityV1::GOVERNANCE_MIGRATION_GENESIS_ONLY
    );
    assert_eq!(
        zdex.burn_authority,
        LocalSupplyAuthorityV1::ZDEX_TOKENOMICS_EXACT_SOURCE
    );

    let zusd = profile.policy_for("zUSD").unwrap();
    assert_eq!(
        zusd.issue_authority,
        LocalSupplyAuthorityV1::ZUSD_MONETARY_KERNEL
    );
    assert_eq!(
        zusd.burn_authority,
        LocalSupplyAuthorityV1::ZUSD_MONETARY_KERNEL
    );

    let lp = profile.policy_for("LP_SHARE_RELEASE_DEFINED").unwrap();
    assert_eq!(
        lp.issue_authority,
        LocalSupplyAuthorityV1::SPOT_LIQUIDITY_POOL_KERNEL
    );
    assert_eq!(
        lp.burn_authority,
        LocalSupplyAuthorityV1::SPOT_LIQUIDITY_POOL_KERNEL
    );
}

#[test]
fn matrix_mutations_fail_closed() {
    // Arrange
    let baseline = g1_testnet_asset_authority_candidate_v1(root(1));

    let mut tau_issue = baseline.clone();
    policy_mut(&mut tau_issue, "TAU").issue_authority =
        LocalSupplyAuthorityV1::GOVERNANCE_MIGRATION_GENESIS_ONLY;

    let mut zdex_issue = baseline.clone();
    policy_mut(&mut zdex_issue, "ZDEX").issue_authority =
        LocalSupplyAuthorityV1::ZDEX_TOKENOMICS_EXACT_SOURCE;

    let mut zusd_burn = baseline.clone();
    policy_mut(&mut zusd_burn, "zUSD").burn_authority = LocalSupplyAuthorityV1::NO_LOCAL_AUTHORITY;

    let mut lp_burn = baseline.clone();
    policy_mut(&mut lp_burn, "LP_SHARE_RELEASE_DEFINED").burn_authority =
        LocalSupplyAuthorityV1::ZUSD_MONETARY_KERNEL;

    // Act
    for malformed in [tau_issue, zdex_issue, zusd_burn, lp_burn] {
        // Assert
        assert_eq!(
            malformed.validate(),
            Err(AbiErrorV1::InvalidBinding(
                "G1 testnet asset authority matrix"
            ))
        );
    }
}

#[test]
fn coverage_order_precision_and_binding_mutations_fail_closed() {
    // Arrange
    let baseline = g1_testnet_asset_authority_candidate_v1(root(1));

    let mut missing = baseline.clone();
    missing.policies.pop();

    let mut reordered = baseline.clone();
    reordered.policies.swap(0, 1);

    let mut duplicate = baseline.clone();
    duplicate.policies[1] = duplicate.policies[0].clone();

    let mut decimals_below = baseline.clone();
    decimals_below.policies[0].ledger_decimals = 7;

    let mut decimals_above = baseline.clone();
    decimals_above.policies[0].ledger_decimals = 9;

    let mut zero_precision_root = baseline.clone();
    zero_precision_root.precision_registry_root =
        RootV1::parse(ZERO_ROOT_V1, "zero root", true).unwrap();

    let mut wrong_schema = baseline;
    wrong_schema.schema = GLOBAL_SETTLEMENT_ABI_V1.to_owned();

    // Act / Assert
    assert_eq!(
        missing.validate(),
        Err(AbiErrorV1::InvalidBounds(
            "G1 testnet asset authority policy count"
        ))
    );
    assert_eq!(
        reordered.validate(),
        Err(AbiErrorV1::InvalidOrder(
            "G1 testnet asset authority policies"
        ))
    );
    assert_eq!(
        duplicate.validate(),
        Err(AbiErrorV1::InvalidOrder(
            "G1 testnet asset authority policies"
        ))
    );
    for malformed in [decimals_below, decimals_above] {
        assert_eq!(
            malformed.validate(),
            Err(AbiErrorV1::InvalidBounds(
                "asset authority policy ledger decimals"
            ))
        );
    }
    assert_eq!(
        zero_precision_root.validate(),
        Err(AbiErrorV1::InvalidRoot(
            "asset authority precision registry root"
        ))
    );
    assert_eq!(wrong_schema.validate(), Err(AbiErrorV1::InvalidSchema));
}

#[test]
fn precision_binding_changes_candidate_root() {
    // Arrange
    let first = g1_testnet_asset_authority_candidate_v1(root(1));
    let second = g1_testnet_asset_authority_candidate_v1(root(2));

    // Act / Assert
    assert_ne!(
        first.profile_root().unwrap(),
        second.profile_root().unwrap()
    );
}

#[test]
fn canonical_wire_labels_match_the_evidence_contract() {
    // Arrange / Act
    let encoded = serde_json::to_value(g1_testnet_asset_authority_candidate_v1(root(1))).unwrap();

    // Assert
    assert_eq!(
        encoded["policies"][1]["asset_class"],
        "TAU_ORIGINATED_TOKEN"
    );
    assert_eq!(
        encoded["policies"][1]["issue_authority"],
        "NO_LOCAL_AUTHORITY"
    );
    assert_eq!(
        encoded["policies"][2]["issue_authority"],
        "GOVERNANCE_MIGRATION_GENESIS_ONLY"
    );
    assert_eq!(
        encoded["policies"][3]["terminal_rule"],
        "ZERO_AFTER_LIABILITIES_AND_CLAIMS_DRAIN"
    );
    assert_eq!(
        encoded["automatic_governance_role"],
        "REGISTERED_PROPOSAL_ORIGINATOR"
    );
    assert_eq!(
        encoded["selection"],
        "CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED"
    );
}

#[test]
fn python_and_rust_candidate_profile_roots_match() {
    // Arrange
    let artifact: serde_json::Value = serde_json::from_str(include_str!(
        "../../../docs/research/PRODUCTION_READINESS_G1_ASSET_AUTHORITY_V1.json"
    ))
    .unwrap();
    let precision_root = RootV1::parse(
        artifact["canonical_rust_binding"]["precision_registry_root"]
            .as_str()
            .unwrap(),
        "golden precision root",
        false,
    )
    .unwrap();
    let expected_profile_root = artifact["canonical_rust_binding"]["candidate_profile_root"]
        .as_str()
        .unwrap();

    // Act
    let observed_profile_root = g1_testnet_asset_authority_candidate_v1(precision_root)
        .profile_root()
        .unwrap();

    // Assert
    assert_eq!(observed_profile_root.as_str(), expected_profile_root);
}

#[test]
fn serde_rejects_automatic_governance_as_supply_authority() {
    // Arrange
    let mut encoded =
        serde_json::to_value(g1_testnet_asset_authority_candidate_v1(root(1))).unwrap();
    encoded["policies"][1]["issue_authority"] =
        serde_json::Value::String("automatic_governance".to_owned());

    // Act
    let decoded = serde_json::from_value::<G1AssetAuthorityCandidateV1>(encoded);

    // Assert
    assert!(decoded.is_err());
}
