#[path = "support/spot_certificate_fixture.rs"]
mod fixture;

use zenodex_zrpf_protocol_v3::{
    CommitmentV3, ProposedValueAggregateV5, SettlementEpochCertificateV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    compose_ordinary_spot_settlement_certificate_v1, OrdinarySpotSettlementCertificateErrorV1,
    SpotSettlementAuthorizationInputV1, SpotSettlementProjectionErrorV1,
};

use fixture::{authorization, authorization_with, commitment, proposal, FixtureConfig};

const CLAIM_BINDING_SEED: u8 = 70;
const DA_ROOT_SEED: u8 = 71;

#[test]
fn every_composer_source_field_mutation_changes_the_journal_or_rejects() {
    let baseline_config = FixtureConfig::default();
    let baseline = compose(&proposal(baseline_config), authorization()).unwrap();

    assert_proposal_source_mutations(baseline_config, &baseline);
    assert_authorization_source_mutations(baseline_config, &baseline);
    assert_opaque_source_mutations(baseline_config, &baseline);
    assert_profile_rejects(baseline_config);
}

fn proposal_source_mutations(baseline: FixtureConfig) -> Vec<(&'static str, FixtureConfig)> {
    let mut mutations = Vec::new();
    macro_rules! mutate {
        ($name:literal, $field:ident, $value:expr) => {{
            let mut config = baseline;
            config.$field = $value;
            mutations.push(($name, config));
        }};
    }
    mutate!("aggregate_level", aggregate_level, 2);
    mutate!("child_count", row_count, 1);
    mutate!("application_id", application_seed, 81);
    mutate!("chain_or_domain_id", domain_seed, 82);
    mutate!("epoch", epoch, 28);
    mutate!("public_policy_hash", policy_seed, 83);
    mutate!("feature_suite_hash", feature_seed, 84);
    mutate!("dependency_lock_hash", dependency_seed, 85);
    mutate!("toolchain_lock_hash", toolchain_seed, 86);
    mutate!("value_subtree", lane_seed, 87);
    mutate!("authority_grants_root", authority_grants_seed, 88);
    mutate!("asset_flow", flow_amount, 18);
    mutate!("child_program", child_program_seed, 89);
    mutate!("child_profile", child_profile_seed, 90);
    mutate!("child_manifest", child_manifest_seed, 91);
    mutate!("child_journal", child_journal_seed, 92);
    mutate!("child_claim", child_claim_seed, 93);
    mutate!("child_subtree", child_subtree_seed, 94);
    mutate!("child_conflict_schedule", child_conflict_schedule_seed, 95);
    mutations
}

fn assert_proposal_source_mutations(
    baseline_config: FixtureConfig,
    baseline: &SettlementEpochCertificateV1,
) {
    for (name, config) in proposal_source_mutations(baseline_config) {
        let changed = compose(&proposal(config), authorization()).unwrap();
        assert_ne!(
            changed.canonical_journal_hash().unwrap(),
            baseline.canonical_journal_hash().unwrap(),
            "{name}"
        );
        assert_ne!(
            changed.semantic_journal_hash(),
            baseline.semantic_journal_hash(),
            "{name}"
        );
        assert_ne!(
            changed.schedule_certificate_root(),
            baseline.schedule_certificate_root(),
            "{name}"
        );
        if is_proof_tree_source(name) {
            assert_ne!(
                changed.proof_tree_root(),
                baseline.proof_tree_root(),
                "{name}"
            );
        } else {
            assert_eq!(
                changed.proof_tree_root(),
                baseline.proof_tree_root(),
                "{name}"
            );
        }
        if matches!(name, "child_program" | "child_profile" | "child_manifest") {
            assert_ne!(
                changed.dependency_manifest_root(),
                baseline.dependency_manifest_root(),
                "{name}"
            );
        } else {
            assert_eq!(
                changed.dependency_manifest_root(),
                baseline.dependency_manifest_root(),
                "{name}"
            );
        }
    }
}

fn is_proof_tree_source(name: &str) -> bool {
    matches!(
        name,
        "aggregate_level"
            | "child_count"
            | "child_program"
            | "child_profile"
            | "child_manifest"
            | "child_journal"
            | "child_claim"
            | "child_subtree"
            | "child_conflict_schedule"
    )
}

fn assert_authorization_source_mutations(
    baseline_config: FixtureConfig,
    baseline: &SettlementEpochCertificateV1,
) {
    for (name, changed_authorization) in [
        ("authorization_subject", authorization_with(53, 51, 7, 52)),
        ("authorization_scope", authorization_with(50, 54, 7, 52)),
        ("authorization_nonce", authorization_with(50, 51, 8, 52)),
        ("authorization_grant", authorization_with(50, 51, 7, 55)),
    ] {
        let changed = compose(&proposal(baseline_config), changed_authorization).unwrap();
        assert_ne!(
            changed.canonical_journal_hash().unwrap(),
            baseline.canonical_journal_hash().unwrap(),
            "{name}"
        );
        assert_ne!(
            changed.schedule_certificate_root(),
            baseline.schedule_certificate_root(),
            "{name}"
        );
        assert_eq!(
            changed.semantic_journal_hash(),
            baseline.semantic_journal_hash(),
            "{name}"
        );
        assert_eq!(
            changed.proof_tree_root(),
            baseline.proof_tree_root(),
            "{name}"
        );
        assert_eq!(changed.semantic_root(), baseline.semantic_root(), "{name}");
        assert_eq!(
            changed.dependency_manifest_root(),
            baseline.dependency_manifest_root(),
            "{name}"
        );
    }
}

fn assert_opaque_source_mutations(
    baseline_config: FixtureConfig,
    baseline: &SettlementEpochCertificateV1,
) {
    let base_proposal = proposal(baseline_config);
    let changed_claim = compose_with(
        &base_proposal,
        authorization(),
        commitment(72),
        commitment(DA_ROOT_SEED),
    )
    .unwrap();
    let mut expected_claim = baseline.to_input();
    expected_claim.semantic_claim_binding = commitment(72);
    assert_eq!(changed_claim.to_input(), expected_claim);
    assert_ne!(
        changed_claim.canonical_journal_hash().unwrap(),
        baseline.canonical_journal_hash().unwrap()
    );

    let changed_da = compose_with(
        &base_proposal,
        authorization(),
        commitment(CLAIM_BINDING_SEED),
        commitment(73),
    )
    .unwrap();
    let mut expected_da = baseline.to_input();
    expected_da.data_availability_certificate_root = commitment(73);
    assert_eq!(changed_da.to_input(), expected_da);
    assert_ne!(
        changed_da.canonical_journal_hash().unwrap(),
        baseline.canonical_journal_hash().unwrap()
    );
}

fn assert_profile_rejects(baseline_config: FixtureConfig) {
    let mut wrong_profile = baseline_config;
    wrong_profile.wrong_value_profile = true;
    assert_eq!(
        compose(&proposal(wrong_profile), authorization()).unwrap_err(),
        OrdinarySpotSettlementCertificateErrorV1::Projection(
            SpotSettlementProjectionErrorV1::ProfileMismatch("value_profile_id")
        )
    );
    let mut supply_change = baseline_config;
    supply_change.supply_change = true;
    assert_eq!(
        compose(&proposal(supply_change), authorization()).unwrap_err(),
        OrdinarySpotSettlementCertificateErrorV1::Projection(
            SpotSettlementProjectionErrorV1::SupplyChangingFlow
        )
    );
}

fn compose(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    compose_with(
        proposal,
        authorization,
        commitment(CLAIM_BINDING_SEED),
        commitment(DA_ROOT_SEED),
    )
}

fn compose_with(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    claim_binding: CommitmentV3,
    da_root: CommitmentV3,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    compose_ordinary_spot_settlement_certificate_v1(proposal, authorization, claim_binding, da_root)
}
