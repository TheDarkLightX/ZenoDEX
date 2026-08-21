use serde::{Deserialize, Serialize};

use crate::asset_precision::TARGET_COMMON_DECIMALS_V1;
use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};

pub const G1_ASSET_AUTHORITY_CANDIDATE_SCHEMA_V1: &str = "zenodex/g1-asset-authority-candidate/v1";
pub const G1_ASSET_AUTHORITY_POLICY_COUNT_V1: usize = 4;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetAuthorityClassV1 {
    TAU_ORIGINATED_TOKEN,
    ZDEX_PROTOCOL_TOKEN,
    CANONICAL_ZUSD,
    LP_SHARE,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum LocalSupplyAuthorityV1 {
    NO_LOCAL_AUTHORITY,
    GOVERNANCE_MIGRATION_GENESIS_ONLY,
    ZDEX_TOKENOMICS_EXACT_SOURCE,
    ZUSD_MONETARY_KERNEL,
    SPOT_LIQUIDITY_POOL_KERNEL,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum TerminalSupplyRuleV1 {
    RETURN_ALL_TAU_CLAIMS_BEFORE_DISABLE,
    EXPLICIT_ASSET_RETIREMENT,
    ZERO_AFTER_LIABILITIES_AND_CLAIMS_DRAIN,
    POOL_CLOSE_DRAINS_ALL_RESERVES_FEES_AND_RESIDUE,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetProfileAvailabilityV1 {
    TAU_INTEGRATION_HOLD,
    CANDIDATE_UNSELECTED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AutomaticGovernanceRoleV1 {
    REGISTERED_PROPOSAL_ORIGINATOR,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum G1AssetAuthoritySelectionV1 {
    CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetAuthorityPolicyV1 {
    pub asset: String,
    pub asset_class: AssetAuthorityClassV1,
    pub ledger_decimals: u8,
    pub issue_authority: LocalSupplyAuthorityV1,
    pub burn_authority: LocalSupplyAuthorityV1,
    pub terminal_rule: TerminalSupplyRuleV1,
    pub availability: AssetProfileAvailabilityV1,
}

impl AssetAuthorityPolicyV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "asset authority policy asset")?;
        if self.ledger_decimals != TARGET_COMMON_DECIMALS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "asset authority policy ledger decimals",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct G1AssetAuthorityCandidateV1 {
    pub schema: String,
    pub precision_registry_root: RootV1,
    pub policies: Vec<AssetAuthorityPolicyV1>,
    pub automatic_governance_role: AutomaticGovernanceRoleV1,
    pub selection: G1AssetAuthoritySelectionV1,
}

impl G1AssetAuthorityCandidateV1 {
    /// Validates the exact, inactive four-asset G1 authority candidate.
    ///
    /// The candidate describes which module would own each local supply action.
    /// Validation supplies no activation, transition, proof, or publication
    /// authority.
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != G1_ASSET_AUTHORITY_CANDIDATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.precision_registry_root
            .validate("asset authority precision registry root", false)?;
        if self.policies.len() != G1_ASSET_AUTHORITY_POLICY_COUNT_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "G1 testnet asset authority policy count",
            ));
        }
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder(
                "G1 testnet asset authority policies",
            ));
        }

        let expected =
            g1_testnet_asset_authority_candidate_v1(self.precision_registry_root.clone());
        if self.policies != expected.policies
            || self.automatic_governance_role != expected.automatic_governance_role
            || self.selection != expected.selection
        {
            return Err(AbiErrorV1::InvalidBinding(
                "G1 testnet asset authority matrix",
            ));
        }
        Ok(())
    }

    pub fn profile_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("g1-asset-authority-candidate-v1", self)
    }

    pub fn policy_for(&self, asset: &str) -> Option<&AssetAuthorityPolicyV1> {
        self.policies.iter().find(|policy| policy.asset == asset)
    }
}

/// Constructs the only G1 four-asset authority candidate accepted by V1.
///
/// TAU movements require a future verified occurrence adapter and therefore
/// have no local issue or burn authority. The other three asset families bind
/// supply actions to their owning economic module. AutoGov can originate a
/// registered proposal and has no supply or publication role in this type.
pub fn g1_testnet_asset_authority_candidate_v1(
    precision_registry_root: RootV1,
) -> G1AssetAuthorityCandidateV1 {
    let mut policies = vec![
        AssetAuthorityPolicyV1 {
            asset: "TAU".to_owned(),
            asset_class: AssetAuthorityClassV1::TAU_ORIGINATED_TOKEN,
            ledger_decimals: TARGET_COMMON_DECIMALS_V1,
            issue_authority: LocalSupplyAuthorityV1::NO_LOCAL_AUTHORITY,
            burn_authority: LocalSupplyAuthorityV1::NO_LOCAL_AUTHORITY,
            terminal_rule: TerminalSupplyRuleV1::RETURN_ALL_TAU_CLAIMS_BEFORE_DISABLE,
            availability: AssetProfileAvailabilityV1::TAU_INTEGRATION_HOLD,
        },
        AssetAuthorityPolicyV1 {
            asset: "ZDEX".to_owned(),
            asset_class: AssetAuthorityClassV1::ZDEX_PROTOCOL_TOKEN,
            ledger_decimals: TARGET_COMMON_DECIMALS_V1,
            issue_authority: LocalSupplyAuthorityV1::GOVERNANCE_MIGRATION_GENESIS_ONLY,
            burn_authority: LocalSupplyAuthorityV1::ZDEX_TOKENOMICS_EXACT_SOURCE,
            terminal_rule: TerminalSupplyRuleV1::EXPLICIT_ASSET_RETIREMENT,
            availability: AssetProfileAvailabilityV1::CANDIDATE_UNSELECTED,
        },
        AssetAuthorityPolicyV1 {
            asset: "zUSD".to_owned(),
            asset_class: AssetAuthorityClassV1::CANONICAL_ZUSD,
            ledger_decimals: TARGET_COMMON_DECIMALS_V1,
            issue_authority: LocalSupplyAuthorityV1::ZUSD_MONETARY_KERNEL,
            burn_authority: LocalSupplyAuthorityV1::ZUSD_MONETARY_KERNEL,
            terminal_rule: TerminalSupplyRuleV1::ZERO_AFTER_LIABILITIES_AND_CLAIMS_DRAIN,
            availability: AssetProfileAvailabilityV1::CANDIDATE_UNSELECTED,
        },
        AssetAuthorityPolicyV1 {
            asset: "LP_SHARE_RELEASE_DEFINED".to_owned(),
            asset_class: AssetAuthorityClassV1::LP_SHARE,
            ledger_decimals: TARGET_COMMON_DECIMALS_V1,
            issue_authority: LocalSupplyAuthorityV1::SPOT_LIQUIDITY_POOL_KERNEL,
            burn_authority: LocalSupplyAuthorityV1::SPOT_LIQUIDITY_POOL_KERNEL,
            terminal_rule: TerminalSupplyRuleV1::POOL_CLOSE_DRAINS_ALL_RESERVES_FEES_AND_RESIDUE,
            availability: AssetProfileAvailabilityV1::CANDIDATE_UNSELECTED,
        },
    ];
    policies.sort_by(|left, right| left.asset.cmp(&right.asset));
    G1AssetAuthorityCandidateV1 {
        schema: G1_ASSET_AUTHORITY_CANDIDATE_SCHEMA_V1.to_owned(),
        precision_registry_root,
        policies,
        automatic_governance_role: AutomaticGovernanceRoleV1::REGISTERED_PROPOSAL_ORIGINATOR,
        selection: G1AssetAuthoritySelectionV1::CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED,
    }
}
