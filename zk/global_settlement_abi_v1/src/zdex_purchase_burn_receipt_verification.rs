use serde::Serialize;

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::{EconomicCommandOccurrenceV1, ReceiptKindV1};
use crate::release::{LaneIdV1, LaneModuleReleaseV1, ReleaseStatusV1, RouteReleaseV1};
use crate::state::GlobalEconomicStateV1;
use crate::zdex_buyback_price_authority::{
    verify_zdex_buyback_price_authority_v1, ZDEXBuybackPriceAuthorityCandidateV1,
};
use crate::zdex_buyback_price_safety::{
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyPolicyV1,
};
use crate::zdex_current_authority::VerifiedZDEXCurrentAuthorityV1;
use crate::zdex_fee_allocation_types::FEE_BUYBACK_PRINCIPAL_V1;
use crate::zdex_purchase_burn_effects::{burn_effects_v1, purchase_effects_v1};
use crate::zdex_purchase_burn_types::{
    zdex_amm_purchase_port_schema_root_v1, zdex_burn_port_schema_root_v1,
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1, ZDEXBuybackExecutionPolicyV1, AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, ZDEX_BURN_INPUT_ROLE_V1,
};

pub const VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2: &str = "zenodex/verified-zdex-amm-purchase/v2";
pub const VERIFIED_ZDEX_BURN_SCHEMA_V1: &str = "zenodex/verified-zdex-burn/v1";

pub trait ZDEXLaneSuccinctReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()>;
}

pub trait ZDEXBoundLaneSuccinctReceiptVerifierV1: ZDEXLaneSuccinctReceiptVerifierV1 {
    fn verifier_binding_root(&self) -> &RootV1;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXLaneReceiptEnvelopeV1 {
    pub receipt_kind: ReceiptKindV1,
    pub receipt_bytes: Vec<u8>,
}

pub struct ZDEXPurchaseReceiptCandidateV2<'a> {
    pub route_release: &'a RouteReleaseV1,
    pub module_release: &'a LaneModuleReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub pre_state: &'a GlobalEconomicStateV1,
    pub execution_policy: &'a ZDEXBuybackExecutionPolicyV1,
    pub price_policy: &'a ZDEXBuybackPriceSafetyPolicyV1,
    pub price_occurrence: &'a ZDEXBuybackOraclePriceOccurrenceV1,
    pub journal: &'a ZDEXAMMPurchaseJournalV2,
    pub effects: &'a GlobalEconomicEffectPlanV1,
    pub receipt: &'a ZDEXLaneReceiptEnvelopeV1,
}

pub struct ZDEXBurnReceiptCandidateV1<'a> {
    pub route_release: &'a RouteReleaseV1,
    pub module_release: &'a LaneModuleReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub journal: &'a ZDEXBurnJournalV1,
    pub effects: &'a GlobalEconomicEffectPlanV1,
    pub receipt: &'a ZDEXLaneReceiptEnvelopeV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifiedZDEXLaneFieldsV1 {
    route_release_id: RootV1,
    module_release_id: RootV1,
    command_occurrence_id: RootV1,
    profile_root: RootV1,
    writer_epoch: u64,
    journal_root: RootV1,
    journal_digest: RootV1,
    effect_plan_root: RootV1,
    expected_image_id: RootV1,
    receipt_digest: RootV1,
    receipt_kind: ReceiptKindV1,
    price_authority_root: Option<RootV1>,
    price_safety_policy_root: Option<RootV1>,
}

fn verified_purchase_binding_root_v2(fields: &VerifiedZDEXLaneFieldsV1) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Binding<'a> {
        schema: &'static str,
        route_release_id: &'a RootV1,
        module_release_id: &'a RootV1,
        command_occurrence_id: &'a RootV1,
        profile_root: &'a RootV1,
        writer_epoch: u64,
        journal_root: &'a RootV1,
        journal_digest: &'a RootV1,
        effect_plan_root: &'a RootV1,
        expected_image_id: &'a RootV1,
        receipt_digest: &'a RootV1,
        receipt_kind: ReceiptKindV1,
        price_authority_root: &'a RootV1,
        price_safety_policy_root: &'a RootV1,
    }
    let price_authority_root = fields
        .price_authority_root
        .as_ref()
        .ok_or(AbiErrorV1::InvalidBinding("ZDEX purchase price authority"))?;
    let price_safety_policy_root = fields
        .price_safety_policy_root
        .as_ref()
        .ok_or(AbiErrorV1::InvalidBinding("ZDEX purchase price policy"))?;
    hash_global_v1(
        "verified-zdex-amm-purchase-v2",
        &Binding {
            schema: VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2,
            route_release_id: &fields.route_release_id,
            module_release_id: &fields.module_release_id,
            command_occurrence_id: &fields.command_occurrence_id,
            profile_root: &fields.profile_root,
            writer_epoch: fields.writer_epoch,
            journal_root: &fields.journal_root,
            journal_digest: &fields.journal_digest,
            effect_plan_root: &fields.effect_plan_root,
            expected_image_id: &fields.expected_image_id,
            receipt_digest: &fields.receipt_digest,
            receipt_kind: fields.receipt_kind,
            price_authority_root,
            price_safety_policy_root,
        },
    )
}

fn verified_burn_binding_root_v1(fields: &VerifiedZDEXLaneFieldsV1) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Binding<'a> {
        schema: &'static str,
        route_release_id: &'a RootV1,
        module_release_id: &'a RootV1,
        command_occurrence_id: &'a RootV1,
        profile_root: &'a RootV1,
        writer_epoch: u64,
        journal_root: &'a RootV1,
        journal_digest: &'a RootV1,
        effect_plan_root: &'a RootV1,
        expected_image_id: &'a RootV1,
        receipt_digest: &'a RootV1,
        receipt_kind: ReceiptKindV1,
    }
    if fields.price_authority_root.is_some() || fields.price_safety_policy_root.is_some() {
        return Err(AbiErrorV1::InvalidBinding("ZDEX burn price authority"));
    }
    hash_global_v1(
        "verified-zdex-burn-v1",
        &Binding {
            schema: VERIFIED_ZDEX_BURN_SCHEMA_V1,
            route_release_id: &fields.route_release_id,
            module_release_id: &fields.module_release_id,
            command_occurrence_id: &fields.command_occurrence_id,
            profile_root: &fields.profile_root,
            writer_epoch: fields.writer_epoch,
            journal_root: &fields.journal_root,
            journal_digest: &fields.journal_digest,
            effect_plan_root: &fields.effect_plan_root,
            expected_image_id: &fields.expected_image_id,
            receipt_digest: &fields.receipt_digest,
            receipt_kind: fields.receipt_kind,
        },
    )
}

pub(crate) struct ZDEXVerifiedLaneExpectationV1<'a> {
    pub route_release_id: &'a RootV1,
    pub occurrence_id: &'a RootV1,
    pub profile_root: &'a RootV1,
    pub writer_epoch: u64,
    pub journal_root: &'a RootV1,
    pub effect_plan_root: &'a RootV1,
}

macro_rules! verified_lane_type {
    ($name:ident, $binding_root:path) => {
        #[derive(Clone, Debug, Eq, PartialEq)]
        pub struct $name(VerifiedZDEXLaneFieldsV1);

        impl $name {
            pub fn route_release_id(&self) -> &RootV1 {
                &self.0.route_release_id
            }
            pub fn module_release_id(&self) -> &RootV1 {
                &self.0.module_release_id
            }
            pub fn command_occurrence_id(&self) -> &RootV1 {
                &self.0.command_occurrence_id
            }
            pub fn profile_root(&self) -> &RootV1 {
                &self.0.profile_root
            }
            pub fn writer_epoch(&self) -> u64 {
                self.0.writer_epoch
            }
            pub fn journal_root(&self) -> &RootV1 {
                &self.0.journal_root
            }
            pub fn journal_digest(&self) -> &RootV1 {
                &self.0.journal_digest
            }
            pub fn effect_plan_root(&self) -> &RootV1 {
                &self.0.effect_plan_root
            }
            pub fn expected_image_id(&self) -> &RootV1 {
                &self.0.expected_image_id
            }
            pub fn receipt_digest(&self) -> &RootV1 {
                &self.0.receipt_digest
            }
            pub fn receipt_kind(&self) -> ReceiptKindV1 {
                self.0.receipt_kind
            }
            pub fn price_authority_root(&self) -> Option<&RootV1> {
                self.0.price_authority_root.as_ref()
            }
            pub fn price_safety_policy_root(&self) -> Option<&RootV1> {
                self.0.price_safety_policy_root.as_ref()
            }
            pub fn binding_root(&self) -> AbiResultV1<RootV1> {
                $binding_root(&self.0)
            }
            pub(crate) fn matches_route_input<T: Serialize>(
                &self,
                journal: &T,
                expected: ZDEXVerifiedLaneExpectationV1<'_>,
            ) -> AbiResultV1<bool> {
                let journal_digest =
                    digest_root_v1(&canonical_bytes_v1(journal)?, "ZDEX route journal digest")?;
                Ok(self.route_release_id() == expected.route_release_id
                    && self.command_occurrence_id() == expected.occurrence_id
                    && self.profile_root() == expected.profile_root
                    && self.writer_epoch() == expected.writer_epoch
                    && self.journal_root() == expected.journal_root
                    && self.journal_digest() == &journal_digest
                    && self.effect_plan_root() == expected.effect_plan_root
                    && self.receipt_kind() == ReceiptKindV1::SUCCINCT)
            }
        }
    };
}

verified_lane_type!(VerifiedZDEXAMMPurchaseV2, verified_purchase_binding_root_v2);
verified_lane_type!(VerifiedZDEXBurnV1, verified_burn_binding_root_v1);

macro_rules! governed_verified_lane_type {
    ($name:ident, $leaf:ty, $domain:literal) => {
        #[derive(Clone, Debug, Eq, PartialEq)]
        pub struct $name {
            leaf: $leaf,
            authority_head_root: RootV1,
            authority_generation: u64,
            policy_registry_root: RootV1,
            verifier_binding_root: RootV1,
        }

        impl $name {
            pub fn leaf(&self) -> &$leaf {
                &self.leaf
            }

            pub fn authority_head_root(&self) -> &RootV1 {
                &self.authority_head_root
            }

            pub fn authority_generation(&self) -> u64 {
                self.authority_generation
            }

            pub fn policy_registry_root(&self) -> &RootV1 {
                &self.policy_registry_root
            }

            pub fn verifier_binding_root(&self) -> &RootV1 {
                &self.verifier_binding_root
            }

            pub fn binding_root(&self) -> AbiResultV1<RootV1> {
                #[derive(Serialize)]
                struct Binding<'a> {
                    leaf_binding_root: RootV1,
                    authority_head_root: &'a RootV1,
                    authority_generation: u64,
                    policy_registry_root: &'a RootV1,
                    verifier_binding_root: &'a RootV1,
                }
                hash_global_v1(
                    $domain,
                    &Binding {
                        leaf_binding_root: self.leaf.binding_root()?,
                        authority_head_root: &self.authority_head_root,
                        authority_generation: self.authority_generation,
                        policy_registry_root: &self.policy_registry_root,
                        verifier_binding_root: &self.verifier_binding_root,
                    },
                )
            }
        }
    };
}

governed_verified_lane_type!(
    GovernedVerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXAMMPurchaseV2,
    "governed-verified-zdex-amm-purchase-v2"
);
governed_verified_lane_type!(
    GovernedVerifiedZDEXBurnV1,
    VerifiedZDEXBurnV1,
    "governed-verified-zdex-burn-v1"
);

fn require_current_authority_v1(
    occurrence: &EconomicCommandOccurrenceV1,
    writer_epoch: u64,
    authority: &VerifiedZDEXCurrentAuthorityV1,
    verifier: &impl ZDEXBoundLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<()> {
    if authority.profile_root() != &occurrence.profile_root
        || authority.authority_epoch() != writer_epoch
        || authority.receipt_verifier_binding_root() != verifier.verifier_binding_root()
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX current authority receipt verifier",
        ));
    }
    Ok(())
}

fn require_route_shape_v1(route: &RouteReleaseV1) -> AbiResultV1<()> {
    route.validate()?;
    if route.status != ReleaseStatusV1::SHADOW {
        return Err(AbiErrorV1::InvalidBinding("ZDEX route release status"));
    }
    if route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        || route.ordered_lanes != [LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS]
    {
        return Err(AbiErrorV1::InvalidBinding("ZDEX route command or lanes"));
    }
    if route.dependency_roles
        != [
            AMM_PURCHASE_OUTPUT_ROLE_V1.to_owned(),
            ZDEX_BURN_INPUT_ROLE_V1.to_owned(),
        ]
    {
        return Err(AbiErrorV1::InvalidBinding("ZDEX route dependency roles"));
    }
    let expected_ports = [
        zdex_amm_purchase_port_schema_root_v1()?,
        zdex_burn_port_schema_root_v1()?,
    ];
    if route.port_schema_roots != expected_ports {
        return Err(AbiErrorV1::InvalidBinding("ZDEX route port schemas"));
    }
    Ok(())
}

fn require_release_and_occurrence_v1(
    route: &RouteReleaseV1,
    release: &LaneModuleReleaseV1,
    occurrence: &EconomicCommandOccurrenceV1,
    lane_id: LaneIdV1,
    route_index: usize,
) -> AbiResultV1<()> {
    require_route_shape_v1(route)?;
    release.validate()?;
    occurrence.validate()?;
    if release.status != ReleaseStatusV1::SHADOW
        || release.lane_id != lane_id
        || route.module_release_ids.get(route_index) != Some(&release.release_id)
        || !release
            .command_variants
            .iter()
            .any(|command| command == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
        || occurrence.command_kind != route.command_kind
        || occurrence.route_release_id != route.route_release_id
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX route release occurrence binding",
        ));
    }
    Ok(())
}

pub(crate) fn digest_root_v1(bytes: &[u8], field: &'static str) -> AbiResultV1<RootV1> {
    RootV1::parse(format!("0x{}", hash_bytes_sha256_v1(bytes)), field, false)
}

pub(crate) fn verify_receipt_v1(
    receipt: &ZDEXLaneReceiptEnvelopeV1,
    journal_bytes: &[u8],
    release: &LaneModuleReleaseV1,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<(RootV1, RootV1)> {
    if receipt.receipt_kind != ReceiptKindV1::SUCCINCT || receipt.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBinding("ZDEX succinct receipt"));
    }
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX journal byte width"))?;
    if journal_len > release.max_journal_bytes {
        return Err(AbiErrorV1::InvalidBounds("ZDEX journal byte ceiling"));
    }
    verifier.verify_succinct_receipt(
        &receipt.receipt_bytes,
        &release.guest_image_id,
        journal_bytes,
    )?;
    Ok((
        digest_root_v1(journal_bytes, "ZDEX journal digest")?,
        digest_root_v1(&receipt.receipt_bytes, "ZDEX receipt digest")?,
    ))
}

pub fn verify_zdex_amm_purchase_receipt_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXAMMPurchaseV2> {
    require_release_and_occurrence_v1(
        candidate.route_release,
        candidate.module_release,
        candidate.occurrence,
        LaneIdV1::SPOT_LIQUIDITY,
        0,
    )?;
    candidate.journal.validate()?;
    candidate.effects.validate()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let journal = candidate.journal;
    let execution_policy_root = candidate.execution_policy.policy_root()?;
    let price_policy_root = candidate.price_policy.policy_root()?;
    let price_occurrence_root = candidate.price_occurrence.occurrence_root()?;
    let expected_quote_pool = zdex_pool_reserve_principal_v1(
        &candidate.execution_policy.pool_id,
        &candidate.execution_policy.quote_asset_id,
    )?;
    let expected_zdex_pool = zdex_pool_reserve_principal_v1(
        &candidate.execution_policy.pool_id,
        &candidate.execution_policy.zdex_asset_id,
    )?;
    let expected_burn_bucket = zdex_occurrence_burn_port_v1(
        &candidate.occurrence.profile_root,
        &candidate.route_release.route_release_id,
        &occurrence_id,
    )?;
    if journal.chain_id != candidate.occurrence.chain_id
        || journal.deployment_root != candidate.occurrence.deployment_root
        || journal.profile_root != candidate.occurrence.profile_root
        || journal.route_release_id != candidate.route_release.route_release_id
        || journal.command_occurrence_id != occurrence_id
        || journal.spot_module_release_id != candidate.module_release.release_id
        || journal.issue_burn_policy_root != candidate.route_release.issue_burn_policy_root
        || journal.buyback_execution_policy_root != execution_policy_root
        || journal.price_safety_policy_root != price_policy_root
        || journal.oracle_occurrence_root != price_occurrence_root
        || journal.oracle_observed_height != candidate.price_occurrence.observed_height
        || journal.oracle_quote_numerator_atoms != candidate.price_occurrence.quote_numerator_atoms
        || journal.oracle_zdex_denominator_atoms
            != candidate.price_occurrence.zdex_denominator_atoms
        || journal.quote_asset_id != candidate.execution_policy.quote_asset_id
        || journal.zdex_asset_id != candidate.execution_policy.zdex_asset_id
        || journal.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1
        || journal.quote_pool_bucket_id != expected_quote_pool
        || journal.zdex_pool_bucket_id != expected_zdex_pool
        || journal.burn_bucket_id != expected_burn_bucket
        || journal.effect_plan_root != candidate.effects.effect_plan_root()?
        || candidate.effects != &purchase_effects_v1(journal)?
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase journal or effects",
        ));
    }
    let price_authority =
        verify_zdex_buyback_price_authority_v1(ZDEXBuybackPriceAuthorityCandidateV1 {
            pre_state: candidate.pre_state,
            route: candidate.route_release,
            occurrence: candidate.occurrence,
            execution_policy: candidate.execution_policy,
            price_policy: candidate.price_policy,
            price_occurrence: candidate.price_occurrence,
            route_safe_quote_limit_atoms: journal.route_safe_quote_limit_atoms,
            minimum_output_atoms: journal.minimum_output_atoms,
            expected_quote_reserve_atoms: journal.quote_pool_pre_atoms,
            expected_zdex_reserve_atoms: journal.zdex_pool_pre_atoms,
            quote_amount_in_atoms: journal.quote_amount_in_atoms,
            purchased_zdex_atoms: journal.purchased_zdex_atoms,
        })?;
    let journal_bytes = canonical_bytes_v1(journal)?;
    let (journal_digest, receipt_digest) = verify_receipt_v1(
        candidate.receipt,
        &journal_bytes,
        candidate.module_release,
        verifier,
    )?;
    Ok(VerifiedZDEXAMMPurchaseV2(VerifiedZDEXLaneFieldsV1 {
        route_release_id: candidate.route_release.route_release_id.clone(),
        module_release_id: candidate.module_release.release_id.clone(),
        command_occurrence_id: occurrence_id,
        profile_root: candidate.occurrence.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
        journal_root: journal.journal_root()?,
        journal_digest,
        effect_plan_root: candidate.effects.effect_plan_root()?,
        expected_image_id: candidate.module_release.guest_image_id.clone(),
        receipt_digest,
        receipt_kind: candidate.receipt.receipt_kind,
        price_authority_root: Some(price_authority.authority_root()?),
        price_safety_policy_root: Some(price_policy_root),
    }))
}

pub fn verify_governed_zdex_amm_purchase_receipt_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2<'_>,
    authority: &VerifiedZDEXCurrentAuthorityV1,
    verifier: &impl ZDEXBoundLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<GovernedVerifiedZDEXAMMPurchaseV2> {
    require_current_authority_v1(
        candidate.occurrence,
        candidate.journal.writer_epoch,
        authority,
        verifier,
    )?;
    let leaf = verify_zdex_amm_purchase_receipt_v2(candidate, verifier)?;
    Ok(GovernedVerifiedZDEXAMMPurchaseV2 {
        leaf,
        authority_head_root: authority.authority_head_root().clone(),
        authority_generation: authority.authority_generation(),
        policy_registry_root: authority.policy_registry_root().clone(),
        verifier_binding_root: authority.receipt_verifier_binding_root().clone(),
    })
}

pub fn verify_zdex_burn_receipt_v1(
    candidate: ZDEXBurnReceiptCandidateV1<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXBurnV1> {
    require_release_and_occurrence_v1(
        candidate.route_release,
        candidate.module_release,
        candidate.occurrence,
        LaneIdV1::ZDEX_TOKENOMICS,
        1,
    )?;
    candidate.journal.validate()?;
    candidate.effects.validate()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let journal = candidate.journal;
    if journal.chain_id != candidate.occurrence.chain_id
        || journal.deployment_root != candidate.occurrence.deployment_root
        || journal.profile_root != candidate.occurrence.profile_root
        || journal.route_release_id != candidate.route_release.route_release_id
        || journal.command_occurrence_id != occurrence_id
        || journal.tokenomics_module_release_id != candidate.module_release.release_id
        || journal.issue_burn_policy_root != candidate.route_release.issue_burn_policy_root
        || journal.effect_plan_root != candidate.effects.effect_plan_root()?
        || candidate.effects != &burn_effects_v1(journal)?
    {
        return Err(AbiErrorV1::InvalidBinding("ZDEX burn journal or effects"));
    }
    let journal_bytes = canonical_bytes_v1(journal)?;
    let (journal_digest, receipt_digest) = verify_receipt_v1(
        candidate.receipt,
        &journal_bytes,
        candidate.module_release,
        verifier,
    )?;
    Ok(VerifiedZDEXBurnV1(VerifiedZDEXLaneFieldsV1 {
        route_release_id: candidate.route_release.route_release_id.clone(),
        module_release_id: candidate.module_release.release_id.clone(),
        command_occurrence_id: occurrence_id,
        profile_root: candidate.occurrence.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
        journal_root: journal.journal_root()?,
        journal_digest,
        effect_plan_root: candidate.effects.effect_plan_root()?,
        expected_image_id: candidate.module_release.guest_image_id.clone(),
        receipt_digest,
        receipt_kind: candidate.receipt.receipt_kind,
        price_authority_root: None,
        price_safety_policy_root: None,
    }))
}

pub fn verify_governed_zdex_burn_receipt_v1(
    candidate: ZDEXBurnReceiptCandidateV1<'_>,
    authority: &VerifiedZDEXCurrentAuthorityV1,
    verifier: &impl ZDEXBoundLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<GovernedVerifiedZDEXBurnV1> {
    require_current_authority_v1(
        candidate.occurrence,
        candidate.journal.writer_epoch,
        authority,
        verifier,
    )?;
    let leaf = verify_zdex_burn_receipt_v1(candidate, verifier)?;
    Ok(GovernedVerifiedZDEXBurnV1 {
        leaf,
        authority_head_root: authority.authority_head_root().clone(),
        authority_generation: authority.authority_generation(),
        policy_registry_root: authority.policy_registry_root().clone(),
        verifier_binding_root: authority.receipt_verifier_binding_root().clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root(value: &str) -> RootV1 {
        RootV1::parse(value, "verified purchase V2 golden root", false).unwrap()
    }

    #[test]
    fn verified_purchase_v2_binding_root_matches_python_golden_vector() {
        let fields = VerifiedZDEXLaneFieldsV1 {
            route_release_id: root(
                "0x43d48c9f73f7b50df62720804e6bfb8504ec1b9f46724deaa6c8c88b9481dcbc",
            ),
            module_release_id: root(
                "0x7930bfefe4715aa91d5e5564d62d01db16f363a2810f3c6f3914ba76866a9053",
            ),
            command_occurrence_id: root(
                "0x96ba9fc2145f579d8f3fe37d51bc106121b6da3cea6727b047d61f3e6e791515",
            ),
            profile_root: root(
                "0xf78649ee6f1098e078d3e31b563d9d129c8cacc34df08158718488015ddff828",
            ),
            writer_epoch: 11,
            journal_root: root(
                "0x722ca8ffc80528e280a27f6757ae279aa176a9e5aa005fe6de1fc6ab31f77ed9",
            ),
            journal_digest: root(
                "0x1c5fb2195d3d70f22eee7e3c65bf47d102bc6d8ade77d66bcf94194c2f20e502",
            ),
            effect_plan_root: root(
                "0x9f1b3b07ec308297b0cae14fd5384070c5e269ee8806057db95839c24bc00e1d",
            ),
            expected_image_id: root(
                "0x0000000000000000000000000000000000000000000000000000000000000429",
            ),
            receipt_digest: root(
                "0xc381c4517fce61a3bbff8ab84753dc996990d266aa181ee0d35ebc4c3e864544",
            ),
            receipt_kind: ReceiptKindV1::SUCCINCT,
            price_authority_root: Some(root(
                "0x15ecdaa5390b408ee4439e5f96491fbddf6f1f339249c8135af787b933b7b421",
            )),
            price_safety_policy_root: Some(root(
                "0x6247a62b46b80561c4f9bb7694a90cfaa514eea6a228e9defd1da392efd4e93a",
            )),
        };

        assert_eq!(
            verified_purchase_binding_root_v2(&fields).unwrap().as_str(),
            "0x4c28917c9a832f1402e19a18575ad6c2d1b689adcb99f598978d2138b10e0466"
        );
    }
}
