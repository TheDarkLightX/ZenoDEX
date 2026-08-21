use serde::Serialize;

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::{EconomicCommandOccurrenceV1, ReceiptKindV1};
use crate::release::{LaneIdV1, LaneModuleReleaseV1, ReleaseStatusV1, RouteReleaseV1};
use crate::zdex_purchase_burn_effects::{burn_effects_v1, purchase_effects_v1};
use crate::zdex_purchase_burn_types::{
    zdex_amm_purchase_port_schema_root_v1, zdex_burn_port_schema_root_v1, ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1, AMM_PURCHASE_OUTPUT_ROLE_V1, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
};

pub const VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1: &str = "zenodex/verified-zdex-amm-purchase/v1";
pub const VERIFIED_ZDEX_BURN_SCHEMA_V1: &str = "zenodex/verified-zdex-burn/v1";

pub trait ZDEXLaneSuccinctReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()>;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXLaneReceiptEnvelopeV1 {
    pub receipt_kind: ReceiptKindV1,
    pub receipt_bytes: Vec<u8>,
}

pub struct ZDEXPurchaseReceiptCandidateV1<'a> {
    pub route_release: &'a RouteReleaseV1,
    pub module_release: &'a LaneModuleReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub journal: &'a ZDEXAMMPurchaseJournalV1,
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
    ($name:ident, $schema:expr, $domain:expr) => {
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
            pub fn binding_root(&self) -> AbiResultV1<RootV1> {
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
                hash_global_v1(
                    $domain,
                    &Binding {
                        schema: $schema,
                        route_release_id: self.route_release_id(),
                        module_release_id: self.module_release_id(),
                        command_occurrence_id: self.command_occurrence_id(),
                        profile_root: self.profile_root(),
                        writer_epoch: self.writer_epoch(),
                        journal_root: self.journal_root(),
                        journal_digest: self.journal_digest(),
                        effect_plan_root: self.effect_plan_root(),
                        expected_image_id: self.expected_image_id(),
                        receipt_digest: self.receipt_digest(),
                        receipt_kind: self.receipt_kind(),
                    },
                )
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

verified_lane_type!(
    VerifiedZDEXAMMPurchaseV1,
    VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1,
    "verified-zdex-amm-purchase-v1"
);
verified_lane_type!(
    VerifiedZDEXBurnV1,
    VERIFIED_ZDEX_BURN_SCHEMA_V1,
    "verified-zdex-burn-v1"
);

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

pub fn verify_zdex_amm_purchase_receipt_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXAMMPurchaseV1> {
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
    if journal.chain_id != candidate.occurrence.chain_id
        || journal.deployment_root != candidate.occurrence.deployment_root
        || journal.profile_root != candidate.occurrence.profile_root
        || journal.route_release_id != candidate.route_release.route_release_id
        || journal.command_occurrence_id != occurrence_id
        || journal.spot_module_release_id != candidate.module_release.release_id
        || journal.issue_burn_policy_root != candidate.route_release.issue_burn_policy_root
        || journal.effect_plan_root != candidate.effects.effect_plan_root()?
        || candidate.effects != &purchase_effects_v1(journal)?
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase journal or effects",
        ));
    }
    let journal_bytes = canonical_bytes_v1(journal)?;
    let (journal_digest, receipt_digest) = verify_receipt_v1(
        candidate.receipt,
        &journal_bytes,
        candidate.module_release,
        verifier,
    )?;
    Ok(VerifiedZDEXAMMPurchaseV1(VerifiedZDEXLaneFieldsV1 {
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
    }))
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
    }))
}
