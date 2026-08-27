use serde::Serialize;

use crate::asset_transfer_lane_module::{
    AssetTransferLaneModuleAcceptedV1, AssetTransferLaneModuleInputV1,
};
use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::economic_command_authentication::AuthenticatedEconomicCommandV1;
use crate::global_oracle_price_occurrence::VerifiedGlobalOraclePriceV1;
use crate::lane_module_release_route_binding::{
    bind_asset_transfer_lane_output_to_release_route_v1,
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1,
    bind_perps_margin_lane_output_to_release_route_v1,
    ManagedAssetLifecycleReleaseRouteBindingCandidateV1, PerpsMarginReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
};
use crate::managed_asset_lifecycle_lane_module::{
    ManagedAssetLifecycleLaneModuleAcceptedV1, ManagedAssetLifecycleLaneModuleInputV1,
};
use crate::managed_asset_policy_registry::ManagedAssetPolicyRegistryV1;
use crate::perps_margin_lane_module::{
    recompute_perps_margin_accepted_v1, PerpsMarginLaneModuleInputV1,
};
use crate::perps_margin_types::PerpsMarginAcceptedV1;
use crate::perps_market_policy::PerpsMarketPolicyV1;
use crate::proof::{LaneModuleTransitionJournalV1, ReceiptKindV1};
use crate::release::{
    EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneRegistryV1,
    ReleaseStatusV1, RouteRegistryV1,
};

pub const VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1: &str =
    "zenodex/verified-lane-module-transition/v1";

/// Cryptographic verifier port selected by the settlement shell.
///
/// The caller supplies the implementation. This ABI supplies the expected
/// release image and exact canonical journal bytes and propagates every reject.
pub trait LaneModuleSuccinctReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()>;
}

#[derive(Clone, Copy, Debug)]
pub struct LaneModuleReceiptEnvelopeV1<'a> {
    pub receipt_kind: ReceiptKindV1,
    pub receipt_bytes: &'a [u8],
}

pub struct AssetTransferLaneModuleReceiptCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub authenticated_command: &'a AuthenticatedEconomicCommandV1,
    pub module_input: &'a AssetTransferLaneModuleInputV1,
    pub accepted: &'a AssetTransferLaneModuleAcceptedV1,
    pub release_route_binding: &'a ReleaseRouteBoundLaneTransitionV1,
    pub receipt: LaneModuleReceiptEnvelopeV1<'a>,
}

pub struct ManagedAssetLifecycleLaneModuleReceiptCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub policy_registry: &'a EconomicPolicyRegistryV1,
    pub asset_policy_registry: &'a ManagedAssetPolicyRegistryV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub authenticated_command: &'a AuthenticatedEconomicCommandV1,
    pub module_input: &'a ManagedAssetLifecycleLaneModuleInputV1,
    pub accepted: &'a ManagedAssetLifecycleLaneModuleAcceptedV1,
    pub release_route_binding: &'a ReleaseRouteBoundLaneTransitionV1,
    pub receipt: LaneModuleReceiptEnvelopeV1<'a>,
}

pub struct PerpsMarginLaneModuleReceiptCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub policy_registry: &'a EconomicPolicyRegistryV1,
    pub market_policy: &'a PerpsMarketPolicyV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub authenticated_command: &'a AuthenticatedEconomicCommandV1,
    pub module_input: &'a PerpsMarginLaneModuleInputV1,
    pub accepted: &'a PerpsMarginAcceptedV1,
    pub release_route_binding: &'a ReleaseRouteBoundLaneTransitionV1,
    pub verified_price: Option<&'a VerifiedGlobalOraclePriceV1>,
    pub receipt: LaneModuleReceiptEnvelopeV1<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedLaneModuleTransitionV1 {
    authenticated_command_binding_root: RootV1,
    release_route_binding_root: RootV1,
    expected_image_id: RootV1,
    module_journal_root: RootV1,
    module_journal_digest: RootV1,
    statement_root: RootV1,
    command_occurrence_id: RootV1,
    receipt_digest: RootV1,
    receipt_kind: ReceiptKindV1,
}

#[derive(Serialize)]
struct VerifiedLaneModuleTransitionContentV1<'a> {
    schema: &'static str,
    authenticated_command_binding_root: &'a RootV1,
    release_route_binding_root: &'a RootV1,
    expected_image_id: &'a RootV1,
    module_journal_root: &'a RootV1,
    module_journal_digest: &'a RootV1,
    statement_root: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    receipt_digest: &'a RootV1,
    receipt_kind: ReceiptKindV1,
}

impl VerifiedLaneModuleTransitionV1 {
    pub fn authenticated_command_binding_root(&self) -> &RootV1 {
        &self.authenticated_command_binding_root
    }

    pub fn release_route_binding_root(&self) -> &RootV1 {
        &self.release_route_binding_root
    }

    pub fn expected_image_id(&self) -> &RootV1 {
        &self.expected_image_id
    }

    pub fn module_journal_root(&self) -> &RootV1 {
        &self.module_journal_root
    }

    pub fn module_journal_digest(&self) -> &RootV1 {
        &self.module_journal_digest
    }

    pub fn statement_root(&self) -> &RootV1 {
        &self.statement_root
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn receipt_digest(&self) -> &RootV1 {
        &self.receipt_digest
    }

    pub fn receipt_kind(&self) -> ReceiptKindV1 {
        self.receipt_kind
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "verified-lane-module-transition-v1",
            &VerifiedLaneModuleTransitionContentV1 {
                schema: VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1,
                authenticated_command_binding_root: &self.authenticated_command_binding_root,
                release_route_binding_root: &self.release_route_binding_root,
                expected_image_id: &self.expected_image_id,
                module_journal_root: &self.module_journal_root,
                module_journal_digest: &self.module_journal_digest,
                statement_root: &self.statement_root,
                command_occurrence_id: &self.command_occurrence_id,
                receipt_digest: &self.receipt_digest,
                receipt_kind: self.receipt_kind,
            },
        )
    }
}

fn sha256_root_v1(bytes: &[u8], field: &'static str) -> AbiResultV1<RootV1> {
    RootV1::parse(format!("0x{}", hash_bytes_sha256_v1(bytes)), field, false)
}

struct ReboundLaneModuleReceiptCandidateV1<'a> {
    lanes: &'a LaneRegistryV1,
    authenticated_command_binding_root: RootV1,
    module_journal: &'a LaneModuleTransitionJournalV1,
    release_route_binding: &'a ReleaseRouteBoundLaneTransitionV1,
    rebound: ReleaseRouteBoundLaneTransitionV1,
    receipt: LaneModuleReceiptEnvelopeV1<'a>,
}

fn verify_rebound_module_receipt_v1(
    candidate: ReboundLaneModuleReceiptCandidateV1<'_>,
    receipt_verifier: &dyn LaneModuleSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedLaneModuleTransitionV1> {
    if candidate.release_route_binding.binding_root()? != candidate.rebound.binding_root()? {
        return Err(AbiErrorV1::InvalidBinding("lane module structural binding"));
    }
    if candidate.receipt.receipt_kind != ReceiptKindV1::SUCCINCT {
        return Err(AbiErrorV1::InvalidBinding("lane module receipt kind"));
    }
    if candidate.receipt.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBounds("lane module receipt bytes"));
    }

    let release = candidate
        .lanes
        .release_for(candidate.rebound.lane_id())
        .ok_or(AbiErrorV1::InvalidBinding("lane module verified release"))?;
    if &release.release_id != candidate.rebound.module_release_id() {
        return Err(AbiErrorV1::InvalidBinding("lane module verified release"));
    }
    if release.status != ReleaseStatusV1::ACTIVE_NEW || !release.accepts_new_objects {
        return Err(AbiErrorV1::InvalidBinding(
            "lane module release is not active new",
        ));
    }

    candidate.module_journal.validate()?;
    let journal_bytes = canonical_bytes_v1(candidate.module_journal)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("lane module canonical journal bytes"))?;
    if journal_len > release.max_journal_bytes {
        return Err(AbiErrorV1::InvalidBounds(
            "lane module canonical journal bytes",
        ));
    }
    let module_journal_digest =
        sha256_root_v1(&journal_bytes, "lane module canonical journal digest")?;
    let receipt_digest = sha256_root_v1(
        candidate.receipt.receipt_bytes,
        "lane module receipt digest",
    )?;
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        &release.guest_image_id,
        &journal_bytes,
    )?;

    Ok(VerifiedLaneModuleTransitionV1 {
        authenticated_command_binding_root: candidate.authenticated_command_binding_root,
        release_route_binding_root: candidate.rebound.binding_root()?,
        expected_image_id: release.guest_image_id.clone(),
        module_journal_root: candidate.rebound.module_journal_root().clone(),
        module_journal_digest,
        statement_root: candidate.rebound.statement_root().clone(),
        command_occurrence_id: candidate.rebound.command_occurrence_id().clone(),
        receipt_digest,
        receipt_kind: candidate.receipt.receipt_kind,
    })
}

pub fn verify_asset_transfer_lane_module_receipt_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1<'_>,
    receipt_verifier: &dyn LaneModuleSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedLaneModuleTransitionV1> {
    let occurrence = candidate.authenticated_command.occurrence();
    let rebound = bind_asset_transfer_lane_output_to_release_route_v1(
        candidate.profile,
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
        occurrence,
        candidate.module_input,
        candidate.accepted,
    )?;
    verify_rebound_module_receipt_v1(
        ReboundLaneModuleReceiptCandidateV1 {
            lanes: candidate.lanes,
            authenticated_command_binding_root: candidate.authenticated_command.binding_root()?,
            module_journal: &candidate.accepted.module_journal,
            release_route_binding: candidate.release_route_binding,
            rebound,
            receipt: candidate.receipt,
        },
        receipt_verifier,
    )
}

pub fn verify_managed_asset_lifecycle_lane_module_receipt_v1(
    candidate: ManagedAssetLifecycleLaneModuleReceiptCandidateV1<'_>,
    receipt_verifier: &dyn LaneModuleSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedLaneModuleTransitionV1> {
    let occurrence = candidate.authenticated_command.occurrence();
    let rebound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        ManagedAssetLifecycleReleaseRouteBindingCandidateV1 {
            profile: candidate.profile,
            policy_registry: candidate.policy_registry,
            asset_policy_registry: candidate.asset_policy_registry,
            lanes: candidate.lanes,
            coordinators: candidate.coordinators,
            routes: candidate.routes,
            occurrence,
            module_input: candidate.module_input,
            accepted: candidate.accepted,
        },
    )?;
    verify_rebound_module_receipt_v1(
        ReboundLaneModuleReceiptCandidateV1 {
            lanes: candidate.lanes,
            authenticated_command_binding_root: candidate.authenticated_command.binding_root()?,
            module_journal: &candidate.accepted.module_journal,
            release_route_binding: candidate.release_route_binding,
            rebound,
            receipt: candidate.receipt,
        },
        receipt_verifier,
    )
}

pub fn verify_perps_margin_lane_module_receipt_v1(
    candidate: PerpsMarginLaneModuleReceiptCandidateV1<'_>,
    receipt_verifier: &dyn LaneModuleSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedLaneModuleTransitionV1> {
    let occurrence = candidate.authenticated_command.occurrence();
    let rebound = bind_perps_margin_lane_output_to_release_route_v1(
        PerpsMarginReleaseRouteBindingCandidateV1 {
            profile: candidate.profile,
            policy_registry: candidate.policy_registry,
            market_policy: candidate.market_policy,
            lanes: candidate.lanes,
            coordinators: candidate.coordinators,
            routes: candidate.routes,
            occurrence,
            module_input: candidate.module_input,
            accepted: candidate.accepted,
            verified_price: candidate.verified_price,
        },
    )?;
    let expected = recompute_perps_margin_accepted_v1(candidate.module_input, candidate.accepted)?;
    verify_rebound_module_receipt_v1(
        ReboundLaneModuleReceiptCandidateV1 {
            lanes: candidate.lanes,
            authenticated_command_binding_root: candidate.authenticated_command.binding_root()?,
            module_journal: &expected.module_journal,
            release_route_binding: candidate.release_route_binding,
            rebound,
            receipt: candidate.receipt,
        },
        receipt_verifier,
    )
}
