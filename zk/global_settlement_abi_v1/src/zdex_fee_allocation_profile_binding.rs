use crate::canonical::{AbiErrorV1, AbiResultV1, RootV1};
use crate::release::{
    EconomicPolicyBindingV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1,
    LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1,
    LaneRegistryV1, ProfileStatusV1, ReleaseStatusV1, RouteRegistryV1, RouteReleaseV1,
};
use crate::zdex_fee_allocation_types::{
    zdex_fee_allocation_port_schema_root_v1, FEE_ALLOCATION_OUTPUT_ROLE_V1,
    PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1, ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
};
use crate::zdex_purchase_burn_types::{
    zdex_amm_purchase_port_schema_root_v1, zdex_burn_port_schema_root_v1,
    AMM_PURCHASE_OUTPUT_ROLE_V1, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, ZDEX_BURN_INPUT_ROLE_V1,
};

pub struct GovernedZDEXFeeAllocationProfileV1<'a> {
    pub(crate) profile: &'a EconomicProfileSnapshotV1,
    pub(crate) allocation_route: &'a RouteReleaseV1,
    pub(crate) buyback_route: &'a RouteReleaseV1,
    pub(crate) module_release: &'a LaneModuleReleaseV1,
    pub(crate) coordinator_release: &'a LaneCoordinatorReleaseV1,
    pub(crate) policy_binding: &'a EconomicPolicyBindingV1,
}

impl GovernedZDEXFeeAllocationProfileV1<'_> {
    pub(crate) fn profile(&self) -> &EconomicProfileSnapshotV1 {
        self.profile
    }

    pub(crate) fn allocation_route(&self) -> &RouteReleaseV1 {
        self.allocation_route
    }

    pub(crate) fn buyback_route(&self) -> &RouteReleaseV1 {
        self.buyback_route
    }

    pub(crate) fn module_release(&self) -> &LaneModuleReleaseV1 {
        self.module_release
    }

    pub(crate) fn coordinator_release(&self) -> &LaneCoordinatorReleaseV1 {
        self.coordinator_release
    }

    pub(crate) fn policy_binding(&self) -> &EconomicPolicyBindingV1 {
        self.policy_binding
    }
}

pub struct ZDEXFeeAllocationProfileRegistriesV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub policy_registry: &'a EconomicPolicyRegistryV1,
}

fn registered_route_v1<'a>(
    routes: &'a RouteRegistryV1,
    command_kind: &str,
) -> AbiResultV1<&'a RouteReleaseV1> {
    routes
        .routes
        .iter()
        .find(|route| route.command_kind == command_kind)
        .ok_or(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation governed route absent",
        ))
}

pub fn bind_zdex_fee_allocation_shadow_profile_v1<'a>(
    expected_profile_id: &RootV1,
    expected_authority_epoch: u64,
    registries: ZDEXFeeAllocationProfileRegistriesV1<'a>,
) -> AbiResultV1<GovernedZDEXFeeAllocationProfileV1<'a>> {
    let ZDEXFeeAllocationProfileRegistriesV1 {
        profile,
        lanes,
        coordinators,
        routes,
        policy_registry,
    } = registries;
    profile.validate()?;
    if &profile.profile_id != expected_profile_id {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation expected profile",
        ));
    }
    if profile.authority_epoch != expected_authority_epoch {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation expected authority epoch",
        ));
    }
    if profile.status != ProfileStatusV1::SHADOW {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation profile status",
        ));
    }
    profile.validate_registries(lanes, coordinators, routes)?;
    if profile.policy_registry_root != policy_registry.registry_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation policy registry",
        ));
    }
    let module_release =
        lanes
            .release_for(LaneIdV1::ZDEX_TOKENOMICS)
            .ok_or(AbiErrorV1::InvalidBinding(
                "ZDEX fee-allocation module release absent",
            ))?;
    let coordinator_release =
        coordinators
            .release_for(LaneIdV1::ZDEX_TOKENOMICS)
            .ok_or(AbiErrorV1::InvalidBinding(
                "ZDEX fee-allocation coordinator release absent",
            ))?;
    let governed = GovernedZDEXFeeAllocationProfileV1 {
        profile,
        allocation_route: registered_route_v1(routes, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1)?,
        buyback_route: registered_route_v1(routes, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)?,
        module_release,
        coordinator_release,
        policy_binding: policy_registry.require_binding(
            ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
            PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        )?,
    };
    require_release_shapes_v1(&governed)?;
    Ok(governed)
}

fn require_release_shapes_v1(governed: &GovernedZDEXFeeAllocationProfileV1<'_>) -> AbiResultV1<()> {
    let allocation = governed.allocation_route;
    let buyback = governed.buyback_route;
    let module = governed.module_release;
    let coordinator = governed.coordinator_release;
    allocation.validate()?;
    buyback.validate()?;
    module.validate()?;
    coordinator.validate()?;
    if allocation.status != ReleaseStatusV1::SHADOW
        || allocation.accepts_new_objects
        || allocation.command_kind != PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
        || allocation.ordered_lanes != [LaneIdV1::ZDEX_TOKENOMICS]
        || allocation.module_release_ids != [module.release_id.clone()]
        || allocation.dependency_roles != [FEE_ALLOCATION_OUTPUT_ROLE_V1.to_owned()]
        || allocation.port_schema_roots != [zdex_fee_allocation_port_schema_root_v1()?]
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation route shape",
        ));
    }
    if buyback.status != ReleaseStatusV1::SHADOW
        || buyback.accepts_new_objects
        || buyback.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        || buyback.ordered_lanes != [LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS]
        || buyback.module_release_ids.get(1) != Some(&module.release_id)
        || buyback.dependency_roles
            != [
                AMM_PURCHASE_OUTPUT_ROLE_V1.to_owned(),
                ZDEX_BURN_INPUT_ROLE_V1.to_owned(),
            ]
        || buyback.port_schema_roots
            != [
                zdex_amm_purchase_port_schema_root_v1()?,
                zdex_burn_port_schema_root_v1()?,
            ]
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX authorized buyback route shape",
        ));
    }
    if module.status != ReleaseStatusV1::SHADOW
        || module.accepts_new_objects
        || module.lane_id != LaneIdV1::ZDEX_TOKENOMICS
        || !module
            .command_variants
            .iter()
            .any(|command| command == PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1)
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation module release shape",
        ));
    }
    if coordinator.status != ReleaseStatusV1::SHADOW
        || coordinator.accepts_new_objects
        || coordinator.lane_id != LaneIdV1::ZDEX_TOKENOMICS
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation coordinator release shape",
        ));
    }
    Ok(())
}
