pub use crate::state_support::{application_id, domain_id, fixture, root, state_for_fixture};
pub use zenodex_zrpf_protocol_v3::{
    bind_economic_command_occurrence_to_active_profile_v1,
    bind_global_economic_effect_plan_to_occurrence_v1, bind_global_economic_state_to_profile_v1,
    bind_profile_bound_occurrence_to_global_state_v1, decode_exact_global_economic_effect_plan_v1,
    encode_global_economic_effect_plan_v1, ActionAuthorizationBindingIdV1, ApplicationIdV3,
    AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
    AuthorizedEconomicActionV1, CommitmentV3, DomainIdV3, EconomicActionRecordInputV1,
    EconomicActionRecordV1, EconomicActionTypeIdV1, EconomicCommandOccurrenceContentV1,
    EconomicCommandOccurrenceIdV1, EconomicCommandOccurrenceV1, EconomicLaneIdV1,
    EconomicOccurrencePositionV1, EconomicProfileIdV1, GlobalAccountMovementInputV1,
    GlobalAssetReconciliationInputV1, GlobalAssetReconciliationV1, GlobalCustodyEffectInputV1,
    GlobalEconomicEffectBodyInputV1, GlobalEconomicEffectBodyV1, GlobalEconomicEffectKindV1,
    GlobalEconomicEffectPlanErrorV1, GlobalEconomicEffectPlanInputV1, GlobalEconomicEffectPlanV1,
    GlobalEconomicEffectRowV1, GlobalEconomicStateRootV1, GlobalEconomicStateV1,
    GlobalExternalOutboxInputV1, GlobalFeeEffectInputV1, GlobalIssueBurnInputV1,
    GlobalIssueBurnKindV1, GlobalLiabilityEffectInputV1, GlobalOccurrenceConsumptionKindV1,
    GlobalReserveEffectInputV1, GlobalRewardSlashInputV1, GlobalRewardSlashKindV1,
    RouteReleaseIdV1,
};

pub fn state_root(seed: u16) -> GlobalEconomicStateRootV1 {
    GlobalEconomicStateRootV1::new(root(seed).into_bytes()).unwrap()
}

// The fixture exposes every reconciliation axis so BVA tests can perturb one
// quantity without hiding it behind a preset.
#[allow(clippy::too_many_arguments)]
pub fn reconciliation(
    asset_id: CommitmentV3,
    owned_pre: u128,
    owned_post: u128,
    supply_pre: u128,
    supply_post: u128,
    liabilities_pre: u128,
    liabilities_post: u128,
    reserves_pre: u128,
    reserves_post: u128,
) -> GlobalAssetReconciliationV1 {
    GlobalAssetReconciliationV1::new(GlobalAssetReconciliationInputV1 {
        asset_id,
        owned_and_custodied_pre_atoms: owned_pre,
        owned_and_custodied_post_atoms: owned_post,
        supply_pre_atoms: supply_pre,
        supply_post_atoms: supply_post,
        liabilities_pre_atoms: liabilities_pre,
        liabilities_post_atoms: liabilities_post,
        named_reserves_pre_atoms: reserves_pre,
        named_reserves_post_atoms: reserves_post,
    })
}

pub fn transfer_row(asset_id: CommitmentV3, amount: u128) -> GlobalEconomicEffectRowV1 {
    GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        asset_id,
        source_id: root(20),
        destination_id: root(21),
        amount_atoms: amount,
    })
    .unwrap()
}

pub fn transfer_body(
    amount: u128,
    extra_rows: Vec<GlobalEconomicEffectRowV1>,
) -> GlobalEconomicEffectBodyV1 {
    let asset = root(10);
    let mut effects = vec![transfer_row(asset, amount)];
    effects.extend(extra_rows);
    GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(202),
        effects,
        reconciliations: vec![reconciliation(
            asset, amount, amount, amount, amount, 0, 0, 0, 0,
        )],
    })
    .unwrap()
}

// The fixture exposes every envelope binding so mismatch tests can perturb one
// authority field at a time.
#[allow(clippy::too_many_arguments)]
pub fn plan_input(
    body: GlobalEconomicEffectBodyV1,
    application_id: ApplicationIdV3,
    domain_id: DomainIdV3,
    profile_id: EconomicProfileIdV1,
    writer_epoch: u64,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    route_release_id: RouteReleaseIdV1,
    pre_state_root: GlobalEconomicStateRootV1,
) -> GlobalEconomicEffectPlanInputV1 {
    GlobalEconomicEffectPlanInputV1 {
        application_id,
        chain_or_domain_id: domain_id,
        profile_id,
        writer_epoch,
        occurrence_id,
        route_release_id,
        pre_state_root,
        body,
    }
}

pub fn authorized_action(
    fixture: &crate::profile_support::EconomicRegistryFixture,
    state: &GlobalEconomicStateV1,
    effect_commitment: CommitmentV3,
    consumed_object_ids: Vec<CommitmentV3>,
) -> AuthorizedEconomicActionV1 {
    let route = &fixture.route_registry.routes()[0];
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: state.content().application_id(),
        chain_or_domain_id: state.content().chain_or_domain_id(),
        action_type_id: EconomicActionTypeIdV1::new(
            route.content().command_variant_root().into_bytes(),
        )
        .unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([3; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([4; 32]).unwrap(),
        authorization_nonce: 17,
        valid_from_epoch: 0,
        valid_through_epoch: u64::MAX,
        pre_state_root: CommitmentV3::new(state.state_root().into_bytes()).unwrap(),
        action_semantics_hash: root(6),
        effect_commitment,
        consumed_object_ids,
    })
    .unwrap();
    AuthorizedEconomicActionV1::new(record, AuthorizationGrantIdV1::new([8; 32]).unwrap()).unwrap()
}

pub fn occurrence(
    fixture: &crate::profile_support::EconomicRegistryFixture,
    action: AuthorizedEconomicActionV1,
) -> EconomicCommandOccurrenceV1 {
    let route = &fixture.route_registry.routes()[0];
    EconomicCommandOccurrenceV1::new(
        EconomicCommandOccurrenceContentV1::new(
            EconomicOccurrencePositionV1::new(500, 7, 11),
            fixture.profile.profile_id(),
            fixture.profile.content().writer_epoch(),
            route.route_release_id(),
            action,
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn grant_spend_row(action: &AuthorizedEconomicActionV1) -> GlobalEconomicEffectRowV1 {
    GlobalEconomicEffectRowV1::occurrence_consumption(
        GlobalOccurrenceConsumptionKindV1::AuthorizationGrantSpend,
        CommitmentV3::new(action.authorization_grant_spend().unwrap().into_bytes()).unwrap(),
    )
    .unwrap()
}

pub fn rejection<T>(
    result: Result<T, GlobalEconomicEffectPlanErrorV1>,
) -> GlobalEconomicEffectPlanErrorV1 {
    match result {
        Ok(_) => panic!("expected typed rejection"),
        Err(error) => error,
    }
}
