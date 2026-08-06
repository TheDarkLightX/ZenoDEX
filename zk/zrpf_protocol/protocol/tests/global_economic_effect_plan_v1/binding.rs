use super::support::*;
use zenodex_zrpf_protocol_v3::StateBoundEconomicCommandOccurrenceV1;

fn state_bound<'a>(
    fixture: &'a crate::profile_support::EconomicRegistryFixture,
    state: &'a GlobalEconomicStateV1,
    occurrence: &'a EconomicCommandOccurrenceV1,
) -> StateBoundEconomicCommandOccurrenceV1<'a> {
    let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
        &fixture.profile,
        &fixture.route_registry,
        occurrence,
    )
    .unwrap();
    let profile_state = bind_global_economic_state_to_profile_v1(
        state,
        &fixture.profile,
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    )
    .unwrap();
    bind_profile_bound_occurrence_to_global_state_v1(profile_occurrence, profile_state, &[])
        .unwrap()
}

fn plan_for(
    fixture: &crate::profile_support::EconomicRegistryFixture,
    state: &GlobalEconomicStateV1,
    occurrence: &EconomicCommandOccurrenceV1,
    body: GlobalEconomicEffectBodyV1,
) -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1::new(plan_input(
        body,
        state.content().application_id(),
        state.content().chain_or_domain_id(),
        fixture.profile.profile_id(),
        fixture.profile.content().writer_epoch(),
        occurrence.occurrence_id(),
        occurrence.content().route_release_id(),
        GlobalEconomicStateRootV1::new(state.state_root().into_bytes()).unwrap(),
    ))
    .unwrap()
}

fn transfer_body_with_grant(grant_id: CommitmentV3) -> GlobalEconomicEffectBodyV1 {
    transfer_body(
        5,
        vec![GlobalEconomicEffectRowV1::occurrence_consumption(
            GlobalOccurrenceConsumptionKindV1::AuthorizationGrantSpend,
            grant_id,
        )
        .unwrap()],
    )
}

#[test]
fn exact_plan_action_state_and_replay_rows_construct_an_opaque_witness() {
    // Arrange
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let provisional = transfer_body_with_grant(root(90));
    let action = authorized_action(&fixture, &state, provisional.effect_commitment(), vec![]);
    let final_body = transfer_body(5, vec![grant_spend_row(&action)]);
    assert_eq!(
        provisional.effect_commitment(),
        final_body.effect_commitment()
    );
    let occurrence = occurrence(&fixture, action);
    let bound_occurrence = state_bound(&fixture, &state, &occurrence);
    let plan = plan_for(&fixture, &state, &occurrence, final_body);

    // Act
    let bound =
        bind_global_economic_effect_plan_to_occurrence_v1(&plan, &bound_occurrence).unwrap();

    // Assert
    assert_eq!(bound.plan(), &plan);
    assert_eq!(bound.occurrence().global_state(), &state);
}

#[test]
fn envelope_binding_fields_reject_independently() {
    // Arrange
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let provisional = transfer_body_with_grant(root(90));
    let action = authorized_action(&fixture, &state, provisional.effect_commitment(), vec![]);
    let body = transfer_body(5, vec![grant_spend_row(&action)]);
    let occurrence = occurrence(&fixture, action);
    let bound_occurrence = state_bound(&fixture, &state, &occurrence);
    let base = |body| {
        plan_input(
            body,
            state.content().application_id(),
            state.content().chain_or_domain_id(),
            fixture.profile.profile_id(),
            fixture.profile.content().writer_epoch(),
            occurrence.occurrence_id(),
            occurrence.content().route_release_id(),
            GlobalEconomicStateRootV1::new(state.state_root().into_bytes()).unwrap(),
        )
    };
    let mut cases = Vec::new();
    let mut application = base(body.clone());
    application.application_id = application_id(99);
    cases.push((
        application,
        GlobalEconomicEffectPlanErrorV1::ApplicationMismatch,
    ));
    let mut domain = base(body.clone());
    domain.chain_or_domain_id = domain_id(99);
    cases.push((domain, GlobalEconomicEffectPlanErrorV1::DomainMismatch));
    let mut profile = base(body.clone());
    profile.profile_id = EconomicProfileIdV1::new(root(99).into_bytes()).unwrap();
    cases.push((profile, GlobalEconomicEffectPlanErrorV1::ProfileMismatch));
    let mut writer = base(body.clone());
    writer.writer_epoch += 1;
    cases.push((writer, GlobalEconomicEffectPlanErrorV1::WriterEpochMismatch));
    let mut occurrence_id = base(body.clone());
    occurrence_id.occurrence_id =
        EconomicCommandOccurrenceIdV1::new(root(99).into_bytes()).unwrap();
    cases.push((
        occurrence_id,
        GlobalEconomicEffectPlanErrorV1::OccurrenceMismatch,
    ));
    let mut route = base(body.clone());
    route.route_release_id = RouteReleaseIdV1::new(root(99).into_bytes()).unwrap();
    cases.push((route, GlobalEconomicEffectPlanErrorV1::RouteMismatch));
    let mut pre_state = base(body);
    pre_state.pre_state_root = state_root(99);
    cases.push((pre_state, GlobalEconomicEffectPlanErrorV1::PreStateMismatch));

    // Act
    let actual = cases
        .into_iter()
        .map(|(input, expected)| {
            let plan = GlobalEconomicEffectPlanV1::new(input).unwrap();
            (
                rejection(bind_global_economic_effect_plan_to_occurrence_v1(
                    &plan,
                    &bound_occurrence,
                )),
                expected,
            )
        })
        .collect::<Vec<_>>();

    // Assert
    assert!(actual
        .into_iter()
        .all(|(actual, expected)| actual == expected));
}

#[test]
fn semantic_effect_commitment_rejects_mutated_amounts() {
    // Arrange
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let original = transfer_body_with_grant(root(90));
    let action = authorized_action(&fixture, &state, original.effect_commitment(), vec![]);
    let mutated = transfer_body(6, vec![grant_spend_row(&action)]);
    let occurrence = occurrence(&fixture, action);
    let bound_occurrence = state_bound(&fixture, &state, &occurrence);
    let plan = plan_for(&fixture, &state, &occurrence, mutated);

    // Act / Assert
    assert_eq!(
        rejection(bind_global_economic_effect_plan_to_occurrence_v1(
            &plan,
            &bound_occurrence
        )),
        GlobalEconomicEffectPlanErrorV1::EffectCommitmentMismatch
    );
}

fn issue_body(
    binding: ActionAuthorizationBindingIdV1,
    grant_id: CommitmentV3,
) -> GlobalEconomicEffectBodyV1 {
    let asset = root(10);
    let issue = GlobalEconomicEffectRowV1::issue_burn(GlobalIssueBurnInputV1 {
        lane_id: EconomicLaneIdV1::ZusdMonetary,
        asset_id: asset,
        kind: GlobalIssueBurnKindV1::Issue,
        bucket_id: root(20),
        amount_atoms: 1,
        authority_scope_id: AuthorizationScopeIdV1::new([4; 32]).unwrap(),
        action_authorization_binding: binding,
    })
    .unwrap();
    let grant = GlobalEconomicEffectRowV1::occurrence_consumption(
        GlobalOccurrenceConsumptionKindV1::AuthorizationGrantSpend,
        grant_id,
    )
    .unwrap();
    GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(202),
        effects: vec![issue, grant],
        reconciliations: vec![reconciliation(asset, 10, 11, 10, 11, 0, 0, 0, 0)],
    })
    .unwrap()
}

#[test]
fn authorization_rows_bind_exact_action_scope_and_binding_before_route_policy() {
    // Arrange
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let wrong_binding = ActionAuthorizationBindingIdV1::new([9; 32]).unwrap();
    let provisional = issue_body(wrong_binding, root(90));
    let action = authorized_action(&fixture, &state, provisional.effect_commitment(), vec![]);
    let wrong = issue_body(
        wrong_binding,
        CommitmentV3::new(action.authorization_grant_spend().unwrap().into_bytes()).unwrap(),
    );
    let occurrence = occurrence(&fixture, action);
    let bound_occurrence = state_bound(&fixture, &state, &occurrence);
    let plan = plan_for(&fixture, &state, &occurrence, wrong);

    // Act / Assert
    assert_eq!(
        rejection(bind_global_economic_effect_plan_to_occurrence_v1(
            &plan,
            &bound_occurrence
        )),
        GlobalEconomicEffectPlanErrorV1::AuthorizationMismatch
    );
}

#[test]
fn governed_route_issue_burn_policy_rejects_forbidden_issue_rows() {
    // Arrange
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let provisional = issue_body(
        ActionAuthorizationBindingIdV1::new([9; 32]).unwrap(),
        root(90),
    );
    let action = authorized_action(&fixture, &state, provisional.effect_commitment(), vec![]);
    let final_body = issue_body(
        action.action_authorization_binding().unwrap(),
        CommitmentV3::new(action.authorization_grant_spend().unwrap().into_bytes()).unwrap(),
    );
    let occurrence = occurrence(&fixture, action);
    let bound_occurrence = state_bound(&fixture, &state, &occurrence);
    let plan = plan_for(&fixture, &state, &occurrence, final_body);

    // Act / Assert
    assert_eq!(
        rejection(bind_global_economic_effect_plan_to_occurrence_v1(
            &plan,
            &bound_occurrence
        )),
        GlobalEconomicEffectPlanErrorV1::IssueBurnPolicyMismatch
    );
}

#[test]
fn consumed_objects_and_grant_spend_are_exact_replay_rows() {
    // Arrange
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let provisional = transfer_body_with_grant(root(90));
    let action = authorized_action(&fixture, &state, provisional.effect_commitment(), vec![]);
    let correct_grant = grant_spend_row(&action);
    let wrong_object_body = transfer_body(
        5,
        vec![
            correct_grant.clone(),
            GlobalEconomicEffectRowV1::occurrence_consumption(
                GlobalOccurrenceConsumptionKindV1::ConsumedObject,
                root(91),
            )
            .unwrap(),
        ],
    );
    let wrong_grant_body = transfer_body_with_grant(root(92));
    let occurrence = occurrence(&fixture, action);
    let bound_occurrence = state_bound(&fixture, &state, &occurrence);
    let object_plan = plan_for(&fixture, &state, &occurrence, wrong_object_body);
    let grant_plan = plan_for(&fixture, &state, &occurrence, wrong_grant_body);

    // Act / Assert
    assert_eq!(
        rejection(bind_global_economic_effect_plan_to_occurrence_v1(
            &object_plan,
            &bound_occurrence
        )),
        GlobalEconomicEffectPlanErrorV1::ConsumedObjectMismatch
    );
    assert_eq!(
        rejection(bind_global_economic_effect_plan_to_occurrence_v1(
            &grant_plan,
            &bound_occurrence
        )),
        GlobalEconomicEffectPlanErrorV1::AuthorizationGrantSpendMismatch
    );
}
