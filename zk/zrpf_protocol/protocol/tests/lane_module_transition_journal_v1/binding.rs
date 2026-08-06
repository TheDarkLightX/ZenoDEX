use super::support::*;
use zenodex_zrpf_protocol_v3::{LaneModuleReleaseIdV1, LaneModuleReleaseStatusV1};

#[test]
fn exact_accepted_journal_binds_route_release_plan_and_openings() {
    // Arrange
    let fixture = accepted_fixture(2);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let bound_plan =
        bind_global_economic_effect_plan_to_occurrence_v1(&fixture.plan, &bound_occurrence)
            .unwrap();

    // Act
    let bound = bind_accepted_lane_module_transition_journal_v1(
        &fixture.journal,
        &bound_plan,
        &fixture.state_transition,
    )
    .unwrap();

    // Assert
    assert_eq!(bound.journal(), &fixture.journal);
    assert_eq!(
        bound.module_release().release_id(),
        fixture.journal.module_release_id()
    );
    assert_eq!(
        bound.route_dependency().module_release_id(),
        fixture.journal.module_release_id()
    );
}

#[test]
fn plan_lane_writes_must_equal_authenticated_openings_atom_for_atom() {
    // Arrange
    let fixture = accepted_fixture_with_write_mutation(2, true);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let bound_plan =
        bind_global_economic_effect_plan_to_occurrence_v1(&fixture.plan, &bound_occurrence)
            .unwrap();

    // Act
    let error = rejection(bind_accepted_lane_module_transition_journal_v1(
        &fixture.journal,
        &bound_plan,
        &fixture.state_transition,
    ));

    // Assert
    assert_eq!(error, LaneModuleTransitionJournalErrorV1::LaneWriteMismatch);
}

#[test]
fn occurrence_envelope_fields_reject_independently() {
    // Arrange
    let fixture = accepted_fixture(1);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let outcome = fixture.journal.outcome();
    let base = || {
        journal_input(
            &fixture.registries,
            &fixture.state,
            &fixture.occurrence,
            outcome,
        )
    };
    let mut application = base();
    application.application_id = application_id(99);
    let mut domain = base();
    domain.chain_or_domain_id = domain_id(99);
    let mut profile = base();
    profile.profile_id = EconomicProfileIdV1::new(root(99).into_bytes()).unwrap();
    let mut writer = base();
    writer.writer_epoch += 1;
    let mut occurrence = base();
    occurrence.occurrence_id = EconomicCommandOccurrenceIdV1::new(root(99).into_bytes()).unwrap();
    let mut route = base();
    route.route_release_id = RouteReleaseIdV1::new(root(99).into_bytes()).unwrap();
    let mut action = base();
    action.economic_action_id = EconomicActionIdV1::new(root(99).into_bytes()).unwrap();
    let mut global_pre = base();
    global_pre.global_pre_state_root = state_root(99);
    let mut lane_pre = base();
    lane_pre.lane_pre_state_root = root(99);
    let cases = vec![
        (
            application,
            LaneModuleTransitionJournalErrorV1::ApplicationMismatch,
        ),
        (domain, LaneModuleTransitionJournalErrorV1::DomainMismatch),
        (profile, LaneModuleTransitionJournalErrorV1::ProfileMismatch),
        (
            writer,
            LaneModuleTransitionJournalErrorV1::WriterEpochMismatch,
        ),
        (
            occurrence,
            LaneModuleTransitionJournalErrorV1::OccurrenceMismatch,
        ),
        (route, LaneModuleTransitionJournalErrorV1::RouteMismatch),
        (
            action,
            LaneModuleTransitionJournalErrorV1::EconomicActionMismatch,
        ),
        (
            global_pre,
            LaneModuleTransitionJournalErrorV1::GlobalPreStateMismatch,
        ),
        (
            lane_pre,
            LaneModuleTransitionJournalErrorV1::LanePreStateMismatch,
        ),
    ];

    // Act
    let actual = cases
        .into_iter()
        .map(|(input, expected)| {
            let journal = LaneModuleTransitionJournalV1::new(input).unwrap();
            (
                rejection(bind_rejected_lane_module_transition_journal_v1(
                    &journal,
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
fn release_and_route_metadata_are_derived_from_the_profile() {
    // Arrange
    let fixture = accepted_fixture(1);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let outcome = LaneModuleTransitionOutcomeV1::Rejected(LaneModuleRejectCodeV1::new(41).unwrap());
    let base = || {
        journal_input(
            &fixture.registries,
            &fixture.state,
            &fixture.occurrence,
            outcome,
        )
    };
    let mut release = base();
    release.module_release_id = LaneModuleReleaseIdV1::new(root(99).into_bytes()).unwrap();
    let mut image = base();
    image.guest_image_id = ProgramIdV3::new(root(99).into_bytes()).unwrap();
    let mut state_schema = base();
    state_schema.state_schema_root = root(99);
    let mut command_schema = base();
    command_schema.command_schema_root = root(99);
    let mut effect_schema = base();
    effect_schema.effect_schema_root = root(99);
    let mut private_schema = base();
    private_schema.private_port_schema_root = root(99);
    let mut variants = base();
    variants.command_variants_root = root(99);
    let mut spec = base();
    spec.spec_root = root(99);
    let mut source = base();
    source.source_root = root(99);
    let mut toolchain = base();
    toolchain.toolchain_root = root(99);
    let mut journal_schema = base();
    journal_schema.receipt_journal_schema_root = root(99);
    let mut input_schema = base();
    input_schema.input_port_schema_root = root(99);
    let mut output_schema = base();
    output_schema.output_port_schema_root = root(99);
    let cases = vec![
        (
            release,
            LaneModuleTransitionJournalErrorV1::ModuleReleaseMismatch,
        ),
        (
            image,
            LaneModuleTransitionJournalErrorV1::GuestImageMismatch,
        ),
        (
            state_schema,
            LaneModuleTransitionJournalErrorV1::StateSchemaMismatch,
        ),
        (
            command_schema,
            LaneModuleTransitionJournalErrorV1::CommandSchemaMismatch,
        ),
        (
            effect_schema,
            LaneModuleTransitionJournalErrorV1::EffectSchemaMismatch,
        ),
        (
            private_schema,
            LaneModuleTransitionJournalErrorV1::PrivatePortSchemaMismatch,
        ),
        (
            variants,
            LaneModuleTransitionJournalErrorV1::CommandVariantsMismatch,
        ),
        (spec, LaneModuleTransitionJournalErrorV1::SpecRootMismatch),
        (
            source,
            LaneModuleTransitionJournalErrorV1::SourceRootMismatch,
        ),
        (
            toolchain,
            LaneModuleTransitionJournalErrorV1::ToolchainRootMismatch,
        ),
        (
            journal_schema,
            LaneModuleTransitionJournalErrorV1::JournalSchemaMismatch,
        ),
        (
            input_schema,
            LaneModuleTransitionJournalErrorV1::InputPortSchemaMismatch,
        ),
        (
            output_schema,
            LaneModuleTransitionJournalErrorV1::OutputPortSchemaMismatch,
        ),
    ];

    // Act
    let actual = cases
        .into_iter()
        .map(|(input, expected)| {
            let journal = LaneModuleTransitionJournalV1::new(input).unwrap();
            (
                rejection(bind_rejected_lane_module_transition_journal_v1(
                    &journal,
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
fn exact_rejection_binds_without_an_effect_plan_or_state_opening() {
    // Arrange
    let fixture = accepted_fixture(1);
    let journal = rejected_journal(&fixture);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);

    // Act
    let bound =
        bind_rejected_lane_module_transition_journal_v1(&journal, &bound_occurrence).unwrap();

    // Assert
    assert_eq!(bound.journal(), &journal);
    assert!(matches!(
        journal.outcome(),
        LaneModuleTransitionOutcomeV1::Rejected(_)
    ));
}

#[test]
fn accepted_and_rejected_binders_are_outcome_disjoint() {
    // Arrange
    let fixture = accepted_fixture(1);
    let rejected = rejected_journal(&fixture);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let bound_plan =
        bind_global_economic_effect_plan_to_occurrence_v1(&fixture.plan, &bound_occurrence)
            .unwrap();

    // Act
    let accepted_as_rejected = rejection(bind_rejected_lane_module_transition_journal_v1(
        &fixture.journal,
        &bound_occurrence,
    ));
    let rejected_as_accepted = rejection(bind_accepted_lane_module_transition_journal_v1(
        &rejected,
        &bound_plan,
        &fixture.state_transition,
    ));

    // Assert
    assert_eq!(
        accepted_as_rejected,
        LaneModuleTransitionJournalErrorV1::OutcomeMismatch
    );
    assert_eq!(
        rejected_as_accepted,
        LaneModuleTransitionJournalErrorV1::OutcomeMismatch
    );
}

#[test]
fn a_lane_absent_from_the_governed_route_cannot_bind() {
    // Arrange
    let fixture = accepted_fixture(1);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let mut input = journal_input(
        &fixture.registries,
        &fixture.state,
        &fixture.occurrence,
        LaneModuleTransitionOutcomeV1::Rejected(LaneModuleRejectCodeV1::new(41).unwrap()),
    );
    input.lane_id = EconomicLaneIdV1::SpotLiquidity;
    input.lane_pre_state_root = fixture.state.content().lane_state_roots()[1].state_root();
    let journal = LaneModuleTransitionJournalV1::new(input).unwrap();

    // Act
    let error = rejection(bind_rejected_lane_module_transition_journal_v1(
        &journal,
        &bound_occurrence,
    ));

    // Assert
    assert_eq!(
        error,
        LaneModuleTransitionJournalErrorV1::RouteDependencyMissing
    );
}

#[test]
fn unchanged_opening_cannot_cover_nonempty_lane_write_rows() {
    // Arrange
    let fixture = accepted_fixture(1);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let bound_plan =
        bind_global_economic_effect_plan_to_occurrence_v1(&fixture.plan, &bound_occurrence)
            .unwrap();
    let unchanged = LaneStateTransitionWitnessV1::unchanged(
        EconomicLaneIdV1::AssetTransfer,
        fixture.journal.economic_action_id(),
        fixture.journal.lane_pre_state_root(),
    );

    // Act
    let error = rejection(bind_accepted_lane_module_transition_journal_v1(
        &fixture.journal,
        &bound_plan,
        &unchanged,
    ));

    // Assert
    assert_eq!(
        error,
        LaneModuleTransitionJournalErrorV1::LanePostStateMismatch
    );
}

#[test]
fn module_release_journal_byte_ceiling_is_enforced_at_binding() {
    // Arrange
    let registries = crate::profile_support::economic_fixture_with_module_journal_limit(
        &[EconomicLaneIdV1::AssetTransfer],
        EconomicLaneIdV1::AssetTransfer,
        LaneModuleReleaseStatusV1::ActiveNew,
        1,
    );
    let fixture = accepted_fixture_for_registries(registries, 1, false);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);

    // Act
    let error = rejection(bind_rejected_lane_module_transition_journal_v1(
        &rejected_journal(&fixture),
        &bound_occurrence,
    ));

    // Assert
    assert!(matches!(
        error,
        LaneModuleTransitionJournalErrorV1::JournalResourceLimitExceeded {
            actual,
            module_maximum: 1,
            route_maximum: 32_768,
        } if actual > 1
    ));
}

#[test]
fn accepted_plan_and_state_roots_reject_independent_mutation() {
    // Arrange
    let fixture = accepted_fixture(1);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let bound_plan =
        bind_global_economic_effect_plan_to_occurrence_v1(&fixture.plan, &bound_occurrence)
            .unwrap();
    let LaneModuleTransitionOutcomeV1::Accepted(exact) = fixture.journal.outcome() else {
        panic!("accepted fixture must be accepted");
    };
    let accepted_with = |field: &str| {
        LaneModuleAcceptedTransitionV1::new(LaneModuleAcceptedTransitionInputV1 {
            global_post_state_root: if field == "global_post" {
                state_root(999)
            } else {
                exact.global_post_state_root()
            },
            global_effect_plan_commitment: if field == "effect_plan" {
                root(999)
            } else {
                exact.global_effect_plan_commitment()
            },
            lane_post_state_root: if field == "lane_post" {
                root(999)
            } else {
                exact.lane_post_state_root()
            },
            lane_effect_rows_root: if field == "lane_effects" {
                root(999)
            } else {
                exact.lane_effect_rows_root()
            },
            state_transition_root: if field == "state_transition" {
                root(999)
            } else {
                exact.state_transition_root()
            },
            private_input_ports_root: exact.private_input_ports_root(),
            private_output_ports_root: exact.private_output_ports_root(),
            terminal_obligations_root: if field == "terminal" {
                root(999)
            } else {
                exact.terminal_obligations_root()
            },
        })
    };
    let cases = [
        (
            "global_post",
            LaneModuleTransitionJournalErrorV1::GlobalPostStateMismatch,
        ),
        (
            "effect_plan",
            LaneModuleTransitionJournalErrorV1::EffectPlanCommitmentMismatch,
        ),
        (
            "lane_post",
            LaneModuleTransitionJournalErrorV1::LanePostStateMismatch,
        ),
        (
            "lane_effects",
            LaneModuleTransitionJournalErrorV1::LaneEffectRowsRootMismatch,
        ),
        (
            "state_transition",
            LaneModuleTransitionJournalErrorV1::StateTransitionRootMismatch,
        ),
        (
            "terminal",
            LaneModuleTransitionJournalErrorV1::TerminalObligationsRootMismatch,
        ),
    ];

    // Act
    let actual = cases
        .into_iter()
        .map(|(field, expected)| {
            let journal = LaneModuleTransitionJournalV1::new(journal_input(
                &fixture.registries,
                &fixture.state,
                &fixture.occurrence,
                LaneModuleTransitionOutcomeV1::Accepted(accepted_with(field)),
            ))
            .unwrap();
            (
                rejection(bind_accepted_lane_module_transition_journal_v1(
                    &journal,
                    &bound_plan,
                    &fixture.state_transition,
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
fn opening_lane_and_action_identity_are_checked_before_root_projection() {
    // Arrange
    let fixture = accepted_fixture(1);
    let bound_occurrence =
        bind_occurrence(&fixture.registries, &fixture.state, &fixture.occurrence);
    let bound_plan =
        bind_global_economic_effect_plan_to_occurrence_v1(&fixture.plan, &bound_occurrence)
            .unwrap();
    let wrong_lane = LaneStateTransitionWitnessV1::unchanged(
        EconomicLaneIdV1::SpotLiquidity,
        fixture.journal.economic_action_id(),
        fixture.journal.lane_pre_state_root(),
    );
    let wrong_action = LaneStateTransitionWitnessV1::unchanged(
        EconomicLaneIdV1::AssetTransfer,
        EconomicActionIdV1::new(root(999).into_bytes()).unwrap(),
        fixture.journal.lane_pre_state_root(),
    );

    // Act
    let lane_error = rejection(bind_accepted_lane_module_transition_journal_v1(
        &fixture.journal,
        &bound_plan,
        &wrong_lane,
    ));
    let action_error = rejection(bind_accepted_lane_module_transition_journal_v1(
        &fixture.journal,
        &bound_plan,
        &wrong_action,
    ));

    // Assert
    assert_eq!(lane_error, LaneModuleTransitionJournalErrorV1::LaneMismatch);
    assert_eq!(
        action_error,
        LaneModuleTransitionJournalErrorV1::EconomicActionMismatch
    );
}
