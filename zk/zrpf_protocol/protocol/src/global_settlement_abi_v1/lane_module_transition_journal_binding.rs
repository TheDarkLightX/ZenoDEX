use super::{
    LaneModuleReleaseV1, LaneModuleTransitionJournalErrorV1, LaneModuleTransitionJournalV1,
    LaneModuleTransitionOutcomeV1, LaneStateTransitionWitnessV1,
    OccurrenceBoundGlobalEconomicEffectPlanV1, RouteModuleDependencyV1,
    StateBoundEconomicCommandOccurrenceV1,
};

/// Constructor-private structural witness for one journal bound to its exact
/// occurrence, governed route dependency, and module release.
///
/// It carries no receipt, image verification, recursion, settlement, or
/// publication authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::BoundLaneModuleTransitionJournalV1;
/// let journal = unimplemented!();
/// let occurrence = unimplemented!();
/// let module_release = unimplemented!();
/// let route_dependency = unimplemented!();
/// let _ = BoundLaneModuleTransitionJournalV1 {
///     journal,
///     occurrence,
///     module_release,
///     route_dependency,
/// };
/// ```
///
/// ```compile_fail
/// use serde::Serialize;
/// use zenodex_zrpf_protocol_v3::BoundLaneModuleTransitionJournalV1;
/// fn require_serializable<T: Serialize>() {}
/// require_serializable::<BoundLaneModuleTransitionJournalV1<'static>>();
/// ```
#[must_use]
pub struct BoundLaneModuleTransitionJournalV1<'a> {
    journal: &'a LaneModuleTransitionJournalV1,
    occurrence: &'a StateBoundEconomicCommandOccurrenceV1<'a>,
    module_release: &'a LaneModuleReleaseV1,
    route_dependency: &'a RouteModuleDependencyV1,
}

impl<'a> BoundLaneModuleTransitionJournalV1<'a> {
    pub const fn journal(&self) -> &'a LaneModuleTransitionJournalV1 {
        self.journal
    }

    pub const fn occurrence(&self) -> &'a StateBoundEconomicCommandOccurrenceV1<'a> {
        self.occurrence
    }

    pub const fn module_release(&self) -> &'a LaneModuleReleaseV1 {
        self.module_release
    }

    pub const fn route_dependency(&self) -> &'a RouteModuleDependencyV1 {
        self.route_dependency
    }
}

pub fn bind_accepted_lane_module_transition_journal_v1<'a>(
    journal: &'a LaneModuleTransitionJournalV1,
    plan: &'a OccurrenceBoundGlobalEconomicEffectPlanV1<'a>,
    state_transition: &'a LaneStateTransitionWitnessV1,
) -> Result<BoundLaneModuleTransitionJournalV1<'a>, LaneModuleTransitionJournalErrorV1> {
    let occurrence = plan.occurrence();
    let (module_release, route_dependency) = validate_common(journal, occurrence)?;
    let LaneModuleTransitionOutcomeV1::Accepted(accepted) = journal.outcome() else {
        return Err(LaneModuleTransitionJournalErrorV1::OutcomeMismatch);
    };
    validate_accepted(journal, accepted, plan, state_transition)?;
    Ok(BoundLaneModuleTransitionJournalV1 {
        journal,
        occurrence,
        module_release,
        route_dependency,
    })
}

pub fn bind_rejected_lane_module_transition_journal_v1<'a>(
    journal: &'a LaneModuleTransitionJournalV1,
    occurrence: &'a StateBoundEconomicCommandOccurrenceV1<'a>,
) -> Result<BoundLaneModuleTransitionJournalV1<'a>, LaneModuleTransitionJournalErrorV1> {
    let (module_release, route_dependency) = validate_common(journal, occurrence)?;
    if !matches!(
        journal.outcome(),
        LaneModuleTransitionOutcomeV1::Rejected(_)
    ) {
        return Err(LaneModuleTransitionJournalErrorV1::OutcomeMismatch);
    }
    Ok(BoundLaneModuleTransitionJournalV1 {
        journal,
        occurrence,
        module_release,
        route_dependency,
    })
}

fn validate_common<'a>(
    journal: &LaneModuleTransitionJournalV1,
    occurrence: &'a StateBoundEconomicCommandOccurrenceV1<'a>,
) -> Result<
    (&'a LaneModuleReleaseV1, &'a RouteModuleDependencyV1),
    LaneModuleTransitionJournalErrorV1,
> {
    journal.validate_self_consistency()?;
    validate_occurrence_envelope(journal, occurrence)?;
    let route = occurrence.profile_bound_occurrence().route_release();
    let dependency = route
        .content()
        .dependencies()
        .iter()
        .find(|dependency| dependency.lane_id() == journal.lane_id())
        .ok_or(LaneModuleTransitionJournalErrorV1::RouteDependencyMissing)?;
    if dependency.module_release_id() != journal.module_release_id() {
        return Err(LaneModuleTransitionJournalErrorV1::ModuleReleaseMismatch);
    }
    let registry =
        &occurrence.profile_state().module_registries()[usize::from(journal.lane_id().code())];
    let module_release = registry
        .releases()
        .binary_search_by_key(
            &journal.module_release_id(),
            LaneModuleReleaseV1::release_id,
        )
        .ok()
        .map(|position| &registry.releases()[position])
        .ok_or(LaneModuleTransitionJournalErrorV1::ModuleReleaseMissing)?;
    validate_release_metadata(journal, module_release, dependency)?;
    validate_journal_resource_limits(journal, module_release, route)?;
    Ok((module_release, dependency))
}

fn validate_occurrence_envelope(
    journal: &LaneModuleTransitionJournalV1,
    occurrence: &StateBoundEconomicCommandOccurrenceV1<'_>,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    let command = occurrence.profile_bound_occurrence().occurrence();
    let content = command.content();
    let action = content.authorized_action();
    let record = action.record();
    if journal.application_id() != record.application_id() {
        return Err(LaneModuleTransitionJournalErrorV1::ApplicationMismatch);
    }
    if journal.chain_or_domain_id() != record.chain_or_domain_id() {
        return Err(LaneModuleTransitionJournalErrorV1::DomainMismatch);
    }
    if journal.profile_id() != content.profile_id() {
        return Err(LaneModuleTransitionJournalErrorV1::ProfileMismatch);
    }
    if journal.writer_epoch() != content.writer_epoch() {
        return Err(LaneModuleTransitionJournalErrorV1::WriterEpochMismatch);
    }
    if journal.occurrence_id() != command.occurrence_id() {
        return Err(LaneModuleTransitionJournalErrorV1::OccurrenceMismatch);
    }
    if journal.route_release_id() != content.route_release_id() {
        return Err(LaneModuleTransitionJournalErrorV1::RouteMismatch);
    }
    if journal.economic_action_id() != action.action_id()? {
        return Err(LaneModuleTransitionJournalErrorV1::EconomicActionMismatch);
    }
    let global_state = occurrence.global_state();
    if journal.global_pre_state_root() != global_state.state_root() {
        return Err(LaneModuleTransitionJournalErrorV1::GlobalPreStateMismatch);
    }
    let lane_pre_root = global_state.content().lane_state_roots()
        [usize::from(journal.lane_id().code())]
    .state_root();
    if journal.lane_pre_state_root() != lane_pre_root {
        return Err(LaneModuleTransitionJournalErrorV1::LanePreStateMismatch);
    }
    Ok(())
}

fn validate_release_metadata(
    journal: &LaneModuleTransitionJournalV1,
    module_release: &LaneModuleReleaseV1,
    dependency: &RouteModuleDependencyV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    validate_module_release_metadata(journal, module_release)?;
    validate_route_dependency_metadata(journal, dependency)
}

fn validate_module_release_metadata(
    journal: &LaneModuleTransitionJournalV1,
    module_release: &LaneModuleReleaseV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    let content = module_release.content();
    if content.lane_id() != journal.lane_id()
        || module_release.release_id() != journal.module_release_id()
    {
        return Err(LaneModuleTransitionJournalErrorV1::ModuleReleaseMismatch);
    }
    let schemas = content.schemas();
    let provenance = content.provenance();
    require_equal(
        journal.guest_image_id(),
        provenance.guest_image_id(),
        LaneModuleTransitionJournalErrorV1::GuestImageMismatch,
    )?;
    require_equal(
        journal.state_schema_root(),
        schemas.state_schema_root(),
        LaneModuleTransitionJournalErrorV1::StateSchemaMismatch,
    )?;
    require_equal(
        journal.command_schema_root(),
        schemas.command_schema_root(),
        LaneModuleTransitionJournalErrorV1::CommandSchemaMismatch,
    )?;
    require_equal(
        journal.effect_schema_root(),
        schemas.effect_schema_root(),
        LaneModuleTransitionJournalErrorV1::EffectSchemaMismatch,
    )?;
    require_equal(
        journal.private_port_schema_root(),
        schemas.private_port_schema_root(),
        LaneModuleTransitionJournalErrorV1::PrivatePortSchemaMismatch,
    )?;
    require_equal(
        journal.command_variants_root(),
        content.command_variants_root(),
        LaneModuleTransitionJournalErrorV1::CommandVariantsMismatch,
    )?;
    require_equal(
        journal.spec_root(),
        provenance.spec_root(),
        LaneModuleTransitionJournalErrorV1::SpecRootMismatch,
    )?;
    require_equal(
        journal.source_root(),
        provenance.source_root(),
        LaneModuleTransitionJournalErrorV1::SourceRootMismatch,
    )?;
    require_equal(
        journal.toolchain_root(),
        provenance.toolchain_root(),
        LaneModuleTransitionJournalErrorV1::ToolchainRootMismatch,
    )
}

fn validate_route_dependency_metadata(
    journal: &LaneModuleTransitionJournalV1,
    dependency: &RouteModuleDependencyV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    require_equal(
        journal.receipt_journal_schema_root(),
        dependency.receipt_journal_schema_root(),
        LaneModuleTransitionJournalErrorV1::JournalSchemaMismatch,
    )?;
    require_equal(
        journal.input_port_schema_root(),
        dependency.input_port_schema_root(),
        LaneModuleTransitionJournalErrorV1::InputPortSchemaMismatch,
    )?;
    require_equal(
        journal.output_port_schema_root(),
        dependency.output_port_schema_root(),
        LaneModuleTransitionJournalErrorV1::OutputPortSchemaMismatch,
    )
}

fn validate_journal_resource_limits(
    journal: &LaneModuleTransitionJournalV1,
    module_release: &LaneModuleReleaseV1,
    route: &super::RouteReleaseV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    let actual = super::encode_lane_module_transition_journal_v1(journal)?.len();
    let module_maximum = usize::try_from(
        module_release
            .content()
            .resource_limits()
            .max_journal_bytes(),
    )
    .map_err(|_| LaneModuleTransitionJournalErrorV1::ArithmeticOverflow("module_journal_limit"))?;
    let route_maximum = usize::try_from(
        route.content().resource_limits().max_total_journal_bytes(),
    )
    .map_err(|_| LaneModuleTransitionJournalErrorV1::ArithmeticOverflow("route_journal_limit"))?;
    if actual > module_maximum || actual > route_maximum {
        return Err(
            LaneModuleTransitionJournalErrorV1::JournalResourceLimitExceeded {
                actual,
                module_maximum,
                route_maximum,
            },
        );
    }
    Ok(())
}

fn validate_accepted(
    journal: &LaneModuleTransitionJournalV1,
    accepted: super::LaneModuleAcceptedTransitionV1,
    plan: &OccurrenceBoundGlobalEconomicEffectPlanV1<'_>,
    state_transition: &LaneStateTransitionWitnessV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    let plan = plan.plan();
    let body = plan.body();
    state_transition.validate_self_consistency()?;
    if accepted.global_post_state_root() != body.post_state_root() {
        return Err(LaneModuleTransitionJournalErrorV1::GlobalPostStateMismatch);
    }
    if accepted.global_effect_plan_commitment() != plan.canonical_commitment()? {
        return Err(LaneModuleTransitionJournalErrorV1::EffectPlanCommitmentMismatch);
    }
    if state_transition.lane_id() != journal.lane_id() {
        return Err(LaneModuleTransitionJournalErrorV1::LaneMismatch);
    }
    if state_transition.economic_action_id() != journal.economic_action_id() {
        return Err(LaneModuleTransitionJournalErrorV1::EconomicActionMismatch);
    }
    if state_transition.lane_pre_state_root() != journal.lane_pre_state_root() {
        return Err(LaneModuleTransitionJournalErrorV1::LanePreStateMismatch);
    }
    if accepted.lane_post_state_root() != state_transition.lane_post_state_root() {
        return Err(LaneModuleTransitionJournalErrorV1::LanePostStateMismatch);
    }
    if accepted.lane_effect_rows_root() != body.lane_effect_rows_root(journal.lane_id())? {
        return Err(LaneModuleTransitionJournalErrorV1::LaneEffectRowsRootMismatch);
    }
    if accepted.state_transition_root() != state_transition.canonical_commitment()? {
        return Err(LaneModuleTransitionJournalErrorV1::StateTransitionRootMismatch);
    }
    if accepted.terminal_obligations_root()
        != body.lane_terminal_obligations_root(journal.lane_id())?
    {
        return Err(LaneModuleTransitionJournalErrorV1::TerminalObligationsRootMismatch);
    }
    validate_lane_writes(plan, journal.lane_id(), state_transition)
}

fn validate_lane_writes(
    plan: &super::GlobalEconomicEffectPlanV1,
    lane_id: super::EconomicLaneIdV1,
    state_transition: &LaneStateTransitionWitnessV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    let writes = plan.body().lane_writes(lane_id);
    let Some(batch) = state_transition.changed_batch() else {
        return if writes.is_empty() {
            Ok(())
        } else {
            Err(LaneModuleTransitionJournalErrorV1::LaneWriteMismatch)
        };
    };
    if writes.len() != batch.witnesses().len() {
        return Err(LaneModuleTransitionJournalErrorV1::LaneWriteMismatch);
    }
    for (write, witness) in writes.iter().zip(batch.witnesses()) {
        if write.object_id() != witness.cell_key()
            || write.pre_value_hash().as_bytes() != witness.pre_value_hash().as_bytes()
            || write.post_value_hash().as_bytes() != witness.post_value_hash().as_bytes()
        {
            return Err(LaneModuleTransitionJournalErrorV1::LaneWriteMismatch);
        }
    }
    Ok(())
}

fn require_equal<T: PartialEq>(
    actual: T,
    expected: T,
    error: LaneModuleTransitionJournalErrorV1,
) -> Result<(), LaneModuleTransitionJournalErrorV1> {
    if actual == expected {
        Ok(())
    } else {
        Err(error)
    }
}
