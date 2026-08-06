pub use crate::state_support::{application_id, domain_id, root};
pub use zenodex_zrpf_protocol_v3::{
    bind_accepted_lane_module_transition_journal_v1,
    bind_economic_command_occurrence_to_active_profile_v1,
    bind_global_economic_effect_plan_to_occurrence_v1, bind_global_economic_state_to_profile_v1,
    bind_profile_bound_occurrence_to_global_state_v1,
    bind_rejected_lane_module_transition_journal_v1,
    decode_exact_lane_module_transition_journal_v1, decode_exact_lane_state_transition_witness_v1,
    encode_lane_module_transition_journal_v1, encode_lane_state_transition_witness_v1,
    AuthorizedEconomicActionV1, CommitmentV3, EconomicActionIdV1, EconomicCommandOccurrenceIdV1,
    EconomicCommandOccurrenceV1, EconomicLaneIdV1, EconomicProfileIdV1,
    GlobalAssetReconciliationInputV1, GlobalAssetReconciliationV1, GlobalEconomicEffectBodyInputV1,
    GlobalEconomicEffectBodyV1, GlobalEconomicEffectPlanInputV1, GlobalEconomicEffectPlanV1,
    GlobalEconomicEffectRowV1, GlobalEconomicLaneStateRootV1, GlobalEconomicStateContentInputV1,
    GlobalEconomicStateContentV1, GlobalEconomicStateRootV1, GlobalEconomicStateV1,
    GlobalOccurrenceConsumptionKindV1, LaneModuleAcceptedTransitionInputV1,
    LaneModuleAcceptedTransitionV1, LaneModuleRejectCodeV1, LaneModuleTransitionJournalErrorV1,
    LaneModuleTransitionJournalInputV1, LaneModuleTransitionJournalV1,
    LaneModuleTransitionOutcomeV1, LaneStateOpeningBatchInputV1, LaneStateOpeningBatchV1,
    LaneStateTransitionErrorV1, LaneStateTransitionWitnessV1, ProgramIdV3, RouteReleaseIdV1,
    SparseMerkleCellTransitionWitnessInputV1, SparseMerkleCellTransitionWitnessV1,
    StateBoundEconomicCommandOccurrenceV1, SPARSE_MERKLE_WITNESS_VERSION_V1,
};

pub struct AcceptedFixture {
    pub registries: crate::profile_support::EconomicRegistryFixture,
    pub state: GlobalEconomicStateV1,
    pub occurrence: EconomicCommandOccurrenceV1,
    pub plan: GlobalEconomicEffectPlanV1,
    pub state_transition: LaneStateTransitionWitnessV1,
    pub journal: LaneModuleTransitionJournalV1,
}

pub fn state_root(seed: u16) -> GlobalEconomicStateRootV1 {
    GlobalEconomicStateRootV1::new(root(seed).into_bytes()).unwrap()
}

pub fn rejection<T, E>(result: Result<T, E>) -> E {
    match result {
        Ok(_) => panic!("expected typed rejection"),
        Err(error) => error,
    }
}

pub fn same_action_witnesses(
    count: usize,
    action_id: EconomicActionIdV1,
) -> Vec<SparseMerkleCellTransitionWitnessV1> {
    let input = crate::sparse_support::canonical_batch_input(count);
    input
        .entries
        .iter()
        .map(|entry| witness_for_action(entry.witness(), action_id))
        .collect()
}

pub fn witness_for_action(
    witness: &SparseMerkleCellTransitionWitnessV1,
    action_id: EconomicActionIdV1,
) -> SparseMerkleCellTransitionWitnessV1 {
    SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
        witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
        economic_action_id: action_id,
        cell_key: witness.cell_key(),
        pre_value_hash: witness.pre_value_hash(),
        post_value_hash: witness.post_value_hash(),
        sibling_commitments: witness.sibling_commitments().clone(),
        claimed_pre_root: witness.claimed_pre_root(),
        claimed_post_root: witness.claimed_post_root(),
    })
    .unwrap()
}

pub fn opening_batch(
    witnesses: Vec<SparseMerkleCellTransitionWitnessV1>,
) -> Result<LaneStateOpeningBatchV1, LaneStateTransitionErrorV1> {
    let first = witnesses.first().expect("test fixture requires witnesses");
    let last = witnesses.last().expect("test fixture requires witnesses");
    LaneStateOpeningBatchV1::new(LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: first.economic_action_id(),
        lane_pre_state_root: first.claimed_pre_root(),
        lane_post_state_root: last.claimed_post_root(),
        witnesses,
    })
}

pub fn accepted_fixture(write_count: usize) -> AcceptedFixture {
    accepted_fixture_with_write_mutation(write_count, false)
}

pub fn accepted_fixture_with_write_mutation(
    write_count: usize,
    mutate_first_write: bool,
) -> AcceptedFixture {
    let registries = crate::state_support::fixture();
    accepted_fixture_for_registries(registries, write_count, mutate_first_write)
}

pub fn accepted_fixture_for_registries(
    registries: crate::profile_support::EconomicRegistryFixture,
    write_count: usize,
    mutate_first_write: bool,
) -> AcceptedFixture {
    let sparse_input = crate::sparse_support::canonical_batch_input(write_count);
    let skeleton_witnesses = sparse_input
        .entries
        .iter()
        .map(|entry| entry.witness().clone())
        .collect::<Vec<_>>();
    let lane_pre_state_root = sparse_input.batch_pre_root;
    let lane_post_state_root = sparse_input.batch_post_root;
    let state = state_with_asset_lane_root(&registries, lane_pre_state_root);
    let lane_writes = lane_write_rows(&skeleton_witnesses, mutate_first_write);
    let provisional_body = effect_body(&state, lane_writes.clone(), root(900));
    let action = crate::global_economic_effect_plan_support::authorized_action(
        &registries,
        &state,
        provisional_body.effect_commitment(),
        vec![],
    );
    let final_body = effect_body(&state, lane_writes, grant_spend_id(&action));
    assert_eq!(
        provisional_body.effect_commitment(),
        final_body.effect_commitment()
    );
    let occurrence = crate::global_economic_effect_plan_support::occurrence(&registries, action);
    let plan = plan_for(&registries, &state, &occurrence, final_body);
    let state_transition = state_transition_for(
        &skeleton_witnesses,
        occurrence
            .content()
            .authorized_action()
            .action_id()
            .unwrap(),
        lane_pre_state_root,
        lane_post_state_root,
    );
    let journal =
        accepted_journal_for((&registries, &state, &occurrence), &plan, &state_transition);
    AcceptedFixture {
        registries,
        state,
        occurrence,
        plan,
        state_transition,
        journal,
    }
}

fn state_transition_for(
    skeleton_witnesses: &[SparseMerkleCellTransitionWitnessV1],
    action_id: EconomicActionIdV1,
    lane_pre_state_root: CommitmentV3,
    lane_post_state_root: CommitmentV3,
) -> LaneStateTransitionWitnessV1 {
    let witnesses = skeleton_witnesses
        .iter()
        .map(|witness| witness_for_action(witness, action_id))
        .collect::<Vec<_>>();
    let batch = LaneStateOpeningBatchV1::new(LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: action_id,
        witnesses,
        lane_pre_state_root,
        lane_post_state_root,
    })
    .unwrap();
    LaneStateTransitionWitnessV1::changed(batch).unwrap()
}

fn accepted_journal_for(
    context: (
        &crate::profile_support::EconomicRegistryFixture,
        &GlobalEconomicStateV1,
        &EconomicCommandOccurrenceV1,
    ),
    plan: &GlobalEconomicEffectPlanV1,
    transition: &LaneStateTransitionWitnessV1,
) -> LaneModuleTransitionJournalV1 {
    let (registries, state, occurrence) = context;
    LaneModuleTransitionJournalV1::new(journal_input(
        registries,
        state,
        occurrence,
        LaneModuleTransitionOutcomeV1::Accepted(accepted_transition(plan, transition)),
    ))
    .unwrap()
}

pub fn bind_occurrence<'a>(
    registries: &'a crate::profile_support::EconomicRegistryFixture,
    state: &'a GlobalEconomicStateV1,
    occurrence: &'a EconomicCommandOccurrenceV1,
) -> StateBoundEconomicCommandOccurrenceV1<'a> {
    let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
        &registries.profile,
        &registries.route_registry,
        occurrence,
    )
    .unwrap();
    let profile_state = bind_global_economic_state_to_profile_v1(
        state,
        &registries.profile,
        &registries.lane_registry,
        &registries.module_registries,
        &registries.route_registry,
    )
    .unwrap();
    bind_profile_bound_occurrence_to_global_state_v1(profile_occurrence, profile_state, &[])
        .unwrap()
}

pub fn journal_input(
    registries: &crate::profile_support::EconomicRegistryFixture,
    state: &GlobalEconomicStateV1,
    occurrence: &EconomicCommandOccurrenceV1,
    outcome: LaneModuleTransitionOutcomeV1,
) -> LaneModuleTransitionJournalInputV1 {
    let route = &registries.route_registry.routes()[0];
    let dependency = &route.content().dependencies()[0];
    let release = &registries.module_registries[0].releases()[0];
    let release_content = release.content();
    let schemas = release_content.schemas();
    let provenance = release_content.provenance();
    LaneModuleTransitionJournalInputV1 {
        application_id: state.content().application_id(),
        chain_or_domain_id: state.content().chain_or_domain_id(),
        profile_id: registries.profile.profile_id(),
        writer_epoch: registries.profile.content().writer_epoch(),
        occurrence_id: occurrence.occurrence_id(),
        route_release_id: route.route_release_id(),
        economic_action_id: occurrence
            .content()
            .authorized_action()
            .action_id()
            .unwrap(),
        lane_id: EconomicLaneIdV1::AssetTransfer,
        module_release_id: release.release_id(),
        guest_image_id: provenance.guest_image_id(),
        state_schema_root: schemas.state_schema_root(),
        command_schema_root: schemas.command_schema_root(),
        effect_schema_root: schemas.effect_schema_root(),
        private_port_schema_root: schemas.private_port_schema_root(),
        command_variants_root: release_content.command_variants_root(),
        spec_root: provenance.spec_root(),
        source_root: provenance.source_root(),
        toolchain_root: provenance.toolchain_root(),
        receipt_journal_schema_root: dependency.receipt_journal_schema_root(),
        input_port_schema_root: dependency.input_port_schema_root(),
        output_port_schema_root: dependency.output_port_schema_root(),
        global_pre_state_root: state.state_root(),
        lane_pre_state_root: state.content().lane_state_roots()[0].state_root(),
        outcome,
    }
}

pub fn rejected_journal(fixture: &AcceptedFixture) -> LaneModuleTransitionJournalV1 {
    LaneModuleTransitionJournalV1::new(journal_input(
        &fixture.registries,
        &fixture.state,
        &fixture.occurrence,
        LaneModuleTransitionOutcomeV1::Rejected(LaneModuleRejectCodeV1::new(41).unwrap()),
    ))
    .unwrap()
}

fn state_with_asset_lane_root(
    registries: &crate::profile_support::EconomicRegistryFixture,
    asset_lane_root: CommitmentV3,
) -> GlobalEconomicStateV1 {
    let mut lanes = crate::state_support::lane_state_roots(100);
    lanes[0] = GlobalEconomicLaneStateRootV1::new(EconomicLaneIdV1::AssetTransfer, asset_lane_root);
    GlobalEconomicStateV1::new(
        GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
            application_id: application_id(1),
            chain_or_domain_id: domain_id(2),
            height: 500,
            writer_epoch: registries.profile.content().writer_epoch(),
            profile_id: registries.profile.profile_id(),
            lane_state_roots: lanes,
            partition_roots: crate::state_support::partition_roots(root(900)),
        })
        .unwrap(),
    )
    .unwrap()
}

fn lane_write_rows(
    witnesses: &[SparseMerkleCellTransitionWitnessV1],
    mutate_first_write: bool,
) -> Vec<GlobalEconomicEffectRowV1> {
    witnesses
        .iter()
        .enumerate()
        .map(|(index, witness)| {
            let post_hash = if mutate_first_write && index == 0 {
                root(4_000)
            } else {
                CommitmentV3::new(witness.post_value_hash().into_bytes()).unwrap()
            };
            GlobalEconomicEffectRowV1::lane_write(
                EconomicLaneIdV1::AssetTransfer,
                witness.cell_key(),
                CommitmentV3::new(witness.pre_value_hash().into_bytes()).unwrap(),
                post_hash,
            )
            .unwrap()
        })
        .collect()
}

fn effect_body(
    _state: &GlobalEconomicStateV1,
    mut lane_writes: Vec<GlobalEconomicEffectRowV1>,
    grant_spend: CommitmentV3,
) -> GlobalEconomicEffectBodyV1 {
    let asset = root(10);
    let mut effects = vec![crate::global_economic_effect_plan_support::transfer_row(
        asset, 5,
    )];
    effects.append(&mut lane_writes);
    effects.push(
        GlobalEconomicEffectRowV1::terminal_obligation(
            EconomicLaneIdV1::AssetTransfer,
            root(40),
            root(41),
            root(42),
        )
        .unwrap(),
    );
    effects.push(
        GlobalEconomicEffectRowV1::occurrence_consumption(
            GlobalOccurrenceConsumptionKindV1::AuthorizationGrantSpend,
            grant_spend,
        )
        .unwrap(),
    );
    GlobalEconomicEffectBodyV1::new(GlobalEconomicEffectBodyInputV1 {
        post_state_root: state_root(202),
        effects,
        reconciliations: vec![GlobalAssetReconciliationV1::new(
            GlobalAssetReconciliationInputV1 {
                asset_id: asset,
                owned_and_custodied_pre_atoms: 5,
                owned_and_custodied_post_atoms: 5,
                supply_pre_atoms: 5,
                supply_post_atoms: 5,
                liabilities_pre_atoms: 0,
                liabilities_post_atoms: 0,
                named_reserves_pre_atoms: 0,
                named_reserves_post_atoms: 0,
            },
        )],
    })
    .unwrap()
}

fn grant_spend_id(action: &AuthorizedEconomicActionV1) -> CommitmentV3 {
    CommitmentV3::new(action.authorization_grant_spend().unwrap().into_bytes()).unwrap()
}

fn plan_for(
    registries: &crate::profile_support::EconomicRegistryFixture,
    state: &GlobalEconomicStateV1,
    occurrence: &EconomicCommandOccurrenceV1,
    body: GlobalEconomicEffectBodyV1,
) -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1::new(GlobalEconomicEffectPlanInputV1 {
        application_id: state.content().application_id(),
        chain_or_domain_id: state.content().chain_or_domain_id(),
        profile_id: registries.profile.profile_id(),
        writer_epoch: registries.profile.content().writer_epoch(),
        occurrence_id: occurrence.occurrence_id(),
        route_release_id: occurrence.content().route_release_id(),
        pre_state_root: state.state_root(),
        body,
    })
    .unwrap()
}

fn accepted_transition(
    plan: &GlobalEconomicEffectPlanV1,
    transition: &LaneStateTransitionWitnessV1,
) -> LaneModuleAcceptedTransitionV1 {
    LaneModuleAcceptedTransitionV1::new(LaneModuleAcceptedTransitionInputV1 {
        global_post_state_root: plan.body().post_state_root(),
        global_effect_plan_commitment: plan.canonical_commitment().unwrap(),
        lane_post_state_root: transition.lane_post_state_root(),
        lane_effect_rows_root: plan
            .body()
            .lane_effect_rows_root(EconomicLaneIdV1::AssetTransfer)
            .unwrap(),
        state_transition_root: transition.canonical_commitment().unwrap(),
        private_input_ports_root: root(501),
        private_output_ports_root: root(502),
        terminal_obligations_root: plan
            .body()
            .lane_terminal_obligations_root(EconomicLaneIdV1::AssetTransfer)
            .unwrap(),
    })
}
