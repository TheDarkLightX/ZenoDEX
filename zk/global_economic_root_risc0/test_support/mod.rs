#![allow(dead_code)]
// Fixtures are research-only structural statements, never source authorization.
// The retained fixture has one needless borrow at its policy-binding call.
// Keep that historical source unchanged while checking the new crate strictly.
#[allow(clippy::needless_borrow)]
#[path = "../../economic_initial_state_risc0/host/tests/support/mod.rs"]
mod historical;

use zenodex_economic_initial_state_risc0_shared::{
    canonical_economic_initial_state_guest_input_bytes_v1, EconomicInitialStateGuestInputV1,
};
use zenodex_global_economic_epoch_risc0_shared as epoch;
use zenodex_global_economic_root_risc0_shared::RootGuestInputV1;
use zenodex_global_settlement_abi_v1 as abi;

pub fn initial_input(image: &str) -> EconomicInitialStateGuestInputV1 {
    let mut input =
        historical::guest_input(abi::RootV1::parse(image, "root image", false).unwrap());
    input.state.height = 0;
    input.state.replay_state.clear();
    input.state.terminal_obligations.clear();
    input.state.outbox.clear();
    input.predecessor_state = None;
    input.source_manifest.kind = abi::EconomicInitialStateKindV1::GENESIS;
    input.source_manifest.rows =
        abi::derive_economic_initial_state_atom_occurrences_v1(&input.state)
            .unwrap()
            .into_iter()
            .enumerate()
            .map(
                |(index, occurrence)| abi::EconomicInitialStateAtomSourceV1 {
                    occurrence,
                    classification:
                        abi::EconomicInitialStateAtomClassificationV1::GenesisAllocation,
                    source_authorization_root: historical::root(1000 + index as u64),
                },
            )
            .collect();
    let coverage =
        abi::economic_initial_state_atom_coverage_policy_binding_v1(&input.source_manifest)
            .unwrap();
    let binding = input
        .policy_registry
        .bindings
        .iter_mut()
        .find(|b| b.policy_kind == coverage.policy_kind)
        .unwrap();
    *binding = coverage;
    input.profile.policy_registry_root = input.policy_registry.registry_root().unwrap();
    let mut content = serde_json::to_value(&input.profile).unwrap();
    content.as_object_mut().unwrap().remove("profile_id");
    content.as_object_mut().unwrap().remove("status");
    input.profile.profile_id =
        abi::hash_global_v1("global-economic-profile-content-v1", &content).unwrap();
    input.state.profile_root = input.profile.profile_id.clone();
    bind_genesis_statement(&mut input);
    input
}

fn bind_genesis_statement(input: &mut EconomicInitialStateGuestInputV1) {
    let statement = &mut input.statement;
    statement.kind = abi::EconomicInitialStateKindV1::GENESIS;
    statement.height = 0;
    statement.profile_root = input.profile.profile_id.clone();
    statement.state_root = input.state.state_root().unwrap();
    statement.source_profile_root =
        abi::RootV1::parse(format!("0x{:064x}", 0), "zero source", true).unwrap();
    statement.source_state_root = statement.source_profile_root.clone();
    statement.source_writer_epoch = 0;
    statement.source_height = 0;
    statement.state_atom_coverage_root = input.source_manifest.manifest_root().unwrap();
    statement.replay_continuity_root =
        abi::derive_economic_initial_state_replay_continuity_root_v1(
            statement.kind,
            &input.state,
            None,
        )
        .unwrap();
    statement.terminal_continuity_root =
        abi::derive_economic_initial_state_terminal_continuity_root_v1(
            statement.kind,
            &input.state,
            None,
        )
        .unwrap();
    statement.outbox_continuity_root =
        abi::derive_economic_initial_state_outbox_continuity_root_v1(
            statement.kind,
            &input.state,
            None,
        )
        .unwrap();
}

pub fn initial_root_input(image: &str) -> RootGuestInputV1 {
    RootGuestInputV1::InitialStateV1(
        canonical_economic_initial_state_guest_input_bytes_v1(&initial_input(image)).unwrap(),
    )
}

pub fn root(n: u64) -> epoch::RootV1 {
    epoch::RootV1::parse(format!("0x{n:064x}"), "fixture root", n == 0).unwrap()
}

pub fn epoch_input(
    initial: &EconomicInitialStateGuestInputV1,
    count: usize,
    route_image: [u32; 8],
) -> epoch::EconomicEpochGuestInputV1 {
    let cast = |r: &abi::RootV1| epoch::RootV1::parse(r.as_str(), "ABI root", false).unwrap();
    let profile = cast(&initial.profile.profile_id);
    let deployment = cast(&initial.state.deployment_root);
    let pre = cast(&initial.statement.state_root);
    let mut current = pre.clone();
    let mut routes = Vec::new();
    let mut occurrences = Vec::new();
    let mut journals = Vec::new();
    let mut assumptions = Vec::new();
    for index in 0..count {
        let journal = epoch::RouteCompositionJournalV1 {
            schema: epoch::GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            chain_id: initial.state.chain_id.clone(),
            deployment_root: deployment.clone(),
            profile_root: profile.clone(),
            writer_epoch: initial.state.writer_epoch,
            route_release_id: root(2000),
            command_occurrence_id: root(3000 + index as u64),
            ordered_lane_journal_roots: vec![root(4000 + index as u64)],
            pre_state_root: current,
            post_state_root: root(5000 + index as u64),
            effect_plan_root: root(6000 + index as u64),
            terminal_obligations_root: root(0),
        };
        let bytes = epoch::canonical_json_bytes_v1(&journal, "fixture route").unwrap();
        let journal_root = journal.journal_root().unwrap();
        assumptions.push(
            epoch::derive_route_composition_assumption_root_v1(
                &epoch::RouteCompositionAssumptionInputV1 {
                    profile_id: &profile,
                    route_release_id: &journal.route_release_id,
                    command_occurrence_id: &journal.command_occurrence_id,
                    writer_epoch: journal.writer_epoch,
                    route_journal_root: &journal_root,
                    route_journal_digest: &epoch::sha256_root_v1(&bytes),
                    expected_image_id: &epoch::image_id_root_v1(route_image).unwrap(),
                },
            )
            .unwrap(),
        );
        occurrences.push(journal.command_occurrence_id);
        journals.push(journal_root);
        routes.push(epoch::RouteReceiptClaimV1 {
            image_id: route_image,
            journal_bytes: bytes,
        });
        current = journal.post_state_root;
    }
    let certificate = epoch::GlobalEconomicEpochJournalV1 {
        schema: epoch::GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: initial.state.chain_id.clone(),
        deployment_root: deployment,
        profile_root: profile,
        writer_epoch: initial.state.writer_epoch,
        height: 1,
        pre_state_root: pre,
        post_state_root: current,
        ordered_occurrence_ids: occurrences,
        ordered_route_journal_roots: journals,
        ordered_route_assumption_roots: assumptions,
        module_leaf_occurrences: count as u64,
        aggregation_fanout: 8,
        aggregation_levels: u64::from(count > 8),
        effect_plan_root: root(20),
        terminal_obligations_root: root(0),
        body_commitment: root(21),
        data_availability_root: root(22),
        finality_root: root(23),
        source_manifest_root: root(24),
        toolchain_manifest_root: root(25),
        root_image_id: cast(&initial.profile.root_image_id),
    };
    epoch::EconomicEpochGuestInputV1 {
        certificate_journal_bytes: epoch::canonical_json_bytes_v1(&certificate, "fixture epoch")
            .unwrap(),
        route_receipts: routes,
    }
}

pub fn aggregation_inputs(
    direct: &epoch::EconomicEpochGuestInputV1,
) -> Vec<epoch::CommandAggregationGuestInputV1> {
    let c: epoch::GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&direct.certificate_journal_bytes).unwrap();
    direct
        .route_receipts
        .chunks(8)
        .enumerate()
        .map(|(group, routes)| {
            let first = group * 8;
            let end = first + routes.len();
            let first_route: epoch::RouteCompositionJournalV1 =
                serde_json::from_slice(&routes[0].journal_bytes).unwrap();
            let last_route: epoch::RouteCompositionJournalV1 =
                serde_json::from_slice(&routes[routes.len() - 1].journal_bytes).unwrap();
            let journal = epoch::CommandAggregationJournalV1 {
                schema: epoch::COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1.to_owned(),
                settlement_abi: epoch::GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
                chain_id: c.chain_id.clone(),
                deployment_root: c.deployment_root.clone(),
                profile_root: c.profile_root.clone(),
                writer_epoch: c.writer_epoch,
                epoch_height: c.height,
                group_index: group as u64,
                first_command_index: first as u64,
                ordered_occurrence_ids: c.ordered_occurrence_ids[first..end].to_vec(),
                ordered_route_journal_roots: c.ordered_route_journal_roots[first..end].to_vec(),
                ordered_route_assumption_roots: c.ordered_route_assumption_roots[first..end]
                    .to_vec(),
                pre_state_root: first_route.pre_state_root,
                post_state_root: last_route.post_state_root,
                module_leaf_occurrences: routes.len() as u64,
            };
            epoch::CommandAggregationGuestInputV1 {
                aggregation_journal_bytes: journal.canonical_bytes().unwrap(),
                route_receipts: routes.to_vec(),
            }
        })
        .collect()
}

pub fn aggregated_input(
    direct: &epoch::EconomicEpochGuestInputV1,
    image: [u32; 8],
) -> epoch::AggregatedEconomicEpochGuestInputV1 {
    epoch::AggregatedEconomicEpochGuestInputV1 {
        certificate_journal_bytes: direct.certificate_journal_bytes.clone(),
        command_aggregation_receipts: aggregation_inputs(direct)
            .into_iter()
            .map(|group| epoch::CommandAggregationReceiptClaimV1 {
                image_id: image,
                journal_bytes: group.aggregation_journal_bytes,
            })
            .collect(),
    }
}
