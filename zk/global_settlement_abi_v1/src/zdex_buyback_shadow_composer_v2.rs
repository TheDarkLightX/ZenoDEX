//! Pure SHADOW predicates and crate-private replay experiment for Buyback V2.
//!
//! The public surface exposes deterministic binding predicates only.  The
//! complete plan builder remains crate-private because its inputs are locally
//! rederived SHADOW values, not opaque verifier-created witnesses.  It neither
//! executes effects nor grants settlement authority.

use std::collections::BTreeMap;

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::release::LaneIdV1;
use crate::zdex_spot_buyback_transition::ZDEXSpotTerminalObligationV1;
use crate::zdex_spot_buyback_transition_v2::{
    effect_plan_from_spot_accepted_v2, ZDEXSpotBuybackAcceptedV2, ZDEXSpotTerminalObligationV2,
};
use crate::zdex_tokenomics_buyback_transition_v2::ZDEXTokenomicsBuybackAcceptedV2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXBuybackRouteTerminalRejectCodeV2 {
    TERMINAL_MALFORMED,
    TERMINAL_VERSION_MISMATCH,
    PROFILE_MISMATCH,
    OCCURRENCE_MISMATCH,
    QUOTE_PORT_MISMATCH,
    POST_STATE_MISMATCH,
    FLOW_MISMATCH,
    AMOUNT_MISMATCH,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXBuybackRouteTerminalInputV2 {
    TERMINAL(Box<ZDEXSpotTerminalObligationV2>),
    V1_REWRAP(Box<ZDEXSpotTerminalObligationV1>),
    MALFORMED,
}

/// Data a receipt verifier must bind to its authenticated route transcript.
/// It is intentionally caller-constructible data, never an authority witness.
///
/// The public crate API has no effect-applying Buyback V2 composer while the
/// required opaque route witness does not exist:
///
/// ```compile_fail
/// use zenodex_global_settlement_abi_v1::apply_final_composite_once_v2;
/// let _ = apply_final_composite_once_v2;
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXBuybackRouteReceiptClaimsV2 {
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub quote_port_root: RootV1,
    pub post_state_root: RootV1,
    pub quote_input_flow_id: RootV1,
    pub purchased_output_flow_id: RootV1,
    pub terminal_obligation_id: RootV1,
    pub purchased_atoms: u128,
}

impl ZDEXBuybackRouteReceiptClaimsV2 {
    pub fn from_terminal(terminal: &ZDEXSpotTerminalObligationV2) -> AbiResultV1<Self> {
        terminal.validate()?;
        Ok(Self {
            profile_root: terminal.context.coordinates.profile_root.clone(),
            route_release_id: terminal.context.coordinates.route_release_id.clone(),
            command_occurrence_id: terminal.context.coordinates.command_occurrence_id.clone(),
            quote_port_root: terminal.context.coordinates.quote_port_root.clone(),
            post_state_root: terminal.post_state_root.clone(),
            quote_input_flow_id: terminal.quote_input_flow_id.clone(),
            purchased_output_flow_id: terminal.purchased_output_flow_id.clone(),
            terminal_obligation_id: terminal.obligation_id()?,
            purchased_atoms: terminal.purchased_atoms,
        })
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.quote_port_root,
            &self.post_state_root,
            &self.quote_input_flow_id,
            &self.purchased_output_flow_id,
            &self.terminal_obligation_id,
        ] {
            root.validate("Buyback V2 route claim root", false)?;
        }
        if self.purchased_atoms == 0 || self.purchased_atoms > i128::MAX.unsigned_abs() {
            return Err(AbiErrorV1::InvalidBounds("Buyback V2 route claim amount"));
        }
        Ok(())
    }
}

/// Deterministic binding check to run after a receipt verifier has produced
/// claims.  The function authenticates nothing by itself.
pub fn validate_route_terminal_claims_v2(
    claims: &ZDEXBuybackRouteReceiptClaimsV2,
    input: &ZDEXBuybackRouteTerminalInputV2,
) -> AbiResultV1<Result<(), ZDEXBuybackRouteTerminalRejectCodeV2>> {
    claims.validate()?;
    let terminal = match input {
        ZDEXBuybackRouteTerminalInputV2::TERMINAL(terminal) if terminal.validate().is_ok() => {
            terminal.as_ref()
        }
        ZDEXBuybackRouteTerminalInputV2::V1_REWRAP(_) => {
            return Ok(Err(
                ZDEXBuybackRouteTerminalRejectCodeV2::TERMINAL_VERSION_MISMATCH,
            ));
        }
        ZDEXBuybackRouteTerminalInputV2::TERMINAL(_)
        | ZDEXBuybackRouteTerminalInputV2::MALFORMED => {
            return Ok(Err(
                ZDEXBuybackRouteTerminalRejectCodeV2::TERMINAL_MALFORMED,
            ));
        }
    };
    let coordinates = &terminal.context.coordinates;
    if claims.profile_root != coordinates.profile_root {
        return Ok(Err(ZDEXBuybackRouteTerminalRejectCodeV2::PROFILE_MISMATCH));
    }
    if claims.route_release_id != coordinates.route_release_id
        || claims.command_occurrence_id != coordinates.command_occurrence_id
    {
        return Ok(Err(
            ZDEXBuybackRouteTerminalRejectCodeV2::OCCURRENCE_MISMATCH,
        ));
    }
    if claims.quote_port_root != coordinates.quote_port_root {
        return Ok(Err(
            ZDEXBuybackRouteTerminalRejectCodeV2::QUOTE_PORT_MISMATCH,
        ));
    }
    if claims.post_state_root != terminal.post_state_root {
        return Ok(Err(
            ZDEXBuybackRouteTerminalRejectCodeV2::POST_STATE_MISMATCH,
        ));
    }
    if claims.purchased_atoms != terminal.purchased_atoms {
        return Ok(Err(ZDEXBuybackRouteTerminalRejectCodeV2::AMOUNT_MISMATCH));
    }
    if claims.quote_input_flow_id != terminal.quote_input_flow_id
        || claims.purchased_output_flow_id != terminal.purchased_output_flow_id
        || claims.terminal_obligation_id != terminal.obligation_id()?
    {
        return Ok(Err(ZDEXBuybackRouteTerminalRejectCodeV2::FLOW_MISMATCH));
    }
    Ok(Ok(()))
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ZDEXBuybackShadowComposerStateV2 {
    accepted_bindings_by_occurrence: BTreeMap<RootV1, RootV1>,
}

impl ZDEXBuybackShadowComposerStateV2 {
    pub(crate) fn accepted_binding_for(&self, command_occurrence_id: &RootV1) -> Option<&RootV1> {
        self.accepted_bindings_by_occurrence
            .get(command_occurrence_id)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXBuybackShadowComposerRejectCodeV2 {
    SPOT_ACCEPTED_WRAPPER_INVALID,
    TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
    CROSS_LANE_BINDING_MISMATCH,
    FINAL_EFFECT_PLAN_MISMATCH,
    EQUIVOCATION,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ZDEXBuybackShadowComposerAppliedV2 {
    pub(crate) next_state: ZDEXBuybackShadowComposerStateV2,
    pub(crate) command_occurrence_id: RootV1,
    pub(crate) accepted_binding_root: RootV1,
    pub(crate) final_effect_plan: GlobalEconomicEffectPlanV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ZDEXBuybackShadowComposerAlreadyAcceptedV2 {
    pub(crate) command_occurrence_id: RootV1,
    pub(crate) accepted_binding_root: RootV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ZDEXBuybackShadowComposerRejectedV2 {
    pub(crate) code: ZDEXBuybackShadowComposerRejectCodeV2,
    pub(crate) retained_state: ZDEXBuybackShadowComposerStateV2,
    pub(crate) effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXBuybackShadowComposerRejectedV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.effects.validate()?;
        if !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "Buyback V2 composer rejection exact no-op",
            ));
        }
        Ok(())
    }
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ZDEXBuybackShadowComposerResultV2 {
    Applied(ZDEXBuybackShadowComposerAppliedV2),
    AlreadyAccepted(ZDEXBuybackShadowComposerAlreadyAcceptedV2),
    Rejected(ZDEXBuybackShadowComposerRejectedV2),
}

struct ZDEXBuybackShadowComposedPlanV2 {
    command_occurrence_id: RootV1,
    spot_journal_root: RootV1,
    tokenomics_journal_root: RootV1,
    terminal_obligation_id: RootV1,
    final_effect_plan: GlobalEconomicEffectPlanV1,
}

/// Validate that a caller-supplied plan is exactly the two-lane SHADOW
/// composition.  This is a predicate only.  It returns no authority witness,
/// never updates replay state, and cannot apply the plan.
pub fn validate_shadow_composed_effect_plan_v2(
    spot_accepted: &ZDEXSpotBuybackAcceptedV2,
    tokenomics_accepted: &ZDEXTokenomicsBuybackAcceptedV2,
    candidate_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Result<(), ZDEXBuybackShadowComposerRejectCodeV2>> {
    let expected = match derive_complete_composed_plan_v2(spot_accepted, tokenomics_accepted)? {
        Ok(expected) => expected,
        Err(code) => return Ok(Err(code)),
    };
    let expected_root = expected.final_effect_plan.effect_plan_root()?;
    let candidate_root = candidate_plan.effect_plan_root()?;
    if expected_root != candidate_root {
        return Ok(Err(
            ZDEXBuybackShadowComposerRejectCodeV2::FINAL_EFFECT_PLAN_MISMATCH,
        ));
    }
    Ok(Ok(()))
}

/// Crate-private SHADOW replay experiment.  It takes locally rederived lane
/// wrappers and is intentionally unreachable through the public API.
pub(crate) fn apply_final_composite_once_v2(
    state: &ZDEXBuybackShadowComposerStateV2,
    spot_accepted: &ZDEXSpotBuybackAcceptedV2,
    tokenomics_accepted: &ZDEXTokenomicsBuybackAcceptedV2,
) -> AbiResultV1<ZDEXBuybackShadowComposerResultV2> {
    let composed = match derive_complete_composed_plan_v2(spot_accepted, tokenomics_accepted)? {
        Ok(composed) => composed,
        Err(code) => return composer_reject_v2(code, state),
    };
    let binding = accepted_binding_v2(&composed)?;
    record_accepted_binding_v2(
        state,
        composed.command_occurrence_id,
        binding,
        composed.final_effect_plan,
    )
}

/// Record a rederived accepted binding for this SHADOW-only experiment.
///
/// The command occurrence is the replay key. The binding covers the exact
/// two-lane journals, terminal, and fully composed effect-plan root. This is
/// deliberately private: no caller-supplied claim can drive replay state or
/// obtain an effect plan through the public crate API.
fn record_accepted_binding_v2(
    state: &ZDEXBuybackShadowComposerStateV2,
    command_occurrence_id: RootV1,
    accepted_binding_root: RootV1,
    final_effect_plan: GlobalEconomicEffectPlanV1,
) -> AbiResultV1<ZDEXBuybackShadowComposerResultV2> {
    final_effect_plan.validate()?;
    match state.accepted_binding_for(&command_occurrence_id) {
        Some(existing) if existing == &accepted_binding_root => {
            Ok(ZDEXBuybackShadowComposerResultV2::AlreadyAccepted(
                ZDEXBuybackShadowComposerAlreadyAcceptedV2 {
                    command_occurrence_id,
                    accepted_binding_root,
                },
            ))
        }
        Some(_) => composer_reject_v2(ZDEXBuybackShadowComposerRejectCodeV2::EQUIVOCATION, state),
        None => {
            let mut next_state = state.clone();
            next_state
                .accepted_bindings_by_occurrence
                .insert(command_occurrence_id.clone(), accepted_binding_root.clone());
            Ok(ZDEXBuybackShadowComposerResultV2::Applied(
                ZDEXBuybackShadowComposerAppliedV2 {
                    next_state,
                    command_occurrence_id,
                    accepted_binding_root,
                    final_effect_plan,
                },
            ))
        }
    }
}

fn derive_complete_composed_plan_v2(
    spot_accepted: &ZDEXSpotBuybackAcceptedV2,
    tokenomics_accepted: &ZDEXTokenomicsBuybackAcceptedV2,
) -> AbiResultV1<Result<ZDEXBuybackShadowComposedPlanV2, ZDEXBuybackShadowComposerRejectCodeV2>> {
    if spot_accepted.validate().is_err() {
        return Ok(Err(
            ZDEXBuybackShadowComposerRejectCodeV2::SPOT_ACCEPTED_WRAPPER_INVALID,
        ));
    }
    let phase_a_is_nonapplicable = matches!(
        tokenomics_accepted.phase_a_effect_plan_is_applicable(),
        Ok(false)
    );
    if tokenomics_accepted.validate().is_err() || !phase_a_is_nonapplicable {
        return Ok(Err(
            ZDEXBuybackShadowComposerRejectCodeV2::TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
        ));
    }

    let spot_terminal = match spot_accepted.terminal_obligation() {
        Ok(terminal) => terminal,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::SPOT_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let tokenomics_terminal = match tokenomics_accepted.terminal_obligation() {
        Ok(terminal) => terminal,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    if spot_terminal != tokenomics_terminal {
        return Ok(Err(
            ZDEXBuybackShadowComposerRejectCodeV2::CROSS_LANE_BINDING_MISMATCH,
        ));
    }

    let spot_effects = match effect_plan_from_spot_accepted_v2(spot_accepted) {
        Ok(effects) => effects,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::SPOT_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let tokenomics_effects = match tokenomics_accepted.effects() {
        Ok(effects) => effects.clone(),
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let spot_pre_root = match spot_accepted.pre_state() {
        Ok(state) => state.state_root()?,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::SPOT_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let spot_post_root = match spot_accepted.post_state() {
        Ok(state) => state.state_root()?,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::SPOT_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let tokenomics_pre_root = match tokenomics_accepted.pre_state() {
        Ok(state) => state.state_root()?,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let tokenomics_post_root = match tokenomics_accepted.post_state() {
        Ok(state) => state.state_root()?,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let expected_spot_write = LaneWriteV1 {
        lane_id: LaneIdV1::SPOT_LIQUIDITY,
        pre_root: spot_pre_root,
        post_root: spot_post_root,
    };
    let expected_tokenomics_write = LaneWriteV1 {
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        pre_root: tokenomics_pre_root,
        post_root: tokenomics_post_root,
    };
    let command_occurrence_id = spot_terminal
        .context
        .coordinates
        .command_occurrence_id
        .clone();
    if spot_effects.lane_writes != vec![expected_spot_write.clone()]
        || tokenomics_effects.lane_writes != vec![expected_tokenomics_write.clone()]
        || !spot_effects.asset_conservation.is_empty()
        || !spot_effects.fee_conservation.is_empty()
        || !spot_effects.occurrence_consumptions.is_empty()
        || !spot_effects.external_outbox_enqueue.is_empty()
        || tokenomics_effects.occurrence_consumptions != vec![command_occurrence_id.clone()]
        || !tokenomics_effects.external_outbox_enqueue.is_empty()
    {
        return Ok(Err(
            ZDEXBuybackShadowComposerRejectCodeV2::CROSS_LANE_BINDING_MISMATCH,
        ));
    }

    let final_effect_plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: compose_effect_rows_v2(&spot_effects, &tokenomics_effects)?,
        asset_conservation: tokenomics_effects.asset_conservation.clone(),
        fee_conservation: tokenomics_effects.fee_conservation.clone(),
        lane_writes: vec![expected_spot_write, expected_tokenomics_write],
        occurrence_consumptions: vec![command_occurrence_id.clone()],
        external_outbox_enqueue: Vec::new(),
    };
    final_effect_plan.validate()?;
    let spot_journal_root = match spot_accepted.journal() {
        Ok(journal) => journal.journal_root()?,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::SPOT_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    let tokenomics_journal_root = match tokenomics_accepted.journal() {
        Ok(journal) => journal.journal_root()?,
        Err(_) => {
            return Ok(Err(
                ZDEXBuybackShadowComposerRejectCodeV2::TOKENOMICS_ACCEPTED_WRAPPER_INVALID,
            ))
        }
    };
    Ok(Ok(ZDEXBuybackShadowComposedPlanV2 {
        command_occurrence_id,
        spot_journal_root,
        tokenomics_journal_root,
        terminal_obligation_id: spot_terminal.obligation_id()?,
        final_effect_plan,
    }))
}

fn compose_effect_rows_v2(
    spot_effects: &GlobalEconomicEffectPlanV1,
    tokenomics_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<EconomicEffectRowV1>> {
    type EffectKey = (String, String, String, String);
    let mut totals = BTreeMap::<EffectKey, (EconomicEffectRowV1, i128)>::new();
    for row in spot_effects.rows.iter().chain(&tokenomics_effects.rows) {
        let key = (
            effect_kind_label_v2(row.kind).to_owned(),
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let prior = totals.get(&key).map(|(_, value)| *value).unwrap_or(0);
        let total = prior
            .checked_add(row.delta_atoms)
            .ok_or(AbiErrorV1::Conservation(
                "Buyback V2 composed effect overflow",
            ))?;
        totals.insert(key, (row.clone(), total));
    }
    Ok(totals
        .into_values()
        .filter_map(|(mut row, total)| {
            if total == 0 {
                None
            } else {
                row.delta_atoms = total;
                Some(row)
            }
        })
        .collect())
}

fn effect_kind_label_v2(kind: EconomicEffectKindV1) -> &'static str {
    match kind {
        EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV1::ISSUE => "ISSUE",
        EconomicEffectKindV1::BURN => "BURN",
        EconomicEffectKindV1::CUSTODY => "CUSTODY",
        EconomicEffectKindV1::LIABILITY => "LIABILITY",
        EconomicEffectKindV1::RESERVE => "RESERVE",
        EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV1::REWARD => "REWARD",
        EconomicEffectKindV1::SLASH => "SLASH",
    }
}

fn accepted_binding_v2(composed: &ZDEXBuybackShadowComposedPlanV2) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Canonical<'a> {
        schema: &'static str,
        command_occurrence_id: &'a RootV1,
        spot_journal_root: &'a RootV1,
        tokenomics_journal_root: &'a RootV1,
        terminal_obligation_id: &'a RootV1,
        final_effect_plan_root: &'a RootV1,
    }
    let final_effect_plan_root = composed.final_effect_plan.effect_plan_root()?;
    hash_global_v1(
        "zdex-buyback-shadow-composer-binding-research-draft-v2",
        &Canonical {
            schema: "zenodex/zdex-buyback-shadow-composer-binding-research-draft/v2",
            command_occurrence_id: &composed.command_occurrence_id,
            spot_journal_root: &composed.spot_journal_root,
            tokenomics_journal_root: &composed.tokenomics_journal_root,
            terminal_obligation_id: &composed.terminal_obligation_id,
            final_effect_plan_root: &final_effect_plan_root,
        },
    )
}

fn composer_reject_v2(
    code: ZDEXBuybackShadowComposerRejectCodeV2,
    state: &ZDEXBuybackShadowComposerStateV2,
) -> AbiResultV1<ZDEXBuybackShadowComposerResultV2> {
    let rejected = ZDEXBuybackShadowComposerRejectedV2 {
        code,
        retained_state: state.clone(),
        effects: empty_effect_plan_v2(),
    };
    rejected.validate()?;
    Ok(ZDEXBuybackShadowComposerResultV2::Rejected(rejected))
}

fn empty_effect_plan_v2() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: Vec::new(),
        occurrence_consumptions: Vec::new(),
        external_outbox_enqueue: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        accepted_binding_v2, record_accepted_binding_v2, ZDEXBuybackShadowComposedPlanV2,
        ZDEXBuybackShadowComposerRejectCodeV2, ZDEXBuybackShadowComposerResultV2,
        ZDEXBuybackShadowComposerStateV2,
    };
    use crate::canonical::{RootV1, GLOBAL_SETTLEMENT_ABI_V1};
    use crate::effects::GlobalEconomicEffectPlanV1;

    fn root(value: u64) -> RootV1 {
        RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root")
    }

    fn empty_plan() -> GlobalEconomicEffectPlanV1 {
        GlobalEconomicEffectPlanV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            rows: Vec::new(),
            asset_conservation: Vec::new(),
            fee_conservation: Vec::new(),
            lane_writes: Vec::new(),
            occurrence_consumptions: Vec::new(),
            external_outbox_enqueue: Vec::new(),
        }
    }

    fn composed_for_terminal(terminal_marker: u64) -> ZDEXBuybackShadowComposedPlanV2 {
        ZDEXBuybackShadowComposedPlanV2 {
            command_occurrence_id: root(92),
            spot_journal_root: root(101),
            tokenomics_journal_root: root(102),
            terminal_obligation_id: root(terminal_marker),
            final_effect_plan: empty_plan(),
        }
    }

    #[test]
    fn same_occurrence_with_terminal_110_and_111_is_equivocation() {
        let binding_110 =
            accepted_binding_v2(&composed_for_terminal(110)).expect("binding for terminal 110");
        let binding_111 =
            accepted_binding_v2(&composed_for_terminal(111)).expect("binding for terminal 111");
        assert_ne!(binding_110, binding_111);
        let ZDEXBuybackShadowComposerResultV2::Applied(first) = record_accepted_binding_v2(
            &ZDEXBuybackShadowComposerStateV2::default(),
            root(92),
            binding_110,
            empty_plan(),
        )
        .expect("first accepted binding") else {
            panic!("first occurrence must record its accepted binding");
        };
        let ZDEXBuybackShadowComposerResultV2::Rejected(rejected) =
            record_accepted_binding_v2(&first.next_state, root(92), binding_111, empty_plan())
                .expect("second accepted binding")
        else {
            panic!("same occurrence with a distinct accepted binding must reject");
        };
        assert_eq!(
            rejected.code,
            ZDEXBuybackShadowComposerRejectCodeV2::EQUIVOCATION
        );
        assert_eq!(rejected.retained_state, first.next_state);
        rejected.validate().expect("equivocation is exact no-op");
    }

    #[test]
    fn same_occurrence_with_identical_binding_is_idempotent() {
        let binding = accepted_binding_v2(&composed_for_terminal(111)).expect("binding");
        let ZDEXBuybackShadowComposerResultV2::Applied(first) = record_accepted_binding_v2(
            &ZDEXBuybackShadowComposerStateV2::default(),
            root(92),
            binding.clone(),
            empty_plan(),
        )
        .expect("first accepted binding") else {
            panic!("first occurrence must record its accepted binding");
        };
        let ZDEXBuybackShadowComposerResultV2::AlreadyAccepted(retry) =
            record_accepted_binding_v2(&first.next_state, root(92), binding.clone(), empty_plan())
                .expect("exact retry")
        else {
            panic!("exact accepted binding retry must report already accepted");
        };
        assert_eq!(retry.command_occurrence_id, root(92));
        assert_eq!(retry.accepted_binding_root, binding);
    }
}
