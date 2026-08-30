//! Pure SHADOW route-binding and final-plan replay guard for Buyback V2.
//!
//! `ZDEXBuybackRouteReceiptClaimsV2` is deliberately only a claim shape.  An
//! outer route receipt verifier must authenticate it before calling a host
//! adapter.  This module checks exact bindings and records a local replay key;
//! it does not execute economic effects or grant settlement authority.

use std::collections::BTreeSet;

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::zdex_spot_buyback_transition::ZDEXSpotTerminalObligationV1;
use crate::zdex_spot_buyback_transition_v2::ZDEXSpotTerminalObligationV2;
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
pub struct ZDEXBuybackShadowComposerStateV2 {
    consumed_replay_keys: BTreeSet<RootV1>,
}

impl ZDEXBuybackShadowComposerStateV2 {
    pub fn is_consumed(&self, replay_key: &RootV1) -> bool {
        self.consumed_replay_keys.contains(replay_key)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXBuybackShadowComposerRejectCodeV2 {
    ACCEPTED_WRAPPER_INVALID,
    ROUTE_TERMINAL_REJECTED(ZDEXBuybackRouteTerminalRejectCodeV2),
    REPLAYED,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXBuybackShadowComposerAppliedV2 {
    pub next_state: ZDEXBuybackShadowComposerStateV2,
    pub replay_key: RootV1,
    pub final_effect_plan: GlobalEconomicEffectPlanV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXBuybackShadowComposerRejectedV2 {
    pub code: ZDEXBuybackShadowComposerRejectCodeV2,
    pub retained_state: ZDEXBuybackShadowComposerStateV2,
    pub effects: GlobalEconomicEffectPlanV1,
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
pub enum ZDEXBuybackShadowComposerResultV2 {
    Applied(ZDEXBuybackShadowComposerAppliedV2),
    Rejected(ZDEXBuybackShadowComposerRejectedV2),
}

/// Apply the final composite only to the pure replay registry and return its
/// final plan once.  A real shell must authenticate the claims and atomically
/// execute that returned plan elsewhere.
pub fn apply_final_composite_once_v2(
    state: &ZDEXBuybackShadowComposerStateV2,
    accepted: &ZDEXTokenomicsBuybackAcceptedV2,
    claims: &ZDEXBuybackRouteReceiptClaimsV2,
) -> AbiResultV1<ZDEXBuybackShadowComposerResultV2> {
    let terminal = match accepted.terminal_obligation() {
        Ok(terminal) => terminal,
        Err(_) => {
            return composer_reject_v2(
                ZDEXBuybackShadowComposerRejectCodeV2::ACCEPTED_WRAPPER_INVALID,
                state,
            )
        }
    };
    if accepted.phase_a_effect_plan_is_applicable()? {
        return Err(AbiErrorV1::InvalidBinding(
            "Buyback V2 Phase A must remain non-applicable",
        ));
    }
    if let Err(code) = validate_route_terminal_claims_v2(
        claims,
        &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(terminal.clone())),
    )? {
        return composer_reject_v2(
            ZDEXBuybackShadowComposerRejectCodeV2::ROUTE_TERMINAL_REJECTED(code),
            state,
        );
    }
    let effects = accepted.effects()?.clone();
    let replay_key = replay_key_v2(&terminal.obligation_id()?, &effects.effect_plan_root()?)?;
    if state.is_consumed(&replay_key) {
        return composer_reject_v2(ZDEXBuybackShadowComposerRejectCodeV2::REPLAYED, state);
    }
    let mut next_state = state.clone();
    next_state.consumed_replay_keys.insert(replay_key.clone());
    Ok(ZDEXBuybackShadowComposerResultV2::Applied(
        ZDEXBuybackShadowComposerAppliedV2 {
            next_state,
            replay_key,
            final_effect_plan: effects,
        },
    ))
}

fn replay_key_v2(terminal_id: &RootV1, effect_plan_root: &RootV1) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Canonical<'a> {
        schema: &'static str,
        terminal_obligation_id: &'a RootV1,
        effect_plan_root: &'a RootV1,
    }
    hash_global_v1(
        "zdex-buyback-shadow-composer-replay-v2",
        &Canonical {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            terminal_obligation_id: terminal_id,
            effect_plan_root,
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
