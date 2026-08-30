//! SHADOW-only Tokenomics V2 terminal leaf.
//!
//! Phase A is rederived from the stable V1 intent kernel.  Its effect plan is
//! a commitment, never an independently applicable plan.  Phase B consumes a
//! deeply validated V2 terminal and builds one final composite plan.  This
//! module proves no Spot provenance and performs no receipt authentication.

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::release::LaneIdV1;
use crate::zdex_atomic_buyback_quote_port_v2::ZDEXAtomicBuybackQuotePortV2;
use crate::zdex_hyperdeflation::retained_supply_atoms_v1;
use crate::zdex_purchase_burn_types::{
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1, ZDEX_SUPPLY_PRINCIPAL_V1,
};
use crate::zdex_spot_buyback_transition::{ZDEXSpotFlowRoleV1, ZDEXSpotTerminalObligationV1};
use crate::zdex_spot_buyback_transition_v2::{
    ZDEXSpotFlowIdentityV2, ZDEXSpotTerminalObligationV2,
};
use crate::zdex_tokenomics_buyback_transition::{
    derive_zdex_tokenomics_buyback_intent_v1, ZDEXTokenomicsBurnRejectCodeV1,
    ZDEXTokenomicsBuybackAuthorityInputV1, ZDEXTokenomicsBuybackIntentInputV1,
    ZDEXTokenomicsBuybackIntentResultV1, ZDEXTokenomicsBuybackIntentV1,
    ZDEXTokenomicsBuybackLaneStateV1, ZDEXTokenomicsBuybackRejectCodeV1,
    ZDEXTokenomicsSafeLimitPortV1,
};

pub const ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2: &str =
    "zenodex/zdex-tokenomics-buyback-transition-journal/v2";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsBuybackRejectCodeV2 {
    PHASE_A_REJECTED(ZDEXTokenomicsBuybackRejectCodeV1),
    TERMINAL_MALFORMED,
    TERMINAL_VERSION_MISMATCH,
    TERMINAL_BINDING_MISMATCH,
    QUOTE_FLOW_MISMATCH,
    BURN_REJECTED(ZDEXTokenomicsBurnRejectCodeV1),
}

/// Closed terminal input keeps a V2 terminal structurally distinct from a
/// V1 rewrap.  The latter never reaches arithmetic or an effect plan.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsTerminalInputV2 {
    TERMINAL(Box<ZDEXSpotTerminalObligationV2>),
    V1_REWRAP(Box<ZDEXSpotTerminalObligationV1>),
    MALFORMED,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackInputV2 {
    pub intent_input: ZDEXTokenomicsBuybackIntentInputV1,
    pub terminal_obligation: ZDEXTokenomicsTerminalInputV2,
}

/// Phase A remains a commitment.  No API exposes a plan-application path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackIntentV2 {
    stable_intent: ZDEXTokenomicsBuybackIntentV1,
}

impl ZDEXTokenomicsBuybackIntentV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.stable_intent.validate()
    }

    pub fn quote_output(&self) -> AbiResultV1<&ZDEXAtomicBuybackQuotePortV2> {
        self.validate()?;
        Ok(self.stable_intent.quote_output())
    }

    pub fn phase_a_effect_plan_is_applicable(&self) -> AbiResultV1<bool> {
        self.validate()?;
        Ok(false)
    }
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXTokenomicsBuybackIntentResultV2 {
    Accepted(Box<ZDEXTokenomicsBuybackIntentV2>),
    Rejected(Box<ZDEXTokenomicsBuybackRejectedV2>),
}

pub fn derive_zdex_tokenomics_buyback_intent_v2(
    candidate: &ZDEXTokenomicsBuybackIntentInputV1,
) -> AbiResultV1<ZDEXTokenomicsBuybackIntentResultV2> {
    match derive_zdex_tokenomics_buyback_intent_v1(candidate)? {
        ZDEXTokenomicsBuybackIntentResultV1::Accepted(intent) => {
            Ok(ZDEXTokenomicsBuybackIntentResultV2::Accepted(Box::new(
                ZDEXTokenomicsBuybackIntentV2 {
                    stable_intent: *intent,
                },
            )))
        }
        ZDEXTokenomicsBuybackIntentResultV1::Rejected(rejected) => {
            Ok(ZDEXTokenomicsBuybackIntentResultV2::Rejected(Box::new(
                ZDEXTokenomicsBuybackRejectedV2::new(
                    ZDEXTokenomicsBuybackRejectCodeV2::PHASE_A_REJECTED(rejected.code()),
                    &candidate.pre_state,
                )?,
            )))
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackJournalV2 {
    pub phase_a_context_root: RootV1,
    pub quote_port_root: RootV1,
    pub terminal_obligation_id: RootV1,
    pub pre_state_root: RootV1,
    pub spend_post_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effect_plan_root: RootV1,
    pub purchased_zdex_atoms: u128,
    pub burned_zdex_atoms: u128,
    pub live_supply_pre_atoms: u128,
    pub live_supply_post_atoms: u128,
    pub retained_supply_atoms: u128,
    pub remaining_epoch_burn_cap_pre_atoms: u128,
    pub remaining_epoch_burn_cap_post_atoms: u128,
}

impl ZDEXTokenomicsBuybackJournalV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.phase_a_context_root,
            &self.quote_port_root,
            &self.terminal_obligation_id,
            &self.pre_state_root,
            &self.spend_post_state_root,
            &self.post_state_root,
            &self.effect_plan_root,
        ] {
            root.validate("Tokenomics V2 journal root", false)?;
        }
        let burn_holds = self.burned_zdex_atoms != 0
            && self.purchased_zdex_atoms == self.burned_zdex_atoms
            && self
                .live_supply_post_atoms
                .checked_add(self.burned_zdex_atoms)
                == Some(self.live_supply_pre_atoms)
            && self.retained_supply_atoms != 0
            && self.retained_supply_atoms <= self.live_supply_post_atoms
            && self
                .remaining_epoch_burn_cap_post_atoms
                .checked_add(self.burned_zdex_atoms)
                == Some(self.remaining_epoch_burn_cap_pre_atoms)
            && self.pre_state_root != self.spend_post_state_root
            && self.spend_post_state_root != self.post_state_root;
        if !burn_holds {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics V2 journal accounting projection",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            phase_a_context_root: &'a RootV1,
            quote_port_root: &'a RootV1,
            terminal_obligation_id: &'a RootV1,
            pre_state_root: &'a RootV1,
            spend_post_state_root: &'a RootV1,
            post_state_root: &'a RootV1,
            effect_plan_root: &'a RootV1,
            purchased_zdex_atoms: u128,
            burned_zdex_atoms: u128,
            live_supply_pre_atoms: u128,
            live_supply_post_atoms: u128,
            retained_supply_atoms: u128,
            remaining_epoch_burn_cap_pre_atoms: u128,
            remaining_epoch_burn_cap_post_atoms: u128,
        }
        hash_global_v1(
            "zdex-tokenomics-buyback-transition-journal-v2",
            &Canonical {
                schema: ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2,
                phase_a_context_root: &self.phase_a_context_root,
                quote_port_root: &self.quote_port_root,
                terminal_obligation_id: &self.terminal_obligation_id,
                pre_state_root: &self.pre_state_root,
                spend_post_state_root: &self.spend_post_state_root,
                post_state_root: &self.post_state_root,
                effect_plan_root: &self.effect_plan_root,
                purchased_zdex_atoms: self.purchased_zdex_atoms,
                burned_zdex_atoms: self.burned_zdex_atoms,
                live_supply_pre_atoms: self.live_supply_pre_atoms,
                live_supply_post_atoms: self.live_supply_post_atoms,
                retained_supply_atoms: self.retained_supply_atoms,
                remaining_epoch_burn_cap_pre_atoms: self.remaining_epoch_burn_cap_pre_atoms,
                remaining_epoch_burn_cap_post_atoms: self.remaining_epoch_burn_cap_post_atoms,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackRejectedV2 {
    code: ZDEXTokenomicsBuybackRejectCodeV2,
    pre_state: ZDEXTokenomicsBuybackLaneStateV1,
    post_state: ZDEXTokenomicsBuybackLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXTokenomicsBuybackRejectedV2 {
    fn new(
        code: ZDEXTokenomicsBuybackRejectCodeV2,
        state: &ZDEXTokenomicsBuybackLaneStateV1,
    ) -> AbiResultV1<Self> {
        state.validate()?;
        Ok(Self {
            code,
            pre_state: state.clone(),
            post_state: state.clone(),
            effects: empty_effect_plan_v2(),
        })
    }

    pub fn code(&self) -> ZDEXTokenomicsBuybackRejectCodeV2 {
        self.code
    }

    pub fn pre_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics V2 rejection exact no-effect no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ZDEXTokenomicsBuybackAcceptedFieldsV2 {
    intent: ZDEXTokenomicsBuybackIntentV1,
    post_state: ZDEXTokenomicsBuybackLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    terminal: ZDEXSpotTerminalObligationV2,
    journal: ZDEXTokenomicsBuybackJournalV2,
}

impl ZDEXTokenomicsBuybackAcceptedFieldsV2 {
    fn validate(&self) -> AbiResultV1<()> {
        self.intent.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.terminal.validate()?;
        self.journal.validate()?;
        let pre_root = self.intent.pre_state().state_root()?;
        let spend_post_root = self.intent.spend_post_state().state_root()?;
        let post_root = self.post_state.state_root()?;
        if self.journal.phase_a_context_root != *self.intent.context_root()
            || self.journal.quote_port_root != self.intent.quote_output().port_root()?
            || self.journal.terminal_obligation_id != self.terminal.obligation_id()?
            || self.journal.pre_state_root != pre_root
            || self.journal.spend_post_state_root != spend_post_root
            || self.journal.post_state_root != post_root
            || self.journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.journal.live_supply_post_atoms != self.post_state.supply.live_supply_atoms
            || self.journal.remaining_epoch_burn_cap_post_atoms
                != self.post_state.supply.remaining_epoch_burn_cap_atoms
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics V2 accepted projection binding",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackAcceptedV2 {
    subject: ZDEXTokenomicsBuybackInputV2,
    fields: ZDEXTokenomicsBuybackAcceptedFieldsV2,
}

impl ZDEXTokenomicsBuybackAcceptedV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.fields.validate()?;
        match derive_zdex_tokenomics_buyback_v2(&self.subject)? {
            ZDEXTokenomicsBuybackDerivationV2::Accepted(expected)
                if expected.as_ref() == &self.fields =>
            {
                Ok(())
            }
            _ => Err(AbiErrorV1::InvalidBinding(
                "Tokenomics V2 accepted projection no longer rederives",
            )),
        }
    }

    pub fn phase_a_effect_plan_is_applicable(&self) -> AbiResultV1<bool> {
        self.validate()?;
        Ok(false)
    }

    pub fn pre_state(&self) -> AbiResultV1<&ZDEXTokenomicsBuybackLaneStateV1> {
        self.validate()?;
        Ok(self.fields.intent.pre_state())
    }

    pub fn post_state(&self) -> AbiResultV1<&ZDEXTokenomicsBuybackLaneStateV1> {
        self.validate()?;
        Ok(&self.fields.post_state)
    }

    pub fn effects(&self) -> AbiResultV1<&GlobalEconomicEffectPlanV1> {
        self.validate()?;
        Ok(&self.fields.effects)
    }

    pub fn terminal_obligation(&self) -> AbiResultV1<&ZDEXSpotTerminalObligationV2> {
        self.validate()?;
        Ok(&self.fields.terminal)
    }

    pub fn journal(&self) -> AbiResultV1<&ZDEXTokenomicsBuybackJournalV2> {
        self.validate()?;
        Ok(&self.fields.journal)
    }
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXTokenomicsBuybackResultV2 {
    Accepted(Box<ZDEXTokenomicsBuybackAcceptedV2>),
    Rejected(Box<ZDEXTokenomicsBuybackRejectedV2>),
}

enum ZDEXTokenomicsBuybackDerivationV2 {
    Accepted(Box<ZDEXTokenomicsBuybackAcceptedFieldsV2>),
    Rejected(ZDEXTokenomicsBuybackRejectCodeV2),
}

pub fn transition_zdex_tokenomics_buyback_v2(
    candidate: &ZDEXTokenomicsBuybackInputV2,
) -> AbiResultV1<ZDEXTokenomicsBuybackResultV2> {
    match derive_zdex_tokenomics_buyback_v2(candidate)? {
        ZDEXTokenomicsBuybackDerivationV2::Accepted(fields) => Ok(
            ZDEXTokenomicsBuybackResultV2::Accepted(Box::new(ZDEXTokenomicsBuybackAcceptedV2 {
                subject: candidate.clone(),
                fields: *fields,
            })),
        ),
        ZDEXTokenomicsBuybackDerivationV2::Rejected(code) => {
            Ok(ZDEXTokenomicsBuybackResultV2::Rejected(Box::new(
                ZDEXTokenomicsBuybackRejectedV2::new(code, &candidate.intent_input.pre_state)?,
            )))
        }
    }
}

fn derive_zdex_tokenomics_buyback_v2(
    candidate: &ZDEXTokenomicsBuybackInputV2,
) -> AbiResultV1<ZDEXTokenomicsBuybackDerivationV2> {
    let intent = match derive_zdex_tokenomics_buyback_intent_v1(&candidate.intent_input)? {
        ZDEXTokenomicsBuybackIntentResultV1::Accepted(intent) => *intent,
        ZDEXTokenomicsBuybackIntentResultV1::Rejected(rejected) => {
            return Ok(ZDEXTokenomicsBuybackDerivationV2::Rejected(
                ZDEXTokenomicsBuybackRejectCodeV2::PHASE_A_REJECTED(rejected.code()),
            ));
        }
    };
    let terminal = match &candidate.terminal_obligation {
        ZDEXTokenomicsTerminalInputV2::TERMINAL(terminal) if terminal.validate().is_ok() => {
            terminal.as_ref()
        }
        ZDEXTokenomicsTerminalInputV2::V1_REWRAP(_) => {
            return Ok(ZDEXTokenomicsBuybackDerivationV2::Rejected(
                ZDEXTokenomicsBuybackRejectCodeV2::TERMINAL_VERSION_MISMATCH,
            ));
        }
        ZDEXTokenomicsTerminalInputV2::TERMINAL(_) | ZDEXTokenomicsTerminalInputV2::MALFORMED => {
            return Ok(ZDEXTokenomicsBuybackDerivationV2::Rejected(
                ZDEXTokenomicsBuybackRejectCodeV2::TERMINAL_MALFORMED,
            ));
        }
    };
    let authority = match &candidate.intent_input.authority {
        ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority) => authority.as_ref(),
        ZDEXTokenomicsBuybackAuthorityInputV1::MALFORMED => {
            return Ok(ZDEXTokenomicsBuybackDerivationV2::Rejected(
                ZDEXTokenomicsBuybackRejectCodeV2::PHASE_A_REJECTED(
                    ZDEXTokenomicsBuybackRejectCodeV1::AUTHORITY_MALFORMED,
                ),
            ));
        }
    };
    if let Some(code) = terminal_binding_reject_v2(
        &intent,
        authority,
        &candidate.intent_input.safe_limit_port,
        terminal,
    )? {
        return Ok(ZDEXTokenomicsBuybackDerivationV2::Rejected(code));
    }
    let amounts = match burn_amounts_v2(
        &candidate.intent_input.pre_state,
        terminal.purchased_atoms,
        authority,
    )? {
        Ok(amounts) => amounts,
        Err(code) => {
            return Ok(ZDEXTokenomicsBuybackDerivationV2::Rejected(
                ZDEXTokenomicsBuybackRejectCodeV2::BURN_REJECTED(code),
            ));
        }
    };
    let mut post_state = intent.spend_post_state().clone();
    post_state.supply.live_supply_atoms = amounts.live_post;
    post_state.supply.remaining_epoch_burn_cap_atoms = amounts.cap_post;
    let effects = build_effects_v2(
        &intent,
        &post_state,
        &authority.execution_policy.zdex_asset_id,
        &amounts,
    )?;
    let journal = ZDEXTokenomicsBuybackJournalV2 {
        phase_a_context_root: intent.context_root().clone(),
        quote_port_root: intent.quote_output().port_root()?,
        terminal_obligation_id: terminal.obligation_id()?,
        pre_state_root: intent.pre_state().state_root()?,
        spend_post_state_root: intent.spend_post_state().state_root()?,
        post_state_root: post_state.state_root()?,
        effect_plan_root: effects.effect_plan_root()?,
        purchased_zdex_atoms: terminal.purchased_atoms,
        burned_zdex_atoms: amounts.purchased,
        live_supply_pre_atoms: amounts.live_pre,
        live_supply_post_atoms: amounts.live_post,
        retained_supply_atoms: amounts.retained,
        remaining_epoch_burn_cap_pre_atoms: amounts.cap_pre,
        remaining_epoch_burn_cap_post_atoms: amounts.cap_post,
    };
    let fields = ZDEXTokenomicsBuybackAcceptedFieldsV2 {
        intent,
        post_state,
        effects,
        terminal: terminal.clone(),
        journal,
    };
    fields.validate()?;
    Ok(ZDEXTokenomicsBuybackDerivationV2::Accepted(Box::new(
        fields,
    )))
}

fn terminal_binding_reject_v2(
    intent: &ZDEXTokenomicsBuybackIntentV1,
    authority: &crate::ZDEXTokenomicsBuybackAuthorityContextV1,
    safe_limit: &ZDEXTokenomicsSafeLimitPortV1,
    terminal: &ZDEXSpotTerminalObligationV2,
) -> AbiResultV1<Option<ZDEXTokenomicsBuybackRejectCodeV2>> {
    let quote = intent.quote_output();
    let coordinates = &terminal.context.coordinates;
    let roots_match = coordinates.profile_root == authority.profile_root
        && coordinates.route_release_id == authority.route_release_id
        && coordinates.command_occurrence_id == authority.command_occurrence_id
        && coordinates.global_pre_state_root == authority.global_pre_state_root
        && coordinates.producer_quote_pre_state_root == quote.producer_quote_pre_state_root
        && coordinates.producer_quote_post_state_root == quote.producer_quote_post_state_root
        && coordinates.producer_quote_effect_plan_root == quote.producer_quote_effect_plan_root
        && coordinates.quote_port_root == quote.port_root()?;
    let context_match = terminal.context.chain_id == authority.chain_id
        && terminal.context.deployment_root == authority.deployment_root
        && terminal.context.writer_epoch == authority.writer_epoch
        && terminal.context.current_height == authority.current_height
        && terminal.context.spot_module_release_id == authority.spot_module_release_id
        && terminal.context.tokenomics_module_release_id == authority.tokenomics_module_release_id
        && terminal.context.execution_policy_root == authority.execution_policy.policy_root()?
        && terminal.context.price_policy_root == authority.price_policy_root
        && terminal.context.oracle_occurrence_id == safe_limit.oracle_occurrence_id;
    let burn_principal = zdex_occurrence_burn_port_v1(
        &authority.profile_root,
        &authority.route_release_id,
        &authority.command_occurrence_id,
    )?;
    if !roots_match
        || !context_match
        || terminal.consumer_module_release_id != authority.tokenomics_module_release_id
        || terminal.burn_asset != authority.execution_policy.zdex_asset_id
        || terminal.burn_principal != burn_principal
        || terminal.selected_pool_id != authority.execution_policy.pool_id
    {
        return Ok(Some(
            ZDEXTokenomicsBuybackRejectCodeV2::TERMINAL_BINDING_MISMATCH,
        ));
    }
    let expected_quote = ZDEXSpotFlowIdentityV2 {
        role: ZDEXSpotFlowRoleV1::QUOTE_INPUT,
        context: terminal.context.clone(),
        selected_pool_id: authority.execution_policy.pool_id.clone(),
        asset: authority.execution_policy.quote_asset_id.clone(),
        source_principal: quote.source_principal().to_owned(),
        destination_principal: quote.destination_principal()?,
        amount_atoms: quote.amount_atoms,
    };
    let expected_purchased = ZDEXSpotFlowIdentityV2 {
        role: ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT,
        context: terminal.context.clone(),
        selected_pool_id: authority.execution_policy.pool_id.clone(),
        asset: authority.execution_policy.zdex_asset_id.clone(),
        source_principal: zdex_pool_reserve_principal_v1(
            &authority.execution_policy.pool_id,
            &authority.execution_policy.zdex_asset_id,
        )?,
        destination_principal: burn_principal,
        amount_atoms: terminal.purchased_atoms,
    };
    if terminal.quote_input_flow_id != expected_quote.flow_id()?
        || terminal.purchased_output_flow_id != expected_purchased.flow_id()?
    {
        return Ok(Some(ZDEXTokenomicsBuybackRejectCodeV2::QUOTE_FLOW_MISMATCH));
    }
    Ok(None)
}

struct BurnAmountsV2 {
    purchased: u128,
    retained: u128,
    live_pre: u128,
    live_post: u128,
    cap_pre: u128,
    cap_post: u128,
}

fn burn_amounts_v2(
    state: &ZDEXTokenomicsBuybackLaneStateV1,
    purchased: u128,
    authority: &crate::ZDEXTokenomicsBuybackAuthorityContextV1,
) -> AbiResultV1<Result<BurnAmountsV2, ZDEXTokenomicsBurnRejectCodeV1>> {
    let supply = &state.supply;
    let retained =
        retained_supply_atoms_v1(supply.live_supply_atoms, &authority.hyperdeflation_policy)?;
    let ratio_headroom = supply
        .live_supply_atoms
        .checked_sub(retained)
        .ok_or(AbiErrorV1::InvalidBounds("Tokenomics V2 retained supply"))?;
    if ratio_headroom == 0 {
        return Ok(Err(
            ZDEXTokenomicsBurnRejectCodeV1::RETAINED_SUPPLY_FLOOR_REACHED,
        ));
    }
    if supply.remaining_epoch_burn_cap_atoms == 0 {
        return Ok(Err(ZDEXTokenomicsBurnRejectCodeV1::EPOCH_BURN_CAP_REACHED));
    }
    if purchased > ratio_headroom.min(supply.remaining_epoch_burn_cap_atoms) {
        return Ok(Err(ZDEXTokenomicsBurnRejectCodeV1::BURN_EXCEEDS_CAPACITY));
    }
    Ok(Ok(BurnAmountsV2 {
        purchased,
        retained,
        live_pre: supply.live_supply_atoms,
        live_post: supply.live_supply_atoms - purchased,
        cap_pre: supply.remaining_epoch_burn_cap_atoms,
        cap_post: supply.remaining_epoch_burn_cap_atoms - purchased,
    }))
}

fn build_effects_v2(
    intent: &ZDEXTokenomicsBuybackIntentV1,
    post_state: &ZDEXTokenomicsBuybackLaneStateV1,
    zdex_asset_id: &RootV1,
    amounts: &BurnAmountsV2,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let mut rows = intent.spend_effects().rows.clone();
    let burn_delta = i128::try_from(amounts.purchased)
        .map_err(|_| AbiErrorV1::InvalidBounds("Tokenomics V2 burn effect width"))?;
    rows.push(EconomicEffectRowV1 {
        kind: EconomicEffectKindV1::BURN,
        principal: ZDEX_SUPPLY_PRINCIPAL_V1.to_owned(),
        asset: zdex_asset_id.to_string(),
        custody_domain: PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1.to_owned(),
        delta_atoms: -burn_delta,
    });
    rows.sort_by(effect_row_order_v2);
    let mut asset_conservation = intent.spend_effects().asset_conservation.clone();
    asset_conservation.push(AssetConservationRowV1 {
        asset: zdex_asset_id.to_string(),
        owned_and_custodied_pre_atoms: amounts.live_pre,
        owned_and_custodied_post_atoms: amounts.live_post,
        supply_pre_atoms: amounts.live_pre,
        supply_post_atoms: amounts.live_post,
        authorized_issue_atoms: 0,
        authorized_burn_atoms: amounts.purchased,
    });
    asset_conservation.sort_by(|left, right| left.asset.cmp(&right.asset));
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows,
        asset_conservation,
        fee_conservation: intent.spend_effects().fee_conservation.clone(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: intent.pre_state().state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: intent.spend_effects().occurrence_consumptions.clone(),
        external_outbox_enqueue: Vec::new(),
    };
    effects.validate()?;
    Ok(effects)
}

fn effect_row_order_v2(
    left: &EconomicEffectRowV1,
    right: &EconomicEffectRowV1,
) -> std::cmp::Ordering {
    (
        effect_kind_name_v2(left.kind),
        left.asset.as_str(),
        left.principal.as_str(),
        left.custody_domain.as_str(),
    )
        .cmp(&(
            effect_kind_name_v2(right.kind),
            right.asset.as_str(),
            right.principal.as_str(),
            right.custody_domain.as_str(),
        ))
}

fn effect_kind_name_v2(kind: EconomicEffectKindV1) -> &'static str {
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
