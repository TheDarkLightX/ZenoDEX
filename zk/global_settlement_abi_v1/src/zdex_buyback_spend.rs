use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::zdex_fee_allocation::transition_zdex_fee_allocation_v1;
use crate::zdex_fee_allocation_types::{
    ZDEXFeeAllocationAcceptedV1, ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1, ZDEXFeeAllocationRejectCodeV1, ZDEXFeeAllocationResultV1,
    ZDEXFeeDestinationV1, ZDEXFeeStateV1,
};

pub const ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1: &str = "zenodex/zdex-buyback-spend-policy/v1";
pub const ZDEX_BUYBACK_SPEND_POLICY_KIND_V1: &str = "zdex_buyback_spend_v1";
pub const ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1: &str = "zenodex/zdex-buyback-spend-state/v1";
pub const ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1: &str = "zenodex/zdex-buyback-spend-context/v1";
pub const ZDEX_BUYBACK_SPEND_INTENT_SCHEMA_V1: &str = "zenodex/zdex-buyback-spend-intent/v1";

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ZDEXBuybackSpendRejectCodeV1 {
    POLICY_MISMATCH,
    SAME_OCCURRENCE_MISMATCH,
    STALE_STATE,
    HEIGHT_REGRESSION,
    COOLDOWN_NOT_ELAPSED,
    FEE_ALLOCATION_REJECTED,
    VERIFIED_SAFETY_MISMATCH,
    ROUTE_SAFE_LIMIT_ZERO,
    SPEND_BELOW_MINIMUM,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBuybackSpendPolicyV1 {
    pub schema: String,
    pub quote_asset_id: RootV1,
    pub minimum_quote_spend_atoms: u128,
    pub per_command_quote_cap_atoms: u128,
    pub minimum_interval_blocks: u64,
}

impl ZDEXBuybackSpendPolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback spend policy schema",
            ));
        }
        self.quote_asset_id
            .validate("ZDEX buyback spend quote asset", false)?;
        if self.minimum_quote_spend_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback minimum quote spend",
            ));
        }
        if self.per_command_quote_cap_atoms < self.minimum_quote_spend_atoms
            || self.per_command_quote_cap_atoms > i128::MAX.unsigned_abs()
        {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback per-command quote cap",
            ));
        }
        if self.minimum_interval_blocks == 0 {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback minimum interval blocks",
            ));
        }
        Ok(())
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-buyback-spend-policy-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBuybackSpendStateV1 {
    /// Cadence only. The canonical buyback balance remains in `ZDEXFeeStateV1`.
    pub schema: String,
    pub quote_asset_id: RootV1,
    pub policy_root: RootV1,
    pub last_execution_height: Option<u64>,
}

impl ZDEXBuybackSpendStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback spend state schema",
            ));
        }
        self.quote_asset_id
            .validate("ZDEX buyback spend state quote asset", false)?;
        self.policy_root
            .validate("ZDEX buyback spend state policy", false)
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-buyback-spend-state-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBuybackSpendContextV1 {
    pub schema: String,
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub expected_fee_pre_state_root: RootV1,
    pub expected_cadence_pre_state_root: RootV1,
    pub safety_limit_binding_root: RootV1,
    pub quote_asset_id: RootV1,
    pub current_height: u64,
    pub route_safe_quote_limit_atoms: u128,
}

impl ZDEXBuybackSpendContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback spend context schema",
            ));
        }
        for (root, field) in [
            (&self.profile_root, "ZDEX buyback spend profile"),
            (&self.route_release_id, "ZDEX buyback spend route release"),
            (
                &self.command_occurrence_id,
                "ZDEX buyback spend command occurrence",
            ),
            (
                &self.expected_fee_pre_state_root,
                "ZDEX buyback spend expected fee pre-state",
            ),
            (
                &self.expected_cadence_pre_state_root,
                "ZDEX buyback spend expected cadence pre-state",
            ),
            (
                &self.safety_limit_binding_root,
                "ZDEX buyback spend safety-limit binding",
            ),
            (&self.quote_asset_id, "ZDEX buyback spend quote asset"),
        ] {
            root.validate(field, false)?;
        }
        if self.route_safe_quote_limit_atoms > i128::MAX.unsigned_abs() {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback route-safe quote limit",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBuybackSpendIntentV1 {
    pub schema: String,
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub spend_policy_root: RootV1,
    pub cadence_pre_state_root: RootV1,
    pub fee_allocation_occurrence_root: RootV1,
    pub fee_pre_state_root: RootV1,
    pub fee_allocated_state_root: RootV1,
    pub safety_limit_binding_root: RootV1,
    pub quote_asset_id: RootV1,
    pub current_height: u64,
    pub buyback_reserve_before_atoms: u128,
    pub buyback_allocation_atoms: u128,
    pub available_buyback_reserve_atoms: u128,
    pub quote_spend_atoms: u128,
}

impl ZDEXBuybackSpendIntentV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_BUYBACK_SPEND_INTENT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback spend intent schema",
            ));
        }
        for (root, field) in [
            (&self.profile_root, "ZDEX buyback intent profile"),
            (&self.route_release_id, "ZDEX buyback intent route release"),
            (
                &self.command_occurrence_id,
                "ZDEX buyback intent command occurrence",
            ),
            (&self.spend_policy_root, "ZDEX buyback intent spend policy"),
            (
                &self.cadence_pre_state_root,
                "ZDEX buyback intent cadence pre-state",
            ),
            (
                &self.fee_allocation_occurrence_root,
                "ZDEX buyback intent fee occurrence",
            ),
            (
                &self.fee_pre_state_root,
                "ZDEX buyback intent fee pre-state",
            ),
            (
                &self.fee_allocated_state_root,
                "ZDEX buyback intent allocated fee state",
            ),
            (
                &self.safety_limit_binding_root,
                "ZDEX buyback intent safety-limit binding",
            ),
            (&self.quote_asset_id, "ZDEX buyback intent quote asset"),
        ] {
            root.validate(field, false)?;
        }
        if self.quote_spend_atoms == 0 || self.quote_spend_atoms > i128::MAX.unsigned_abs() {
            return Err(AbiErrorV1::InvalidBounds("ZDEX buyback intent quote spend"));
        }
        let available = self
            .buyback_reserve_before_atoms
            .checked_add(self.buyback_allocation_atoms)
            .ok_or(AbiErrorV1::InvalidBounds(
                "ZDEX buyback intent available reserve",
            ))?;
        if available != self.available_buyback_reserve_atoms
            || self.quote_spend_atoms > self.available_buyback_reserve_atoms
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX buyback intent reserve projection",
            ));
        }
        Ok(())
    }

    pub fn intent_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-buyback-spend-intent-v1", self)
    }
}

/// A validated transition result. Its fields are intentionally private so a
/// caller cannot construct a mismatched accepted result or a non-no-op reject.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXBuybackSpendAcceptedV1 {
    spend_policy: ZDEXBuybackSpendPolicyV1,
    cadence_pre_state: ZDEXBuybackSpendStateV1,
    cadence_post_state: ZDEXBuybackSpendStateV1,
    fee_policy: ZDEXFeeAllocationPolicyV1,
    fee_context: ZDEXFeeAllocationContextV1,
    fee_command: ZDEXFeeAllocationCommandV1,
    fee_allocation: ZDEXFeeAllocationAcceptedV1,
    fee_post_state: ZDEXFeeStateV1,
    context: ZDEXBuybackSpendContextV1,
    intent: ZDEXBuybackSpendIntentV1,
}

impl ZDEXBuybackSpendAcceptedV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.spend_policy.validate()?;
        self.cadence_pre_state.validate()?;
        self.cadence_post_state.validate()?;
        self.fee_policy.validate()?;
        self.fee_context.validate()?;
        self.fee_allocation.validate()?;
        self.fee_post_state.validate()?;
        self.context.validate()?;
        self.intent.validate()?;

        let recomputed = transition_zdex_fee_allocation_v1(
            &self.fee_context,
            &self.fee_allocation.pre_state,
            &self.fee_policy,
            &self.fee_command,
        )?;
        let ZDEXFeeAllocationResultV1::Accepted(recomputed) = recomputed else {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback accepted fee allocation",
            ));
        };
        if *recomputed != self.fee_allocation {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback accepted fee allocation recomputation",
            ));
        }

        let reserve_before = buyback_balance_atoms_v1(&self.fee_allocation.pre_state)?;
        let available_reserve = buyback_balance_atoms_v1(&self.fee_allocation.post_state)?;
        let expected_fee_post = fee_state_with_buyback_balance_v1(
            &self.fee_allocation.post_state,
            available_reserve
                .checked_sub(self.intent.quote_spend_atoms)
                .ok_or(AbiErrorV1::Conservation("ZDEX buyback reserve debit"))?,
        )?;
        let mut expected_cadence_post = self.cadence_pre_state.clone();
        expected_cadence_post.last_execution_height = Some(self.intent.current_height);

        if self.intent.spend_policy_root != self.spend_policy.policy_root()?
            || self.intent.cadence_pre_state_root != self.cadence_pre_state.state_root()?
            || self.intent.fee_allocation_occurrence_root
                != self.fee_allocation.occurrence.occurrence_root()?
            || self.intent.fee_pre_state_root != self.fee_allocation.pre_state.state_root()?
            || self.intent.fee_allocated_state_root
                != self.fee_allocation.post_state.state_root()?
            || self.intent.buyback_reserve_before_atoms != reserve_before
            || self.intent.buyback_allocation_atoms
                != self.fee_allocation.occurrence.buyback_quote_atoms()
            || self.intent.available_buyback_reserve_atoms != available_reserve
            || self.fee_post_state != expected_fee_post
            || self.cadence_post_state != expected_cadence_post
            || self.intent.profile_root != self.context.profile_root
            || self.intent.route_release_id != self.context.route_release_id
            || self.intent.command_occurrence_id != self.context.command_occurrence_id
            || self.intent.safety_limit_binding_root != self.context.safety_limit_binding_root
            || self.intent.quote_asset_id != self.context.quote_asset_id
            || self.intent.current_height != self.context.current_height
            || self.intent.quote_spend_atoms
                != available_reserve
                    .min(self.spend_policy.per_command_quote_cap_atoms)
                    .min(self.context.route_safe_quote_limit_atoms)
            || self.intent.quote_spend_atoms < self.spend_policy.minimum_quote_spend_atoms
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback accepted projection",
            ));
        }
        Ok(())
    }

    pub fn spend_policy(&self) -> &ZDEXBuybackSpendPolicyV1 {
        &self.spend_policy
    }

    pub fn cadence_pre_state(&self) -> &ZDEXBuybackSpendStateV1 {
        &self.cadence_pre_state
    }

    pub fn cadence_post_state(&self) -> &ZDEXBuybackSpendStateV1 {
        &self.cadence_post_state
    }

    pub fn fee_policy(&self) -> &ZDEXFeeAllocationPolicyV1 {
        &self.fee_policy
    }

    pub fn fee_context(&self) -> &ZDEXFeeAllocationContextV1 {
        &self.fee_context
    }

    pub fn fee_command(&self) -> &ZDEXFeeAllocationCommandV1 {
        &self.fee_command
    }

    pub fn fee_allocation(&self) -> &ZDEXFeeAllocationAcceptedV1 {
        &self.fee_allocation
    }

    pub fn fee_post_state(&self) -> &ZDEXFeeStateV1 {
        &self.fee_post_state
    }

    pub fn context(&self) -> &ZDEXBuybackSpendContextV1 {
        &self.context
    }

    pub fn intent(&self) -> &ZDEXBuybackSpendIntentV1 {
        &self.intent
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXBuybackSpendRejectedV1 {
    code: ZDEXBuybackSpendRejectCodeV1,
    fee_code: Option<ZDEXFeeAllocationRejectCodeV1>,
    cadence_state: ZDEXBuybackSpendStateV1,
    fee_state: ZDEXFeeStateV1,
    effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXBuybackSpendRejectedV1 {
    fn new(
        code: ZDEXBuybackSpendRejectCodeV1,
        fee_code: Option<ZDEXFeeAllocationRejectCodeV1>,
        cadence_state: ZDEXBuybackSpendStateV1,
        fee_state: ZDEXFeeStateV1,
    ) -> AbiResultV1<Self> {
        if (code == ZDEXBuybackSpendRejectCodeV1::FEE_ALLOCATION_REJECTED) != fee_code.is_some() {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback fee rejection code",
            ));
        }
        cadence_state.validate()?;
        fee_state.validate()?;
        let effects = empty_effect_plan_v1();
        effects.validate()?;
        Ok(Self {
            code,
            fee_code,
            cadence_state,
            fee_state,
            effects,
        })
    }

    pub fn code(&self) -> ZDEXBuybackSpendRejectCodeV1 {
        self.code
    }

    pub fn fee_code(&self) -> Option<ZDEXFeeAllocationRejectCodeV1> {
        self.fee_code
    }

    pub fn cadence_pre_state(&self) -> &ZDEXBuybackSpendStateV1 {
        &self.cadence_state
    }

    pub fn cadence_post_state(&self) -> &ZDEXBuybackSpendStateV1 {
        &self.cadence_state
    }

    pub fn fee_pre_state(&self) -> &ZDEXFeeStateV1 {
        &self.fee_state
    }

    pub fn fee_post_state(&self) -> &ZDEXFeeStateV1 {
        &self.fee_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXBuybackSpendResultV1 {
    Accepted(Box<ZDEXBuybackSpendAcceptedV1>),
    Rejected(Box<ZDEXBuybackSpendRejectedV1>),
}

fn empty_effect_plan_v1() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn reject_v1(
    code: ZDEXBuybackSpendRejectCodeV1,
    cadence: &ZDEXBuybackSpendStateV1,
    fee_state: &ZDEXFeeStateV1,
    fee_code: Option<ZDEXFeeAllocationRejectCodeV1>,
) -> AbiResultV1<ZDEXBuybackSpendResultV1> {
    Ok(ZDEXBuybackSpendResultV1::Rejected(Box::new(
        ZDEXBuybackSpendRejectedV1::new(code, fee_code, cadence.clone(), fee_state.clone())?,
    )))
}

fn buyback_balance_atoms_v1(state: &ZDEXFeeStateV1) -> AbiResultV1<u128> {
    state.validate()?;
    let value = state
        .destination_balances
        .first()
        .ok_or(AbiErrorV1::InvalidBinding("ZDEX buyback destination"))?;
    if value.destination != ZDEXFeeDestinationV1::BUYBACK {
        return Err(AbiErrorV1::InvalidBinding("ZDEX buyback destination"));
    }
    Ok(value.allocation_atoms)
}

fn fee_state_with_buyback_balance_v1(
    state: &ZDEXFeeStateV1,
    amount: u128,
) -> AbiResultV1<ZDEXFeeStateV1> {
    state.validate()?;
    let mut destination_balances = state.destination_balances.clone();
    let buyback = destination_balances
        .first_mut()
        .ok_or(AbiErrorV1::InvalidBinding("ZDEX buyback destination"))?;
    if buyback.destination != ZDEXFeeDestinationV1::BUYBACK {
        return Err(AbiErrorV1::InvalidBinding("ZDEX buyback destination"));
    }
    buyback.allocation_atoms = amount;
    let post_state = ZDEXFeeStateV1 {
        fee_asset_id: state.fee_asset_id.clone(),
        policy_root: state.policy_root.clone(),
        fee_ingress_atoms: state.fee_ingress_atoms,
        unallocated_reserve_atoms: state.unallocated_reserve_atoms,
        destination_balances,
        owned_and_custodied_atoms: state.owned_and_custodied_atoms,
        supply_atoms: state.supply_atoms,
    };
    post_state.validate()?;
    Ok(post_state)
}

fn policy_or_state_reject_v1(
    spend_policy: &ZDEXBuybackSpendPolicyV1,
    cadence: &ZDEXBuybackSpendStateV1,
    fee_pre_state: &ZDEXFeeStateV1,
    context: &ZDEXBuybackSpendContextV1,
) -> AbiResultV1<Option<ZDEXBuybackSpendRejectCodeV1>> {
    if cadence.policy_root != spend_policy.policy_root()?
        || cadence.quote_asset_id != spend_policy.quote_asset_id
        || fee_pre_state.fee_asset_id != spend_policy.quote_asset_id
        || context.quote_asset_id != spend_policy.quote_asset_id
    {
        return Ok(Some(ZDEXBuybackSpendRejectCodeV1::POLICY_MISMATCH));
    }
    if context.expected_fee_pre_state_root != fee_pre_state.state_root()?
        || context.expected_cadence_pre_state_root != cadence.state_root()?
    {
        return Ok(Some(ZDEXBuybackSpendRejectCodeV1::STALE_STATE));
    }
    Ok(None)
}

fn same_occurrence_reject_v1(
    fee_context: &ZDEXFeeAllocationContextV1,
    context: &ZDEXBuybackSpendContextV1,
) -> Option<ZDEXBuybackSpendRejectCodeV1> {
    if fee_context.profile_root != context.profile_root
        || fee_context.allocation_route_release_id != context.route_release_id
        || fee_context.authorized_buyback_route_release_id != context.route_release_id
        || fee_context.command_occurrence_id != context.command_occurrence_id
    {
        return Some(ZDEXBuybackSpendRejectCodeV1::SAME_OCCURRENCE_MISMATCH);
    }
    None
}

fn cadence_reject_v1(
    spend_policy: &ZDEXBuybackSpendPolicyV1,
    cadence: &ZDEXBuybackSpendStateV1,
    current_height: u64,
) -> Option<ZDEXBuybackSpendRejectCodeV1> {
    let last_execution_height = cadence.last_execution_height?;
    let Some(elapsed) = current_height.checked_sub(last_execution_height) else {
        return Some(ZDEXBuybackSpendRejectCodeV1::HEIGHT_REGRESSION);
    };
    if elapsed < spend_policy.minimum_interval_blocks {
        return Some(ZDEXBuybackSpendRejectCodeV1::COOLDOWN_NOT_ELAPSED);
    }
    None
}

/// Recompute same-occurrence fee allocation, select a capped debit from its
/// canonical BUYBACK destination, and update only cadence.  The caller supplies
/// the safety-limit data here; a release-aware receipt wrapper must authenticate
/// it before this unmounted core can be used in a governed route.
pub fn transition_zdex_buyback_spend_v1(
    spend_policy: &ZDEXBuybackSpendPolicyV1,
    cadence: &ZDEXBuybackSpendStateV1,
    fee_policy: &ZDEXFeeAllocationPolicyV1,
    fee_pre_state: &ZDEXFeeStateV1,
    fee_context: &ZDEXFeeAllocationContextV1,
    fee_command: &ZDEXFeeAllocationCommandV1,
    context: &ZDEXBuybackSpendContextV1,
) -> AbiResultV1<ZDEXBuybackSpendResultV1> {
    spend_policy.validate()?;
    cadence.validate()?;
    fee_policy.validate()?;
    fee_pre_state.validate()?;
    fee_context.validate()?;
    context.validate()?;

    if let Some(code) = policy_or_state_reject_v1(spend_policy, cadence, fee_pre_state, context)? {
        return reject_v1(code, cadence, fee_pre_state, None);
    }
    if let Some(code) = same_occurrence_reject_v1(fee_context, context) {
        return reject_v1(code, cadence, fee_pre_state, None);
    }
    if let Some(code) = cadence_reject_v1(spend_policy, cadence, context.current_height) {
        return reject_v1(code, cadence, fee_pre_state, None);
    }

    let fee_allocation = match transition_zdex_fee_allocation_v1(
        fee_context,
        fee_pre_state,
        fee_policy,
        fee_command,
    )? {
        ZDEXFeeAllocationResultV1::Accepted(accepted) => *accepted,
        ZDEXFeeAllocationResultV1::Rejected(rejected) => {
            return reject_v1(
                ZDEXBuybackSpendRejectCodeV1::FEE_ALLOCATION_REJECTED,
                cadence,
                fee_pre_state,
                Some(rejected.code),
            );
        }
    };
    if context.route_safe_quote_limit_atoms == 0 {
        return reject_v1(
            ZDEXBuybackSpendRejectCodeV1::ROUTE_SAFE_LIMIT_ZERO,
            cadence,
            fee_pre_state,
            None,
        );
    }

    let buyback_reserve_before_atoms = buyback_balance_atoms_v1(&fee_allocation.pre_state)?;
    let buyback_allocation_atoms = fee_allocation.occurrence.buyback_quote_atoms();
    let available_buyback_reserve_atoms = buyback_balance_atoms_v1(&fee_allocation.post_state)?;
    let expected_available = buyback_reserve_before_atoms
        .checked_add(buyback_allocation_atoms)
        .ok_or(AbiErrorV1::Conservation(
            "ZDEX fee allocation buyback projection",
        ))?;
    if expected_available != available_buyback_reserve_atoms {
        return Err(AbiErrorV1::Conservation(
            "ZDEX fee allocation buyback projection",
        ));
    }

    let quote_spend_atoms = available_buyback_reserve_atoms
        .min(spend_policy.per_command_quote_cap_atoms)
        .min(context.route_safe_quote_limit_atoms);
    if quote_spend_atoms < spend_policy.minimum_quote_spend_atoms {
        return reject_v1(
            ZDEXBuybackSpendRejectCodeV1::SPEND_BELOW_MINIMUM,
            cadence,
            fee_pre_state,
            None,
        );
    }

    let intent = ZDEXBuybackSpendIntentV1 {
        schema: ZDEX_BUYBACK_SPEND_INTENT_SCHEMA_V1.to_owned(),
        profile_root: context.profile_root.clone(),
        route_release_id: context.route_release_id.clone(),
        command_occurrence_id: context.command_occurrence_id.clone(),
        spend_policy_root: spend_policy.policy_root()?,
        cadence_pre_state_root: cadence.state_root()?,
        fee_allocation_occurrence_root: fee_allocation.occurrence.occurrence_root()?,
        fee_pre_state_root: fee_allocation.pre_state.state_root()?,
        fee_allocated_state_root: fee_allocation.post_state.state_root()?,
        safety_limit_binding_root: context.safety_limit_binding_root.clone(),
        quote_asset_id: context.quote_asset_id.clone(),
        current_height: context.current_height,
        buyback_reserve_before_atoms,
        buyback_allocation_atoms,
        available_buyback_reserve_atoms,
        quote_spend_atoms,
    };
    let fee_post_state = fee_state_with_buyback_balance_v1(
        &fee_allocation.post_state,
        available_buyback_reserve_atoms
            .checked_sub(quote_spend_atoms)
            .ok_or(AbiErrorV1::Conservation("ZDEX buyback reserve debit"))?,
    )?;
    let mut cadence_post_state = cadence.clone();
    cadence_post_state.last_execution_height = Some(context.current_height);
    let accepted = ZDEXBuybackSpendAcceptedV1 {
        spend_policy: spend_policy.clone(),
        cadence_pre_state: cadence.clone(),
        cadence_post_state,
        fee_policy: fee_policy.clone(),
        fee_context: fee_context.clone(),
        fee_command: fee_command.clone(),
        fee_allocation,
        fee_post_state,
        context: context.clone(),
        intent,
    };
    accepted.validate()?;
    Ok(ZDEXBuybackSpendResultV1::Accepted(Box::new(accepted)))
}
