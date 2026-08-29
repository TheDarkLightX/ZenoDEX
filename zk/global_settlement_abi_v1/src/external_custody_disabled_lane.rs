use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::effects::{
    GlobalEconomicEffectPlanV1, LaneTransitionRejectCodeV1, LaneTransitionRejectedV1,
};

pub const EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1: &str =
    "zenodex/external-custody-disabled-state/v1";

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ExternalCustodyCommandKindV1 {
    #[serde(rename = "registered_external_lock")]
    REGISTERED_EXTERNAL_LOCK,
    #[serde(rename = "registered_external_burn")]
    REGISTERED_EXTERNAL_BURN,
    #[serde(rename = "registered_external_release")]
    REGISTERED_EXTERNAL_RELEASE,
    #[serde(rename = "registered_external_mint")]
    REGISTERED_EXTERNAL_MINT,
    #[serde(rename = "external_finality")]
    EXTERNAL_FINALITY,
    #[serde(rename = "external_timeout")]
    EXTERNAL_TIMEOUT,
    #[serde(rename = "external_refund")]
    EXTERNAL_REFUND,
    #[serde(rename = "outbox_acknowledgment")]
    OUTBOX_ACKNOWLEDGMENT,
    #[serde(rename = "destination_idempotency")]
    DESTINATION_IDEMPOTENCY,
}

pub const EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1: [ExternalCustodyCommandKindV1; 9] = [
    ExternalCustodyCommandKindV1::REGISTERED_EXTERNAL_LOCK,
    ExternalCustodyCommandKindV1::REGISTERED_EXTERNAL_BURN,
    ExternalCustodyCommandKindV1::REGISTERED_EXTERNAL_RELEASE,
    ExternalCustodyCommandKindV1::REGISTERED_EXTERNAL_MINT,
    ExternalCustodyCommandKindV1::EXTERNAL_FINALITY,
    ExternalCustodyCommandKindV1::EXTERNAL_TIMEOUT,
    ExternalCustodyCommandKindV1::EXTERNAL_REFUND,
    ExternalCustodyCommandKindV1::OUTBOX_ACKNOWLEDGMENT,
    ExternalCustodyCommandKindV1::DESTINATION_IDEMPOTENCY,
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalCustodyCommandV1 {
    pub destination_id: String,
    pub external_object_id: String,
    pub kind: ExternalCustodyCommandKindV1,
}

impl ExternalCustodyCommandV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.destination_id, "external destination id")?;
        validate_token_v1(&self.external_object_id, "external object id")
    }

    pub fn command_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("external-custody-command-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalCustodyDisabledStateV1 {
    pub schema: String,
    pub registry_entries: Vec<String>,
    pub pending_external_obligations: Vec<String>,
    pub outbox_acknowledgments: Vec<String>,
}

impl ExternalCustodyDisabledStateV1 {
    pub fn new() -> Self {
        Self {
            schema: EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1.to_owned(),
            registry_entries: Vec::new(),
            pending_external_obligations: Vec::new(),
            outbox_acknowledgments: Vec::new(),
        }
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        if !self.registry_entries.is_empty()
            || !self.pending_external_obligations.is_empty()
            || !self.outbox_acknowledgments.is_empty()
        {
            return Err(AbiErrorV1::InvalidBinding(
                "disabled external lane must remain empty",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("external-custody-disabled-state-v1", self)
    }
}

impl Default for ExternalCustodyDisabledStateV1 {
    fn default() -> Self {
        Self::new()
    }
}

fn empty_effects_v1() -> GlobalEconomicEffectPlanV1 {
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

#[must_use = "a disabled external command must remain an observed rejection"]
pub fn transition_external_custody_disabled_v1(
    pre_state: &ExternalCustodyDisabledStateV1,
    command: &ExternalCustodyCommandV1,
) -> AbiResultV1<LaneTransitionRejectedV1> {
    pre_state.validate()?;
    command.validate()?;
    let pre_state_root = pre_state.state_root()?;
    let rejected = LaneTransitionRejectedV1 {
        code: LaneTransitionRejectCodeV1::DISABLED_FEATURE,
        pre_state_root: pre_state_root.clone(),
        post_state_root: pre_state_root,
        effects: empty_effects_v1(),
    };
    rejected.validate()?;
    Ok(rejected)
}
