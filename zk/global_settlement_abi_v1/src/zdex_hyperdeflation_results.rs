//! Transition-constructed results for the experimental ZDEX hyperdeflation core.

use serde::Serialize;

use crate::canonical::{AbiErrorV1, AbiResultV1};
use crate::zdex_hyperdeflation_types::{
    ZDEXBurnCapacityV1, ZDEXBurnEffectV1, ZDEXBurnRejectCodeV1, ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1, ZDEXPrecisionEffectV1, ZDEXPrecisionRejectCodeV1,
    ZDEXSupplyStateV1,
};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPurchaseAndBurnAcceptedV1 {
    pub(crate) policy: ZDEXHyperdeflationPolicyV1,
    pub(crate) route_context: ZDEXBurnRouteContextV1,
    pub(crate) pre_state: ZDEXSupplyStateV1,
    pub(crate) post_state: ZDEXSupplyStateV1,
    pub(crate) capacity: ZDEXBurnCapacityV1,
    pub(crate) effect: ZDEXBurnEffectV1,
}

impl ZDEXPurchaseAndBurnAcceptedV1 {
    pub fn policy(&self) -> &ZDEXHyperdeflationPolicyV1 {
        &self.policy
    }

    pub fn route_context(&self) -> &ZDEXBurnRouteContextV1 {
        &self.route_context
    }

    pub fn pre_state(&self) -> &ZDEXSupplyStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXSupplyStateV1 {
        &self.post_state
    }

    pub fn capacity(&self) -> &ZDEXBurnCapacityV1 {
        &self.capacity
    }

    pub fn effect(&self) -> &ZDEXBurnEffectV1 {
        &self.effect
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPurchaseAndBurnRejectedV1 {
    pub(crate) code: ZDEXBurnRejectCodeV1,
    pub(crate) pre_state: ZDEXSupplyStateV1,
    pub(crate) post_state: ZDEXSupplyStateV1,
    pub(crate) effects: Vec<ZDEXBurnEffectV1>,
}

impl ZDEXPurchaseAndBurnRejectedV1 {
    pub fn code(&self) -> ZDEXBurnRejectCodeV1 {
        self.code
    }

    pub fn pre_state(&self) -> &ZDEXSupplyStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXSupplyStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &[ZDEXBurnEffectV1] {
        &self.effects
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX burn reject is exact no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "outcome", content = "value", deny_unknown_fields)]
pub enum ZDEXPurchaseAndBurnResultV1 {
    Accepted(Box<ZDEXPurchaseAndBurnAcceptedV1>),
    Rejected(Box<ZDEXPurchaseAndBurnRejectedV1>),
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPrecisionRescaleAcceptedV1 {
    pub(crate) policy: ZDEXHyperdeflationPolicyV1,
    pub(crate) pre_state: ZDEXSupplyStateV1,
    pub(crate) post_state: ZDEXSupplyStateV1,
    pub(crate) effect: ZDEXPrecisionEffectV1,
}

impl ZDEXPrecisionRescaleAcceptedV1 {
    pub fn policy(&self) -> &ZDEXHyperdeflationPolicyV1 {
        &self.policy
    }

    pub fn pre_state(&self) -> &ZDEXSupplyStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXSupplyStateV1 {
        &self.post_state
    }

    pub fn effect(&self) -> &ZDEXPrecisionEffectV1 {
        &self.effect
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPrecisionRescaleRejectedV1 {
    pub(crate) code: ZDEXPrecisionRejectCodeV1,
    pub(crate) pre_state: ZDEXSupplyStateV1,
    pub(crate) post_state: ZDEXSupplyStateV1,
    pub(crate) effects: Vec<ZDEXPrecisionEffectV1>,
}

impl ZDEXPrecisionRescaleRejectedV1 {
    pub fn code(&self) -> ZDEXPrecisionRejectCodeV1 {
        self.code
    }

    pub fn pre_state(&self) -> &ZDEXSupplyStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXSupplyStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &[ZDEXPrecisionEffectV1] {
        &self.effects
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX precision reject is exact no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "outcome", content = "value", deny_unknown_fields)]
pub enum ZDEXPrecisionRescaleResultV1 {
    Accepted(Box<ZDEXPrecisionRescaleAcceptedV1>),
    Rejected(Box<ZDEXPrecisionRescaleRejectedV1>),
}
