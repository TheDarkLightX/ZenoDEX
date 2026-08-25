//! Owned guest input and recomputation boundary for perps margin accounting.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::perps_margin::transition_perps_margin_v1;
use crate::perps_margin_types::{
    PerpsMarginAcceptedV1, PerpsMarginCommandV1, PerpsMarginContextV1, PerpsMarginResultV1,
    PerpsMarginStateV1, PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1,
};

pub const PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1: &str = PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneModuleInputV1 {
    pub schema: String,
    pub context: PerpsMarginContextV1,
    pub pre_state: PerpsMarginStateV1,
    pub command: PerpsMarginCommandV1,
}

impl PerpsMarginLaneModuleInputV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.context.validate()?;
        self.pre_state.validate()?;
        self.command.validate()
    }

    pub fn statement_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("perps-margin-statement-v1", self)
    }
}

#[must_use = "the result owns the only candidate effects and terminal obligations"]
pub fn transition_perps_margin_lane_module_v1(
    module_input: &PerpsMarginLaneModuleInputV1,
) -> AbiResultV1<PerpsMarginResultV1> {
    module_input.validate()?;
    let result = transition_perps_margin_v1(
        &module_input.context,
        &module_input.pre_state,
        &module_input.command,
    )?;
    if let PerpsMarginResultV1::Accepted(accepted) = &result {
        if accepted.statement_root != module_input.statement_root()? {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin transition statement root drift",
            ));
        }
    }
    Ok(result)
}

pub(crate) fn recompute_perps_margin_accepted_v1(
    module_input: &PerpsMarginLaneModuleInputV1,
    accepted: &PerpsMarginAcceptedV1,
) -> AbiResultV1<PerpsMarginAcceptedV1> {
    accepted.validate()?;
    match transition_perps_margin_lane_module_v1(module_input)? {
        PerpsMarginResultV1::Accepted(expected) if expected.as_ref() == accepted => Ok(*expected),
        PerpsMarginResultV1::Accepted(_) => Err(AbiErrorV1::InvalidBinding(
            "perps margin supplied acceptance differs from recomputation",
        )),
        PerpsMarginResultV1::Rejected(_) => Err(AbiErrorV1::InvalidBinding(
            "perps margin supplied acceptance recomputes to rejection",
        )),
    }
}
