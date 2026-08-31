//! Closed accepted/rejected outcomes for global ABI V2 refinement.
//!
//! Acceptance preserves the existing opaque structural witness. Rejection is
//! an exact no-op bound to the submitted pre-state content root and grants no
//! publication, settlement, verifier, or production authority.

use core::fmt;

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v2, AbiErrorV2, AbiResultV2, RootV2};
use crate::effects::{ExternalOutboxEnqueueV2, GlobalEconomicEffectPlanV2};
use crate::global_refinement::{
    refine_global_economic_state_effects_v2, GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
};
use crate::lifecycle::{GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2};
use crate::proof::EconomicCommandOccurrenceV2;

pub const GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2: &str = "NONE";

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[allow(non_camel_case_types)]
pub enum GlobalEconomicRefinementRejectCodeV2 {
    MALFORMED_CANDIDATE,
    EXTERNAL_OUTBOX_REQUIRES_PUBLISHER,
    ZERO_OCCURRENCE_NOT_STATIC,
    FIXED_CONTEXT_CHANGED,
    LANE_OWNERSHIP_CHANGED,
    DISABLED_LANE_WRITE,
    LANE_WRITE_COVERAGE_MISMATCH,
    LANE_WRITE_ROOT_MISMATCH,
    SIGNED_STATE_DELTA_OVERFLOW,
    BALANCES_STATE_EFFECT_MISMATCH,
    CUSTODY_STATE_EFFECT_MISMATCH,
    LIABILITIES_STATE_EFFECT_MISMATCH,
    RESERVES_STATE_EFFECT_MISMATCH,
    SUPPLY_EFFECT_TOTAL_OVERFLOW,
    SUPPLY_ISSUE_BURN_MISMATCH,
    OWNED_ACCOUNTING_TOTAL_OVERFLOW,
    OWNED_TOTAL_NOT_SUPPLY,
    CONSERVATION_ASSET_COVERAGE_MISMATCH,
    CONSERVATION_STATE_MISMATCH,
    ANNOTATION_MIRROR_OVERFLOW,
    FEE_ALLOCATION_NOT_MIRRORED,
    REWARD_OR_SLASH_NOT_MIRRORED,
    ZERO_FEE_CONSERVATION_ROW,
    FEE_RESIDUE_OVERFLOW,
    FEE_RESIDUE_STATE_MISMATCH,
    CUSTODY_BACKING_TOTAL_OVERFLOW,
    LIABILITY_TOTAL_OVERFLOW,
    LIABILITIES_EXCEED_BACKING,
    OPEN_TERMINAL_TOTAL_OVERFLOW,
    OPEN_TERMINAL_EXCEEDS_LIABILITY,
    TERMINAL_LIABILITY_DELTA_OVERFLOW,
    TERMINAL_PRE_STATE_MISMATCH,
    TERMINAL_OWNING_LANE_WRITE_MISSING,
    TERMINAL_PLAN_MISMATCH,
    TERMINAL_LIABILITY_MISMATCH,
    ORACLE_LANE_WRITE_MISSING,
    ORACLE_PRE_STATE_MISMATCH,
    ORACLE_PLAN_MISMATCH,
    OCCURRENCES_NOT_ORDERED_UNIQUE,
    REPLAY_CONSUMPTION_MISMATCH,
    OCCURRENCE_CONTEXT_MISMATCH,
    REPLAY_ALREADY_CONSUMED,
    REPLAY_POST_STATE_MISMATCH,
    HEIGHT_PROGRESSION_MISMATCH,
    OCCURRENCE_HEIGHT_MISMATCH,
    INTERNAL_CONTRACT_DRIFT,
}

pub const ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2: [GlobalEconomicRefinementRejectCodeV2;
    46] = [
    GlobalEconomicRefinementRejectCodeV2::MALFORMED_CANDIDATE,
    GlobalEconomicRefinementRejectCodeV2::EXTERNAL_OUTBOX_REQUIRES_PUBLISHER,
    GlobalEconomicRefinementRejectCodeV2::ZERO_OCCURRENCE_NOT_STATIC,
    GlobalEconomicRefinementRejectCodeV2::FIXED_CONTEXT_CHANGED,
    GlobalEconomicRefinementRejectCodeV2::LANE_OWNERSHIP_CHANGED,
    GlobalEconomicRefinementRejectCodeV2::DISABLED_LANE_WRITE,
    GlobalEconomicRefinementRejectCodeV2::LANE_WRITE_COVERAGE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::LANE_WRITE_ROOT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::SIGNED_STATE_DELTA_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::BALANCES_STATE_EFFECT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::CUSTODY_STATE_EFFECT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::LIABILITIES_STATE_EFFECT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::RESERVES_STATE_EFFECT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::SUPPLY_EFFECT_TOTAL_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::SUPPLY_ISSUE_BURN_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::OWNED_ACCOUNTING_TOTAL_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::OWNED_TOTAL_NOT_SUPPLY,
    GlobalEconomicRefinementRejectCodeV2::CONSERVATION_ASSET_COVERAGE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::CONSERVATION_STATE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::ANNOTATION_MIRROR_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::FEE_ALLOCATION_NOT_MIRRORED,
    GlobalEconomicRefinementRejectCodeV2::REWARD_OR_SLASH_NOT_MIRRORED,
    GlobalEconomicRefinementRejectCodeV2::ZERO_FEE_CONSERVATION_ROW,
    GlobalEconomicRefinementRejectCodeV2::FEE_RESIDUE_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::FEE_RESIDUE_STATE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::CUSTODY_BACKING_TOTAL_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::LIABILITY_TOTAL_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::LIABILITIES_EXCEED_BACKING,
    GlobalEconomicRefinementRejectCodeV2::OPEN_TERMINAL_TOTAL_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::OPEN_TERMINAL_EXCEEDS_LIABILITY,
    GlobalEconomicRefinementRejectCodeV2::TERMINAL_LIABILITY_DELTA_OVERFLOW,
    GlobalEconomicRefinementRejectCodeV2::TERMINAL_PRE_STATE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::TERMINAL_OWNING_LANE_WRITE_MISSING,
    GlobalEconomicRefinementRejectCodeV2::TERMINAL_PLAN_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::TERMINAL_LIABILITY_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::ORACLE_LANE_WRITE_MISSING,
    GlobalEconomicRefinementRejectCodeV2::ORACLE_PRE_STATE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::ORACLE_PLAN_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::OCCURRENCES_NOT_ORDERED_UNIQUE,
    GlobalEconomicRefinementRejectCodeV2::REPLAY_CONSUMPTION_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::OCCURRENCE_CONTEXT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::REPLAY_ALREADY_CONSUMED,
    GlobalEconomicRefinementRejectCodeV2::REPLAY_POST_STATE_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::HEIGHT_PROGRESSION_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::OCCURRENCE_HEIGHT_MISMATCH,
    GlobalEconomicRefinementRejectCodeV2::INTERNAL_CONTRACT_DRIFT,
];

impl GlobalEconomicRefinementRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MALFORMED_CANDIDATE => "MALFORMED_CANDIDATE",
            Self::EXTERNAL_OUTBOX_REQUIRES_PUBLISHER => "EXTERNAL_OUTBOX_REQUIRES_PUBLISHER",
            Self::ZERO_OCCURRENCE_NOT_STATIC => "ZERO_OCCURRENCE_NOT_STATIC",
            Self::FIXED_CONTEXT_CHANGED => "FIXED_CONTEXT_CHANGED",
            Self::LANE_OWNERSHIP_CHANGED => "LANE_OWNERSHIP_CHANGED",
            Self::DISABLED_LANE_WRITE => "DISABLED_LANE_WRITE",
            Self::LANE_WRITE_COVERAGE_MISMATCH => "LANE_WRITE_COVERAGE_MISMATCH",
            Self::LANE_WRITE_ROOT_MISMATCH => "LANE_WRITE_ROOT_MISMATCH",
            Self::SIGNED_STATE_DELTA_OVERFLOW => "SIGNED_STATE_DELTA_OVERFLOW",
            Self::BALANCES_STATE_EFFECT_MISMATCH => "BALANCES_STATE_EFFECT_MISMATCH",
            Self::CUSTODY_STATE_EFFECT_MISMATCH => "CUSTODY_STATE_EFFECT_MISMATCH",
            Self::LIABILITIES_STATE_EFFECT_MISMATCH => "LIABILITIES_STATE_EFFECT_MISMATCH",
            Self::RESERVES_STATE_EFFECT_MISMATCH => "RESERVES_STATE_EFFECT_MISMATCH",
            Self::SUPPLY_EFFECT_TOTAL_OVERFLOW => "SUPPLY_EFFECT_TOTAL_OVERFLOW",
            Self::SUPPLY_ISSUE_BURN_MISMATCH => "SUPPLY_ISSUE_BURN_MISMATCH",
            Self::OWNED_ACCOUNTING_TOTAL_OVERFLOW => "OWNED_ACCOUNTING_TOTAL_OVERFLOW",
            Self::OWNED_TOTAL_NOT_SUPPLY => "OWNED_TOTAL_NOT_SUPPLY",
            Self::CONSERVATION_ASSET_COVERAGE_MISMATCH => "CONSERVATION_ASSET_COVERAGE_MISMATCH",
            Self::CONSERVATION_STATE_MISMATCH => "CONSERVATION_STATE_MISMATCH",
            Self::ANNOTATION_MIRROR_OVERFLOW => "ANNOTATION_MIRROR_OVERFLOW",
            Self::FEE_ALLOCATION_NOT_MIRRORED => "FEE_ALLOCATION_NOT_MIRRORED",
            Self::REWARD_OR_SLASH_NOT_MIRRORED => "REWARD_OR_SLASH_NOT_MIRRORED",
            Self::ZERO_FEE_CONSERVATION_ROW => "ZERO_FEE_CONSERVATION_ROW",
            Self::FEE_RESIDUE_OVERFLOW => "FEE_RESIDUE_OVERFLOW",
            Self::FEE_RESIDUE_STATE_MISMATCH => "FEE_RESIDUE_STATE_MISMATCH",
            Self::CUSTODY_BACKING_TOTAL_OVERFLOW => "CUSTODY_BACKING_TOTAL_OVERFLOW",
            Self::LIABILITY_TOTAL_OVERFLOW => "LIABILITY_TOTAL_OVERFLOW",
            Self::LIABILITIES_EXCEED_BACKING => "LIABILITIES_EXCEED_BACKING",
            Self::OPEN_TERMINAL_TOTAL_OVERFLOW => "OPEN_TERMINAL_TOTAL_OVERFLOW",
            Self::OPEN_TERMINAL_EXCEEDS_LIABILITY => "OPEN_TERMINAL_EXCEEDS_LIABILITY",
            Self::TERMINAL_LIABILITY_DELTA_OVERFLOW => "TERMINAL_LIABILITY_DELTA_OVERFLOW",
            Self::TERMINAL_PRE_STATE_MISMATCH => "TERMINAL_PRE_STATE_MISMATCH",
            Self::TERMINAL_OWNING_LANE_WRITE_MISSING => "TERMINAL_OWNING_LANE_WRITE_MISSING",
            Self::TERMINAL_PLAN_MISMATCH => "TERMINAL_PLAN_MISMATCH",
            Self::TERMINAL_LIABILITY_MISMATCH => "TERMINAL_LIABILITY_MISMATCH",
            Self::ORACLE_LANE_WRITE_MISSING => "ORACLE_LANE_WRITE_MISSING",
            Self::ORACLE_PRE_STATE_MISMATCH => "ORACLE_PRE_STATE_MISMATCH",
            Self::ORACLE_PLAN_MISMATCH => "ORACLE_PLAN_MISMATCH",
            Self::OCCURRENCES_NOT_ORDERED_UNIQUE => "OCCURRENCES_NOT_ORDERED_UNIQUE",
            Self::REPLAY_CONSUMPTION_MISMATCH => "REPLAY_CONSUMPTION_MISMATCH",
            Self::OCCURRENCE_CONTEXT_MISMATCH => "OCCURRENCE_CONTEXT_MISMATCH",
            Self::REPLAY_ALREADY_CONSUMED => "REPLAY_ALREADY_CONSUMED",
            Self::REPLAY_POST_STATE_MISMATCH => "REPLAY_POST_STATE_MISMATCH",
            Self::HEIGHT_PROGRESSION_MISMATCH => "HEIGHT_PROGRESSION_MISMATCH",
            Self::OCCURRENCE_HEIGHT_MISMATCH => "OCCURRENCE_HEIGHT_MISMATCH",
            Self::INTERNAL_CONTRACT_DRIFT => "INTERNAL_CONTRACT_DRIFT",
        }
    }
}

impl fmt::Display for GlobalEconomicRefinementRejectCodeV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalEconomicRefinementAcceptedV2 {
    witness: GlobalEconomicStateEffectRefinementV2,
}

impl GlobalEconomicRefinementAcceptedV2 {
    pub fn witness(&self) -> &GlobalEconomicStateEffectRefinementV2 {
        &self.witness
    }

    pub fn production_authority(&self) -> &'static str {
        GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalEconomicRefinementRejectedV2 {
    reject_code: GlobalEconomicRefinementRejectCodeV2,
    pre_state_root: RootV2,
}

impl GlobalEconomicRefinementRejectedV2 {
    fn new(reject_code: GlobalEconomicRefinementRejectCodeV2, pre_state_root: RootV2) -> Self {
        Self {
            reject_code,
            pre_state_root,
        }
    }

    pub fn reject_code(&self) -> GlobalEconomicRefinementRejectCodeV2 {
        self.reject_code
    }

    pub fn pre_state_root(&self) -> &RootV2 {
        &self.pre_state_root
    }

    pub fn post_state_root(&self) -> &RootV2 {
        &self.pre_state_root
    }

    pub fn effect_plan(&self) -> GlobalEconomicEffectPlanV2 {
        GlobalEconomicEffectPlanV2::empty()
    }

    pub fn terminal_plan(&self) -> GlobalTerminalObligationPlanV2 {
        GlobalTerminalObligationPlanV2::empty()
    }

    pub fn oracle_plan(&self) -> GlobalOracleOccurrencePlanV2 {
        GlobalOracleOccurrencePlanV2::empty()
    }

    pub fn consumed_occurrences(&self) -> &[EconomicCommandOccurrenceV2] {
        &[]
    }

    pub fn outbox(&self) -> &[ExternalOutboxEnqueueV2] {
        &[]
    }

    pub fn production_authority(&self) -> &'static str {
        GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GlobalEconomicRefinementOutcomeV2 {
    Accepted(GlobalEconomicRefinementAcceptedV2),
    Rejected(GlobalEconomicRefinementRejectedV2),
}

impl GlobalEconomicRefinementOutcomeV2 {
    pub fn production_authority(&self) -> &'static str {
        GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2
    }
}

fn known_malformed_candidate_error_v2(error: &AbiErrorV2) -> bool {
    match error {
        AbiErrorV2::InvalidSchema(field) => matches!(
            *field,
            "global economic state"
                | "global economic effect plan"
                | "global terminal obligation plan"
                | "global Oracle occurrence plan"
                | "economic command occurrence"
        ),
        AbiErrorV2::InvalidToken(field) => matches!(
            *field,
            "global state chain id"
                | "economic amount owner"
                | "economic amount asset"
                | "economic amount custody domain"
                | "supply asset"
                | "Oracle id"
                | "replay id"
                | "terminal obligation id"
                | "terminal obligation claimant"
                | "terminal obligation asset"
                | "terminal obligation liability domain"
                | "outbox destination"
                | "economic effect principal"
                | "economic effect asset"
                | "economic effect custody domain"
                | "conservation asset"
                | "fee conservation asset"
                | "external outbox destination"
                | "effect plan occurrence consumptions"
                | "Oracle occurrence delta id"
                | "terminal obligation delta id"
                | "occurrence chain id"
                | "occurrence command kind"
                | "occurrence subject id"
                | "occurrence consumed object ids"
        ),
        AbiErrorV2::InvalidRoot(field) => matches!(
            *field,
            "global state deployment root"
                | "global state profile root"
                | "global state history root"
                | "lane state module release"
                | "lane state root"
                | "Oracle occurrence root"
                | "replay occurrence id"
                | "outbox effect id"
                | "outbox payload hash"
                | "outbox adapter profile root"
                | "outbox commit id"
                | "lane write pre root"
                | "lane write post root"
                | "effect plan occurrence consumption"
                | "external outbox effect id"
                | "external outbox payload hash"
                | "external outbox adapter profile root"
                | "occurrence deployment root"
                | "occurrence command body hash"
                | "occurrence route release id"
                | "occurrence grant root"
                | "occurrence profile root"
                | "occurrence pre-state root"
        ),
        AbiErrorV2::InvalidBounds(field) => matches!(
            *field,
            "global state lane roots"
                | "global state balances"
                | "global state custody"
                | "global state liabilities"
                | "global state reserves"
                | "global state supplies"
                | "global state Oracle occurrences"
                | "global state replay state"
                | "global state terminal obligations"
                | "global state outbox"
                | "open terminal obligation amount must be positive"
                | "effect plan rows"
                | "effect plan asset conservation"
                | "effect plan fee conservation"
                | "effect plan lane writes"
                | "effect plan occurrence consumptions"
                | "effect plan external outbox enqueue"
                | "effect plan total items"
                | "effect plan canonical encoding bytes"
                | "economic effect delta"
                | "global Oracle occurrence plan deltas"
                | "global terminal obligation plan deltas"
        ),
        AbiErrorV2::InvalidOrder(field) => matches!(
            *field,
            "global state lane roots"
                | "global state balances"
                | "global state custody"
                | "global state liabilities"
                | "global state reserves"
                | "global state supplies"
                | "global state Oracle occurrences"
                | "global state replay state"
                | "global state terminal obligations"
                | "global state outbox"
                | "effect plan rows"
                | "asset conservation"
                | "fee conservation"
                | "lane writes"
                | "effect plan occurrence consumptions"
                | "external outbox enqueue"
                | "global Oracle occurrence plan deltas"
                | "global terminal obligation plan deltas"
                | "occurrence consumed object ids"
        ),
        AbiErrorV2::InvalidBinding(field) => matches!(
            *field,
            "same-ledger external outbox"
                | "Oracle observed height exceeds global state height"
                | "global state replay occurrence ids"
                | "issue effect sign"
                | "burn effect sign"
                | "Oracle occurrence delta post identity mismatch"
                | "Oracle occurrence delta pre identity mismatch"
                | "Oracle occurrence delta must change the occurrence"
                | "Oracle occurrence height cannot regress"
                | "Oracle occurrence finality cannot regress"
                | "Oracle occurrence root is immutable at one observed height"
                | "terminal obligation delta post identity mismatch"
                | "new terminal obligation must begin open"
                | "terminal obligation delta pre identity mismatch"
                | "terminal obligation identity fields are immutable"
                | "terminal obligation is already terminal"
                | "open terminal obligation must change amount or become terminal"
                | "terminal transition must preserve the final open amount"
        ),
        AbiErrorV2::Conservation(field) => matches!(
            *field,
            "owned and custodied overflow"
                | "supply overflow"
                | "owned and custodied"
                | "supply"
                | "fee overflow"
                | "fee allocation"
                | "issue or burn overflow"
                | "issue or burn projection"
                | "missing issue or burn asset row"
                | "negative fee allocation"
                | "fee allocation overflow"
                | "fee projection"
                | "missing fee conservation row"
        ),
        AbiErrorV2::CanonicalEncoding(_) => false,
    }
}

pub fn classify_global_economic_refinement_error_v2(
    error: &AbiErrorV2,
) -> GlobalEconomicRefinementRejectCodeV2 {
    use AbiErrorV2::{Conservation, InvalidBinding, InvalidBounds, InvalidOrder};
    use GlobalEconomicRefinementRejectCodeV2 as Code;

    match error {
        InvalidBinding("global refinement external outbox requires the O-009 publisher") => {
            Code::EXTERNAL_OUTBOX_REQUIRES_PUBLISHER
        }
        InvalidBinding("global refinement zero-occurrence relation must be static") => {
            Code::ZERO_OCCURRENCE_NOT_STATIC
        }
        InvalidBinding("global refinement fixed context changed") => Code::FIXED_CONTEXT_CHANGED,
        InvalidBinding("global refinement lane ownership changed outside migration") => {
            Code::LANE_OWNERSHIP_CHANGED
        }
        InvalidBinding("global refinement disabled lane write") => Code::DISABLED_LANE_WRITE,
        InvalidBinding("global refinement lane write coverage mismatch") => {
            Code::LANE_WRITE_COVERAGE_MISMATCH
        }
        InvalidBinding("global refinement lane write root mismatch") => {
            Code::LANE_WRITE_ROOT_MISMATCH
        }
        InvalidBounds("global refinement signed state delta") => Code::SIGNED_STATE_DELTA_OVERFLOW,
        InvalidBinding("global refinement balances state/effect mismatch") => {
            Code::BALANCES_STATE_EFFECT_MISMATCH
        }
        InvalidBinding("global refinement custody state/effect mismatch") => {
            Code::CUSTODY_STATE_EFFECT_MISMATCH
        }
        InvalidBinding("global refinement liabilities state/effect mismatch") => {
            Code::LIABILITIES_STATE_EFFECT_MISMATCH
        }
        InvalidBinding("global refinement reserves state/effect mismatch") => {
            Code::RESERVES_STATE_EFFECT_MISMATCH
        }
        InvalidBounds("global refinement supply effect total") => {
            Code::SUPPLY_EFFECT_TOTAL_OVERFLOW
        }
        InvalidBinding("global refinement supply issue/burn mismatch") => {
            Code::SUPPLY_ISSUE_BURN_MISMATCH
        }
        InvalidBounds("global owned accounting") => Code::OWNED_ACCOUNTING_TOTAL_OVERFLOW,
        Conservation("global refinement owned total does not equal supply") => {
            Code::OWNED_TOTAL_NOT_SUPPLY
        }
        Conservation("global refinement conservation asset coverage mismatch") => {
            Code::CONSERVATION_ASSET_COVERAGE_MISMATCH
        }
        Conservation("global refinement conservation state mismatch") => {
            Code::CONSERVATION_STATE_MISMATCH
        }
        InvalidBounds("global refinement annotation mirror overflow") => {
            Code::ANNOTATION_MIRROR_OVERFLOW
        }
        InvalidBinding("global refinement fee allocation is not mirrored") => {
            Code::FEE_ALLOCATION_NOT_MIRRORED
        }
        InvalidBinding("global refinement reward or slash lacks exact state-bearing mirror") => {
            Code::REWARD_OR_SLASH_NOT_MIRRORED
        }
        InvalidBinding("global refinement zero fee conservation row is noncanonical") => {
            Code::ZERO_FEE_CONSERVATION_ROW
        }
        InvalidBounds("global refinement fee residue") => Code::FEE_RESIDUE_OVERFLOW,
        InvalidBinding("global refinement fee residue state mapping mismatch") => {
            Code::FEE_RESIDUE_STATE_MISMATCH
        }
        InvalidBounds("global refinement custody backing total") => {
            Code::CUSTODY_BACKING_TOTAL_OVERFLOW
        }
        InvalidBounds("global liability") => Code::LIABILITY_TOTAL_OVERFLOW,
        Conservation("global refinement liabilities exceed same-domain accounting backing") => {
            Code::LIABILITIES_EXCEED_BACKING
        }
        InvalidBounds("global refinement open terminal obligation total") => {
            Code::OPEN_TERMINAL_TOTAL_OVERFLOW
        }
        InvalidBinding(
            "global refinement open terminal obligations exceed exact liability row",
        ) => Code::OPEN_TERMINAL_EXCEEDS_LIABILITY,
        InvalidBounds("global refinement terminal liability delta overflow") => {
            Code::TERMINAL_LIABILITY_DELTA_OVERFLOW
        }
        InvalidBinding("global refinement terminal obligation pre-state mismatch") => {
            Code::TERMINAL_PRE_STATE_MISMATCH
        }
        InvalidBinding("global refinement terminal obligation lacks its owning lane write") => {
            Code::TERMINAL_OWNING_LANE_WRITE_MISSING
        }
        InvalidBinding("global refinement terminal obligation plan mismatch") => {
            Code::TERMINAL_PLAN_MISMATCH
        }
        InvalidBinding("global refinement terminal obligation liability mismatch") => {
            Code::TERMINAL_LIABILITY_MISMATCH
        }
        InvalidBinding("global refinement Oracle lane write is missing") => {
            Code::ORACLE_LANE_WRITE_MISSING
        }
        InvalidBinding("global refinement Oracle occurrence pre-state mismatch") => {
            Code::ORACLE_PRE_STATE_MISMATCH
        }
        InvalidBinding("global refinement Oracle occurrence plan mismatch") => {
            Code::ORACLE_PLAN_MISMATCH
        }
        InvalidOrder("global refinement occurrences must be ordered and unique") => {
            Code::OCCURRENCES_NOT_ORDERED_UNIQUE
        }
        InvalidBinding("global refinement replay consumption mismatch") => {
            Code::REPLAY_CONSUMPTION_MISMATCH
        }
        InvalidBinding("global refinement occurrence context mismatch") => {
            Code::OCCURRENCE_CONTEXT_MISMATCH
        }
        InvalidBinding("global refinement replay already consumed") => {
            Code::REPLAY_ALREADY_CONSUMED
        }
        InvalidBinding("global refinement replay post-state mismatch") => {
            Code::REPLAY_POST_STATE_MISMATCH
        }
        InvalidBounds("global refinement height progression mismatch")
        | InvalidBinding("global refinement height progression mismatch") => {
            Code::HEIGHT_PROGRESSION_MISMATCH
        }
        InvalidBinding("global refinement occurrence height mismatch") => {
            Code::OCCURRENCE_HEIGHT_MISMATCH
        }
        known if known_malformed_candidate_error_v2(known) => Code::MALFORMED_CANDIDATE,
        _ => Code::INTERNAL_CONTRACT_DRIFT,
    }
}

pub fn refine_global_economic_state_effects_outcome_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
) -> AbiResultV2<GlobalEconomicRefinementOutcomeV2> {
    // Hash submitted content directly so malformed public Rust structs still
    // receive a rejection bound to their exact submitted pre-state.
    let pre_state_root = hash_global_v2("global-economic-state-root-v2", candidate.pre_state)?;
    match refine_global_economic_state_effects_v2(candidate) {
        Ok(witness) => Ok(GlobalEconomicRefinementOutcomeV2::Accepted(
            GlobalEconomicRefinementAcceptedV2 { witness },
        )),
        Err(error) => Ok(GlobalEconomicRefinementOutcomeV2::Rejected(
            GlobalEconomicRefinementRejectedV2::new(
                classify_global_economic_refinement_error_v2(&error),
                pre_state_root,
            ),
        )),
    }
}
