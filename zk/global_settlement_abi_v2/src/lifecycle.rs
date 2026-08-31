use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v2, validate_schema_v2, validate_token_v2, AbiErrorV2, AbiResultV2, RootV2,
    ValidateCanonicalV2, GLOBAL_SETTLEMENT_ABI_V2,
};
use crate::effects::LaneIdV2;

pub const MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2: usize = 64;
pub const MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2: usize = 64;

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OracleOccurrenceStateV2 {
    pub oracle_id: String,
    pub occurrence_root: RootV2,
    pub observed_height: u64,
    pub finalized: bool,
}

impl OracleOccurrenceStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.oracle_id, "Oracle id")?;
        self.occurrence_root
            .validate("Oracle occurrence root", false)
    }
}

impl ValidateCanonicalV2 for OracleOccurrenceStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OracleOccurrenceDeltaV2 {
    pub oracle_id: String,
    pub pre_occurrence: Option<OracleOccurrenceStateV2>,
    pub post_occurrence: OracleOccurrenceStateV2,
}

impl OracleOccurrenceDeltaV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.oracle_id, "Oracle occurrence delta id")?;
        if let Some(pre) = &self.pre_occurrence {
            pre.validate()?;
        }
        self.post_occurrence.validate()?;
        if self.post_occurrence.oracle_id != self.oracle_id {
            return Err(AbiErrorV2::InvalidBinding(
                "Oracle occurrence delta post identity mismatch",
            ));
        }
        let Some(pre) = &self.pre_occurrence else {
            return Ok(());
        };
        if pre.oracle_id != self.oracle_id {
            return Err(AbiErrorV2::InvalidBinding(
                "Oracle occurrence delta pre identity mismatch",
            ));
        }
        if pre == &self.post_occurrence {
            return Err(AbiErrorV2::InvalidBinding(
                "Oracle occurrence delta must change the occurrence",
            ));
        }
        if self.post_occurrence.observed_height < pre.observed_height {
            return Err(AbiErrorV2::InvalidBinding(
                "Oracle occurrence height cannot regress",
            ));
        }
        if pre.finalized && !self.post_occurrence.finalized {
            return Err(AbiErrorV2::InvalidBinding(
                "Oracle occurrence finality cannot regress",
            ));
        }
        if self.post_occurrence.observed_height == pre.observed_height
            && self.post_occurrence.occurrence_root != pre.occurrence_root
        {
            return Err(AbiErrorV2::InvalidBinding(
                "Oracle occurrence root is immutable at one observed height",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for OracleOccurrenceDeltaV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalOracleOccurrencePlanV2 {
    pub schema: String,
    pub deltas: Vec<OracleOccurrenceDeltaV2>,
}

impl GlobalOracleOccurrencePlanV2 {
    pub fn empty() -> Self {
        Self {
            schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
            deltas: Vec::new(),
        }
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            GLOBAL_SETTLEMENT_ABI_V2,
            "global Oracle occurrence plan",
        )?;
        if self.deltas.len() > MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2 {
            return Err(AbiErrorV2::InvalidBounds(
                "global Oracle occurrence plan deltas",
            ));
        }
        for delta in &self.deltas {
            delta.validate()?;
        }
        if self
            .deltas
            .windows(2)
            .any(|pair| pair[0].oracle_id >= pair[1].oracle_id)
        {
            return Err(AbiErrorV2::InvalidOrder(
                "global Oracle occurrence plan deltas",
            ));
        }
        Ok(())
    }

    pub fn plan_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        if self.deltas.is_empty() {
            return Ok(RootV2::zero());
        }
        hash_global_v2("global-oracle-occurrence-plan-v2", self)
    }
}

impl ValidateCanonicalV2 for GlobalOracleOccurrencePlanV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[allow(non_camel_case_types)]
pub enum TerminalObligationStatusV2 {
    OPEN,
    DRAINED,
    TOMBSTONED,
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TerminalObligationV2 {
    pub obligation_id: String,
    pub lane_id: LaneIdV2,
    pub claimant: String,
    pub asset: String,
    pub liability_domain: String,
    pub amount_atoms: u128,
    pub status: TerminalObligationStatusV2,
}

impl TerminalObligationV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.obligation_id, "terminal obligation id")?;
        validate_token_v2(&self.claimant, "terminal obligation claimant")?;
        validate_token_v2(&self.asset, "terminal obligation asset")?;
        validate_token_v2(
            &self.liability_domain,
            "terminal obligation liability domain",
        )?;
        if self.status == TerminalObligationStatusV2::OPEN && self.amount_atoms == 0 {
            return Err(AbiErrorV2::InvalidBounds(
                "open terminal obligation amount must be positive",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for TerminalObligationV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TerminalObligationDeltaV2 {
    pub obligation_id: String,
    pub pre_obligation: Option<TerminalObligationV2>,
    pub post_obligation: TerminalObligationV2,
}

impl TerminalObligationDeltaV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.obligation_id, "terminal obligation delta id")?;
        if let Some(pre) = &self.pre_obligation {
            pre.validate()?;
        }
        self.post_obligation.validate()?;
        if self.post_obligation.obligation_id != self.obligation_id {
            return Err(AbiErrorV2::InvalidBinding(
                "terminal obligation delta post identity mismatch",
            ));
        }
        let Some(pre) = &self.pre_obligation else {
            if self.post_obligation.status != TerminalObligationStatusV2::OPEN {
                return Err(AbiErrorV2::InvalidBinding(
                    "new terminal obligation must begin open",
                ));
            }
            return Ok(());
        };
        if pre.obligation_id != self.obligation_id {
            return Err(AbiErrorV2::InvalidBinding(
                "terminal obligation delta pre identity mismatch",
            ));
        }
        if (
            pre.lane_id,
            pre.claimant.as_str(),
            pre.asset.as_str(),
            pre.liability_domain.as_str(),
        ) != (
            self.post_obligation.lane_id,
            self.post_obligation.claimant.as_str(),
            self.post_obligation.asset.as_str(),
            self.post_obligation.liability_domain.as_str(),
        ) {
            return Err(AbiErrorV2::InvalidBinding(
                "terminal obligation identity fields are immutable",
            ));
        }
        if pre.status != TerminalObligationStatusV2::OPEN {
            return Err(AbiErrorV2::InvalidBinding(
                "terminal obligation is already terminal",
            ));
        }
        if self.post_obligation.status == TerminalObligationStatusV2::OPEN {
            if self.post_obligation.amount_atoms == pre.amount_atoms {
                return Err(AbiErrorV2::InvalidBinding(
                    "open terminal obligation must change amount or become terminal",
                ));
            }
            return Ok(());
        }
        if self.post_obligation.amount_atoms != pre.amount_atoms {
            return Err(AbiErrorV2::InvalidBinding(
                "terminal transition must preserve the final open amount",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for TerminalObligationDeltaV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalTerminalObligationPlanV2 {
    pub schema: String,
    pub deltas: Vec<TerminalObligationDeltaV2>,
}

impl GlobalTerminalObligationPlanV2 {
    pub fn empty() -> Self {
        Self {
            schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
            deltas: Vec::new(),
        }
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            GLOBAL_SETTLEMENT_ABI_V2,
            "global terminal obligation plan",
        )?;
        if self.deltas.len() > MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2 {
            return Err(AbiErrorV2::InvalidBounds(
                "global terminal obligation plan deltas",
            ));
        }
        for delta in &self.deltas {
            delta.validate()?;
        }
        if self
            .deltas
            .windows(2)
            .any(|pair| pair[0].obligation_id >= pair[1].obligation_id)
        {
            return Err(AbiErrorV2::InvalidOrder(
                "global terminal obligation plan deltas",
            ));
        }
        Ok(())
    }

    pub fn plan_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        if self.deltas.is_empty() {
            return Ok(RootV2::zero());
        }
        hash_global_v2("global-terminal-obligation-plan-v2", self)
    }
}

impl ValidateCanonicalV2 for GlobalTerminalObligationPlanV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
