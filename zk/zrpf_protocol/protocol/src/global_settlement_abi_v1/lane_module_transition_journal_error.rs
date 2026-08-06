use core::fmt;

use crate::EconomicActionBatchErrorV1;

use super::{GlobalEconomicEffectPlanErrorV1, LaneStateTransitionErrorV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaneModuleTransitionJournalErrorV1 {
    EconomicAction(EconomicActionBatchErrorV1),
    EffectPlan(GlobalEconomicEffectPlanErrorV1),
    StateTransition(LaneStateTransitionErrorV1),
    InvalidJournalVersion(u16),
    ZeroRejectCode,
    PreAndPostGlobalStateMatch,
    ApplicationMismatch,
    DomainMismatch,
    ProfileMismatch,
    WriterEpochMismatch,
    OccurrenceMismatch,
    RouteMismatch,
    EconomicActionMismatch,
    GlobalPreStateMismatch,
    LanePreStateMismatch,
    RouteDependencyMissing,
    ModuleReleaseMissing,
    ModuleReleaseMismatch,
    GuestImageMismatch,
    StateSchemaMismatch,
    CommandSchemaMismatch,
    EffectSchemaMismatch,
    PrivatePortSchemaMismatch,
    CommandVariantsMismatch,
    SpecRootMismatch,
    SourceRootMismatch,
    ToolchainRootMismatch,
    JournalSchemaMismatch,
    InputPortSchemaMismatch,
    OutputPortSchemaMismatch,
    JournalResourceLimitExceeded {
        actual: usize,
        module_maximum: usize,
        route_maximum: usize,
    },
    LaneMismatch,
    OutcomeMismatch,
    GlobalPostStateMismatch,
    EffectPlanCommitmentMismatch,
    LanePostStateMismatch,
    LaneEffectRowsRootMismatch,
    StateTransitionRootMismatch,
    TerminalObligationsRootMismatch,
    LaneWriteMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<EconomicActionBatchErrorV1> for LaneModuleTransitionJournalErrorV1 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::EconomicAction(error)
    }
}

impl From<GlobalEconomicEffectPlanErrorV1> for LaneModuleTransitionJournalErrorV1 {
    fn from(error: GlobalEconomicEffectPlanErrorV1) -> Self {
        Self::EffectPlan(error)
    }
}

impl From<LaneStateTransitionErrorV1> for LaneModuleTransitionJournalErrorV1 {
    fn from(error: LaneStateTransitionErrorV1) -> Self {
        Self::StateTransition(error)
    }
}

impl fmt::Display for LaneModuleTransitionJournalErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(message) = self.fixed_message() {
            return formatter.write_str(message);
        }
        match self {
            Self::EconomicAction(error) => write!(formatter, "economic action: {error}"),
            Self::EffectPlan(error) => write!(formatter, "global effect plan: {error}"),
            Self::StateTransition(error) => write!(formatter, "lane state transition: {error}"),
            Self::InvalidJournalVersion(version) => {
                write!(formatter, "invalid lane journal version: {version}")
            }
            Self::JournalResourceLimitExceeded {
                actual,
                module_maximum,
                route_maximum,
            } => write!(
                formatter,
                "lane journal size {actual} exceeds module {module_maximum} or route {route_maximum}"
            ),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived commitment: {field}")
            }
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "lane journal input {actual} exceeds {maximum}")
            }
            _ => formatter.write_str("unclassified fixed lane journal error"),
        }
    }
}

impl LaneModuleTransitionJournalErrorV1 {
    fn fixed_message(&self) -> Option<&'static str> {
        match self {
            Self::ZeroRejectCode
            | Self::PreAndPostGlobalStateMatch
            | Self::ApplicationMismatch
            | Self::DomainMismatch
            | Self::ProfileMismatch
            | Self::WriterEpochMismatch
            | Self::OccurrenceMismatch
            | Self::RouteMismatch
            | Self::EconomicActionMismatch
            | Self::GlobalPreStateMismatch
            | Self::LanePreStateMismatch
            | Self::RouteDependencyMissing
            | Self::LaneMismatch
            | Self::ModuleReleaseMissing
            | Self::ModuleReleaseMismatch
            | Self::GuestImageMismatch
            | Self::StateSchemaMismatch
            | Self::CommandSchemaMismatch
            | Self::EffectSchemaMismatch
            | Self::PrivatePortSchemaMismatch
            | Self::CommandVariantsMismatch
            | Self::SpecRootMismatch
            | Self::SourceRootMismatch
            | Self::ToolchainRootMismatch
            | Self::JournalSchemaMismatch
            | Self::InputPortSchemaMismatch
            | Self::OutputPortSchemaMismatch
            | Self::OutcomeMismatch
            | Self::GlobalPostStateMismatch
            | Self::EffectPlanCommitmentMismatch
            | Self::LanePostStateMismatch
            | Self::LaneEffectRowsRootMismatch
            | Self::StateTransitionRootMismatch
            | Self::TerminalObligationsRootMismatch
            | Self::LaneWriteMismatch
            | Self::EmptyInput
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self
                .envelope_message()
                .or_else(|| self.release_message())
                .or_else(|| self.accepted_message())
                .or_else(|| self.codec_message()),
            Self::EconomicAction(_)
            | Self::EffectPlan(_)
            | Self::StateTransition(_)
            | Self::InvalidJournalVersion(_)
            | Self::JournalResourceLimitExceeded { .. }
            | Self::ArithmeticOverflow(_)
            | Self::InvalidDerivedCommitment(_)
            | Self::InputTooLarge { .. } => None,
        }
    }

    fn envelope_message(&self) -> Option<&'static str> {
        match self {
            Self::ZeroRejectCode => Some("lane reject code is zero"),
            Self::PreAndPostGlobalStateMatch => {
                Some("accepted lane journal has equal global pre/post roots")
            }
            Self::ApplicationMismatch => Some("lane journal application mismatch"),
            Self::DomainMismatch => Some("lane journal domain mismatch"),
            Self::ProfileMismatch => Some("lane journal profile mismatch"),
            Self::WriterEpochMismatch => Some("lane journal writer epoch mismatch"),
            Self::OccurrenceMismatch => Some("lane journal occurrence mismatch"),
            Self::RouteMismatch => Some("lane journal route mismatch"),
            Self::EconomicActionMismatch => Some("lane journal economic action mismatch"),
            Self::GlobalPreStateMismatch => Some("lane journal global pre-state mismatch"),
            Self::LanePreStateMismatch => Some("lane journal lane pre-state mismatch"),
            Self::LaneMismatch => Some("lane journal lane mismatch"),
            Self::RouteDependencyMissing => Some("lane journal route dependency missing"),
            _ => None,
        }
    }

    fn release_message(&self) -> Option<&'static str> {
        match self {
            Self::ModuleReleaseMissing => Some("lane journal module release missing"),
            Self::ModuleReleaseMismatch => Some("lane journal module release mismatch"),
            Self::GuestImageMismatch => Some("lane journal guest image mismatch"),
            Self::StateSchemaMismatch => Some("lane journal state schema mismatch"),
            Self::CommandSchemaMismatch => Some("lane journal command schema mismatch"),
            Self::EffectSchemaMismatch => Some("lane journal effect schema mismatch"),
            Self::PrivatePortSchemaMismatch => Some("lane journal private-port schema mismatch"),
            Self::CommandVariantsMismatch => Some("lane journal command-variants root mismatch"),
            Self::SpecRootMismatch => Some("lane journal spec root mismatch"),
            Self::SourceRootMismatch => Some("lane journal source root mismatch"),
            Self::ToolchainRootMismatch => Some("lane journal toolchain root mismatch"),
            Self::JournalSchemaMismatch => Some("lane journal receipt schema mismatch"),
            Self::InputPortSchemaMismatch => Some("lane journal input-port schema mismatch"),
            Self::OutputPortSchemaMismatch => Some("lane journal output-port schema mismatch"),
            _ => None,
        }
    }

    fn accepted_message(&self) -> Option<&'static str> {
        match self {
            Self::OutcomeMismatch => Some("lane journal outcome mismatch"),
            Self::GlobalPostStateMismatch => Some("lane journal global post-state mismatch"),
            Self::EffectPlanCommitmentMismatch => {
                Some("lane journal effect-plan commitment mismatch")
            }
            Self::LanePostStateMismatch => Some("lane journal lane post-state mismatch"),
            Self::LaneEffectRowsRootMismatch => Some("lane journal lane-effect root mismatch"),
            Self::StateTransitionRootMismatch => {
                Some("lane journal state-transition root mismatch")
            }
            Self::TerminalObligationsRootMismatch => {
                Some("lane journal terminal-obligations root mismatch")
            }
            Self::LaneWriteMismatch => {
                Some("lane journal writes differ from authenticated openings")
            }
            _ => None,
        }
    }

    fn codec_message(&self) -> Option<&'static str> {
        match self {
            Self::EmptyInput => Some("lane journal input is empty"),
            Self::PostcardDecode => Some("lane journal decode failed"),
            Self::TrailingBytes => Some("lane journal has trailing bytes"),
            Self::NonCanonicalEncoding => Some("lane journal encoding is not canonical"),
            _ => None,
        }
    }
}
