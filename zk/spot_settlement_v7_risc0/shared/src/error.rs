use core::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotSettlementV7ErrorV1 {
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    EmptyComponent(&'static str),
    ComponentTooLarge {
        component: &'static str,
        actual: usize,
        maximum: usize,
    },
    LengthOverflow(&'static str),
    TruncatedInput(&'static str),
    TrailingBytes,
    InvalidEnvelopeVersion(u16),
    NonCanonicalEnvelope,
    FinalV6ImageIdUnmaterialized,
    ZeroVerifiedChildImageId,
    ChildClaimBindingMismatch,
    ChildJournalDecode,
    ChildJournalHash,
    DataAvailabilityCertificateDecode,
    DataAvailabilityCertificateRootMismatch,
    DataAvailabilityScopeMismatch,
    DataAvailabilitySchemaMismatch,
    DataAvailabilityPolicyMismatch,
    ReplayBlobMismatch,
    ReplayDecode,
    SourceInputDecode,
    NonCanonicalSourceInput,
    SourceJournalDecode,
    NonCanonicalSourceJournal,
    SourceTransitionRejected,
    SourceJournalMismatch,
    SourceProfileRejected(&'static str),
    HostInputDecode,
    StateJournalComposition,
    StateJournalEncoding,
    EffectBinding,
    SourcePlanMismatch,
    SettlementPlanEncoding,
    SettlementPlanDecode,
    JournalAssociation(&'static str),
    InvalidJournalMagic,
    InvalidJournalVersion(u16),
    JournalLengthMismatch,
    JournalComponentHashMismatch(&'static str),
    NonCanonicalJournal,
    DerivedCommitment(&'static str),
}

impl SpotSettlementV7ErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::EmptyInput => "empty_input",
            Self::InputTooLarge { .. } => "input_too_large",
            Self::EmptyComponent(_) => "empty_component",
            Self::ComponentTooLarge { .. } => "component_too_large",
            Self::LengthOverflow(_) => "length_overflow",
            Self::TruncatedInput(_) => "truncated_input",
            Self::TrailingBytes => "trailing_bytes",
            Self::InvalidEnvelopeVersion(_) => "invalid_envelope_version",
            Self::NonCanonicalEnvelope => "noncanonical_envelope",
            Self::FinalV6ImageIdUnmaterialized => "final_v6_image_id_unmaterialized",
            Self::ZeroVerifiedChildImageId => "zero_verified_child_image_id",
            Self::ChildClaimBindingMismatch => "child_claim_binding_mismatch",
            Self::ChildJournalDecode => "child_journal_decode",
            Self::ChildJournalHash => "child_journal_hash",
            Self::DataAvailabilityCertificateDecode => "da_certificate_decode",
            Self::DataAvailabilityCertificateRootMismatch => "da_certificate_root_mismatch",
            Self::DataAvailabilityScopeMismatch => "da_scope_mismatch",
            Self::DataAvailabilitySchemaMismatch => "da_schema_mismatch",
            Self::DataAvailabilityPolicyMismatch => "da_policy_mismatch",
            Self::ReplayBlobMismatch => "replay_blob_mismatch",
            Self::ReplayDecode => "replay_decode",
            Self::SourceInputDecode => "source_input_decode",
            Self::NonCanonicalSourceInput => "noncanonical_source_input",
            Self::SourceJournalDecode => "source_journal_decode",
            Self::NonCanonicalSourceJournal => "noncanonical_source_journal",
            Self::SourceTransitionRejected => "source_transition_rejected",
            Self::SourceJournalMismatch => "source_journal_mismatch",
            Self::SourceProfileRejected(_) => "source_profile_rejected",
            Self::HostInputDecode => "host_input_decode",
            Self::StateJournalComposition => "state_journal_composition",
            Self::StateJournalEncoding => "state_journal_encoding",
            Self::EffectBinding => "effect_binding",
            Self::SourcePlanMismatch => "source_plan_mismatch",
            Self::SettlementPlanEncoding => "settlement_plan_encoding",
            Self::SettlementPlanDecode => "settlement_plan_decode",
            Self::JournalAssociation(_) => "journal_association",
            Self::InvalidJournalMagic => "invalid_journal_magic",
            Self::InvalidJournalVersion(_) => "invalid_journal_version",
            Self::JournalLengthMismatch => "journal_length_mismatch",
            Self::JournalComponentHashMismatch(_) => "journal_component_hash_mismatch",
            Self::NonCanonicalJournal => "noncanonical_journal",
            Self::DerivedCommitment(_) => "derived_commitment",
        }
    }
}

impl fmt::Display for SpotSettlementV7ErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "input has {actual} bytes, maximum is {maximum}")
            }
            Self::ComponentTooLarge {
                component,
                actual,
                maximum,
            } => write!(
                formatter,
                "{component} has {actual} bytes, maximum is {maximum}"
            ),
            Self::EmptyComponent(component) => write!(formatter, "{component} is empty"),
            Self::LengthOverflow(field) => write!(formatter, "length overflow: {field}"),
            Self::TruncatedInput(field) => write!(formatter, "truncated input: {field}"),
            Self::InvalidEnvelopeVersion(version) => {
                write!(formatter, "invalid envelope version: {version}")
            }
            Self::InvalidJournalVersion(version) => {
                write!(formatter, "invalid journal version: {version}")
            }
            Self::SourceProfileRejected(field) => {
                write!(formatter, "source profile rejected: {field}")
            }
            Self::JournalAssociation(field) => {
                write!(formatter, "journal association mismatch: {field}")
            }
            Self::JournalComponentHashMismatch(field) => {
                write!(formatter, "journal component hash mismatch: {field}")
            }
            Self::DerivedCommitment(field) => {
                write!(formatter, "derived commitment rejected: {field}")
            }
            _ => formatter.write_str(self.code()),
        }
    }
}
