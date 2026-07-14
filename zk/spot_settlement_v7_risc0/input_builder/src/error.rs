use core::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotSettlementV7InputBuilderErrorV1 {
    UnknownOption,
    DuplicateOption(&'static str),
    MissingOption(&'static str),
    MissingOptionValue(&'static str),
    InputOpen(&'static str),
    InputMetadata(&'static str),
    InputNotSingleLinkRegular(&'static str),
    InputLength(&'static str),
    InputRead(&'static str),
    InputChanged(&'static str),
    ComponentDecode(&'static str),
    ComponentEncode(&'static str),
    ComponentNonCanonical(&'static str),
    EnvelopeConstruction,
    EnvelopeEncoding,
    EnvelopeRoundTrip,
    OutputCreate,
    OutputPermissions,
    OutputMetadata,
    OutputWrite,
    OutputSync,
    OutputSeek,
    OutputRead,
    OutputChanged,
}

impl SpotSettlementV7InputBuilderErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::UnknownOption => "unknown_option",
            Self::DuplicateOption(_) => "duplicate_option",
            Self::MissingOption(_) => "missing_option",
            Self::MissingOptionValue(_) => "missing_option_value",
            Self::InputOpen(_) => "input_open",
            Self::InputMetadata(_) => "input_metadata",
            Self::InputNotSingleLinkRegular(_) => "input_not_single_link_regular",
            Self::InputLength(_) => "input_length",
            Self::InputRead(_) => "input_read",
            Self::InputChanged(_) => "input_changed",
            Self::ComponentDecode(_) => "component_decode",
            Self::ComponentEncode(_) => "component_encode",
            Self::ComponentNonCanonical(_) => "component_noncanonical",
            Self::EnvelopeConstruction => "envelope_construction",
            Self::EnvelopeEncoding => "envelope_encoding",
            Self::EnvelopeRoundTrip => "envelope_round_trip",
            Self::OutputCreate => "output_create",
            Self::OutputPermissions => "output_permissions",
            Self::OutputMetadata => "output_metadata",
            Self::OutputWrite => "output_write",
            Self::OutputSync => "output_sync",
            Self::OutputSeek => "output_seek",
            Self::OutputRead => "output_read",
            Self::OutputChanged => "output_changed",
        }
    }

    const fn field(self) -> Option<&'static str> {
        match self {
            Self::DuplicateOption(field)
            | Self::MissingOption(field)
            | Self::MissingOptionValue(field)
            | Self::InputOpen(field)
            | Self::InputMetadata(field)
            | Self::InputNotSingleLinkRegular(field)
            | Self::InputLength(field)
            | Self::InputRead(field)
            | Self::InputChanged(field)
            | Self::ComponentDecode(field)
            | Self::ComponentEncode(field)
            | Self::ComponentNonCanonical(field) => Some(field),
            _ => None,
        }
    }
}

impl fmt::Display for SpotSettlementV7InputBuilderErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(field) = self.field() {
            write!(formatter, "{}:{field}", self.code())
        } else {
            formatter.write_str(self.code())
        }
    }
}

impl std::error::Error for SpotSettlementV7InputBuilderErrorV1 {}
