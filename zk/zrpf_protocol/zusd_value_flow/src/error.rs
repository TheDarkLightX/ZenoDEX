use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZusdValueFlowErrorV1 {
    InvalidContext(&'static str),
    InvalidOperationVersion(u16),
    ActionIndexOutOfRange {
        actual: u32,
        maximum: u32,
    },
    ZeroAmount {
        action_index: u32,
    },
    AmountOutOfRange {
        action_index: u32,
        field: &'static str,
    },
    ScopeAlias {
        action_index: u32,
    },
    BasisPointsOutOfRange {
        action_index: u32,
        actual: u16,
    },
    ZeroOraclePrice {
        action_index: u32,
    },
    ArithmeticOverflow {
        action_index: u32,
        field: &'static str,
    },
    GrossCollateralZero {
        action_index: u32,
    },
    FeeConsumesCollateral {
        action_index: u32,
    },
    EmptyOperations,
    TooManyOperations {
        actual: usize,
        maximum: usize,
    },
    DuplicateActionIndex {
        action_index: u32,
    },
    NonCanonicalOperationOrder,
    InvalidRowVersion(u16),
    InvalidRowShape,
    RowSetMismatch,
    TooManyRows {
        actual: usize,
        maximum: usize,
    },
    ConservationOverflow,
    ConservationMismatch,
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

impl fmt::Display for ZusdValueFlowErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidContext(field) => write!(formatter, "invalid zUSD context: {field}"),
            Self::InvalidOperationVersion(version) => {
                write!(formatter, "invalid zUSD operation version: {version}")
            }
            Self::ActionIndexOutOfRange { actual, maximum } => {
                write!(formatter, "zUSD action index {actual} exceeds {maximum}")
            }
            Self::ZeroAmount { action_index } => {
                write!(formatter, "zUSD action {action_index} has a zero amount")
            }
            Self::AmountOutOfRange {
                action_index,
                field,
            } => write!(
                formatter,
                "zUSD action {action_index} amount is out of range: {field}"
            ),
            Self::ScopeAlias { action_index } => {
                write!(
                    formatter,
                    "zUSD action {action_index} aliases distinct scopes"
                )
            }
            Self::BasisPointsOutOfRange {
                action_index,
                actual,
            } => write!(
                formatter,
                "zUSD action {action_index} basis points {actual} exceed 10000"
            ),
            Self::ZeroOraclePrice { action_index } => {
                write!(
                    formatter,
                    "zUSD action {action_index} has a zero oracle price"
                )
            }
            Self::ArithmeticOverflow {
                action_index,
                field,
            } => write!(
                formatter,
                "zUSD action {action_index} arithmetic overflow: {field}"
            ),
            Self::GrossCollateralZero { action_index } => write!(
                formatter,
                "zUSD redemption {action_index} rounds gross collateral to zero"
            ),
            Self::FeeConsumesCollateral { action_index } => write!(
                formatter,
                "zUSD redemption {action_index} fee consumes gross collateral"
            ),
            Self::TooManyOperations { actual, maximum } => write!(
                formatter,
                "zUSD proposal has {actual} operations; maximum is {maximum}"
            ),
            Self::DuplicateActionIndex { action_index } => {
                write!(formatter, "duplicate zUSD action index: {action_index}")
            }
            Self::InvalidRowVersion(version) => {
                write!(formatter, "invalid zUSD row version: {version}")
            }
            Self::TooManyRows { actual, maximum } => write!(
                formatter,
                "zUSD proposal has {actual} rows; maximum is {maximum}"
            ),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived zUSD commitment: {field}")
            }
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "zUSD proposal input length {actual} exceeds {maximum}"
            ),
            _ => formatter.write_str(self.static_message()),
        }
    }
}

impl ZusdValueFlowErrorV1 {
    fn static_message(&self) -> &'static str {
        match self {
            Self::EmptyOperations => "zUSD proposal has no operations",
            Self::NonCanonicalOperationOrder => "zUSD operations are not canonically ordered",
            Self::InvalidRowShape => "zUSD value-flow row has an invalid typed shape",
            Self::RowSetMismatch => "zUSD value-flow rows do not match operations",
            Self::ConservationOverflow => "zUSD value-flow conservation total overflow",
            Self::ConservationMismatch => "zUSD value-flow rows do not conserve",
            Self::EmptyInput => "zUSD proposal input is empty",
            Self::PostcardDecode => "zUSD proposal postcard decode failed",
            Self::TrailingBytes => "zUSD proposal input has trailing bytes",
            Self::NonCanonicalEncoding => "zUSD proposal input is not canonical",
            _ => "zUSD value-flow proposal rejected",
        }
    }
}
