use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SparseMerkleCellTransitionErrorV1 {
    InvalidWitnessVersion(u16),
    UnchangedValue,
    DepthOutOfRange(usize),
    ArithmeticOverflow(&'static str),
    DerivedZeroCommitment(&'static str),
    ClaimedPreRootMismatch,
    ClaimedPostRootMismatch,
    EconomicActionMismatch,
    CellKeyMismatch,
    PreValueMismatch,
    PostValueMismatch,
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for SparseMerkleCellTransitionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWitnessVersion(version) => {
                write!(
                    formatter,
                    "invalid sparse-Merkle witness version: {version}"
                )
            }
            Self::UnchangedValue => {
                formatter.write_str("sparse-Merkle cell transition does not change its value")
            }
            Self::DepthOutOfRange(depth) => {
                write!(formatter, "sparse-Merkle depth {depth} is outside 0..256")
            }
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "sparse-Merkle arithmetic overflow: {field}")
            }
            Self::DerivedZeroCommitment(field) => {
                write!(
                    formatter,
                    "sparse-Merkle hash produced zero commitment: {field}"
                )
            }
            Self::ClaimedPreRootMismatch => {
                formatter.write_str("claimed pre-state root differs from derived root")
            }
            Self::ClaimedPostRootMismatch => {
                formatter.write_str("claimed post-state root differs from derived root")
            }
            Self::EconomicActionMismatch => {
                formatter.write_str("witness economic action differs from ledger cell write")
            }
            Self::CellKeyMismatch => {
                formatter.write_str("witness cell key differs from ledger cell write")
            }
            Self::PreValueMismatch => {
                formatter.write_str("witness pre-value differs from ledger cell write")
            }
            Self::PostValueMismatch => {
                formatter.write_str("witness post-value differs from ledger cell write")
            }
            Self::EmptyInput => formatter.write_str("sparse-Merkle witness input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "sparse-Merkle witness input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("sparse-Merkle witness Postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("sparse-Merkle witness contains trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("sparse-Merkle witness encoding is not canonical")
            }
        }
    }
}
