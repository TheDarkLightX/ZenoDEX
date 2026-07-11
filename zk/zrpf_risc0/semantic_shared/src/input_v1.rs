use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{
    V1AdapterSemanticLeafOpeningV1, MAX_IMMEDIATE_CHILDREN_V3, MAX_LEAF_COUNT_V3,
    MAX_NODE_JOURNAL_BYTES_V3,
};

pub const MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1: usize = MAX_IMMEDIATE_CHILDREN_V3;
pub const MAX_SEMANTIC_LEAF_DISCLOSURES_V1: usize = 64;
const _: () = assert!(MAX_LEAF_COUNT_V3 == 64);
const _: () = assert!(
    MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1 * MAX_IMMEDIATE_CHILDREN_V3
        == MAX_SEMANTIC_LEAF_DISCLOSURES_V1
);
pub const MAX_SEMANTIC_DISCLOSED_JOURNAL_BYTES_V1: usize = (MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1
    + MAX_SEMANTIC_LEAF_DISCLOSURES_V1)
    * MAX_NODE_JOURNAL_BYTES_V3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticRecompositionPolicyV1 {
    expected_adapter_image_id: [u32; 8],
    expected_level_one_image_id: [u32; 8],
}

impl SemanticRecompositionPolicyV1 {
    pub fn new(
        expected_adapter_image_id: [u32; 8],
        expected_level_one_image_id: [u32; 8],
    ) -> Result<Self, SemanticRecompositionErrorV1> {
        if expected_adapter_image_id.iter().all(|word| *word == 0) {
            return Err(SemanticRecompositionErrorV1::ZeroAdapterImageId);
        }
        if expected_level_one_image_id.iter().all(|word| *word == 0) {
            return Err(SemanticRecompositionErrorV1::ZeroLevelOneImageId);
        }
        Ok(Self {
            expected_adapter_image_id,
            expected_level_one_image_id,
        })
    }

    pub const fn expected_adapter_image_id(self) -> [u32; 8] {
        self.expected_adapter_image_id
    }

    pub const fn expected_level_one_image_id(self) -> [u32; 8] {
        self.expected_level_one_image_id
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisclosedV1AdapterLeafV1 {
    journal_bytes: Vec<u8>,
    semantic_opening: V1AdapterSemanticLeafOpeningV1,
}

impl DisclosedV1AdapterLeafV1 {
    pub fn new(
        journal_bytes: Vec<u8>,
        semantic_opening: V1AdapterSemanticLeafOpeningV1,
    ) -> Result<Self, SemanticRecompositionErrorV1> {
        validate_journal_length(&journal_bytes).map_err(|length| {
            SemanticRecompositionErrorV1::InvalidAdapterJournalLength { length }
        })?;
        Ok(Self {
            journal_bytes,
            semantic_opening,
        })
    }

    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }

    pub const fn semantic_opening(&self) -> V1AdapterSemanticLeafOpeningV1 {
        self.semantic_opening
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisclosedStructuralLevelOneV1 {
    level_one_journal_bytes: Vec<u8>,
    adapter_leaves: Vec<DisclosedV1AdapterLeafV1>,
}

impl DisclosedStructuralLevelOneV1 {
    pub fn new(
        level_one_journal_bytes: Vec<u8>,
        adapter_leaves: Vec<DisclosedV1AdapterLeafV1>,
    ) -> Result<Self, SemanticRecompositionErrorV1> {
        validate_journal_length(&level_one_journal_bytes).map_err(|length| {
            SemanticRecompositionErrorV1::InvalidLevelOneJournalLength { length }
        })?;
        if adapter_leaves.is_empty() {
            return Err(SemanticRecompositionErrorV1::EmptyAdapterLeaves);
        }
        if adapter_leaves.len() > MAX_IMMEDIATE_CHILDREN_V3 {
            return Err(SemanticRecompositionErrorV1::TooManyAdapterLeaves {
                actual: adapter_leaves.len(),
                maximum: MAX_IMMEDIATE_CHILDREN_V3,
            });
        }
        Ok(Self {
            level_one_journal_bytes,
            adapter_leaves,
        })
    }

    pub fn level_one_journal_bytes(&self) -> &[u8] {
        &self.level_one_journal_bytes
    }

    pub fn adapter_leaves(&self) -> &[DisclosedV1AdapterLeafV1] {
        &self.adapter_leaves
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticRecompositionInputV1 {
    level_one_nodes: Vec<DisclosedStructuralLevelOneV1>,
}

impl SemanticRecompositionInputV1 {
    pub fn new(
        level_one_nodes: Vec<DisclosedStructuralLevelOneV1>,
    ) -> Result<Self, SemanticRecompositionErrorV1> {
        let input = Self { level_one_nodes };
        input.validate_bounds()?;
        Ok(input)
    }

    pub fn level_one_nodes(&self) -> &[DisclosedStructuralLevelOneV1] {
        &self.level_one_nodes
    }

    pub(crate) fn validate_bounds(&self) -> Result<(), SemanticRecompositionErrorV1> {
        if self.level_one_nodes.is_empty() {
            return Err(SemanticRecompositionErrorV1::EmptyLevelOneNodes);
        }
        if self.level_one_nodes.len() > MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1 {
            return Err(SemanticRecompositionErrorV1::TooManyLevelOneNodes {
                actual: self.level_one_nodes.len(),
                maximum: MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1,
            });
        }
        let mut leaf_count = 0usize;
        let mut disclosed_bytes = 0usize;
        for node in &self.level_one_nodes {
            leaf_count = leaf_count.checked_add(node.adapter_leaves.len()).ok_or(
                SemanticRecompositionErrorV1::ArithmeticOverflow("leaf_count"),
            )?;
            disclosed_bytes = disclosed_bytes
                .checked_add(node.level_one_journal_bytes.len())
                .ok_or(SemanticRecompositionErrorV1::ArithmeticOverflow(
                    "disclosed_journal_bytes",
                ))?;
            for leaf in &node.adapter_leaves {
                disclosed_bytes = disclosed_bytes
                    .checked_add(leaf.journal_bytes.len())
                    .ok_or(SemanticRecompositionErrorV1::ArithmeticOverflow(
                        "disclosed_journal_bytes",
                    ))?;
            }
        }
        if leaf_count > MAX_SEMANTIC_LEAF_DISCLOSURES_V1 {
            return Err(SemanticRecompositionErrorV1::TooManySemanticLeaves {
                actual: leaf_count,
                maximum: MAX_SEMANTIC_LEAF_DISCLOSURES_V1,
            });
        }
        if disclosed_bytes > MAX_SEMANTIC_DISCLOSED_JOURNAL_BYTES_V1 {
            return Err(
                SemanticRecompositionErrorV1::DisclosedJournalBytesTooLarge {
                    actual: disclosed_bytes,
                    maximum: MAX_SEMANTIC_DISCLOSED_JOURNAL_BYTES_V1,
                },
            );
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticRecompositionErrorV1 {
    ZeroAdapterImageId,
    ZeroLevelOneImageId,
    EmptyLevelOneNodes,
    TooManyLevelOneNodes {
        actual: usize,
        maximum: usize,
    },
    EmptyAdapterLeaves,
    TooManyAdapterLeaves {
        actual: usize,
        maximum: usize,
    },
    TooManySemanticLeaves {
        actual: usize,
        maximum: usize,
    },
    InvalidLevelOneJournalLength {
        length: usize,
    },
    InvalidAdapterJournalLength {
        length: usize,
    },
    DisclosedJournalBytesTooLarge {
        actual: usize,
        maximum: usize,
    },
    LevelOneJournalDecode {
        subtree: usize,
    },
    AdapterJournalDecode {
        subtree: usize,
        child: usize,
    },
    LevelOneAggregateRequired {
        subtree: usize,
    },
    LevelOneLevelMismatch {
        subtree: usize,
    },
    LevelOneProgramMismatch {
        subtree: usize,
    },
    LevelOneProfileMismatch {
        subtree: usize,
    },
    PartitionMustStartAtZero,
    NonCanonicalSubtreeOrder {
        subtree: usize,
    },
    NonContiguousSubtrees {
        subtree: usize,
    },
    NonCanonicalChildOrder {
        subtree: usize,
        child: usize,
    },
    NonContiguousChildren {
        subtree: usize,
        child: usize,
    },
    StructuralRecomposition {
        subtree: usize,
        error: zenodex_zrpf_risc0_aggregate_shared::StructuralAggregateErrorV1,
    },
    LevelOneJournalMismatch {
        subtree: usize,
    },
    SemanticProjection {
        subtree: usize,
        child: usize,
        error: zenodex_zrpf_protocol_v3::SemanticEpochErrorV1,
    },
    DuplicateSemanticSource,
    DuplicateSourceClaim,
    DuplicateTask,
    Derivation(&'static str),
    Protocol(zenodex_zrpf_protocol_v3::ZrpfErrorV3),
    ArithmeticOverflow(&'static str),
}

impl fmt::Display for SemanticRecompositionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroAdapterImageId => formatter.write_str("adapter image ID is zero"),
            Self::ZeroLevelOneImageId => formatter.write_str("level-one image ID is zero"),
            Self::EmptyLevelOneNodes => formatter.write_str("no level-one nodes were disclosed"),
            Self::TooManyLevelOneNodes { actual, maximum } => {
                write!(formatter, "level-one node count {actual} exceeds {maximum}")
            }
            Self::EmptyAdapterLeaves => formatter.write_str("level-one disclosure has no leaves"),
            Self::TooManyAdapterLeaves { actual, maximum } => {
                write!(formatter, "adapter leaf count {actual} exceeds {maximum}")
            }
            Self::TooManySemanticLeaves { actual, maximum } => {
                write!(formatter, "semantic leaf count {actual} exceeds {maximum}")
            }
            Self::InvalidLevelOneJournalLength { length } => {
                write!(formatter, "invalid level-one journal length: {length}")
            }
            Self::InvalidAdapterJournalLength { length } => {
                write!(formatter, "invalid adapter journal length: {length}")
            }
            Self::DisclosedJournalBytesTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "disclosed journal bytes {actual} exceed {maximum}"
                )
            }
            Self::LevelOneJournalDecode { subtree } => {
                write!(
                    formatter,
                    "level-one journal {subtree} is not exact canonical V3"
                )
            }
            Self::AdapterJournalDecode { subtree, child } => {
                write!(
                    formatter,
                    "adapter journal {subtree}:{child} is not exact canonical V3"
                )
            }
            Self::LevelOneAggregateRequired { subtree } => {
                write!(formatter, "level-one journal {subtree} is not an aggregate")
            }
            Self::LevelOneLevelMismatch { subtree } => {
                write!(formatter, "level-one journal {subtree} has the wrong level")
            }
            Self::LevelOneProgramMismatch { subtree } => {
                write!(
                    formatter,
                    "level-one journal {subtree} has the wrong program"
                )
            }
            Self::LevelOneProfileMismatch { subtree } => {
                write!(
                    formatter,
                    "level-one journal {subtree} has the wrong profile"
                )
            }
            Self::PartitionMustStartAtZero => {
                formatter.write_str("semantic partitions must start at zero")
            }
            Self::NonCanonicalSubtreeOrder { subtree } => {
                write!(
                    formatter,
                    "level-one journal {subtree} is out of canonical order"
                )
            }
            Self::NonContiguousSubtrees { subtree } => {
                write!(formatter, "level-one journal {subtree} is not contiguous")
            }
            Self::NonCanonicalChildOrder { subtree, child } => {
                write!(
                    formatter,
                    "adapter journal {subtree}:{child} is out of canonical order"
                )
            }
            Self::NonContiguousChildren { subtree, child } => {
                write!(
                    formatter,
                    "adapter journal {subtree}:{child} is not contiguous"
                )
            }
            Self::StructuralRecomposition { subtree, error } => {
                write!(
                    formatter,
                    "level-one journal {subtree} failed recomposition: {error}"
                )
            }
            Self::LevelOneJournalMismatch { subtree } => {
                write!(
                    formatter,
                    "level-one journal {subtree} differs from recomposition"
                )
            }
            Self::SemanticProjection {
                subtree,
                child,
                error,
            } => write!(
                formatter,
                "semantic leaf {subtree}:{child} rejected: {error}"
            ),
            Self::DuplicateSemanticSource => formatter.write_str("duplicate semantic source"),
            Self::DuplicateSourceClaim => formatter.write_str("duplicate source claim"),
            Self::DuplicateTask => formatter.write_str("duplicate semantic task"),
            Self::Derivation(field) => write!(formatter, "semantic derivation failed: {field}"),
            Self::Protocol(error) => write!(formatter, "ZRPF protocol rejected input: {error}"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
        }
    }
}

impl From<zenodex_zrpf_protocol_v3::ZrpfErrorV3> for SemanticRecompositionErrorV1 {
    fn from(error: zenodex_zrpf_protocol_v3::ZrpfErrorV3) -> Self {
        Self::Protocol(error)
    }
}

fn validate_journal_length(bytes: &[u8]) -> Result<(), usize> {
    if bytes.is_empty() || bytes.len() > MAX_NODE_JOURNAL_BYTES_V3 {
        return Err(bytes.len());
    }
    Ok(())
}
