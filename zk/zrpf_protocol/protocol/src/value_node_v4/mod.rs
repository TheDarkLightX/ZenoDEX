mod bounded;
mod error;
mod journal;
mod records;
mod subtree;

pub use error::ValueNodeErrorV4;
pub use journal::{
    decode_exact_node_journal_v4, derive_verifier_id_v4, encode_node_journal_v4,
    NodeJournalInputV4, NodeJournalV4, VerifierIdentityInputV4,
};
pub use records::{
    SemanticAssetFlowInputV2, SemanticAssetFlowV2, SemanticAuthorityUseInputV2,
    SemanticAuthorityUseV2, SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2,
};
pub use subtree::{
    decode_exact_semantic_subtree_v2, encode_semantic_subtree_v2, SemanticSubtreeInputV2,
    SemanticSubtreeV2,
};

pub const SEMANTIC_SUBTREE_VERSION_V2: u16 = 2;
pub const NODE_JOURNAL_VERSION_V4: u16 = 4;
pub const MAX_SEMANTIC_VALUE_RECORDS_V2: usize = 64;
pub const MAX_SEMANTIC_ASSET_FLOWS_V2: usize = 128;
pub const MAX_SEMANTIC_AUTHORITY_USES_V2: usize = 128;
pub const MAX_SEMANTIC_REPRESENTED_ROWS_V2: u64 = 128;
pub const MAX_SEMANTIC_SUBTREE_BYTES_V2: usize = 60_000;
pub const MAX_NODE_JOURNAL_BYTES_V4: usize = 65_536;

const _: () = assert!(MAX_SEMANTIC_VALUE_RECORDS_V2 == super::MAX_LEAF_COUNT_V3 as usize);
const _: () = assert!(super::MAX_IMMEDIATE_CHILDREN_V3 == 8);
