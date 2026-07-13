mod child;
mod codec;
mod error;
mod hash;
mod operational;
mod proposal;
mod proposal_validation;

pub use child::{ValueAggregateChildDescriptorInputV5, ValueAggregateChildDescriptorV5};
pub use codec::{decode_exact_value_aggregate_proposal_v5, encode_value_aggregate_proposal_v5};
pub use error::ValueAggregateErrorV5;
pub use hash::aggregate_value_operational_commitments_v5;
pub use operational::{
    ValueAggregateOperationalCommitmentsInputV5, ValueAggregateOperationalCommitmentsV5,
};
pub use proposal::{ProposedValueAggregateV5, ValueAggregateProposalInputV5};

pub const VALUE_AGGREGATE_PROPOSAL_VERSION_V5: u16 = 5;
pub const MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5: usize = 65_536;

const _: () = assert!(super::MAX_IMMEDIATE_CHILDREN_V3 == 8);
const _: () = assert!(super::MAX_NODE_LEVEL_V3 == 2);
