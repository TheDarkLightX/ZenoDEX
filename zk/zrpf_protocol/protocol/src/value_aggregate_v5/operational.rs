use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::operational_commitments_hash_v5;
use super::ValueAggregateErrorV5;
use crate::{CommitmentV3, NodeCommitmentsV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueAggregateOperationalCommitmentsInputV5 {
    pub data_availability_root: CommitmentV3,
    pub data_availability_certificate_root: CommitmentV3,
    pub conflict_schedule_root: CommitmentV3,
    pub cross_lane_outbox_root: CommitmentV3,
    pub cross_lane_inbox_root: CommitmentV3,
    pub cross_lane_message_ids_root: CommitmentV3,
    pub carry_queue_pre_root: CommitmentV3,
    pub carry_queue_post_root: CommitmentV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
/// Proof-neutral operational commitments propagated through a V5 tree.
///
/// These fields commit to child claims. Construction and aggregation establish
/// no data-availability, scheduling, message, or carry semantics.
pub struct ValueAggregateOperationalCommitmentsV5 {
    data_availability_root: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    conflict_schedule_root: CommitmentV3,
    cross_lane_outbox_root: CommitmentV3,
    cross_lane_inbox_root: CommitmentV3,
    cross_lane_message_ids_root: CommitmentV3,
    carry_queue_pre_root: CommitmentV3,
    carry_queue_post_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ValueAggregateOperationalCommitmentsWireV5 {
    data_availability_root: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    conflict_schedule_root: CommitmentV3,
    cross_lane_outbox_root: CommitmentV3,
    cross_lane_inbox_root: CommitmentV3,
    cross_lane_message_ids_root: CommitmentV3,
    carry_queue_pre_root: CommitmentV3,
    carry_queue_post_root: CommitmentV3,
}

impl ValueAggregateOperationalCommitmentsV5 {
    pub fn new(
        input: ValueAggregateOperationalCommitmentsInputV5,
    ) -> Result<Self, ValueAggregateErrorV5> {
        let commitments = Self {
            data_availability_root: input.data_availability_root,
            data_availability_certificate_root: input.data_availability_certificate_root,
            conflict_schedule_root: input.conflict_schedule_root,
            cross_lane_outbox_root: input.cross_lane_outbox_root,
            cross_lane_inbox_root: input.cross_lane_inbox_root,
            cross_lane_message_ids_root: input.cross_lane_message_ids_root,
            carry_queue_pre_root: input.carry_queue_pre_root,
            carry_queue_post_root: input.carry_queue_post_root,
        };
        commitments.validate()?;
        Ok(commitments)
    }

    pub fn from_node_commitments_v3(
        commitments: &NodeCommitmentsV3,
    ) -> Result<Self, ValueAggregateErrorV5> {
        let input = commitments.to_input();
        Self::new(ValueAggregateOperationalCommitmentsInputV5 {
            data_availability_root: input.data_availability_root,
            data_availability_certificate_root: input.data_availability_certificate_root,
            conflict_schedule_root: input.conflict_schedule_hash,
            cross_lane_outbox_root: input.cross_lane_outbox_root,
            cross_lane_inbox_root: input.cross_lane_inbox_root,
            cross_lane_message_ids_root: input.cross_lane_message_ids_root,
            carry_queue_pre_root: input.carry_queue_pre_root,
            carry_queue_post_root: input.carry_queue_post_root,
        })
    }

    pub fn validate(&self) -> Result<(), ValueAggregateErrorV5> {
        for value in self.to_array() {
            CommitmentV3::new(value.into_bytes()).map_err(ValueAggregateErrorV5::Structural)?;
        }
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ValueAggregateErrorV5> {
        self.validate()?;
        operational_commitments_hash_v5(self)
    }

    pub const fn data_availability_root(self) -> CommitmentV3 {
        self.data_availability_root
    }

    pub const fn data_availability_certificate_root(self) -> CommitmentV3 {
        self.data_availability_certificate_root
    }

    pub const fn conflict_schedule_root(self) -> CommitmentV3 {
        self.conflict_schedule_root
    }

    pub const fn cross_lane_outbox_root(self) -> CommitmentV3 {
        self.cross_lane_outbox_root
    }

    pub const fn cross_lane_inbox_root(self) -> CommitmentV3 {
        self.cross_lane_inbox_root
    }

    pub const fn cross_lane_message_ids_root(self) -> CommitmentV3 {
        self.cross_lane_message_ids_root
    }

    pub const fn carry_queue_pre_root(self) -> CommitmentV3 {
        self.carry_queue_pre_root
    }

    pub const fn carry_queue_post_root(self) -> CommitmentV3 {
        self.carry_queue_post_root
    }

    pub(crate) const fn to_array(self) -> [CommitmentV3; 8] {
        [
            self.data_availability_root,
            self.data_availability_certificate_root,
            self.conflict_schedule_root,
            self.cross_lane_outbox_root,
            self.cross_lane_inbox_root,
            self.cross_lane_message_ids_root,
            self.carry_queue_pre_root,
            self.carry_queue_post_root,
        ]
    }
}

impl<'de> Deserialize<'de> for ValueAggregateOperationalCommitmentsV5 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ValueAggregateOperationalCommitmentsWireV5::deserialize(deserializer)?;
        Self::new(ValueAggregateOperationalCommitmentsInputV5 {
            data_availability_root: wire.data_availability_root,
            data_availability_certificate_root: wire.data_availability_certificate_root,
            conflict_schedule_root: wire.conflict_schedule_root,
            cross_lane_outbox_root: wire.cross_lane_outbox_root,
            cross_lane_inbox_root: wire.cross_lane_inbox_root,
            cross_lane_message_ids_root: wire.cross_lane_message_ids_root,
            carry_queue_pre_root: wire.carry_queue_pre_root,
            carry_queue_post_root: wire.carry_queue_post_root,
        })
        .map_err(de::Error::custom)
    }
}
