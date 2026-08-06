use alloc::vec::Vec;

use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::{Digest, Sha256};

use super::{
    EconomicLaneIdV1, EconomicProfileIdV1, GlobalEconomicStateErrorV1, ECONOMIC_LANE_COUNT_V1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicLaneStateRootV1 {
    lane_id: EconomicLaneIdV1,
    state_root: CommitmentV3,
}

impl GlobalEconomicLaneStateRootV1 {
    pub const fn new(lane_id: EconomicLaneIdV1, state_root: CommitmentV3) -> Self {
        Self {
            lane_id,
            state_root,
        }
    }

    pub const fn lane_id(self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn state_root(self) -> CommitmentV3 {
        self.state_root
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalEconomicPartitionRootsInputV1 {
    pub balances_root: CommitmentV3,
    pub supplies_root: CommitmentV3,
    pub custody_root: CommitmentV3,
    pub liabilities_root: CommitmentV3,
    pub reserves_root: CommitmentV3,
    pub oracle_occurrences_root: CommitmentV3,
    pub replay_state_root: CommitmentV3,
    pub terminal_obligations_root: CommitmentV3,
    pub release_observations_root: CommitmentV3,
    pub history_root: CommitmentV3,
    pub external_outbox_root: CommitmentV3,
    pub object_release_registry_root: CommitmentV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicPartitionRootsV1 {
    balances_root: CommitmentV3,
    supplies_root: CommitmentV3,
    custody_root: CommitmentV3,
    liabilities_root: CommitmentV3,
    reserves_root: CommitmentV3,
    oracle_occurrences_root: CommitmentV3,
    replay_state_root: CommitmentV3,
    terminal_obligations_root: CommitmentV3,
    release_observations_root: CommitmentV3,
    history_root: CommitmentV3,
    external_outbox_root: CommitmentV3,
    object_release_registry_root: CommitmentV3,
}

impl GlobalEconomicPartitionRootsV1 {
    pub const fn new(input: GlobalEconomicPartitionRootsInputV1) -> Self {
        Self {
            balances_root: input.balances_root,
            supplies_root: input.supplies_root,
            custody_root: input.custody_root,
            liabilities_root: input.liabilities_root,
            reserves_root: input.reserves_root,
            oracle_occurrences_root: input.oracle_occurrences_root,
            replay_state_root: input.replay_state_root,
            terminal_obligations_root: input.terminal_obligations_root,
            release_observations_root: input.release_observations_root,
            history_root: input.history_root,
            external_outbox_root: input.external_outbox_root,
            object_release_registry_root: input.object_release_registry_root,
        }
    }

    pub const fn balances_root(self) -> CommitmentV3 {
        self.balances_root
    }
    pub const fn supplies_root(self) -> CommitmentV3 {
        self.supplies_root
    }
    pub const fn custody_root(self) -> CommitmentV3 {
        self.custody_root
    }
    pub const fn liabilities_root(self) -> CommitmentV3 {
        self.liabilities_root
    }
    pub const fn reserves_root(self) -> CommitmentV3 {
        self.reserves_root
    }
    pub const fn oracle_occurrences_root(self) -> CommitmentV3 {
        self.oracle_occurrences_root
    }
    pub const fn replay_state_root(self) -> CommitmentV3 {
        self.replay_state_root
    }
    pub const fn terminal_obligations_root(self) -> CommitmentV3 {
        self.terminal_obligations_root
    }
    pub const fn release_observations_root(self) -> CommitmentV3 {
        self.release_observations_root
    }
    pub const fn history_root(self) -> CommitmentV3 {
        self.history_root
    }
    pub const fn external_outbox_root(self) -> CommitmentV3 {
        self.external_outbox_root
    }
    pub const fn object_release_registry_root(self) -> CommitmentV3 {
        self.object_release_registry_root
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        for root in [
            self.balances_root,
            self.supplies_root,
            self.custody_root,
            self.liabilities_root,
            self.reserves_root,
            self.oracle_occurrences_root,
            self.replay_state_root,
            self.terminal_obligations_root,
            self.release_observations_root,
            self.history_root,
            self.external_outbox_root,
            self.object_release_registry_root,
        ] {
            hasher.update(root.as_bytes());
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalEconomicStateContentInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub height: u64,
    pub writer_epoch: u64,
    pub profile_id: EconomicProfileIdV1,
    pub lane_state_roots: Vec<GlobalEconomicLaneStateRootV1>,
    pub partition_roots: GlobalEconomicPartitionRootsV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[must_use = "the state content must be committed into GlobalEconomicStateV1"]
pub struct GlobalEconomicStateContentV1 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    height: u64,
    writer_epoch: u64,
    profile_id: EconomicProfileIdV1,
    lane_state_roots: Vec<GlobalEconomicLaneStateRootV1>,
    partition_roots: GlobalEconomicPartitionRootsV1,
}

impl GlobalEconomicStateContentV1 {
    pub fn new(
        input: GlobalEconomicStateContentInputV1,
    ) -> Result<Self, GlobalEconomicStateErrorV1> {
        validate_lane_state_roots(&input.lane_state_roots)?;
        Ok(Self {
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            height: input.height,
            writer_epoch: input.writer_epoch,
            profile_id: input.profile_id,
            lane_state_roots: input.lane_state_roots,
            partition_roots: input.partition_roots,
        })
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }
    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }
    pub const fn height(&self) -> u64 {
        self.height
    }
    pub const fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }
    pub const fn profile_id(&self) -> EconomicProfileIdV1 {
        self.profile_id
    }
    pub fn lane_state_roots(&self) -> &[GlobalEconomicLaneStateRootV1] {
        &self.lane_state_roots
    }
    pub const fn partition_roots(&self) -> GlobalEconomicPartitionRootsV1 {
        self.partition_roots
    }

    pub(super) fn validate_self_consistency(&self) -> Result<(), GlobalEconomicStateErrorV1> {
        validate_lane_state_roots(&self.lane_state_roots)
    }

    pub(super) fn update_hasher(
        &self,
        hasher: &mut Sha256,
    ) -> Result<(), GlobalEconomicStateErrorV1> {
        self.validate_self_consistency()?;
        hasher.update(self.application_id.as_bytes());
        hasher.update(self.chain_or_domain_id.as_bytes());
        hasher.update(self.height.to_be_bytes());
        hasher.update(self.writer_epoch.to_be_bytes());
        hasher.update(self.profile_id.as_bytes());
        let count = u8::try_from(self.lane_state_roots.len())
            .map_err(|_| GlobalEconomicStateErrorV1::ArithmeticOverflow("lane_state_root_count"))?;
        hasher.update([count]);
        for lane in &self.lane_state_roots {
            hasher.update([lane.lane_id().code()]);
            hasher.update(lane.state_root().as_bytes());
        }
        self.partition_roots.update_hasher(hasher);
        Ok(())
    }
}

impl<'de> Deserialize<'de> for GlobalEconomicStateContentV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            application_id: ApplicationIdV3,
            chain_or_domain_id: DomainIdV3,
            height: u64,
            writer_epoch: u64,
            profile_id: EconomicProfileIdV1,
            #[serde(deserialize_with = "deserialize_lane_state_roots")]
            lane_state_roots: Vec<GlobalEconomicLaneStateRootV1>,
            partition_roots: GlobalEconomicPartitionRootsV1,
        }
        let wire = Wire::deserialize(deserializer)?;
        Self::new(GlobalEconomicStateContentInputV1 {
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            height: wire.height,
            writer_epoch: wire.writer_epoch,
            profile_id: wire.profile_id,
            lane_state_roots: wire.lane_state_roots,
            partition_roots: wire.partition_roots,
        })
        .map_err(de::Error::custom)
    }
}

fn deserialize_lane_state_roots<'de, D>(
    deserializer: D,
) -> Result<Vec<GlobalEconomicLaneStateRootV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct LaneStateRootsVisitor;

    impl<'de> Visitor<'de> for LaneStateRootsVisitor {
        type Value = Vec<GlobalEconomicLaneStateRootV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "exactly {ECONOMIC_LANE_COUNT_V1} global economic lane-state roots"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > ECONOMIC_LANE_COUNT_V1 {
                return Err(de::Error::invalid_length(declared, &self));
            }
            let mut roots = Vec::with_capacity(declared.min(ECONOMIC_LANE_COUNT_V1));
            while let Some(root) = sequence.next_element()? {
                if roots.len() == ECONOMIC_LANE_COUNT_V1 {
                    return Err(de::Error::invalid_length(ECONOMIC_LANE_COUNT_V1 + 1, &self));
                }
                roots.push(root);
            }
            Ok(roots)
        }
    }

    deserializer.deserialize_seq(LaneStateRootsVisitor)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct GlobalEconomicStateRootV1([u8; 32]);

impl GlobalEconomicStateRootV1 {
    pub fn new(bytes: [u8; 32]) -> Result<Self, GlobalEconomicStateErrorV1> {
        if bytes == [0; 32] {
            return Err(GlobalEconomicStateErrorV1::ZeroStateRoot);
        }
        Ok(Self(bytes))
    }
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl<'de> Deserialize<'de> for GlobalEconomicStateRootV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(<[u8; 32]>::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

fn validate_lane_state_roots(
    lane_state_roots: &[GlobalEconomicLaneStateRootV1],
) -> Result<(), GlobalEconomicStateErrorV1> {
    if lane_state_roots.len() != ECONOMIC_LANE_COUNT_V1 {
        return Err(GlobalEconomicStateErrorV1::WrongLaneStateRootCount {
            actual: lane_state_roots.len(),
            expected: ECONOMIC_LANE_COUNT_V1,
        });
    }
    for (position, lane) in lane_state_roots.iter().enumerate() {
        if lane_state_roots[..position]
            .iter()
            .any(|earlier| earlier.lane_id() == lane.lane_id())
        {
            return Err(GlobalEconomicStateErrorV1::DuplicateLaneStateRoot(
                lane.lane_id(),
            ));
        }
    }
    for (position, (actual, expected)) in lane_state_roots
        .iter()
        .zip(EconomicLaneIdV1::ALL)
        .enumerate()
    {
        if actual.lane_id() != expected {
            return Err(GlobalEconomicStateErrorV1::NonCanonicalLaneStateRootOrder {
                position,
                expected,
                actual: actual.lane_id(),
            });
        }
    }
    Ok(())
}
