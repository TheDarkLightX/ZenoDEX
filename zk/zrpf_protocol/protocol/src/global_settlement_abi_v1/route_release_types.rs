use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::{Digest, Sha256};

use super::{
    EconomicLaneIdV1, LaneModuleReleaseIdV1, RouteDependencyRoleV1, RouteDependencyRolesV1,
    RouteIssueBurnPolicyV1, RouteOraclePolicyV1, RouteReleaseErrorV1, MAX_ROUTE_DEPENDENCIES_V1,
};
use crate::CommitmentV3;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RouteModuleDependencyV1 {
    lane_id: EconomicLaneIdV1,
    module_release_id: LaneModuleReleaseIdV1,
    roles: RouteDependencyRolesV1,
    receipt_journal_schema_root: CommitmentV3,
    input_port_schema_root: CommitmentV3,
    output_port_schema_root: CommitmentV3,
}

impl RouteModuleDependencyV1 {
    pub const fn new(
        lane_id: EconomicLaneIdV1,
        module_release_id: LaneModuleReleaseIdV1,
        roles: RouteDependencyRolesV1,
        receipt_journal_schema_root: CommitmentV3,
        input_port_schema_root: CommitmentV3,
        output_port_schema_root: CommitmentV3,
    ) -> Self {
        Self {
            lane_id,
            module_release_id,
            roles,
            receipt_journal_schema_root,
            input_port_schema_root,
            output_port_schema_root,
        }
    }

    pub const fn lane_id(&self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn module_release_id(&self) -> LaneModuleReleaseIdV1 {
        self.module_release_id
    }

    pub const fn roles(&self) -> RouteDependencyRolesV1 {
        self.roles
    }

    pub const fn receipt_journal_schema_root(&self) -> CommitmentV3 {
        self.receipt_journal_schema_root
    }

    pub const fn input_port_schema_root(&self) -> CommitmentV3 {
        self.input_port_schema_root
    }

    pub const fn output_port_schema_root(&self) -> CommitmentV3 {
        self.output_port_schema_root
    }

    pub(super) fn update_hasher(&self, hasher: &mut Sha256) {
        hasher.update([self.lane_id.code()]);
        hasher.update(self.module_release_id.as_bytes());
        hasher.update([self.roles.bits()]);
        update_commitment(hasher, self.receipt_journal_schema_root);
        update_commitment(hasher, self.input_port_schema_root);
        update_commitment(hasher, self.output_port_schema_root);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct RouteResourceLimitsV1 {
    max_total_journal_bytes: u32,
    max_private_port_bytes: u32,
    max_composition_cycles: u64,
}

impl RouteResourceLimitsV1 {
    pub fn new(
        max_total_journal_bytes: u32,
        max_private_port_bytes: u32,
        max_composition_cycles: u64,
    ) -> Result<Self, RouteReleaseErrorV1> {
        require_nonzero(max_total_journal_bytes, "max_total_journal_bytes")?;
        require_nonzero(max_private_port_bytes, "max_private_port_bytes")?;
        if max_composition_cycles == 0 {
            return Err(RouteReleaseErrorV1::ZeroResourceLimit(
                "max_composition_cycles",
            ));
        }
        Ok(Self {
            max_total_journal_bytes,
            max_private_port_bytes,
            max_composition_cycles,
        })
    }

    pub const fn max_total_journal_bytes(self) -> u32 {
        self.max_total_journal_bytes
    }

    pub const fn max_private_port_bytes(self) -> u32 {
        self.max_private_port_bytes
    }

    pub const fn max_composition_cycles(self) -> u64 {
        self.max_composition_cycles
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        hasher.update(self.max_total_journal_bytes.to_be_bytes());
        hasher.update(self.max_private_port_bytes.to_be_bytes());
        hasher.update(self.max_composition_cycles.to_be_bytes());
    }
}

impl<'de> Deserialize<'de> for RouteResourceLimitsV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            max_total_journal_bytes: u32,
            max_private_port_bytes: u32,
            max_composition_cycles: u64,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(
            wire.max_total_journal_bytes,
            wire.max_private_port_bytes,
            wire.max_composition_cycles,
        )
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RouteReleaseContentV1 {
    command_variant_root: CommitmentV3,
    dependencies: Vec<RouteModuleDependencyV1>,
    port_pairing_root: CommitmentV3,
    oracle_policy: RouteOraclePolicyV1,
    issue_burn_policy: RouteIssueBurnPolicyV1,
    resource_limits: RouteResourceLimitsV1,
}

impl RouteReleaseContentV1 {
    /// Constructs the complete route commitment in canonical field order.
    ///
    /// The six explicit arguments are intentional: each is independently
    /// identity-bound, and a partial builder would permit an incompletely
    /// specified route to exist between calls.
    pub fn new(
        command_variant_root: CommitmentV3,
        dependencies: Vec<RouteModuleDependencyV1>,
        port_pairing_root: CommitmentV3,
        oracle_policy: RouteOraclePolicyV1,
        issue_burn_policy: RouteIssueBurnPolicyV1,
        resource_limits: RouteResourceLimitsV1,
    ) -> Result<Self, RouteReleaseErrorV1> {
        validate_dependencies(&dependencies, oracle_policy, issue_burn_policy)?;
        Ok(Self {
            command_variant_root,
            dependencies,
            port_pairing_root,
            oracle_policy,
            issue_burn_policy,
            resource_limits,
        })
    }

    pub fn dependencies(&self) -> &[RouteModuleDependencyV1] {
        &self.dependencies
    }

    pub const fn command_variant_root(&self) -> CommitmentV3 {
        self.command_variant_root
    }

    pub const fn port_pairing_root(&self) -> CommitmentV3 {
        self.port_pairing_root
    }

    pub const fn oracle_policy(&self) -> RouteOraclePolicyV1 {
        self.oracle_policy
    }

    pub const fn issue_burn_policy(&self) -> RouteIssueBurnPolicyV1 {
        self.issue_burn_policy
    }

    pub const fn resource_limits(&self) -> RouteResourceLimitsV1 {
        self.resource_limits
    }

    pub(super) fn update_hasher(&self, hasher: &mut Sha256) -> Result<(), RouteReleaseErrorV1> {
        validate_dependencies(
            &self.dependencies,
            self.oracle_policy,
            self.issue_burn_policy,
        )?;
        update_commitment(hasher, self.command_variant_root);
        let count = u8::try_from(self.dependencies.len())
            .map_err(|_| RouteReleaseErrorV1::ArithmeticOverflow("dependency_count"))?;
        hasher.update([count]);
        for dependency in &self.dependencies {
            dependency.update_hasher(hasher);
        }
        update_commitment(hasher, self.port_pairing_root);
        self.oracle_policy.update_hasher(hasher);
        self.issue_burn_policy.update_hasher(hasher);
        self.resource_limits.update_hasher(hasher);
        Ok(())
    }
}

impl<'de> Deserialize<'de> for RouteReleaseContentV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            command_variant_root: CommitmentV3,
            #[serde(deserialize_with = "deserialize_dependencies")]
            dependencies: Vec<RouteModuleDependencyV1>,
            port_pairing_root: CommitmentV3,
            oracle_policy: RouteOraclePolicyV1,
            issue_burn_policy: RouteIssueBurnPolicyV1,
            resource_limits: RouteResourceLimitsV1,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(
            wire.command_variant_root,
            wire.dependencies,
            wire.port_pairing_root,
            wire.oracle_policy,
            wire.issue_burn_policy,
            wire.resource_limits,
        )
        .map_err(de::Error::custom)
    }
}

fn deserialize_dependencies<'de, D>(
    deserializer: D,
) -> Result<Vec<RouteModuleDependencyV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct DependenciesVisitor;

    impl<'de> Visitor<'de> for DependenciesVisitor {
        type Value = Vec<RouteModuleDependencyV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "one to {MAX_ROUTE_DEPENDENCIES_V1} route dependencies"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ROUTE_DEPENDENCIES_V1 {
                return Err(de::Error::custom("route dependency count exceeds bound"));
            }
            let mut dependencies = Vec::with_capacity(declared);
            while let Some(dependency) = sequence.next_element()? {
                if dependencies.len() == MAX_ROUTE_DEPENDENCIES_V1 {
                    return Err(de::Error::custom("route dependency count exceeds bound"));
                }
                dependencies.push(dependency);
            }
            Ok(dependencies)
        }
    }

    deserializer.deserialize_seq(DependenciesVisitor)
}

fn validate_dependencies(
    dependencies: &[RouteModuleDependencyV1],
    oracle_policy: RouteOraclePolicyV1,
    issue_burn_policy: RouteIssueBurnPolicyV1,
) -> Result<(), RouteReleaseErrorV1> {
    if dependencies.is_empty() {
        return Err(RouteReleaseErrorV1::EmptyDependencies);
    }
    if dependencies.len() > MAX_ROUTE_DEPENDENCIES_V1 {
        return Err(RouteReleaseErrorV1::TooManyDependencies {
            actual: dependencies.len(),
            maximum: MAX_ROUTE_DEPENDENCIES_V1,
        });
    }

    let mut primary_count = 0usize;
    let mut oracle_count = 0usize;
    let mut issue_burn_count = 0usize;
    for (position, dependency) in dependencies.iter().enumerate() {
        if dependencies[..position]
            .iter()
            .any(|earlier| earlier.lane_id == dependency.lane_id)
        {
            return Err(RouteReleaseErrorV1::DuplicateDependencyLane(
                dependency.lane_id,
            ));
        }
        primary_count += usize::from(dependency.roles.contains(RouteDependencyRoleV1::Primary));
        oracle_count += usize::from(dependency.roles.contains(RouteDependencyRoleV1::Oracle));
        issue_burn_count +=
            usize::from(dependency.roles.contains(RouteDependencyRoleV1::IssueBurn));
    }
    if primary_count != 1 {
        return Err(RouteReleaseErrorV1::PrimaryDependencyCount(primary_count));
    }
    let expected_oracle_count = usize::from(oracle_policy.requires_oracle());
    if oracle_count != expected_oracle_count {
        return Err(RouteReleaseErrorV1::OracleDependencyCount(oracle_count));
    }
    let expected_issue_burn_count = usize::from(issue_burn_policy.authorizes_issue_or_burn());
    if issue_burn_count != expected_issue_burn_count {
        return Err(RouteReleaseErrorV1::IssueBurnDependencyCount(
            issue_burn_count,
        ));
    }
    Ok(())
}

fn require_nonzero(value: u32, field: &'static str) -> Result<(), RouteReleaseErrorV1> {
    if value == 0 {
        return Err(RouteReleaseErrorV1::ZeroResourceLimit(field));
    }
    Ok(())
}

fn update_commitment(hasher: &mut Sha256, commitment: CommitmentV3) {
    hasher.update(commitment.as_bytes());
}
