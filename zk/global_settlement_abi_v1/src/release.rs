use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_root_sequence_v1, validate_schema_v1,
    validate_semantic_unique_tokens_v1, validate_sorted_unique_tokens_v1, validate_token_v1,
    AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, MAX_CYCLE_BUDGET_V1,
    MAX_JOURNAL_BYTES_V1, MAX_POLICY_BINDINGS_V1, MAX_ROUTE_MODULES_V1,
};

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[allow(non_camel_case_types)]
pub enum LaneIdV1 {
    ASSET_TRANSFER,
    SPOT_LIQUIDITY,
    FARM_INCENTIVES,
    ZDEX_TOKENOMICS,
    ZUSD_MONETARY,
    PERPS_MARKET,
    ORACLE_MARKET,
    SEALED_AUCTION,
    STRATEGY_ESCROW,
    PROOF_REWARDS,
    EXTERNAL_CUSTODY,
    GOVERNANCE_MIGRATION,
}

pub const ALL_LANE_IDS_V1: [LaneIdV1; 12] = [
    LaneIdV1::ASSET_TRANSFER,
    LaneIdV1::SPOT_LIQUIDITY,
    LaneIdV1::FARM_INCENTIVES,
    LaneIdV1::ZDEX_TOKENOMICS,
    LaneIdV1::ZUSD_MONETARY,
    LaneIdV1::PERPS_MARKET,
    LaneIdV1::ORACLE_MARKET,
    LaneIdV1::SEALED_AUCTION,
    LaneIdV1::STRATEGY_ESCROW,
    LaneIdV1::PROOF_REWARDS,
    LaneIdV1::EXTERNAL_CUSTODY,
    LaneIdV1::GOVERNANCE_MIGRATION,
];

impl LaneIdV1 {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::ASSET_TRANSFER => "ASSET_TRANSFER",
            Self::SPOT_LIQUIDITY => "SPOT_LIQUIDITY",
            Self::FARM_INCENTIVES => "FARM_INCENTIVES",
            Self::ZDEX_TOKENOMICS => "ZDEX_TOKENOMICS",
            Self::ZUSD_MONETARY => "ZUSD_MONETARY",
            Self::PERPS_MARKET => "PERPS_MARKET",
            Self::ORACLE_MARKET => "ORACLE_MARKET",
            Self::SEALED_AUCTION => "SEALED_AUCTION",
            Self::STRATEGY_ESCROW => "STRATEGY_ESCROW",
            Self::PROOF_REWARDS => "PROOF_REWARDS",
            Self::EXTERNAL_CUSTODY => "EXTERNAL_CUSTODY",
            Self::GOVERNANCE_MIGRATION => "GOVERNANCE_MIGRATION",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ReleaseStatusV1 {
    CANDIDATE,
    SHADOW,
    ACTIVE_NEW,
    DRAIN_ONLY,
    VERIFY_ONLY,
    RETIRED,
    REVOKED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum EvidenceStatusV1 {
    SPECIFIED,
    IMPLEMENTED,
    PROVED,
    MOUNTED,
    TESTED,
    TERMINAL_COMPLETE,
    MIGRATABLE,
    NO_BYPASS,
    RELEASE_BACKED,
    DISABLED_PROVED_NO_WRITER,
}

impl EvidenceStatusV1 {
    fn as_str(self) -> &'static str {
        match self {
            Self::SPECIFIED => "SPECIFIED",
            Self::IMPLEMENTED => "IMPLEMENTED",
            Self::PROVED => "PROVED",
            Self::MOUNTED => "MOUNTED",
            Self::TESTED => "TESTED",
            Self::TERMINAL_COMPLETE => "TERMINAL_COMPLETE",
            Self::MIGRATABLE => "MIGRATABLE",
            Self::NO_BYPASS => "NO_BYPASS",
            Self::RELEASE_BACKED => "RELEASE_BACKED",
            Self::DISABLED_PROVED_NO_WRITER => "DISABLED_PROVED_NO_WRITER",
        }
    }
}

const REQUIRED_ACTIVE_EVIDENCE_V1: [&str; 9] = [
    "IMPLEMENTED",
    "MIGRATABLE",
    "MOUNTED",
    "NO_BYPASS",
    "PROVED",
    "RELEASE_BACKED",
    "SPECIFIED",
    "TERMINAL_COMPLETE",
    "TESTED",
];

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ProfileStatusV1 {
    CANDIDATE,
    SHADOW,
    ACTIVE,
    RETIRED,
    REVOKED,
}

fn validate_evidence_v1(
    statuses: &[EvidenceStatusV1],
    field: &'static str,
) -> AbiResultV1<Vec<&'static str>> {
    let names: Vec<_> = statuses.iter().map(|status| status.as_str()).collect();
    if names.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AbiErrorV1::InvalidOrder(field));
    }
    Ok(names)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneModuleReleaseV1 {
    pub schema: String,
    pub lane_id: LaneIdV1,
    pub release_id: RootV1,
    pub semantic_version: String,
    pub state_schema_root: RootV1,
    pub command_variants: Vec<String>,
    pub terminal_command_variants: Vec<String>,
    pub guest_image_id: RootV1,
    pub specification_root: RootV1,
    pub source_root: RootV1,
    pub toolchain_root: RootV1,
    pub terminal_coverage_root: RootV1,
    pub migration_compatibility_root: RootV1,
    pub max_cycles: u64,
    pub max_journal_bytes: u64,
    pub status: ReleaseStatusV1,
    pub accepts_new_objects: bool,
    pub evidence_statuses: Vec<EvidenceStatusV1>,
}

#[derive(Serialize)]
struct LaneModuleReleaseContentV1<'a> {
    schema: &'static str,
    lane_id: LaneIdV1,
    state_schema_root: &'a RootV1,
    command_variants: &'a [String],
    terminal_command_variants: &'a [String],
    guest_image_id: &'a RootV1,
    specification_root: &'a RootV1,
    source_root: &'a RootV1,
    toolchain_root: &'a RootV1,
    terminal_coverage_root: &'a RootV1,
    migration_compatibility_root: &'a RootV1,
    max_cycles: u64,
    max_journal_bytes: u64,
}

impl LaneModuleReleaseV1 {
    fn content(&self) -> LaneModuleReleaseContentV1<'_> {
        LaneModuleReleaseContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            lane_id: self.lane_id,
            state_schema_root: &self.state_schema_root,
            command_variants: &self.command_variants,
            terminal_command_variants: &self.terminal_command_variants,
            guest_image_id: &self.guest_image_id,
            specification_root: &self.specification_root,
            source_root: &self.source_root,
            toolchain_root: &self.toolchain_root,
            terminal_coverage_root: &self.terminal_coverage_root,
            migration_compatibility_root: &self.migration_compatibility_root,
            max_cycles: self.max_cycles,
            max_journal_bytes: self.max_journal_bytes,
        }
    }

    fn recompute_release_id(&self) -> AbiResultV1<RootV1> {
        hash_global_v1("global-lane-module-release-content-v1", &self.content())
    }

    pub fn derived_release_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        self.recompute_release_id()
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        self.release_id.validate("lane release id", false)?;
        validate_token_v1(&self.semantic_version, "lane semantic version")?;
        validate_sorted_unique_tokens_v1(&self.command_variants, "lane command variants", true)?;
        validate_sorted_unique_tokens_v1(
            &self.terminal_command_variants,
            "lane terminal command variants",
            true,
        )?;
        if self
            .terminal_command_variants
            .iter()
            .any(|command| !self.command_variants.contains(command))
        {
            return Err(AbiErrorV1::InvalidBinding("lane terminal command variants"));
        }
        for root in [
            &self.state_schema_root,
            &self.guest_image_id,
            &self.specification_root,
            &self.source_root,
            &self.toolchain_root,
            &self.terminal_coverage_root,
            &self.migration_compatibility_root,
        ] {
            root.validate("lane release root", false)?;
        }
        if self.max_cycles == 0 || self.max_cycles > MAX_CYCLE_BUDGET_V1 {
            return Err(AbiErrorV1::InvalidBounds("lane max cycles"));
        }
        if self.max_journal_bytes == 0 || self.max_journal_bytes > MAX_JOURNAL_BYTES_V1 {
            return Err(AbiErrorV1::InvalidBounds("lane max journal bytes"));
        }
        let evidence = validate_evidence_v1(&self.evidence_statuses, "lane evidence statuses")?;
        let disabled = evidence.as_slice() == ["DISABLED_PROVED_NO_WRITER"];
        if evidence.contains(&"DISABLED_PROVED_NO_WRITER") && !disabled {
            return Err(AbiErrorV1::InvalidBinding("proved-disabled lane evidence"));
        }
        if disabled && (self.accepts_new_objects || self.status == ReleaseStatusV1::ACTIVE_NEW) {
            return Err(AbiErrorV1::InvalidBinding("proved-disabled lane status"));
        }
        validate_new_object_status_v1(
            self.status,
            self.accepts_new_objects,
            "lane release status",
        )?;
        if self.status == ReleaseStatusV1::ACTIVE_NEW
            && evidence.as_slice() != REQUIRED_ACTIVE_EVIDENCE_V1
        {
            return Err(AbiErrorV1::InvalidBinding("active lane evidence"));
        }
        if self.release_id != self.recompute_release_id()? {
            return Err(AbiErrorV1::InvalidBinding(
                "lane content-derived release id",
            ));
        }
        Ok(())
    }
}

fn validate_new_object_status_v1(
    status: ReleaseStatusV1,
    accepts_new_objects: bool,
    field: &'static str,
) -> AbiResultV1<()> {
    if accepts_new_objects != (status == ReleaseStatusV1::ACTIVE_NEW) {
        return Err(AbiErrorV1::InvalidBinding(field));
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneRegistryV1 {
    pub schema: String,
    pub releases: Vec<LaneModuleReleaseV1>,
}

impl LaneRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        if self.releases.len() != ALL_LANE_IDS_V1.len()
            || self
                .releases
                .iter()
                .map(|release| release.lane_id)
                .ne(ALL_LANE_IDS_V1)
        {
            return Err(AbiErrorV1::InvalidOrder("lane registry"));
        }
        for release in &self.releases {
            release.validate()?;
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-lane-registry-v1", self)
    }

    pub fn release_for(&self, lane_id: LaneIdV1) -> Option<&LaneModuleReleaseV1> {
        self.releases
            .iter()
            .find(|release| release.lane_id == lane_id)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneCoordinatorReleaseV1 {
    pub schema: String,
    pub lane_id: LaneIdV1,
    pub coordinator_release_id: RootV1,
    pub semantic_version: String,
    pub coordinator_schema_root: RootV1,
    pub guest_image_id: RootV1,
    pub specification_root: RootV1,
    pub source_root: RootV1,
    pub toolchain_root: RootV1,
    pub max_cycles: u64,
    pub max_journal_bytes: u64,
    pub status: ReleaseStatusV1,
    pub accepts_new_objects: bool,
    pub evidence_statuses: Vec<EvidenceStatusV1>,
}

#[derive(Serialize)]
struct LaneCoordinatorReleaseContentV1<'a> {
    schema: &'static str,
    lane_id: LaneIdV1,
    coordinator_schema_root: &'a RootV1,
    guest_image_id: &'a RootV1,
    specification_root: &'a RootV1,
    source_root: &'a RootV1,
    toolchain_root: &'a RootV1,
    max_cycles: u64,
    max_journal_bytes: u64,
}

impl LaneCoordinatorReleaseV1 {
    fn content(&self) -> LaneCoordinatorReleaseContentV1<'_> {
        LaneCoordinatorReleaseContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            lane_id: self.lane_id,
            coordinator_schema_root: &self.coordinator_schema_root,
            guest_image_id: &self.guest_image_id,
            specification_root: &self.specification_root,
            source_root: &self.source_root,
            toolchain_root: &self.toolchain_root,
            max_cycles: self.max_cycles,
            max_journal_bytes: self.max_journal_bytes,
        }
    }

    fn recompute_coordinator_release_id(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            &self.content(),
        )
    }

    pub fn derived_coordinator_release_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        self.recompute_coordinator_release_id()
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        self.coordinator_release_id
            .validate("lane coordinator release id", false)?;
        validate_token_v1(&self.semantic_version, "lane coordinator semantic version")?;
        for root in [
            &self.coordinator_schema_root,
            &self.guest_image_id,
            &self.specification_root,
            &self.source_root,
            &self.toolchain_root,
        ] {
            root.validate("lane coordinator release root", false)?;
        }
        if self.max_cycles == 0 || self.max_cycles > MAX_CYCLE_BUDGET_V1 {
            return Err(AbiErrorV1::InvalidBounds("lane coordinator max cycles"));
        }
        if self.max_journal_bytes == 0 || self.max_journal_bytes > MAX_JOURNAL_BYTES_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "lane coordinator max journal bytes",
            ));
        }
        let evidence = validate_evidence_v1(
            &self.evidence_statuses,
            "lane coordinator evidence statuses",
        )?;
        let disabled = evidence.as_slice() == ["DISABLED_PROVED_NO_WRITER"];
        if evidence.contains(&"DISABLED_PROVED_NO_WRITER") && !disabled {
            return Err(AbiErrorV1::InvalidBinding(
                "proved-disabled lane coordinator evidence",
            ));
        }
        if disabled && (self.accepts_new_objects || self.status == ReleaseStatusV1::ACTIVE_NEW) {
            return Err(AbiErrorV1::InvalidBinding(
                "proved-disabled lane coordinator status",
            ));
        }
        validate_new_object_status_v1(
            self.status,
            self.accepts_new_objects,
            "lane coordinator status",
        )?;
        if self.status == ReleaseStatusV1::ACTIVE_NEW
            && evidence.as_slice() != REQUIRED_ACTIVE_EVIDENCE_V1
        {
            return Err(AbiErrorV1::InvalidBinding(
                "active lane coordinator evidence",
            ));
        }
        if self.coordinator_release_id != self.recompute_coordinator_release_id()? {
            return Err(AbiErrorV1::InvalidBinding(
                "lane coordinator content-derived release id",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneCoordinatorRegistryV1 {
    pub schema: String,
    pub releases: Vec<LaneCoordinatorReleaseV1>,
}

impl LaneCoordinatorRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        if self.releases.len() != ALL_LANE_IDS_V1.len()
            || self
                .releases
                .iter()
                .map(|release| release.lane_id)
                .ne(ALL_LANE_IDS_V1)
        {
            return Err(AbiErrorV1::InvalidOrder("lane coordinator registry"));
        }
        for release in &self.releases {
            release.validate()?;
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-lane-coordinator-registry-v1", self)
    }

    pub fn release_for(&self, lane_id: LaneIdV1) -> Option<&LaneCoordinatorReleaseV1> {
        self.releases
            .iter()
            .find(|release| release.lane_id == lane_id)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RouteReleaseV1 {
    pub schema: String,
    pub route_release_id: RootV1,
    pub semantic_version: String,
    pub command_kind: String,
    pub ordered_lanes: Vec<LaneIdV1>,
    pub module_release_ids: Vec<RootV1>,
    pub dependency_roles: Vec<String>,
    pub port_schema_roots: Vec<RootV1>,
    pub guest_image_id: RootV1,
    pub specification_root: RootV1,
    pub source_root: RootV1,
    pub toolchain_root: RootV1,
    pub oracle_policy_root: RootV1,
    pub issue_burn_policy_root: RootV1,
    pub max_cycles: u64,
    pub max_journal_bytes: u64,
    pub status: ReleaseStatusV1,
    pub accepts_new_objects: bool,
    pub evidence_statuses: Vec<EvidenceStatusV1>,
}

#[derive(Serialize)]
struct RouteReleaseContentV1<'a> {
    schema: &'static str,
    command_kind: &'a str,
    ordered_lanes: &'a [LaneIdV1],
    module_release_ids: &'a [RootV1],
    dependency_roles: &'a [String],
    port_schema_roots: &'a [RootV1],
    guest_image_id: &'a RootV1,
    specification_root: &'a RootV1,
    source_root: &'a RootV1,
    toolchain_root: &'a RootV1,
    oracle_policy_root: &'a RootV1,
    issue_burn_policy_root: &'a RootV1,
    max_cycles: u64,
    max_journal_bytes: u64,
}

impl RouteReleaseV1 {
    fn content(&self) -> RouteReleaseContentV1<'_> {
        RouteReleaseContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            command_kind: &self.command_kind,
            ordered_lanes: &self.ordered_lanes,
            module_release_ids: &self.module_release_ids,
            dependency_roles: &self.dependency_roles,
            port_schema_roots: &self.port_schema_roots,
            guest_image_id: &self.guest_image_id,
            specification_root: &self.specification_root,
            source_root: &self.source_root,
            toolchain_root: &self.toolchain_root,
            oracle_policy_root: &self.oracle_policy_root,
            issue_burn_policy_root: &self.issue_burn_policy_root,
            max_cycles: self.max_cycles,
            max_journal_bytes: self.max_journal_bytes,
        }
    }

    fn recompute_release_id(&self) -> AbiResultV1<RootV1> {
        hash_global_v1("global-route-release-content-v1", &self.content())
    }

    pub fn derived_release_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        self.recompute_release_id()
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        self.route_release_id.validate("route release id", false)?;
        validate_token_v1(&self.semantic_version, "route semantic version")?;
        validate_token_v1(&self.command_kind, "route command kind")?;
        let width = self.ordered_lanes.len();
        if !(1..=MAX_ROUTE_MODULES_V1).contains(&width) {
            return Err(AbiErrorV1::InvalidBounds("route module count"));
        }
        if self
            .ordered_lanes
            .iter()
            .enumerate()
            .any(|(index, lane)| self.ordered_lanes[..index].contains(lane))
        {
            return Err(AbiErrorV1::InvalidOrder("route lanes"));
        }
        validate_root_sequence_v1(&self.module_release_ids, "route module release ids", true)?;
        validate_semantic_unique_tokens_v1(&self.dependency_roles, "route dependency roles")?;
        for root in &self.port_schema_roots {
            root.validate("route port schema root", false)?;
        }
        if self.module_release_ids.len() != width
            || self.dependency_roles.len() != width
            || self.port_schema_roots.len() != width
        {
            return Err(AbiErrorV1::InvalidBinding("route parallel fields"));
        }
        for root in [
            &self.guest_image_id,
            &self.specification_root,
            &self.source_root,
            &self.toolchain_root,
        ] {
            root.validate("route composer release root", false)?;
        }
        self.oracle_policy_root
            .validate("route oracle policy root", false)?;
        self.issue_burn_policy_root
            .validate("route issue burn policy root", false)?;
        if self.max_cycles == 0 || self.max_cycles > MAX_CYCLE_BUDGET_V1 {
            return Err(AbiErrorV1::InvalidBounds("route max cycles"));
        }
        if self.max_journal_bytes == 0 || self.max_journal_bytes > MAX_JOURNAL_BYTES_V1 {
            return Err(AbiErrorV1::InvalidBounds("route max journal bytes"));
        }
        let evidence = validate_evidence_v1(&self.evidence_statuses, "route evidence statuses")?;
        if evidence.contains(&"DISABLED_PROVED_NO_WRITER") {
            return Err(AbiErrorV1::InvalidBinding("route disabled evidence"));
        }
        validate_new_object_status_v1(self.status, self.accepts_new_objects, "route status")?;
        if self.status == ReleaseStatusV1::ACTIVE_NEW
            && evidence.as_slice() != REQUIRED_ACTIVE_EVIDENCE_V1
        {
            return Err(AbiErrorV1::InvalidBinding("active route evidence"));
        }
        if self.route_release_id != self.recompute_release_id()? {
            return Err(AbiErrorV1::InvalidBinding(
                "route content-derived release id",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RouteRegistryV1 {
    pub schema: String,
    pub routes: Vec<RouteReleaseV1>,
}

impl RouteRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        let command_kinds: Vec<_> = self
            .routes
            .iter()
            .map(|route| route.command_kind.as_str())
            .collect();
        if command_kinds.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(AbiErrorV1::InvalidOrder("route registry"));
        }
        for route in &self.routes {
            route.validate()?;
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-route-registry-v1", self)
    }

    pub fn route_for_command(
        &self,
        command_kind: &str,
        claimed_route_release_id: Option<&RootV1>,
    ) -> AbiResultV1<&RouteReleaseV1> {
        self.validate()?;
        validate_token_v1(command_kind, "command kind")?;
        let route = self
            .routes
            .iter()
            .find(|route| route.command_kind == command_kind)
            .ok_or(AbiErrorV1::InvalidBinding(
                "unknown or unregistered command kind",
            ))?;
        if route.status != ReleaseStatusV1::ACTIVE_NEW || !route.accepts_new_objects {
            return Err(AbiErrorV1::InvalidBinding(
                "command route disabled for new objects",
            ));
        }
        if claimed_route_release_id.is_some_and(|claimed| claimed != &route.route_release_id) {
            return Err(AbiErrorV1::InvalidBinding(
                "caller-selected route does not match governed route",
            ));
        }
        Ok(route)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicPolicyBindingV1 {
    pub policy_kind: String,
    pub command_kind: String,
    pub policy_root: RootV1,
}

impl EconomicPolicyBindingV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.policy_kind, "economic policy kind")?;
        validate_token_v1(&self.command_kind, "economic policy command kind")?;
        self.policy_root.validate("economic policy root", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicPolicyRegistryV1 {
    pub schema: String,
    pub bindings: Vec<EconomicPolicyBindingV1>,
}

pub const M6_CAPABILITY_POLICY_KIND_V1: &str = "m6_capability_manifest_v1";
pub const M6_CAPABILITY_PROFILE_COMMAND_KIND_V1: &str = "global_economic_profile_v1";
pub const M6_CAPABILITY_MANIFEST_ROOT_V1: &str =
    "0x21efc162df198e40a0aa942fcb69b7a5f5cc0f93907b11a3c6b25359e4a464bb";
pub const M6_ASSET_PRECISION_POLICY_SCHEMA_V1: &str = "zenodex/m6-asset-precision-policy/v1";
pub const M6_ASSET_PRECISION_POLICY_DOMAIN_V1: &str = "m6-asset-precision-policy-v1";
pub const M6_ASSET_PRECISION_POLICY_KIND_V1: &str = "m6_asset_precision_v1";
pub const M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1: &str = "global_economic_profile_v1";
pub const M6_ASSET_PRECISION_POLICY_ROOT_V1: &str =
    "0xacfbd1be88e823fcdd1b094b8d2f0c8ee1bf19c826004e89752f27fd22aa49dd";
pub const M6_ASSET_DECIMAL_PLACES_V1: u8 = 8;
pub const M6_ATOMS_PER_DISPLAY_UNIT_V1: u64 = 100_000_000;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct M6AssetPrecisionPolicyV1 {
    pub schema: String,
    pub decimal_places: u8,
    pub atoms_per_display_unit: u64,
    pub amount_representation: String,
    pub conversion_rule: String,
    pub rounding_rule: String,
    pub rescale_rule: String,
    pub floating_point_allowed: bool,
}

impl M6AssetPrecisionPolicyV1 {
    pub fn exact_v1() -> Self {
        Self {
            schema: M6_ASSET_PRECISION_POLICY_SCHEMA_V1.to_owned(),
            decimal_places: M6_ASSET_DECIMAL_PLACES_V1,
            atoms_per_display_unit: M6_ATOMS_PER_DISPLAY_UNIT_V1,
            amount_representation: "unsigned_integer_atoms".to_owned(),
            conversion_rule: "exact_integer_atoms_only".to_owned(),
            rounding_rule: "command_specific_explicit_integer_rounding".to_owned(),
            rescale_rule: "global_settlement_abi_v2_migration_only".to_owned(),
            floating_point_allowed: false,
        }
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        if self != &Self::exact_v1() {
            return Err(AbiErrorV1::InvalidBinding(
                "M6 asset precision policy semantics",
            ));
        }
        Ok(())
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(M6_ASSET_PRECISION_POLICY_DOMAIN_V1, self)
    }
}

pub fn m6_asset_precision_policy_root_v1() -> AbiResultV1<RootV1> {
    let root = M6AssetPrecisionPolicyV1::exact_v1().policy_root()?;
    if root.as_str() != M6_ASSET_PRECISION_POLICY_ROOT_V1 {
        return Err(AbiErrorV1::InvalidBinding(
            "M6 asset precision policy cross-language root",
        ));
    }
    Ok(root)
}

impl EconomicPolicyRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        if self.bindings.len() > MAX_POLICY_BINDINGS_V1 {
            return Err(AbiErrorV1::InvalidBounds("economic policy registry"));
        }
        let keys: Vec<_> = self
            .bindings
            .iter()
            .map(|binding| (binding.policy_kind.as_str(), binding.command_kind.as_str()))
            .collect();
        if keys.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(AbiErrorV1::InvalidOrder("economic policy registry"));
        }
        for binding in &self.bindings {
            binding.validate()?;
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-economic-policy-registry-v1", self)
    }

    pub fn require_binding(
        &self,
        policy_kind: &str,
        command_kind: &str,
    ) -> AbiResultV1<&EconomicPolicyBindingV1> {
        self.validate()?;
        validate_token_v1(policy_kind, "economic policy kind")?;
        validate_token_v1(command_kind, "economic policy command kind")?;
        let binding = self
            .bindings
            .iter()
            .find(|binding| {
                binding.policy_kind == policy_kind && binding.command_kind == command_kind
            })
            .ok_or(AbiErrorV1::InvalidBinding(
                "economic policy binding absent from registry",
            ))?;
        Ok(binding)
    }
}

pub fn validate_m6_capability_profile_binding_v1(
    profile: &EconomicProfileSnapshotV1,
    policy_registry: &EconomicPolicyRegistryV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    if policy_registry.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "M6 capability policy registry root",
        ));
    }
    let binding = policy_registry.require_binding(
        M6_CAPABILITY_POLICY_KIND_V1,
        M6_CAPABILITY_PROFILE_COMMAND_KIND_V1,
    )?;
    if binding.policy_root.as_str() != M6_CAPABILITY_MANIFEST_ROOT_V1 {
        return Err(AbiErrorV1::InvalidBinding("M6 capability manifest root"));
    }
    Ok(())
}

pub fn validate_m6_asset_precision_profile_binding_v1(
    profile: &EconomicProfileSnapshotV1,
    policy_registry: &EconomicPolicyRegistryV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    if policy_registry.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "M6 asset precision policy registry root",
        ));
    }
    let binding = policy_registry.require_binding(
        M6_ASSET_PRECISION_POLICY_KIND_V1,
        M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1,
    )?;
    if binding.policy_root != m6_asset_precision_policy_root_v1()? {
        return Err(AbiErrorV1::InvalidBinding("M6 asset precision policy root"));
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicProfileSnapshotV1 {
    pub schema: String,
    pub profile_id: RootV1,
    pub authority_epoch: u64,
    pub lane_registry_root: RootV1,
    pub lane_coordinator_registry_root: RootV1,
    pub route_registry_root: RootV1,
    pub proof_shape_root: RootV1,
    pub root_image_id: RootV1,
    pub verifier_registry_root: RootV1,
    pub migration_registry_root: RootV1,
    pub policy_registry_root: RootV1,
    pub terminal_registry_root: RootV1,
    pub status: ProfileStatusV1,
}

#[derive(Serialize)]
struct EconomicProfileContentV1<'a> {
    schema: &'static str,
    authority_epoch: u64,
    lane_registry_root: &'a RootV1,
    lane_coordinator_registry_root: &'a RootV1,
    route_registry_root: &'a RootV1,
    proof_shape_root: &'a RootV1,
    root_image_id: &'a RootV1,
    verifier_registry_root: &'a RootV1,
    migration_registry_root: &'a RootV1,
    policy_registry_root: &'a RootV1,
    terminal_registry_root: &'a RootV1,
}

impl EconomicProfileSnapshotV1 {
    fn content(&self) -> EconomicProfileContentV1<'_> {
        EconomicProfileContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            authority_epoch: self.authority_epoch,
            lane_registry_root: &self.lane_registry_root,
            lane_coordinator_registry_root: &self.lane_coordinator_registry_root,
            route_registry_root: &self.route_registry_root,
            proof_shape_root: &self.proof_shape_root,
            root_image_id: &self.root_image_id,
            verifier_registry_root: &self.verifier_registry_root,
            migration_registry_root: &self.migration_registry_root,
            policy_registry_root: &self.policy_registry_root,
            terminal_registry_root: &self.terminal_registry_root,
        }
    }

    fn recompute_profile_id(&self) -> AbiResultV1<RootV1> {
        hash_global_v1("global-economic-profile-content-v1", &self.content())
    }

    pub fn derived_profile_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        self.recompute_profile_id()
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        for root in [
            &self.profile_id,
            &self.lane_registry_root,
            &self.lane_coordinator_registry_root,
            &self.route_registry_root,
            &self.proof_shape_root,
            &self.root_image_id,
            &self.verifier_registry_root,
            &self.migration_registry_root,
            &self.policy_registry_root,
            &self.terminal_registry_root,
        ] {
            root.validate("profile root", false)?;
        }
        if self.profile_id != self.recompute_profile_id()? {
            return Err(AbiErrorV1::InvalidBinding("profile content-derived id"));
        }
        Ok(())
    }

    pub fn validate_registries(
        &self,
        lanes: &LaneRegistryV1,
        coordinators: &LaneCoordinatorRegistryV1,
        routes: &RouteRegistryV1,
    ) -> AbiResultV1<()> {
        lanes.validate()?;
        coordinators.validate()?;
        routes.validate()?;
        if self.lane_registry_root != lanes.registry_root()?
            || self.lane_coordinator_registry_root != coordinators.registry_root()?
            || self.route_registry_root != routes.registry_root()?
        {
            return Err(AbiErrorV1::InvalidBinding("profile registry roots"));
        }
        validate_profile_route_bindings_v1(lanes, coordinators, routes)?;
        if self.status == ProfileStatusV1::ACTIVE {
            validate_active_profile_evidence_v1(lanes, coordinators, routes)?;
        }
        Ok(())
    }
}

fn validate_profile_route_bindings_v1(
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
) -> AbiResultV1<()> {
    for route in &routes.routes {
        for (lane_id, release_id) in route
            .ordered_lanes
            .iter()
            .zip(route.module_release_ids.iter())
        {
            let release = lanes
                .release_for(*lane_id)
                .ok_or(AbiErrorV1::InvalidBinding("route lane registry"))?;
            let coordinator =
                coordinators
                    .release_for(*lane_id)
                    .ok_or(AbiErrorV1::InvalidBinding(
                        "route lane coordinator registry",
                    ))?;
            if &release.release_id != release_id {
                return Err(AbiErrorV1::InvalidBinding("route module release"));
            }
            if route.status == ReleaseStatusV1::ACTIVE_NEW
                && (release.status != ReleaseStatusV1::ACTIVE_NEW || !release.accepts_new_objects)
            {
                return Err(AbiErrorV1::InvalidBinding("active route lane release"));
            }
            if route.status == ReleaseStatusV1::ACTIVE_NEW
                && (coordinator.status != ReleaseStatusV1::ACTIVE_NEW
                    || !coordinator.accepts_new_objects)
            {
                return Err(AbiErrorV1::InvalidBinding("active route lane coordinator"));
            }
        }
    }
    Ok(())
}

fn validate_active_profile_evidence_v1(
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
) -> AbiResultV1<()> {
    for release in &lanes.releases {
        let active = release.status == ReleaseStatusV1::ACTIVE_NEW && release.accepts_new_objects;
        let disabled = release.evidence_statuses == [EvidenceStatusV1::DISABLED_PROVED_NO_WRITER];
        if !active && !disabled {
            return Err(AbiErrorV1::InvalidBinding("active profile lane evidence"));
        }
    }
    for coordinator in &coordinators.releases {
        let active =
            coordinator.status == ReleaseStatusV1::ACTIVE_NEW && coordinator.accepts_new_objects;
        let disabled =
            coordinator.evidence_statuses == [EvidenceStatusV1::DISABLED_PROVED_NO_WRITER];
        if !active && !disabled {
            return Err(AbiErrorV1::InvalidBinding(
                "active profile lane coordinator evidence",
            ));
        }
    }
    if routes
        .routes
        .iter()
        .any(|route| route.status != ReleaseStatusV1::ACTIVE_NEW || !route.accepts_new_objects)
    {
        return Err(AbiErrorV1::InvalidBinding("active profile route status"));
    }
    Ok(())
}
