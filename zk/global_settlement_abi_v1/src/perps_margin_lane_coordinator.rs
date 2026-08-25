//! Complete accounting projection for one perps-margin module transition.
//!
//! ABI `CUSTODY` rows are accounting locations. This module makes no legal
//! claim about custodianship or key control.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::asset_transfer_types::ACCOUNT_CUSTODY_DOMAIN_V1;
use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::perps_margin_types::{
    PerpsMarginPrivatePortV1, PerpsMarginStateV1, PERPS_MARGIN_CUSTODY_DOMAIN_V1,
};
use crate::proof::{LaneCompositionJournalV1, LaneModuleTransitionJournalV1};
use crate::release::LaneIdV1;
use crate::state::{AssetSupplyV1, EconomicAmountV1, TerminalObligationV1};

pub const PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1: &str = "zenodex/perps-margin-lane-projection/v1";
pub const PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1: &str =
    "zenodex/perps-margin-lane-coordinator/v1";

type AmountKeyV1 = (String, String, String);
type EffectKeyV1 = (EconomicEffectKindV1, String, String, String);

fn amount_key(row: &EconomicAmountV1) -> AmountKeyV1 {
    (
        row.asset.clone(),
        row.owner.clone(),
        row.custody_domain.clone(),
    )
}

fn validate_amounts(
    rows: &[EconomicAmountV1],
    field: &'static str,
    domain_mode: Option<bool>,
) -> AbiResultV1<()> {
    let mut previous: Option<AmountKeyV1> = None;
    for row in rows {
        validate_token_v1(&row.owner, field)?;
        validate_token_v1(&row.asset, field)?;
        validate_token_v1(&row.custody_domain, field)?;
        let invalid_domain = match domain_mode {
            Some(true) => row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1,
            Some(false) => row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V1,
            None => false,
        };
        if row.amount_atoms == 0 || invalid_domain {
            return Err(AbiErrorV1::InvalidBinding(field));
        }
        let key = amount_key(row);
        if previous.as_ref().is_some_and(|prior| prior >= &key) {
            return Err(AbiErrorV1::InvalidOrder(field));
        }
        previous = Some(key);
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginModuleCompatibilityV1 {
    pub module_release_id: RootV1,
    pub module_schema: String,
}

impl PerpsMarginModuleCompatibilityV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.module_release_id
            .validate("perps compatible module release", false)?;
        validate_token_v1(&self.module_schema, "perps compatible module schema")
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneProjectionV1 {
    pub schema: String,
    pub lane_state: PerpsMarginStateV1,
    pub balances: Vec<EconomicAmountV1>,
    pub accounting_locations: Vec<EconomicAmountV1>,
    pub liabilities: Vec<EconomicAmountV1>,
    pub supplies: Vec<AssetSupplyV1>,
    pub terminal_obligations: Vec<TerminalObligationV1>,
}

impl PerpsMarginLaneProjectionV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.lane_state.validate()?;
        validate_amounts(&self.balances, "perps lane balances", Some(true))?;
        validate_amounts(
            &self.accounting_locations,
            "perps accounting locations",
            Some(false),
        )?;
        validate_amounts(&self.liabilities, "perps liabilities", None)?;
        self.require_complete_holdings()?;
        self.require_perps_accounting_locations()?;
        self.require_perps_liabilities()?;
        if self.terminal_obligations != self.lane_state.terminal_obligations()? {
            return Err(AbiErrorV1::InvalidBinding(
                "perps lane terminal obligations",
            ));
        }
        Ok(())
    }

    fn require_complete_holdings(&self) -> AbiResultV1<()> {
        let mut totals = BTreeMap::<String, u128>::new();
        let mut previous: Option<&str> = None;
        for supply in &self.supplies {
            validate_token_v1(&supply.asset, "perps lane supply asset")?;
            if previous.is_some_and(|prior| prior >= supply.asset.as_str()) {
                return Err(AbiErrorV1::InvalidOrder("perps lane supplies"));
            }
            previous = Some(&supply.asset);
            totals.insert(supply.asset.clone(), 0);
        }
        for row in self.balances.iter().chain(&self.accounting_locations) {
            let total = totals
                .get(&row.asset)
                .copied()
                .ok_or(AbiErrorV1::InvalidBinding(
                    "perps holding references unnamed supply",
                ))?
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV1::Conservation("perps holding total overflow"))?;
            totals.insert(row.asset.clone(), total);
        }
        if self
            .supplies
            .iter()
            .any(|row| totals.get(&row.asset).copied().unwrap_or(0) != row.amount_atoms)
        {
            return Err(AbiErrorV1::Conservation(
                "perps complete holdings equal supply",
            ));
        }
        Ok(())
    }

    fn require_perps_accounting_locations(&self) -> AbiResultV1<()> {
        let expected = self
            .lane_state
            .accounts
            .iter()
            .filter(|account| account.collateral_atoms != 0)
            .map(|account| {
                (
                    (
                        self.lane_state.collateral_asset.clone(),
                        account.account_id.clone(),
                        PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                    ),
                    account.collateral_atoms,
                )
            })
            .collect::<BTreeMap<_, _>>();
        let actual = self
            .accounting_locations
            .iter()
            .filter(|row| row.custody_domain == PERPS_MARGIN_CUSTODY_DOMAIN_V1)
            .map(|row| (amount_key(row), row.amount_atoms))
            .collect::<BTreeMap<_, _>>();
        if actual != expected {
            return Err(AbiErrorV1::InvalidBinding(
                "perps accounting locations differ from accounts",
            ));
        }
        Ok(())
    }

    fn require_perps_liabilities(&self) -> AbiResultV1<()> {
        let mut expected = BTreeMap::<AmountKeyV1, u128>::new();
        for account in &self.lane_state.accounts {
            if account.collateral_atoms == 0 {
                continue;
            }
            let key = (
                self.lane_state.collateral_asset.clone(),
                account.owner.clone(),
                PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            );
            let amount = expected
                .get(&key)
                .copied()
                .unwrap_or(0)
                .checked_add(account.collateral_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "perps claimant liability overflow",
                ))?;
            expected.insert(key, amount);
        }
        let actual = self
            .liabilities
            .iter()
            .filter(|row| row.custody_domain == PERPS_MARGIN_CUSTODY_DOMAIN_V1)
            .map(|row| (amount_key(row), row.amount_atoms))
            .collect::<BTreeMap<_, _>>();
        if actual != expected {
            return Err(AbiErrorV1::InvalidBinding(
                "perps liabilities differ from claimant entitlements",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("perps-margin-lane-projection-v1", self)
    }

    pub fn owned_and_custodied_atoms(&self, asset: &str) -> AbiResultV1<u128> {
        self.balances
            .iter()
            .chain(&self.accounting_locations)
            .filter(|row| row.asset == asset)
            .try_fold(0_u128, |total, row| {
                total
                    .checked_add(row.amount_atoms)
                    .ok_or(AbiErrorV1::Conservation("perps owned total overflow"))
            })
    }

    pub fn supply_atoms(&self, asset: &str) -> AbiResultV1<u128> {
        self.supplies
            .iter()
            .find(|row| row.asset == asset)
            .map(|row| row.amount_atoms)
            .ok_or(AbiErrorV1::InvalidBinding("perps unknown supply"))
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneCoordinatorContextV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub coordinator_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub compatible_modules: Vec<PerpsMarginModuleCompatibilityV1>,
}

impl PerpsMarginLaneCoordinatorContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.chain_id, "perps coordinator chain")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.coordinator_release_id,
            &self.command_occurrence_id,
        ] {
            root.validate("perps coordinator required root", false)?;
        }
        if self.compatible_modules.is_empty() {
            return Err(AbiErrorV1::InvalidBounds("perps compatible modules"));
        }
        for module in &self.compatible_modules {
            module.validate()?;
        }
        if self
            .compatible_modules
            .windows(2)
            .any(|pair| pair[0].module_release_id >= pair[1].module_release_id)
        {
            return Err(AbiErrorV1::InvalidOrder("perps compatible modules"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum PerpsMarginLaneCoordinatorRejectCodeV1 {
    CONTEXT_MISMATCH,
    MODULE_NOT_REGISTERED,
    MODULE_BINDING_MISMATCH,
    EFFECT_SHAPE_MISMATCH,
    PROJECTION_BINDING_MISMATCH,
    STATE_EFFECT_MISMATCH,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneCompositionCandidateV1 {
    pub context: PerpsMarginLaneCoordinatorContextV1,
    pub module_journal: LaneModuleTransitionJournalV1,
    pub private_port: PerpsMarginPrivatePortV1,
    pub pre_state: PerpsMarginLaneProjectionV1,
    pub post_state: PerpsMarginLaneProjectionV1,
    pub module_effects: GlobalEconomicEffectPlanV1,
}

impl PerpsMarginLaneCompositionCandidateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.context.validate()?;
        self.module_journal.validate()?;
        self.private_port.validate()?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.module_effects.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneCompositionAcceptedV1 {
    pub post_state: PerpsMarginLaneProjectionV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub lane_journal: LaneCompositionJournalV1,
}

impl PerpsMarginLaneCompositionAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.lane_journal.validate()?;
        if self.lane_journal.post_lane_root != self.post_state.state_root()?
            || self.lane_journal.effect_plan_root != self.effects.effect_plan_root()?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "perps accepted lane composition",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneCompositionRejectedV1 {
    pub code: PerpsMarginLaneCoordinatorRejectCodeV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

impl PerpsMarginLaneCompositionRejectedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "perps coordinator rejection exact no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PerpsMarginLaneCompositionResultV1 {
    Accepted(Box<PerpsMarginLaneCompositionAcceptedV1>),
    Rejected(Box<PerpsMarginLaneCompositionRejectedV1>),
}

fn empty_effects() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn reject(
    code: PerpsMarginLaneCoordinatorRejectCodeV1,
    pre_state: &PerpsMarginLaneProjectionV1,
) -> AbiResultV1<PerpsMarginLaneCompositionResultV1> {
    let root = pre_state.state_root()?;
    let rejected = PerpsMarginLaneCompositionRejectedV1 {
        code,
        pre_state_root: root.clone(),
        post_state_root: root,
        effects: empty_effects(),
    };
    rejected.validate()?;
    Ok(PerpsMarginLaneCompositionResultV1::Rejected(Box::new(
        rejected,
    )))
}

fn context_ok(
    context: &PerpsMarginLaneCoordinatorContextV1,
    journal: &LaneModuleTransitionJournalV1,
) -> bool {
    journal.chain_id == context.chain_id
        && journal.deployment_root == context.deployment_root
        && journal.profile_root == context.profile_root
        && journal.writer_epoch == context.writer_epoch
        && journal.lane_id == LaneIdV1::PERPS_MARKET
        && journal.command_occurrence_id == context.command_occurrence_id
}

fn module_ok(
    context: &PerpsMarginLaneCoordinatorContextV1,
    journal: &LaneModuleTransitionJournalV1,
    port: &PerpsMarginPrivatePortV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<bool> {
    let Some(compatibility) = context
        .compatible_modules
        .iter()
        .find(|row| row.module_release_id == journal.module_release_id)
    else {
        return Ok(false);
    };
    Ok(compatibility.module_schema == port.producer_module_schema
        && port.module_release_id == journal.module_release_id
        && port.command_occurrence_id == context.command_occurrence_id
        && journal.private_port_root == port.port_root()?
        && journal.effect_plan_root == effects.effect_plan_root()?
        && port.module_effect_plan_root == effects.effect_plan_root()?
        && journal.terminal_obligations_root == port.terminal_obligations_root)
}

fn effect_shape_ok(
    context: &PerpsMarginLaneCoordinatorContextV1,
    journal: &LaneModuleTransitionJournalV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> bool {
    effects.asset_conservation.is_empty()
        && effects.fee_conservation.is_empty()
        && effects.external_outbox_enqueue.is_empty()
        && effects.occurrence_consumptions == vec![context.command_occurrence_id.clone()]
        && effects.lane_writes
            == vec![LaneWriteV1 {
                lane_id: LaneIdV1::PERPS_MARKET,
                pre_root: journal.pre_lane_root.clone(),
                post_root: journal.post_lane_root.clone(),
            }]
        && effects.rows.iter().all(|row| {
            matches!(
                row.kind,
                EconomicEffectKindV1::ACCOUNT_MOVEMENT
                    | EconomicEffectKindV1::CUSTODY
                    | EconomicEffectKindV1::LIABILITY
            )
        })
}

fn projection_ok(
    journal: &LaneModuleTransitionJournalV1,
    port: &PerpsMarginPrivatePortV1,
    pre_state: &PerpsMarginLaneProjectionV1,
    post_state: &PerpsMarginLaneProjectionV1,
) -> AbiResultV1<bool> {
    Ok(journal.pre_lane_root == pre_state.lane_state.state_root()?
        && journal.post_lane_root == post_state.lane_state.state_root()?
        && port.market_id == pre_state.lane_state.market_id
        && port.market_id == post_state.lane_state.market_id
        && port.terminal_obligations_root == post_state.lane_state.terminal_obligations_root()?)
}

fn projected_rows(state: &PerpsMarginLaneProjectionV1) -> BTreeMap<EffectKeyV1, u128> {
    [
        (EconomicEffectKindV1::ACCOUNT_MOVEMENT, &state.balances),
        (EconomicEffectKindV1::CUSTODY, &state.accounting_locations),
        (EconomicEffectKindV1::LIABILITY, &state.liabilities),
    ]
    .into_iter()
    .flat_map(|(kind, rows)| {
        rows.iter().map(move |row| {
            (
                (
                    kind,
                    row.asset.clone(),
                    row.owner.clone(),
                    row.custody_domain.clone(),
                ),
                row.amount_atoms,
            )
        })
    })
    .collect()
}

fn expected_deltas(
    pre_state: &PerpsMarginLaneProjectionV1,
    post_state: &PerpsMarginLaneProjectionV1,
) -> AbiResultV1<BTreeMap<EffectKeyV1, i128>> {
    let pre = projected_rows(pre_state);
    let post = projected_rows(post_state);
    let mut deltas = BTreeMap::new();
    for key in pre.keys().chain(post.keys()) {
        let pre_atoms = *pre.get(key).unwrap_or(&0);
        let post_atoms = *post.get(key).unwrap_or(&0);
        if pre_atoms == post_atoms {
            continue;
        }
        let delta = signed_projection_delta_v1(pre_atoms, post_atoms)?;
        deltas.insert(key.clone(), delta);
    }
    Ok(deltas)
}

fn signed_projection_delta_v1(pre_atoms: u128, post_atoms: u128) -> AbiResultV1<i128> {
    if post_atoms >= pre_atoms {
        return i128::try_from(post_atoms - pre_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("perps projection delta"));
    }

    let magnitude = pre_atoms - post_atoms;
    if magnitude == i128::MIN.unsigned_abs() {
        return Ok(i128::MIN);
    }
    let magnitude = i128::try_from(magnitude)
        .map_err(|_| AbiErrorV1::InvalidBounds("perps projection delta"))?;
    magnitude
        .checked_neg()
        .ok_or(AbiErrorV1::InvalidBounds("perps projection delta"))
}

fn effect_deltas(effects: &GlobalEconomicEffectPlanV1) -> BTreeMap<EffectKeyV1, i128> {
    effects
        .rows
        .iter()
        .map(|row| {
            (
                (
                    row.kind,
                    row.asset.clone(),
                    row.principal.clone(),
                    row.custody_domain.clone(),
                ),
                row.delta_atoms,
            )
        })
        .collect()
}

fn normalized_effects(
    context: &PerpsMarginLaneCoordinatorContextV1,
    pre_state: &PerpsMarginLaneProjectionV1,
    post_state: &PerpsMarginLaneProjectionV1,
    module_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let pre_rows = projected_rows(pre_state);
    let post_rows = projected_rows(post_state);
    let changed_assets = pre_rows
        .keys()
        .chain(post_rows.keys())
        .filter(|key| pre_rows.get(*key).unwrap_or(&0) != post_rows.get(*key).unwrap_or(&0))
        .map(|key| key.1.clone())
        .collect::<BTreeSet<_>>();
    let conservation = changed_assets
        .into_iter()
        .map(|asset| {
            Ok(AssetConservationRowV1 {
                owned_and_custodied_pre_atoms: pre_state.owned_and_custodied_atoms(&asset)?,
                owned_and_custodied_post_atoms: post_state.owned_and_custodied_atoms(&asset)?,
                supply_pre_atoms: pre_state.supply_atoms(&asset)?,
                supply_post_atoms: post_state.supply_atoms(&asset)?,
                asset,
                authorized_issue_atoms: 0,
                authorized_burn_atoms: 0,
            })
        })
        .collect::<AbiResultV1<Vec<_>>>()?;
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: module_effects.rows.clone(),
        asset_conservation: conservation,
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::PERPS_MARKET,
            pre_root: pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: vec![context.command_occurrence_id.clone()],
        external_outbox_enqueue: vec![],
    };
    effects.validate()?;
    Ok(effects)
}

fn coordinator_rejection_code_v1(
    candidate: &PerpsMarginLaneCompositionCandidateV1,
) -> AbiResultV1<Option<PerpsMarginLaneCoordinatorRejectCodeV1>> {
    let context = &candidate.context;
    let journal = &candidate.module_journal;
    if !context_ok(context, journal) {
        return Ok(Some(
            PerpsMarginLaneCoordinatorRejectCodeV1::CONTEXT_MISMATCH,
        ));
    }
    if !context
        .compatible_modules
        .iter()
        .any(|row| row.module_release_id == journal.module_release_id)
    {
        return Ok(Some(
            PerpsMarginLaneCoordinatorRejectCodeV1::MODULE_NOT_REGISTERED,
        ));
    }
    if !module_ok(
        context,
        journal,
        &candidate.private_port,
        &candidate.module_effects,
    )? {
        return Ok(Some(
            PerpsMarginLaneCoordinatorRejectCodeV1::MODULE_BINDING_MISMATCH,
        ));
    }
    if !effect_shape_ok(context, journal, &candidate.module_effects) {
        return Ok(Some(
            PerpsMarginLaneCoordinatorRejectCodeV1::EFFECT_SHAPE_MISMATCH,
        ));
    }
    if !projection_ok(
        journal,
        &candidate.private_port,
        &candidate.pre_state,
        &candidate.post_state,
    )? {
        return Ok(Some(
            PerpsMarginLaneCoordinatorRejectCodeV1::PROJECTION_BINDING_MISMATCH,
        ));
    }
    if expected_deltas(&candidate.pre_state, &candidate.post_state)?
        != effect_deltas(&candidate.module_effects)
    {
        return Ok(Some(
            PerpsMarginLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH,
        ));
    }
    Ok(None)
}

#[must_use = "composition rejection carries exact no-effect evidence"]
pub fn compose_perps_margin_lane_single_v1(
    candidate: &PerpsMarginLaneCompositionCandidateV1,
) -> AbiResultV1<PerpsMarginLaneCompositionResultV1> {
    candidate.validate()?;
    if let Some(code) = coordinator_rejection_code_v1(candidate)? {
        return reject(code, &candidate.pre_state);
    }
    let context = &candidate.context;
    let effects = normalized_effects(
        context,
        &candidate.pre_state,
        &candidate.post_state,
        &candidate.module_effects,
    )?;
    let lane_journal = LaneCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: context.chain_id.clone(),
        deployment_root: context.deployment_root.clone(),
        profile_root: context.profile_root.clone(),
        writer_epoch: context.writer_epoch,
        lane_id: LaneIdV1::PERPS_MARKET,
        coordinator_release_id: context.coordinator_release_id.clone(),
        command_occurrence_id: context.command_occurrence_id.clone(),
        ordered_module_journal_roots: vec![candidate.module_journal.journal_root()?],
        pre_lane_root: candidate.pre_state.state_root()?,
        post_lane_root: candidate.post_state.state_root()?,
        effect_plan_root: effects.effect_plan_root()?,
        terminal_obligations_root: candidate
            .post_state
            .lane_state
            .terminal_obligations_root()?,
    };
    let accepted = PerpsMarginLaneCompositionAcceptedV1 {
        post_state: candidate.post_state.clone(),
        effects,
        lane_journal,
    };
    accepted.validate()?;
    Ok(PerpsMarginLaneCompositionResultV1::Accepted(Box::new(
        accepted,
    )))
}
