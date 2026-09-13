//! V2 account-to-terminal-claim projection and lifecycle.

use std::collections::{BTreeMap, BTreeSet};

use zenodex_global_settlement_abi_v1::{PerpsMarginStateV1, PERPS_MARGIN_CUSTODY_DOMAIN_V1};
use zenodex_global_settlement_abi_v2::{
    AbiErrorV2, AbiResultV2, EconomicAmountV2, GlobalEconomicStateV2, LaneIdV2, RootV2,
    TerminalObligationDeltaV2, TerminalObligationStatusV2, TerminalObligationV2,
};

use crate::state::{margin_claim_id_v2, PerpsMarginClaimBindingV2, PerpsMarginStateV2};

fn amount_map(rows: &[EconomicAmountV2], domain: &str) -> BTreeMap<(String, String, String), u128> {
    rows.iter()
        .filter(|row| row.custody_domain == domain)
        .map(|row| {
            (
                (
                    row.asset.clone(),
                    row.owner.clone(),
                    row.custody_domain.clone(),
                ),
                row.amount_atoms,
            )
        })
        .collect()
}

/// Require the complete perps lane projection, including claimant identity.
pub fn require_margin_claim_projection_v2(
    margin: &PerpsMarginStateV2,
    state: &GlobalEconomicStateV2,
) -> AbiResultV2<()> {
    margin.validate()?;
    state.validate()?;
    let economic = &margin.economic_state;
    let lane = state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == LaneIdV2::PERPS_MARKET)
        .ok_or(AbiErrorV2::InvalidBinding(
            "margin lane/global root missing",
        ))?;
    let margin_root = margin.state_root()?;
    if lane.state_root != margin_root
        || lane.module_release_id.as_str() != economic.module_release_id.as_str()
        || !lane.enabled
    {
        return Err(AbiErrorV2::InvalidBinding(
            "margin lane/global root mismatch",
        ));
    }

    let expected_custody = economic
        .accounts
        .iter()
        .filter(|account| account.collateral_atoms > 0)
        .map(|account| {
            (
                (
                    economic.collateral_asset.clone(),
                    account.account_id.clone(),
                    PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                ),
                account.collateral_atoms,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let actual_custody = amount_map(&state.custody, PERPS_MARGIN_CUSTODY_DOMAIN_V1);
    if expected_custody != actual_custody {
        return Err(AbiErrorV2::InvalidBinding(
            "margin account custody projection mismatch",
        ));
    }

    let mut expected_liabilities = BTreeMap::<(String, String, String), u128>::new();
    for account in economic
        .accounts
        .iter()
        .filter(|account| account.collateral_atoms > 0)
    {
        let key = (
            economic.collateral_asset.clone(),
            account.owner.clone(),
            PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
        );
        let total = expected_liabilities
            .get(&key)
            .copied()
            .unwrap_or(0)
            .checked_add(account.collateral_atoms)
            .ok_or(AbiErrorV2::InvalidBounds(
                "margin claimant liability overflow",
            ))?;
        expected_liabilities.insert(key, total);
    }
    let actual_liabilities = amount_map(&state.liabilities, PERPS_MARGIN_CUSTODY_DOMAIN_V1);
    if expected_liabilities != actual_liabilities {
        return Err(AbiErrorV2::InvalidBinding(
            "margin claimant liability projection mismatch",
        ));
    }

    let open_claims = state
        .terminal_obligations
        .iter()
        .filter(|row| {
            row.lane_id == LaneIdV2::PERPS_MARKET && row.status == TerminalObligationStatusV2::OPEN
        })
        .map(|row| (row.obligation_id.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let binding_ids = margin
        .active_claims
        .iter()
        .map(|binding| binding.obligation_id.as_str())
        .collect::<BTreeSet<_>>();
    if open_claims.keys().copied().collect::<BTreeSet<_>>() != binding_ids {
        return Err(AbiErrorV2::InvalidBinding(
            "margin open claim coverage mismatch",
        ));
    }

    let accounts = economic
        .accounts
        .iter()
        .map(|account| (account.account_id.as_str(), account))
        .collect::<BTreeMap<_, _>>();
    for binding in &margin.active_claims {
        let account = accounts
            .get(binding.account_id.as_str())
            .ok_or(AbiErrorV2::InvalidBinding("margin claim account missing"))?;
        let claim =
            open_claims
                .get(binding.obligation_id.as_str())
                .ok_or(AbiErrorV2::InvalidBinding(
                    "margin claim obligation missing",
                ))?;
        if claim.claimant != account.owner
            || claim.asset != economic.collateral_asset
            || claim.liability_domain != PERPS_MARGIN_CUSTODY_DOMAIN_V1
            || claim.amount_atoms != account.collateral_atoms
        {
            return Err(AbiErrorV2::InvalidBinding(
                "margin active claim attribution mismatch",
            ));
        }
    }
    Ok(())
}

/// Advance one account's occurrence-bound claim without reopening terminal rows.
///
/// The caller must establish the complete pre-state projection and obtain
/// `post_economic` from the owner-preserving economic transition. This helper
/// derives candidate rows; it does not authorize their publication.
pub fn advance_margin_claims_v2(
    margin: &PerpsMarginStateV2,
    post_economic: PerpsMarginStateV1,
    obligations: &[TerminalObligationV2],
    account_id: &str,
    occurrence_id: &RootV2,
) -> AbiResultV2<(PerpsMarginStateV2, Vec<TerminalObligationV2>)> {
    let account = post_economic
        .account(account_id)
        .ok_or(AbiErrorV2::InvalidBinding(
            "margin successor selected account",
        ))?;
    let mut rows = obligations
        .iter()
        .cloned()
        .map(|row| (row.obligation_id.clone(), row))
        .collect::<BTreeMap<_, _>>();
    let mut bindings = margin
        .active_claims
        .iter()
        .cloned()
        .map(|binding| (binding.account_id.clone(), binding))
        .collect::<BTreeMap<_, _>>();

    if let Some(previous) = bindings.get(account_id).cloned() {
        let old = rows
            .get_mut(&previous.obligation_id)
            .ok_or(AbiErrorV2::InvalidBinding("margin previous claim missing"))?;
        if old.status != TerminalObligationStatusV2::OPEN {
            return Err(AbiErrorV2::InvalidBinding(
                "margin previous claim is terminal",
            ));
        }
        if account.collateral_atoms > 0 {
            old.amount_atoms = account.collateral_atoms;
        } else {
            old.status = TerminalObligationStatusV2::DRAINED;
            bindings.remove(account_id);
        }
    } else if account.collateral_atoms > 0 {
        let claim_id = margin_claim_id_v2(&margin.economic_state, account_id, occurrence_id)?;
        if rows.contains_key(claim_id.as_str()) {
            return Err(AbiErrorV2::InvalidBinding(
                "margin opening claim id collision",
            ));
        }
        rows.insert(
            claim_id.to_string(),
            TerminalObligationV2 {
                obligation_id: claim_id.to_string(),
                lane_id: LaneIdV2::PERPS_MARKET,
                claimant: account.owner.clone(),
                asset: post_economic.collateral_asset.clone(),
                liability_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: account.collateral_atoms,
                status: TerminalObligationStatusV2::OPEN,
            },
        );
        bindings.insert(
            account_id.to_owned(),
            PerpsMarginClaimBindingV2::new(account_id, claim_id.to_string())?,
        );
    }

    let active = bindings.into_values().collect::<Vec<_>>();
    let next_margin = PerpsMarginStateV2::new(post_economic, active)?;
    let next_obligations = rows.into_values().collect::<Vec<_>>();
    for row in &next_obligations {
        row.validate()?;
    }
    Ok((next_margin, next_obligations))
}

/// Build the exact terminal delta relation consumed by the shared V2 checker.
///
/// Inputs must be validated, canonically ordered tables with unique IDs. The
/// shared refinement checker still owns terminal lifecycle admission.
pub fn derive_terminal_plan_v2(
    pre: &[TerminalObligationV2],
    post: &[TerminalObligationV2],
) -> AbiResultV2<Vec<TerminalObligationDeltaV2>> {
    let before = pre
        .iter()
        .map(|row| (row.obligation_id.clone(), row.clone()))
        .collect::<BTreeMap<_, _>>();
    let after = post
        .iter()
        .map(|row| (row.obligation_id.clone(), row.clone()))
        .collect::<BTreeMap<_, _>>();
    let ids = before
        .keys()
        .chain(after.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut deltas = Vec::new();
    for id in ids {
        if before.get(&id) != after.get(&id) {
            let next = after
                .get(&id)
                .cloned()
                .ok_or(AbiErrorV2::InvalidBinding("terminal obligation deletion"))?;
            deltas.push(TerminalObligationDeltaV2 {
                obligation_id: id,
                pre_obligation: before.get(&next.obligation_id).cloned(),
                post_obligation: next,
            });
        }
    }
    Ok(deltas)
}
