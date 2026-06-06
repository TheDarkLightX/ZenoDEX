#!/usr/bin/env python3
"""P0-3 perps-NP guest <-> live-Python-authority differential.

THE STANDARD (owner + advisor): a *valid* RISC0 guest execution of the N-party
perps transition must be OBSERVATIONALLY EQUIVALENT to the live Python authority
(`src/core/perp_np_clearinghouse`). Concretely, for every corpus case:

  (A) TRANSITION equivalence  -- the guest's structured ``post_snapshot`` matches
      the authority's post-state field-by-field (first differing field reported);
  (B) ENCODER equivalence     -- SEPARATELY, the guest's journal ``post_app_hash``
      equals ``_current_snapshot_hash(guest_post_snapshot)`` (the Python encoder
      applied to the guest's own snapshot). Folding (A) and (B) together would let
      a shared encoding bug pass silently, so they are distinct assertions;
  (C) ACCEPT/REJECT agreement -- a guest reject and an authority reject must occur
      together, for the same semantic reason CLASS.

This is refutation-complete corpus CORROBORATION (Popper), NOT an equivalence
proof; the structural fix is the one-shared-kernel convergence.

The guest is host-executed WITHOUT proving via the CLI ``tau_state_transition_execute``
schema (``execute_perps_np_transition_v1_unchecked_with_snapshot``). ``collateral_binding``
(deposits) and ``oracle`` (run_epoch) are guest WITNESS / input-envelope data: the
authority transition does not consume them, and changing a *valid* binding must not
change the post-state (proven by a dedicated test).

Operation correspondence (verified 1:1 before building this; see the P0-3 finding):
  guest DepositCollateral   <-> perp_np_clearinghouse.deposit(state, pubkey, amount_e8)
  guest WithdrawCollateral  <-> perp_np_clearinghouse.withdraw(state, pubkey, amount_e8)
  guest RunEpoch            <-> perp_np_clearinghouse.run_epoch(state, clearing, funding, intents)
  guest InitMarket          <-> perp_np_clearinghouse.init_market(index_price, params, seed)
  (zUSD's atomic DepositMint does NOT map 1:1 to the authority -> deferred.)
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.perp_np_clearinghouse import (  # noqa: E402
    Account,
    MarketParams,
    MarketState,
    deposit,
    init_market,
    run_epoch,
    withdraw,
)
from src.core.perp_np_matching import Intent  # noqa: E402

# The guest-compatible canonical snapshot hash (Python mirror of the guest's
# canonical_app_hash_sha256). Imported from the real-proof smoke (its __main__
# guard makes import side-effect-free).
from tools.zeno_ledger_perp_np_risc0_real_proof_smoke import (  # noqa: E402
    _current_snapshot_hash as guest_compatible_snapshot_hash,
)

ZUSD_PROOF_TYPE = "risc0.zenodex_zusd_transition.v1"
PERPS_NP_PROOF_TYPE = "risc0.zenodex_perps_np_transition.v1"
_CLI_PKG = "tau-state-proof-risc0-cli"
_CLI_DIR = _REPO / "zk" / "state_proof_risc0"
_CLI_BIN = _CLI_DIR / "target" / "debug" / "tau-state-proof-risc0-cli"


class DifferentialError(RuntimeError):
    """Raised when the harness cannot run, or the guest diverges from the authority."""


# --------------------------------------------------------------------------- #
# Trusted-path adapter: authority MarketState/Account/MarketParams -> the guest
# snapshot dict shape (PerpsNpSnapshotV1). These are field-1:1; the dedicated
# adapter teeth test deliberately breaks one mapping and requires a divergence.
# --------------------------------------------------------------------------- #
def account_to_dict(a: Account) -> dict[str, Any]:
    return {
        "pubkey": a.pubkey,
        "position_base": a.position_base,
        "entry_price_e8": a.entry_price_e8,
        "collateral_e8": a.collateral_e8,
        "funding_paid_cum_e8": a.funding_paid_cum_e8,
        "nonce": a.nonce,
    }


def params_to_dict(p: MarketParams) -> dict[str, Any]:
    return {
        "initial_margin_bps": p.initial_margin_bps,
        "maintenance_margin_bps": p.maintenance_margin_bps,
        "depeg_buffer_bps": p.depeg_buffer_bps,
        "liquidation_penalty_bps": p.liquidation_penalty_bps,
        "max_oracle_move_bps": p.max_oracle_move_bps,
        "funding_cap_bps": p.funding_cap_bps,
        "max_position_abs": p.max_position_abs,
        "min_notional_for_bounty_e8": p.min_notional_for_bounty_e8,
    }


def state_to_snapshot(
    state: MarketState, *, market_id: str, collateral_asset: str = "zUSD"
) -> dict[str, Any]:
    """Authority MarketState -> guest PerpsNpSnapshotV1 dict (the comparison form)."""
    return {
        "version": 1,
        "market_id": market_id,
        "collateral_asset": collateral_asset,
        "index_price_e8": state.index_price_e8,
        "params": params_to_dict(state.params),
        "accounts": sorted(
            (account_to_dict(a) for a in state.accounts), key=lambda a: a["pubkey"]
        ),
        "pending_intents": [],  # the harness never leaves intents pending (run_epoch consumes them)
        "now_epoch": state.now_epoch,
        "fee_pool_e8": state.fee_pool_e8,
        "insurance_e8": state.insurance_e8,
        "insurance_ext_e8": state.insurance_ext_e8,
        "claims_paid_e8": state.claims_paid_e8,
        "net_deposited_e8": state.net_deposited_e8,
    }


def _params_from_dict(d: Mapping[str, Any]) -> MarketParams:
    return MarketParams(
        initial_margin_bps=int(d["initial_margin_bps"]),
        maintenance_margin_bps=int(d["maintenance_margin_bps"]),
        depeg_buffer_bps=int(d["depeg_buffer_bps"]),
        liquidation_penalty_bps=int(d["liquidation_penalty_bps"]),
        max_oracle_move_bps=int(d["max_oracle_move_bps"]),
        funding_cap_bps=int(d["funding_cap_bps"]),
        max_position_abs=int(d["max_position_abs"]),
        min_notional_for_bounty_e8=int(d["min_notional_for_bounty_e8"]),
    )


def _account_nonce(state: MarketState, pubkey: str) -> int:
    account = state.by_pubkey().get(pubkey)
    return int(account.nonce) if account is not None else 0


def _with_account_nonce(state: MarketState, pubkey: str, nonce: int) -> MarketState:
    accts = state.by_pubkey()
    account = accts.get(pubkey)
    if account is None:
        raise DifferentialError(f"cannot set nonce for missing account {pubkey!r}")
    accts[pubkey] = replace(account, nonce=nonce)
    return state.with_accounts(accts)


# --------------------------------------------------------------------------- #
# Reject reason classes (semantic, cross-language). The guest reject string and
# the authority exception/error are both mapped to one of these so (C) compares a
# CLASS, not a brittle exact string.
# --------------------------------------------------------------------------- #
REJ_INSUFFICIENT = "insufficient_collateral_or_balance"
REJ_INVARIANT = "invariant_or_domain_violation"
REJ_NEGATIVE = "negative_amount"
REJ_NONCE = "nonce_or_replay"
REJ_OTHER = "other"


def _classify_reject(text: str) -> str:
    t = text.lower()
    if "nonce" in t:
        return REJ_NONCE
    if "insufficient" in t or "exceed" in t or "negative collateral" in t or "underflow" in t:
        return REJ_INSUFFICIENT
    if "must be non-negative" in t or "must be positive" in t or "negative" in t:
        return REJ_NEGATIVE
    if "invariant" in t or "margin" in t or "insolven" in t or "domain" in t:
        return REJ_INVARIANT
    return REJ_OTHER


# --------------------------------------------------------------------------- #
# Guest side: host-execute (no proving) via the CLI execute schema.
# --------------------------------------------------------------------------- #
def _ensure_cli(build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_PERPS_NP_CLI_BIN")
    if env_bin and Path(env_bin).is_file():
        return Path(env_bin)
    if not build:
        if _CLI_BIN.is_file():
            return _CLI_BIN
        raise DifferentialError(f"CLI binary not found at {_CLI_BIN} (set ZENODEX_PERPS_NP_CLI_BIN or build)")
    # REVIEW [B -> A-]: reusing a stale debug binary made the differential a
    # test of yesterday's guest, not the current checkout. Build the local CLI by
    # default; callers that intentionally pin an external binary can set
    # ZENODEX_PERPS_NP_CLI_BIN.
    proc = subprocess.run(
        ["cargo", "build", "-p", _CLI_PKG],
        cwd=_CLI_DIR,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0 or not _CLI_BIN.is_file():
        raise DifferentialError(f"cargo build of {_CLI_PKG} failed: {proc.stderr[-2000:]}")
    return _CLI_BIN


def run_guest(
    actions: Sequence[Mapping[str, Any]],
    *,
    pre_snapshot: Optional[Mapping[str, Any]] = None,
    chain_id: str = "zenodex-perps-np-differential",
    binp: Optional[Path] = None,
) -> dict[str, Any]:
    """Host-execute the guest transition. Returns the parsed result dict
    ({accepted, post_snapshot, meta} or {accepted:False, reject})."""
    binp = binp or _ensure_cli()
    context: dict[str, Any] = {"chain_id": chain_id}
    if pre_snapshot is not None:
        context["perps_state_pre"] = pre_snapshot
        context["app_hash_pre"] = guest_compatible_snapshot_hash(pre_snapshot)
    req = {
        "schema": "tau_state_transition_execute",
        "schema_version": 1,
        "proof_type": PERPS_NP_PROOF_TYPE,
        "state_hash": "11" * 32,
        "context": context,
        "actions": list(actions),
    }
    return _run_guest_json(binp, req)


def _validate_guest_result(parsed: Mapping[str, Any]) -> None:
    # REVIEW [B -> A-]: the first WIP consumed a no-receipt host-execute result
    # without checking that the CLI had labelled it as non-proof evidence. Pin
    # the contract here so a later CLI change cannot be counted as proof output
    # by accident.
    if parsed.get("schema") != "tau_state_transition_result":
        raise DifferentialError(f"guest CLI emitted wrong schema: {parsed.get('schema')!r}")
    if parsed.get("proof_mode") != "host_execute_no_receipt":
        raise DifferentialError(f"guest CLI emitted wrong proof_mode: {parsed.get('proof_mode')!r}")
    if parsed.get("production_security_claim") is not False:
        raise DifferentialError("guest CLI host-execute result must not carry a production claim")
    if parsed.get("expected_post_app_hash_enforced") is not False:
        raise DifferentialError("guest CLI host-execute result must label post-hash as not enforced")
    if "proof" in parsed:
        raise DifferentialError("guest CLI host-execute result must not include a proof field")


def _run_guest_json(binp: Path, req: Mapping[str, Any]) -> dict[str, Any]:
    proc = subprocess.run([str(binp)], input=json.dumps(req), text=True, capture_output=True)
    if proc.returncode != 0:
        raise DifferentialError(f"guest CLI exited {proc.returncode}: {proc.stderr.strip()[:500]}")
    try:
        parsed = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise DifferentialError(f"guest CLI emitted non-JSON: {exc}; stdout={proc.stdout[:300]}") from exc
    if not isinstance(parsed, dict):
        raise DifferentialError("guest CLI emitted non-object JSON")
    _validate_guest_result(parsed)
    return parsed


# --------------------------------------------------------------------------- #
# Authority side: apply the SAME guest actions through the live Python authority.
# Returns (final_state, accepted, reject_class). collateral_binding / oracle are
# NOT consumed (witness). InitMarket seeds the state.
# --------------------------------------------------------------------------- #
def apply_authority(
    actions: Sequence[Mapping[str, Any]],
    *,
    pre_state: Optional[MarketState] = None,
    state_to_snapshot_fn=state_to_snapshot,
) -> tuple[Optional[MarketState], bool, Optional[str], Optional[str]]:
    """Apply the action list to the authority. Returns
    (state_or_None, accepted, reject_class, market_id)."""
    state = pre_state
    market_id: Optional[str] = None
    for action in actions:
        kind = action["kind"]
        try:
            if kind == "init_market":
                params = _params_from_dict(action["params"]) if action.get("params") else None
                state = init_market(
                    int(action["index_price_e8"]),
                    params,
                    int(action.get("insurance_seed_e8", 0)),
                )
                market_id = str(action["market_id"])
            elif kind == "deposit_collateral":
                assert state is not None, "deposit before init_market"
                pubkey = str(action["pubkey"])
                amount = int(action["amount_e8"])
                nonce = int(action["nonce"])
                # REVIEW [B -> A-]: the first differential compared the Python
                # clearing math core directly against the guest envelope state,
                # so every deposit/withdraw diverged on nonce. Model the wrapper
                # nonce effect here while keeping the Python clearing core pure.
                if amount <= 0:
                    return None, False, REJ_NEGATIVE, market_id
                if nonce <= _account_nonce(state, pubkey):
                    return None, False, REJ_NONCE, market_id
                state = deposit(state, pubkey, amount)
                state = _with_account_nonce(state, pubkey, nonce)
            elif kind == "withdraw_collateral":
                assert state is not None, "withdraw before init_market"
                pubkey = str(action["pubkey"])
                amount = int(action["amount_e8"])
                nonce = int(action["nonce"])
                if amount <= 0:
                    return None, False, REJ_NEGATIVE, market_id
                if nonce <= _account_nonce(state, pubkey):
                    return None, False, REJ_NONCE, market_id
                state = withdraw(state, pubkey, amount)
                state = _with_account_nonce(state, pubkey, nonce)
            elif kind == "run_epoch":
                assert state is not None, "run_epoch before init_market"
                intents = [
                    Intent(
                        pubkey=str(i["pubkey"]),
                        target_base=int(i["target_base"]),
                        limit_price_e8=int(i.get("limit_price_e8", 0)),
                        min_fill_base=int(i.get("min_fill_base", 0)),
                        expiry_epoch=int(i.get("expiry_epoch", 1 << 62)),
                        nonce=int(i.get("nonce", 0)),
                    )
                    for i in action.get("intents", [])
                ]
                state, _result = run_epoch(
                    state,
                    int(action["clearing_price_e8"]),
                    int(action["funding_rate_bps"]),
                    intents,
                )
            else:
                raise DifferentialError(f"unsupported action kind for authority: {kind}")
        except (ValueError, AssertionError) as exc:
            return None, False, _classify_reject(str(exc)), market_id
    return state, True, None, market_id


# --------------------------------------------------------------------------- #
# Comparator: field-by-field, first differing path. Lists of accounts are sorted
# by pubkey on both sides before comparison.
# --------------------------------------------------------------------------- #
def first_diff(guest: Any, authority: Any, path: str = "") -> Optional[str]:
    if isinstance(guest, Mapping) and isinstance(authority, Mapping):
        gk, ak = set(guest), set(authority)
        if gk != ak:
            return f"{path or '<root>'}: key sets differ guest={sorted(gk)} authority={sorted(ak)}"
        for k in sorted(gk):
            d = first_diff(guest[k], authority[k], f"{path}.{k}" if path else k)
            if d:
                return d
        return None
    if isinstance(guest, list) and isinstance(authority, list):
        if len(guest) != len(authority):
            return f"{path}: list len guest={len(guest)} authority={len(authority)}"
        for i, (g, a) in enumerate(zip(guest, authority, strict=True)):
            d = first_diff(g, a, f"{path}[{i}]")
            if d:
                return d
        return None
    # Normalize ints (the guest emits JSON numbers; the authority dict has Python ints).
    if guest != authority:
        return f"{path}: guest={guest!r} authority={authority!r}"
    return None


def run_case(
    case: Mapping[str, Any],
    *,
    binp: Optional[Path] = None,
    state_to_snapshot_fn=state_to_snapshot,
) -> dict[str, Any]:
    """Drive both sides for one corpus case and return the equivalence verdict.

    A case is {name, actions, [pre_state (MarketState), pre_snapshot (dict)]}.
    """
    name = case["name"]
    actions = case["actions"]
    pre_state = case.get("pre_state")
    pre_snapshot = case.get("pre_snapshot")

    guest = run_guest(actions, pre_snapshot=pre_snapshot, binp=binp)
    auth_state, auth_ok, auth_reject_class, market_id = apply_authority(
        actions, pre_state=pre_state, state_to_snapshot_fn=state_to_snapshot_fn
    )
    guest_ok = bool(guest.get("accepted"))

    # (C) accept/reject agreement.
    if guest_ok != auth_ok:
        return {
            "name": name,
            "ok": False,
            "reason": f"accept disagreement: guest_accepted={guest_ok} authority_accepted={auth_ok} "
            f"(guest_reject={guest.get('reject')!r} authority_reject_class={auth_reject_class})",
        }
    if not guest_ok:
        # Both rejected: require the same semantic reason CLASS.
        guest_class = _classify_reject(str(guest.get("reject", "")))
        if guest_class != auth_reject_class:
            return {
                "name": name,
                "ok": False,
                "reason": f"both rejected but different class: guest={guest_class} "
                f"authority={auth_reject_class} (guest_reject={guest.get('reject')!r})",
            }
        expected_class = case.get("expect_class")
        if expected_class is not None and guest_class != expected_class:
            return {
                "name": name,
                "ok": False,
                "reason": f"rejected with class {guest_class}, expected {expected_class}",
            }
        return {"name": name, "ok": True, "both_rejected": True, "reject_class": guest_class}

    if case.get("expect_class") is not None:
        return {
            "name": name,
            "ok": False,
            "reason": f"case expected reject class {case['expect_class']} but both accepted",
        }

    # Both accepted: (A) transition equivalence (field-by-field).
    guest_snap = guest["post_snapshot"]
    assert auth_state is not None
    mid = market_id or guest_snap.get("market_id")
    auth_snap = state_to_snapshot_fn(
        auth_state, market_id=mid, collateral_asset=guest_snap.get("collateral_asset", "zUSD")
    )
    diff = first_diff(guest_snap, auth_snap)
    if diff:
        return {"name": name, "ok": False, "reason": f"post_snapshot diverged at {diff}"}

    # (B) encoder equivalence -- SEPARATE assertion: the guest's committed
    # post_app_hash must equal the Python encoder applied to the guest's snapshot.
    guest_hash = (guest.get("meta") or {}).get("post_app_hash")
    recomputed = guest_compatible_snapshot_hash(guest_snap)
    # _current_snapshot_hash returns 0x-prefixed; the guest meta is bare hex.
    norm = recomputed[2:] if recomputed.startswith("0x") else recomputed
    if guest_hash != norm:
        return {
            "name": name,
            "ok": False,
            "reason": f"encoder divergence: guest journal post_app_hash={guest_hash} "
            f"!= python _current_snapshot_hash(post_snapshot)={norm}",
        }
    return {"name": name, "ok": True, "post_app_hash": guest_hash}


def valid_collateral_binding(tag: str = "diff") -> dict[str, Any]:
    """A VALID guest collateral_binding (witness): correct source proof type +
    three valid 32-byte hex hashes. Content is irrelevant to the post-state."""

    def _h(seed: str) -> str:
        import hashlib

        return hashlib.sha256(f"{tag}:{seed}".encode()).hexdigest()

    return {
        "source_proof_type": ZUSD_PROOF_TYPE,
        "source_state_hash": _h("state"),
        "balance_root_hash": _h("balroot"),
        "balance_delta_hash": _h("baldelta"),
    }


if __name__ == "__main__":  # pragma: no cover - CLI convenience
    from tests.runtime import perps_np_differential_corpus as corpus  # type: ignore

    failures = []
    all_cases = [*corpus.CORPUS, *corpus.REJECT_CORPUS]
    for case in all_cases:
        res = run_case(case)
        status = "ok" if res["ok"] else "DIVERGED"
        print(f"[{status}] {case['name']}: {res.get('reason', '')}")
        if not res["ok"]:
            failures.append(res)
    if failures:
        print(f"\n{len(failures)} divergence(s) found", file=sys.stderr)
        sys.exit(1)
    print(f"\nall {len(all_cases)} cases observationally equivalent")
