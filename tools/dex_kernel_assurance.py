#!/usr/bin/env python3
"""
Manifest-backed kernel assurance runner for ZenoDEX.

This tool is intended to make "A+/Verified" kernel claims non-gameable by:
- pinning production kernels + corpora in a single manifest,
- re-running multi-solver verification with deterministic settings,
- enforcing non-trivial CE corpora requirements,
- replaying CE corpora and rejecting vacuous GuardFalse passes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

import yaml


REPO_ROOT = Path(__file__).resolve().parents[1]
ESSO_ROOT = REPO_ROOT / "external" / "ESSO"
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "kernel_assurance_manifest.json"


class AssuranceError(RuntimeError):
    pass


def _git_stdout(*args: str) -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", str(ESSO_ROOT), *args],
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise AssuranceError("git is required to verify the pinned ESSO checkout state") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip()
        if not detail:
            detail = str(exc)
        raise AssuranceError(f"failed to inspect ESSO checkout state: {detail}") from exc
    return proc.stdout.strip()


def _collect_esso_checkout_state() -> Dict[str, Any]:
    if not ESSO_ROOT.exists():
        raise AssuranceError(f"ESSO not found at {ESSO_ROOT} (clone/update external/ESSO).")

    esso_code_hash = _git_stdout("rev-parse", "HEAD")
    status_text = _git_stdout("status", "--porcelain")
    dirty_entries = [line for line in status_text.splitlines() if line.strip()]
    return {
        "esso_code_hash": esso_code_hash,
        "esso_dirty": bool(dirty_entries),
        "esso_dirty_entries": dirty_entries,
        "esso_tree_sha256": _sha256_tree(
            [ESSO_ROOT / "pyproject.toml", ESSO_ROOT / "ESSO"],
            root=ESSO_ROOT,
        ),
    }


def _enforce_before_vars_are_internal_and_overwritten(ir: Any) -> None:
    """
    Fail-closed check for history/snapshot state vars like `reserve_x_before`.

    These vars exist only to express transition invariants (e.g. k non-decreasing).
    They must not be part of the kernel's observable state surface and must be
    overwritten from the corresponding base var on every action step; otherwise
    an external caller could fabricate them and bypass invariants.
    """
    observable = set(str(x) for x in getattr(getattr(ir, "observables", None), "state_vars", ()) or ())
    state_ids = {str(sv.id) for sv in getattr(ir, "state_vars", [])}

    before_vars = [sid for sid in state_ids if sid.endswith("_before")]
    if not before_vars:
        return

    for before in before_vars:
        base = before[: -len("_before")]
        if base not in state_ids:
            raise AssuranceError(f"history var {before!r} missing base state var {base!r}")
        if before in observable:
            raise AssuranceError(f"history var {before!r} must not be observable")

        for act in getattr(ir, "actions", []):
            act_id = str(getattr(act, "id", ""))
            upd = None
            for u in getattr(act, "updates", []) or []:
                if str(getattr(u, "var", "")) == before:
                    upd = u
                    break
            if upd is None:
                raise AssuranceError(f"history var {before!r} not overwritten in action {act_id!r}")
            expr = getattr(upd, "expr", None)
            if getattr(expr, "kind", None) != "var" or str(getattr(expr, "name", "")) != base:
                raise AssuranceError(f"history var {before!r} must be overwritten as var({base!r}) in action {act_id!r}")


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _sha256_tree(paths: Sequence[Path], *, root: Path) -> str:
    h = hashlib.sha256()
    files: list[Path] = []
    ignored_parts = {".git", "__pycache__", ".mypy_cache", ".pytest_cache"}
    ignored_suffixes = {".pyc", ".pyo"}

    for base in paths:
        if base.is_file():
            files.append(base)
            continue
        if not base.is_dir():
            continue
        for p in sorted(base.rglob("*")):
            if not p.is_file():
                continue
            if any(part in ignored_parts for part in p.parts):
                continue
            if p.suffix in ignored_suffixes:
                continue
            files.append(p)

    for p in files:
        rel = p.relative_to(root).as_posix().encode("utf-8")
        h.update(rel)
        h.update(b"\0")
        h.update(_sha256_file(p).encode("ascii"))
        h.update(b"\0")
    return h.hexdigest()


def _ensure_esso_on_path() -> None:
    if not ESSO_ROOT.exists():
        raise AssuranceError(f"ESSO not found at {ESSO_ROOT} (clone/update external/ESSO).")
    sys.path.insert(0, str(ESSO_ROOT))


def _ensure_repo_on_path() -> None:
    # Needed for optional reference checks against src/core/*.py.
    sys.path.insert(0, str(REPO_ROOT))


def _load_yaml_mapping(path: Path) -> Dict[str, Any]:
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise AssuranceError(f"expected YAML mapping at top level: {path}")
    return obj


def _load_manifest(path: Path) -> Dict[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise AssuranceError(f"failed to read manifest JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise AssuranceError("manifest must be a JSON object")
    return obj


def _ir_hash(ir: Any) -> str:
    b = ir.to_json(canonical=True, indent=None).encode("utf-8")
    return "sha256:" + hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class CorpusStats:
    total: int
    per_action: Dict[str, int]
    boundary_per_action: Dict[str, int]
    unique_ids: int
    unique_signatures: int

    @property
    def unique_signature_ratio(self) -> float:
        return 0.0 if self.total <= 0 else float(self.unique_signatures) / float(self.total)


def _iter_jsonl(path: Path) -> Iterable[Dict[str, Any]]:
    with path.open("r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, start=1):
            s = line.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except Exception as exc:
                raise AssuranceError(f"invalid JSONL at {path}:{line_no}: {exc}") from exc
            if not isinstance(obj, dict):
                raise AssuranceError(f"invalid JSONL entry at {path}:{line_no}: expected object")
            yield obj


def _require_int_bounds(value: Any, *, lo: Optional[int], hi: Optional[int]) -> bool:
    if not isinstance(value, int) or isinstance(value, bool):
        return False
    if lo is not None and value < lo:
        return False
    if hi is not None and value > hi:
        return False
    return True


def _collect_type_bounds(ir: Any) -> Tuple[Dict[str, Tuple[Optional[int], Optional[int]]], Dict[str, Dict[str, Tuple[Optional[int], Optional[int]]]]]:
    """
    Return (state_bounds, param_bounds_by_action).

    Bounds are (min, max) for int types; other types map to (None, None).
    """
    nt = {t.id: t.type for t in getattr(ir, "types", [])}  # type: ignore[attr-defined]

    def _resolve_type(t: Any) -> Any:
        if getattr(t, "kind", None) != "ref":
            return t
        ref = getattr(t, "ref", None)
        if not isinstance(ref, str) or not ref:
            return t
        return nt.get(ref, t)

    state_bounds: Dict[str, Tuple[Optional[int], Optional[int]]] = {}
    for sv in ir.state_vars:
        t = _resolve_type(sv.type)
        if getattr(t, "kind", None) == "int":
            state_bounds[str(sv.id)] = (getattr(t, "min", None), getattr(t, "max", None))
        else:
            state_bounds[str(sv.id)] = (None, None)

    param_bounds: Dict[str, Dict[str, Tuple[Optional[int], Optional[int]]]] = {}
    for act in ir.actions:
        pb: Dict[str, Tuple[Optional[int], Optional[int]]] = {}
        for p in act.params:
            t = _resolve_type(p.type)
            if getattr(t, "kind", None) == "int":
                pb[str(p.id)] = (getattr(t, "min", None), getattr(t, "max", None))
            else:
                pb[str(p.id)] = (None, None)
        param_bounds[str(act.id)] = pb
    return state_bounds, param_bounds


def _is_boundary_case(
    *,
    state: Mapping[str, Any],
    cmd_tag: str,
    cmd_args: Mapping[str, Any],
    state_bounds: Mapping[str, Tuple[Optional[int], Optional[int]]],
    param_bounds: Mapping[str, Mapping[str, Tuple[Optional[int], Optional[int]]]],
) -> bool:
    # Any int state var or param at min/max counts as a boundary case.
    for k, v in state.items():
        lo, hi = state_bounds.get(k, (None, None))
        if lo is None and hi is None:
            continue
        if _require_int_bounds(v, lo=lo, hi=hi) and (v == lo or v == hi):
            return True
    pb = param_bounds.get(cmd_tag, {})
    for k, v in cmd_args.items():
        lo, hi = pb.get(k, (None, None))
        if lo is None and hi is None:
            continue
        if _require_int_bounds(v, lo=lo, hi=hi) and (v == lo or v == hi):
            return True
    return False


def _corpus_stats(
    *,
    corpus_path: Path,
    required_actions: Sequence[str],
    state_bounds: Mapping[str, Tuple[Optional[int], Optional[int]]],
    param_bounds: Mapping[str, Mapping[str, Tuple[Optional[int], Optional[int]]]],
) -> CorpusStats:
    per_action: Dict[str, int] = {a: 0 for a in required_actions}
    boundary_per_action: Dict[str, int] = {a: 0 for a in required_actions}
    seen_ids: set[str] = set()
    seen_sigs: set[str] = set()
    total = 0

    for obj in _iter_jsonl(corpus_path):
        total += 1

        retained = bool(obj.get("retained", False))
        duplicate = bool(obj.get("duplicate", False))
        if not retained:
            raise AssuranceError(f"unretained corpus entry found (fail-closed): {corpus_path}")
        if duplicate:
            raise AssuranceError(f"duplicate corpus entry found (fail-closed): {corpus_path}")

        cid = obj.get("id")
        if not isinstance(cid, str) or not cid:
            raise AssuranceError(f"missing/invalid corpus id: {corpus_path}")
        if cid in seen_ids:
            raise AssuranceError(f"duplicate corpus id: {cid}")
        seen_ids.add(cid)

        sig = obj.get("signature")
        if not isinstance(sig, str) or not sig:
            raise AssuranceError(f"missing/invalid corpus signature: {corpus_path}")
        seen_sigs.add(sig)

        t_obj = obj.get("test")
        if not isinstance(t_obj, dict):
            raise AssuranceError(f"missing/invalid corpus test object: {corpus_path}")

        cmd = t_obj.get("command")
        if not isinstance(cmd, dict):
            raise AssuranceError(f"missing/invalid corpus test.command: {corpus_path}")
        tag = cmd.get("tag")
        args = cmd.get("args", {})
        if not isinstance(tag, str) or not tag:
            raise AssuranceError(f"missing/invalid command.tag: {corpus_path}")
        if not isinstance(args, dict):
            raise AssuranceError(f"invalid command.args: {corpus_path}")

        if tag in per_action:
            per_action[tag] += 1
            if _is_boundary_case(
                state=t_obj.get("state", {}) if isinstance(t_obj.get("state"), dict) else {},
                cmd_tag=tag,
                cmd_args=args,
                state_bounds=state_bounds,
                param_bounds=param_bounds,
            ):
                boundary_per_action[tag] += 1

    return CorpusStats(
        total=total,
        per_action=per_action,
        boundary_per_action=boundary_per_action,
        unique_ids=len(seen_ids),
        unique_signatures=len(seen_sigs),
    )


def _step_result_fingerprint(state: Mapping[str, Any], effects: Mapping[str, Any]) -> str:
    return _sha256_bytes(_canonical_json_bytes({"state": dict(state), "effects": dict(effects)}))


def _replay_corpus_fail_closed(*, ir: Any, corpus_path: Path, required_reference_checks: Sequence[str]) -> None:
    from ESSO.kernel.interpreter import Command, StepOk, step

    _ensure_repo_on_path()

    def _require_int(value: Any, *, name: str) -> int:
        if not isinstance(value, int) or isinstance(value, bool):
            raise AssuranceError(f"reference check expected int for {name}, got {type(value)}")
        return int(value)

    def _require_str(value: Any, *, name: str) -> str:
        if not isinstance(value, str):
            raise AssuranceError(f"reference check expected str for {name}, got {type(value)}")
        return value

    def _check_cpmm_swap_reference(
        *,
        pre_state: Mapping[str, Any],
        cmd_tag: str,
        cmd_args: Mapping[str, Any],
        post_state: Mapping[str, Any],
        effects: Mapping[str, Any],
    ) -> None:
        from src.core.cpmm import swap_exact_in

        fee_bps = _require_int(pre_state.get("fee_bps"), name="fee_bps")
        reserve_x0 = _require_int(pre_state.get("reserve_x"), name="reserve_x")
        reserve_y0 = _require_int(pre_state.get("reserve_y"), name="reserve_y")

        if cmd_tag == "swap_x_for_y":
            amount_in = _require_int(cmd_args.get("amount_in_x"), name="amount_in_x")
            amount_out_ref, (rx1, ry1) = swap_exact_in(reserve_x0, reserve_y0, amount_in, fee_bps)
            swap_dir = "XForY"
        elif cmd_tag == "swap_y_for_x":
            amount_in = _require_int(cmd_args.get("amount_in_y"), name="amount_in_y")
            amount_out_ref, (ry1, rx1) = swap_exact_in(reserve_y0, reserve_x0, amount_in, fee_bps)
            swap_dir = "YForX"
        else:
            raise AssuranceError(f"unknown cpmm_swap action: {cmd_tag}")

        # State transition.
        if _require_int(post_state.get("reserve_x"), name="post.reserve_x") != rx1:
            raise AssuranceError(f"cpmm_swap reserve_x mismatch for {cmd_tag}")
        if _require_int(post_state.get("reserve_y"), name="post.reserve_y") != ry1:
            raise AssuranceError(f"cpmm_swap reserve_y mismatch for {cmd_tag}")

        if _require_int(post_state.get("reserve_x_before"), name="post.reserve_x_before") != reserve_x0:
            raise AssuranceError(f"cpmm_swap reserve_x_before mismatch for {cmd_tag}")
        if _require_int(post_state.get("reserve_y_before"), name="post.reserve_y_before") != reserve_y0:
            raise AssuranceError(f"cpmm_swap reserve_y_before mismatch for {cmd_tag}")

        # Effects.
        if _require_str(effects.get("swap_dir"), name="effects.swap_dir") != swap_dir:
            raise AssuranceError(f"cpmm_swap swap_dir mismatch for {cmd_tag}")

        fee_paid_ref = (amount_in * fee_bps + 9999) // 10000
        net_in_ref = amount_in - fee_paid_ref
        k_before_ref = reserve_x0 * reserve_y0
        k_after_ref = rx1 * ry1

        if _require_int(effects.get("amount_in"), name="effects.amount_in") != amount_in:
            raise AssuranceError(f"cpmm_swap amount_in mismatch for {cmd_tag}")
        if _require_int(effects.get("fee_paid"), name="effects.fee_paid") != fee_paid_ref:
            raise AssuranceError(f"cpmm_swap fee_paid mismatch for {cmd_tag}")
        if _require_int(effects.get("net_in"), name="effects.net_in") != net_in_ref:
            raise AssuranceError(f"cpmm_swap net_in mismatch for {cmd_tag}")
        if _require_int(effects.get("amount_out"), name="effects.amount_out") != amount_out_ref:
            raise AssuranceError(f"cpmm_swap amount_out mismatch for {cmd_tag}")
        if _require_int(effects.get("k_before"), name="effects.k_before") != k_before_ref:
            raise AssuranceError(f"cpmm_swap k_before mismatch for {cmd_tag}")
        if _require_int(effects.get("k_after"), name="effects.k_after") != k_after_ref:
            raise AssuranceError(f"cpmm_swap k_after mismatch for {cmd_tag}")
        if k_after_ref < k_before_ref:
            raise AssuranceError(f"cpmm_swap invariant violated in reference check for {cmd_tag}: k decreased")

    def _check_liquidity_pool_reference(
        *,
        pre_state: Mapping[str, Any],
        cmd_tag: str,
        cmd_args: Mapping[str, Any],
        post_state: Mapping[str, Any],
        effects: Mapping[str, Any],
    ) -> None:
        from src.core.cpmm import compute_lp_burn, compute_lp_mint

        reserve_a0 = _require_int(pre_state.get("reserve_a"), name="reserve_a")
        reserve_b0 = _require_int(pre_state.get("reserve_b"), name="reserve_b")
        lp_supply0 = _require_int(pre_state.get("total_lp_shares"), name="total_lp_shares")

        if cmd_tag == "add_liquidity":
            amount_a_in = _require_int(cmd_args.get("amount_a_in"), name="amount_a_in")
            amount_b_in = _require_int(cmd_args.get("amount_b_in"), name="amount_b_in")
            minted_ref = compute_lp_mint(reserve_a0, reserve_b0, amount_a_in, amount_b_in, lp_supply0)

            if _require_int(post_state.get("reserve_a"), name="post.reserve_a") != reserve_a0 + amount_a_in:
                raise AssuranceError("liquidity_pool reserve_a mismatch for add_liquidity")
            if _require_int(post_state.get("reserve_b"), name="post.reserve_b") != reserve_b0 + amount_b_in:
                raise AssuranceError("liquidity_pool reserve_b mismatch for add_liquidity")
            if _require_int(post_state.get("total_lp_shares"), name="post.total_lp_shares") != lp_supply0 + minted_ref:
                raise AssuranceError("liquidity_pool total_lp_shares mismatch for add_liquidity")

            if _require_int(effects.get("lp_shares_minted"), name="effects.lp_shares_minted") != minted_ref:
                raise AssuranceError("liquidity_pool lp_shares_minted mismatch for add_liquidity")
            if _require_int(effects.get("lp_shares_burned"), name="effects.lp_shares_burned") != 0:
                raise AssuranceError("liquidity_pool lp_shares_burned mismatch for add_liquidity")
        elif cmd_tag == "remove_liquidity":
            burn = _require_int(cmd_args.get("lp_shares_burn"), name="lp_shares_burn")
            amount_a_out, amount_b_out = compute_lp_burn(burn, reserve_a0, reserve_b0, lp_supply0)

            if _require_int(post_state.get("reserve_a"), name="post.reserve_a") != reserve_a0 - amount_a_out:
                raise AssuranceError("liquidity_pool reserve_a mismatch for remove_liquidity")
            if _require_int(post_state.get("reserve_b"), name="post.reserve_b") != reserve_b0 - amount_b_out:
                raise AssuranceError("liquidity_pool reserve_b mismatch for remove_liquidity")
            if _require_int(post_state.get("total_lp_shares"), name="post.total_lp_shares") != lp_supply0 - burn:
                raise AssuranceError("liquidity_pool total_lp_shares mismatch for remove_liquidity")

            if _require_int(effects.get("lp_shares_minted"), name="effects.lp_shares_minted") != 0:
                raise AssuranceError("liquidity_pool lp_shares_minted mismatch for remove_liquidity")
            if _require_int(effects.get("lp_shares_burned"), name="effects.lp_shares_burned") != burn:
                raise AssuranceError("liquidity_pool lp_shares_burned mismatch for remove_liquidity")
            removed = amount_a_out + amount_b_out
            if _require_int(effects.get("amounts_removed"), name="effects.amounts_removed") != removed:
                raise AssuranceError("liquidity_pool amounts_removed mismatch for remove_liquidity")
        else:
            raise AssuranceError(f"unknown liquidity_pool action: {cmd_tag}")

        # Snapshot vars (pre -> post).
        if _require_int(post_state.get("reserve_a_before"), name="post.reserve_a_before") != reserve_a0:
            raise AssuranceError(f"liquidity_pool reserve_a_before mismatch for {cmd_tag}")
        if _require_int(post_state.get("reserve_b_before"), name="post.reserve_b_before") != reserve_b0:
            raise AssuranceError(f"liquidity_pool reserve_b_before mismatch for {cmd_tag}")
        if _require_int(post_state.get("total_lp_shares_before"), name="post.total_lp_shares_before") != lp_supply0:
            raise AssuranceError(f"liquidity_pool total_lp_shares_before mismatch for {cmd_tag}")

    model_id = str(ir.meta.get("model_id", ""))
    required_set = set(required_reference_checks)

    supported_checks_by_model: dict[str, set[str]] = {
        "cpmm_swap": {"cpmm_swap_python_core_parity"},
        "liquidity_pool": {"liquidity_pool_python_core_parity"},
    }
    supported = supported_checks_by_model.get(model_id, set())
    unknown = sorted(required_set - supported)
    missing = sorted(supported - required_set)
    if unknown:
        raise AssuranceError(f"unknown required_reference_checks for {model_id}: {unknown}")
    if missing:
        raise AssuranceError(f"missing required_reference_checks for {model_id}: {missing}")

    before_pairs: list[tuple[str, str]] = []
    for sv in getattr(ir, "state_vars", []) or []:
        sid = str(getattr(sv, "id", ""))
        if sid.endswith("_before"):
            before_pairs.append((sid, sid[: -len("_before")]))

    for obj in _iter_jsonl(corpus_path):
        t_obj = obj.get("test")
        assert isinstance(t_obj, dict)
        state = t_obj.get("state", {})
        cmd_obj = t_obj.get("command")
        if not isinstance(state, dict) or not isinstance(cmd_obj, dict):
            raise AssuranceError(f"invalid corpus test shape: {corpus_path}")
        tag = cmd_obj.get("tag")
        args = cmd_obj.get("args")
        if not isinstance(tag, str) or not isinstance(args, dict):
            raise AssuranceError(f"invalid corpus command shape: {corpus_path}")

        # Fail-closed: snapshot/history vars must be internally consistent at the state boundary.
        # If a corpus could fabricate `*_before`, it could trivialize history-based invariants.
        for before, base in before_pairs:
            if before not in state or base not in state:
                raise AssuranceError(f"missing {before!r}/{base!r} in corpus state: {corpus_path} id={obj.get('id')}")
            if state.get(before) != state.get(base):
                raise AssuranceError(
                    f"invalid corpus state: {before!r} != {base!r} (history vars must match base): {corpus_path} id={obj.get('id')}"
                )

        cmd = Command(tag=tag, args=args)
        r1 = step(state, cmd, ir)
        r2 = step(state, cmd, ir)
        if not isinstance(r1, StepOk):
            raise AssuranceError(f"corpus replay failed (expected ok step): {corpus_path} id={obj.get('id')}")
        if not isinstance(r2, StepOk):
            raise AssuranceError(f"corpus replay nondeterministic (second run failed): {corpus_path} id={obj.get('id')}")

        fp1 = _step_result_fingerprint(r1.state, r1.effects)
        fp2 = _step_result_fingerprint(r2.state, r2.effects)
        if fp1 != fp2:
            raise AssuranceError(f"corpus replay nondeterministic (state/effects differ): {corpus_path} id={obj.get('id')}")

        # Semantic reference checks (non-vacuous): compare against src/core implementations.
        if model_id == "cpmm_swap" and "cpmm_swap_python_core_parity" in required_set:
            _check_cpmm_swap_reference(
                pre_state=state,
                cmd_tag=tag,
                cmd_args=args,
                post_state=r1.state,
                effects=r1.effects,
            )
        elif model_id == "liquidity_pool" and "liquidity_pool_python_core_parity" in required_set:
            _check_liquidity_pool_reference(
                pre_state=state,
                cmd_tag=tag,
                cmd_args=args,
                post_state=r1.state,
                effects=r1.effects,
            )


def _verify_kernel(
    *,
    ir: Any,
    solvers: Sequence[str],
    timeout_ms: int,
    determinism_trials: int,
    seeds: Sequence[int],
    produce_proofs: bool = False,
    require_no_trust_proofs: bool = False,
    fingerprint_proofs: bool = False,
    bundle_out_dir: Path | None = None,
    bundle_seed: int | None = None,
) -> Dict[str, Any]:
    from ESSO.export.smtlib import export_smtlib
    from ESSO.verify.bundle import write_verification_bundle
    from ESSO.verify.multi_solver import (
        results_fingerprint,
        results_fingerprint_with_proofs,
        verify_ir_multi_solver,
    )
    from ESSO.repro_env import tool_versions
    from ESSO.verify.multi_solver import SolverResult

    if determinism_trials < 2:
        raise AssuranceError("determinism_trials must be >= 2")
    if not seeds:
        raise AssuranceError("seeds must be non-empty")

    trials: List[Dict[str, Any]] = []
    fingerprints: List[str] = []
    started = time.time()

    bundle_meta: dict[str, Any] | None = None
    if bundle_out_dir is not None and bundle_seed is None:
        bundle_seed = int(seeds[0])

    for i in range(determinism_trials):
        seed = int(seeds[i % len(seeds)])
        res = verify_ir_multi_solver(
            ir,
            timeout_ms=int(timeout_ms),
            solvers=list(solvers),
            solver_seed=seed,
            produce_proofs=bool(produce_proofs),
        )
        fp = (
            results_fingerprint_with_proofs(res)
            if fingerprint_proofs and produce_proofs
            else results_fingerprint(res)
        )
        fingerprints.append(fp)

        solvers_set = set(str(s) for s in solvers)
        # Fail-closed on any non-UNSAT / disagreement / missing solver result.
        for qname, r in res.items():
            if r.final_result != SolverResult.UNSAT:
                raise AssuranceError(f"verification failed: query {qname} => {r.final_result.value}")
            if len(solvers_set) > 1 and not r.agreed:
                raise AssuranceError(f"verification failed: solvers disagreed for query {qname}")
            if "z3" in solvers_set and r.z3_result is None:
                raise AssuranceError(f"verification failed: missing solver result for query {qname}/z3")
            if "cvc5" in solvers_set and r.cvc5_result is None:
                raise AssuranceError(f"verification failed: missing solver result for query {qname}/cvc5")
            if require_no_trust_proofs:
                # Only meaningful for solvers that produce proofs; fail-closed if trust is detected.
                if r.z3_result is not None and r.z3_result.proof_has_trust is True:
                    raise AssuranceError(f"verification failed: z3 proof contains trust step for query {qname}")
                if r.cvc5_result is not None and r.cvc5_result.proof_has_trust is True:
                    raise AssuranceError(f"verification failed: cvc5 proof contains trust step for query {qname}")

        trials.append(
            {
                "seed": seed,
                "fingerprint": fp,
            }
        )

        # Optional: write a deterministic evidence bundle once (single seed).
        if bundle_out_dir is not None and bundle_meta is None and seed == int(bundle_seed):
            # Re-export queries deterministically from the IR and store solver outputs (and proofs if enabled).
            queries = export_smtlib(ir)
            ir_hash = _ir_hash(ir)
            out_dir = (bundle_out_dir / f"{ir_hash}").resolve()
            bundle_paths = write_verification_bundle(
                output_dir=out_dir,
                candidate=ir,
                reference=None,
                queries=queries,
                results=res,
                solvers=list(solvers),
                timeout_ms=int(timeout_ms),
                solver_seed=int(seed),
                k=1,
            )
            bundle_meta = {
                "bundle_dir": str(out_dir),
                "bundle_paths": dict(bundle_paths),
                "bundle_seed": int(seed),
                "produce_proofs": bool(produce_proofs),
                "require_no_trust_proofs": bool(require_no_trust_proofs),
            }

    det_ok = all(fp == fingerprints[0] for fp in fingerprints[1:])
    if not det_ok:
        raise AssuranceError("verification nondeterministic: fingerprints differ across trials")

    out: Dict[str, Any] = {
        "tool_versions": tool_versions(solvers=solvers),
        "timeout_ms": int(timeout_ms),
        "determinism_trials": int(determinism_trials),
        "seeds": [int(x) for x in seeds],
        "fingerprint": fingerprints[0] if fingerprints else "",
        "elapsed_s": time.time() - started,
        "trials": trials,
    }
    if bundle_meta is not None:
        out["evidence_bundle"] = bundle_meta
    return out


def _enforce_toolchain(*, expected: Any, actual: Any, solvers_used: Sequence[str]) -> None:
    if expected is None:
        return
    if not isinstance(expected, Mapping):
        raise AssuranceError("manifest.toolchain must be an object when present")
    if not isinstance(actual, Mapping):
        raise AssuranceError("tool_versions must be an object")

    exp_esso_tree = expected.get("esso_tree_sha256")
    if exp_esso_tree is not None:
        if not isinstance(exp_esso_tree, str) or not exp_esso_tree:
            raise AssuranceError("manifest.toolchain.esso_tree_sha256 must be a non-empty string or null")
        if actual.get("esso_tree_sha256") != exp_esso_tree:
            raise AssuranceError(
                f"ESSO tree hash mismatch: expected {exp_esso_tree}, got {actual.get('esso_tree_sha256')}"
            )
    elif bool(actual.get("esso_dirty")):
        dirty_entries = actual.get("esso_dirty_entries")
        sample = ""
        if isinstance(dirty_entries, Sequence) and not isinstance(dirty_entries, (str, bytes)):
            rendered = [str(x) for x in dirty_entries if str(x)]
            if rendered:
                suffix = " ..." if len(rendered) > 5 else ""
                sample = f": {'; '.join(rendered[:5])}{suffix}"
        raise AssuranceError(
            "ESSO checkout is dirty; kernel assurance requires a clean pinned toolchain"
            f"{sample}"
        )

    exp_esso = expected.get("esso_code_hash")
    if exp_esso is not None:
        if not isinstance(exp_esso, str) or not exp_esso:
            raise AssuranceError("manifest.toolchain.esso_code_hash must be a non-empty string or null")
        if actual.get("esso_code_hash") != exp_esso:
            raise AssuranceError(f"ESSO code hash mismatch: expected {exp_esso}, got {actual.get('esso_code_hash')}")

    exp_solvers = expected.get("solvers")
    if exp_solvers is not None:
        if not isinstance(exp_solvers, Mapping):
            raise AssuranceError("manifest.toolchain.solvers must be an object or null")
        act_solvers = actual.get("solvers", {})
        if not isinstance(act_solvers, Mapping):
            raise AssuranceError("tool_versions.solvers must be an object")
        for solver in solvers_used:
            if not isinstance(solver, str) or not solver:
                raise AssuranceError("solvers_used entries must be non-empty strings")
            exp_ver = exp_solvers.get(solver)
            if exp_ver is None:
                raise AssuranceError(f"manifest.toolchain.solvers missing version pin for {solver}")
            if not isinstance(exp_ver, str) or not exp_ver:
                raise AssuranceError("manifest.toolchain.solvers values must be non-empty strings")
            if act_solvers.get(solver) != exp_ver:
                raise AssuranceError(f"{solver} version mismatch: expected {exp_ver!r}, got {act_solvers.get(solver)!r}")


def _require_manifest_int(obj: Any, *, name: str, lo: int = 1) -> int:
    if not isinstance(obj, int) or isinstance(obj, bool) or obj < lo:
        raise AssuranceError(f"{name} must be an int >= {lo}")
    return int(obj)


def _require_manifest_str(obj: Any, *, name: str, non_empty: bool = True) -> str:
    if not isinstance(obj, str):
        raise AssuranceError(f"{name} must be a string")
    if non_empty and not obj:
        raise AssuranceError(f"{name} must be non-empty")
    return obj


def _relpath(p: Path) -> str:
    try:
        return p.relative_to(REPO_ROOT).as_posix()
    except Exception:
        return p.as_posix()


def _run_one_kernel(
    *,
    kernel_entry: Mapping[str, Any],
    solvers: Sequence[str],
    timeout_ms: int,
    determinism_trials: int,
    seeds: Sequence[int],
    expected_toolchain: Any,
    actual_toolchain: Mapping[str, Any],
    evidence_bundle_base: Path | None = None,
    produce_proofs: bool = False,
    require_no_trust_proofs: bool = False,
    fingerprint_proofs: bool = False,
) -> Dict[str, Any]:
    _ensure_esso_on_path()
    from ESSO.ir.schema import CandidateIR

    model_id = _require_manifest_str(kernel_entry.get("model_id"), name="kernel.model_id")
    kernel_path = REPO_ROOT / _require_manifest_str(kernel_entry.get("kernel_path"), name=f"{model_id}.kernel_path")
    corpus_path = REPO_ROOT / _require_manifest_str(kernel_entry.get("ce_corpus_path"), name=f"{model_id}.ce_corpus_path")

    kernel_solvers = kernel_entry.get("solvers")
    if kernel_solvers is None:
        kernel_solvers = list(solvers)
    if (
        not isinstance(kernel_solvers, list)
        or not kernel_solvers
        or not all(isinstance(s, str) and s for s in kernel_solvers)
    ):
        raise AssuranceError(f"{model_id}.solvers must be a non-empty list of strings when present")

    required_actions = kernel_entry.get("required_actions")
    if not isinstance(required_actions, list) or not all(isinstance(x, str) and x for x in required_actions):
        raise AssuranceError(f"{model_id}.required_actions must be a list of strings")

    required_invariants = kernel_entry.get("required_invariants")
    if not isinstance(required_invariants, list) or not all(isinstance(x, str) and x for x in required_invariants):
        raise AssuranceError(f"{model_id}.required_invariants must be a list of strings")

    required_reference_checks = kernel_entry.get("required_reference_checks")
    if not isinstance(required_reference_checks, list) or not all(
        isinstance(x, str) and x for x in required_reference_checks
    ):
        raise AssuranceError(f"{model_id}.required_reference_checks must be a list of strings")

    if not kernel_path.is_file():
        raise AssuranceError(f"kernel not found: {kernel_path}")
    if not corpus_path.is_file():
        raise AssuranceError(f"ce corpus not found: {corpus_path}")

    obj = _load_yaml_mapping(kernel_path)
    ir = CandidateIR.from_json_dict(obj, path=str(kernel_path)).canonicalized()

    if str(ir.meta.get("model_id", "")) != model_id:
        raise AssuranceError(f"kernel meta.model_id mismatch: expected {model_id!r}, got {ir.meta.get('model_id')!r}")

    # Required interface surface.
    action_ids = [str(a.id) for a in ir.actions]
    missing_actions = sorted(set(required_actions) - set(action_ids))
    extra_actions = sorted(set(action_ids) - set(required_actions))
    if missing_actions:
        raise AssuranceError(f"kernel missing required actions: {missing_actions}")
    if extra_actions:
        raise AssuranceError(f"kernel has unexpected actions: {extra_actions}")

    inv_ids = [str(inv.id) for inv in ir.invariants]
    missing_invs = sorted(set(required_invariants) - set(inv_ids))
    if missing_invs:
        raise AssuranceError(f"kernel missing required invariants: {missing_invs}")

    _enforce_before_vars_are_internal_and_overwritten(ir)

    ir_hash = _ir_hash(ir)
    expected_ir_hash = _require_manifest_str(kernel_entry.get("expected_ir_hash", ""), name=f"{model_id}.expected_ir_hash")
    if expected_ir_hash and ir_hash != expected_ir_hash:
        raise AssuranceError(f"IR hash mismatch for {model_id}: expected {expected_ir_hash}, got {ir_hash}")

    corpus_sha256 = _sha256_file(corpus_path)
    expected_corpus_sha256 = _require_manifest_str(
        kernel_entry.get("expected_ce_corpus_sha256", ""), name=f"{model_id}.expected_ce_corpus_sha256"
    )
    if expected_corpus_sha256 and corpus_sha256 != expected_corpus_sha256:
        raise AssuranceError(
            f"CE corpus hash mismatch for {model_id}: expected {expected_corpus_sha256}, got {corpus_sha256}"
        )

    # Corpus stats + replay.
    state_bounds, param_bounds = _collect_type_bounds(ir)
    stats = _corpus_stats(
        corpus_path=corpus_path,
        required_actions=list(required_actions),
        state_bounds=state_bounds,
        param_bounds=param_bounds,
    )
    min_total = _require_manifest_int(kernel_entry.get("min_corpus_total"), name=f"{model_id}.min_corpus_total")
    min_per_action = _require_manifest_int(kernel_entry.get("min_per_action"), name=f"{model_id}.min_per_action")
    min_boundary = _require_manifest_int(
        kernel_entry.get("min_boundary_per_action"), name=f"{model_id}.min_boundary_per_action"
    )

    if stats.total < min_total:
        raise AssuranceError(f"corpus too small for {model_id}: {stats.total} < {min_total}")
    for a in required_actions:
        if stats.per_action.get(a, 0) < min_per_action:
            raise AssuranceError(
                f"corpus missing per-action coverage for {model_id}/{a}: {stats.per_action.get(a, 0)} < {min_per_action}"
            )
        if stats.boundary_per_action.get(a, 0) < min_boundary:
            raise AssuranceError(
                f"corpus missing boundary coverage for {model_id}/{a}: {stats.boundary_per_action.get(a, 0)} < {min_boundary}"
            )

    if stats.unique_signature_ratio < 0.90:
        raise AssuranceError(
            f"corpus signature uniqueness too low for {model_id}: {stats.unique_signature_ratio:.3f} < 0.900"
        )

    _replay_corpus_fail_closed(ir=ir, corpus_path=corpus_path, required_reference_checks=required_reference_checks)

    # Multi-solver verification.
    verify_report = _verify_kernel(
        ir=ir,
        solvers=kernel_solvers,
        timeout_ms=timeout_ms,
        determinism_trials=determinism_trials,
        seeds=seeds,
        produce_proofs=produce_proofs,
        require_no_trust_proofs=require_no_trust_proofs,
        fingerprint_proofs=fingerprint_proofs,
        bundle_out_dir=(None if evidence_bundle_base is None else (evidence_bundle_base / model_id)),
        bundle_seed=int(seeds[0]) if seeds else 0,
    )
    verify_tool_versions = verify_report.get("tool_versions")
    if not isinstance(verify_tool_versions, Mapping):
        raise AssuranceError("verification report missing tool_versions")
    actual_toolchain_full = dict(verify_tool_versions)
    actual_toolchain_full.update(actual_toolchain)
    _enforce_toolchain(expected=expected_toolchain, actual=actual_toolchain_full, solvers_used=kernel_solvers)

    return {
        "model_id": model_id,
        "kernel_path": _relpath(kernel_path),
        "ir_hash": ir_hash,
        "ce_corpus_path": _relpath(corpus_path),
        "ce_corpus_sha256": corpus_sha256,
        "corpus_stats": {
            "total": stats.total,
            "per_action": dict(stats.per_action),
            "boundary_per_action": dict(stats.boundary_per_action),
            "unique_ids": stats.unique_ids,
            "unique_signatures": stats.unique_signatures,
            "unique_signature_ratio": stats.unique_signature_ratio,
        },
        "verification": verify_report,
    }


def main(argv: List[str]) -> int:
    p = argparse.ArgumentParser(description="Manifest-backed kernel assurance runner for ZenoDEX.")
    p.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Path to kernel_assurance_manifest.json")
    p.add_argument(
        "--kernel",
        action="append",
        default=None,
        help="Restrict to a specific model_id (repeatable). Default: all kernels in manifest.",
    )
    p.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    p.add_argument(
        "--evidence-bundle-out",
        default=None,
        help="If set, write deterministic verification bundles under this directory (one per kernel, keyed by IR hash).",
    )
    p.add_argument(
        "--produce-proofs",
        action="store_true",
        help="Ask solvers to produce UNSAT proofs when supported (stored in evidence bundles when enabled).",
    )
    p.add_argument(
        "--require-no-trust-proofs",
        action="store_true",
        help="Fail-closed if a produced proof contains an explicit trust step (best-effort heuristic).",
    )
    p.add_argument(
        "--fingerprint-proofs",
        action="store_true",
        help="Include proof hashes in the determinism fingerprint (stricter; may fail if solver proof output is nondeterministic).",
    )
    args = p.parse_args(argv)

    manifest_path = Path(args.manifest).expanduser().resolve()
    manifest = _load_manifest(manifest_path)
    manifest_sha256 = _sha256_file(manifest_path)

    manifest_version = manifest.get("manifest_version")
    if manifest_version != 1:
        raise AssuranceError(f"unsupported manifest_version: {manifest_version!r}")

    solvers = manifest.get("solvers", ["z3", "cvc5"])
    if not isinstance(solvers, list) or not solvers or not all(isinstance(s, str) and s for s in solvers):
        raise AssuranceError("manifest.solvers must be a non-empty list of strings")

    timeout_ms = _require_manifest_int(manifest.get("timeout_ms", 30000), name="manifest.timeout_ms")
    determinism_trials = _require_manifest_int(manifest.get("determinism_trials", 20), name="manifest.determinism_trials", lo=2)

    seeds = manifest.get("seeds", [0, 1, 2, 3, 4])
    if not isinstance(seeds, list) or not seeds or not all(isinstance(x, int) and not isinstance(x, bool) for x in seeds):
        raise AssuranceError("manifest.seeds must be a non-empty list of ints")

    kernels = manifest.get("kernels")
    if not isinstance(kernels, list) or not kernels:
        raise AssuranceError("manifest.kernels must be a non-empty list")

    expected_toolchain = manifest.get("toolchain")
    esso_checkout = _collect_esso_checkout_state()

    wanted = set(args.kernel or [])
    selected: List[Mapping[str, Any]] = []
    for k in kernels:
        if not isinstance(k, Mapping):
            continue
        mid = k.get("model_id")
        if not isinstance(mid, str) or not mid:
            continue
        if wanted and mid not in wanted:
            continue
        selected.append(k)

    if wanted and len(selected) != len(wanted):
        known = sorted({str(k.get("model_id")) for k in kernels if isinstance(k, Mapping)})
        missing = sorted(wanted - {str(k.get("model_id")) for k in selected})
        raise AssuranceError(f"unknown --kernel entries: {missing}; known: {known}")

    report: Dict[str, Any] = {
        "ok": True,
        "manifest_sha256": manifest_sha256,
        "manifest": _relpath(manifest_path),
        "manifest_version": 1,
        "repo_root": str(REPO_ROOT),
        "toolchain": esso_checkout,
        "kernels": [],
    }

    out_kernels: List[Dict[str, Any]] = []
    try:
        _enforce_toolchain(expected=expected_toolchain, actual=esso_checkout, solvers_used=[])
        bundle_base = None if args.evidence_bundle_out in (None, "") else (Path(args.evidence_bundle_out).expanduser().resolve())
        for k in selected:
            out_kernels.append(
                _run_one_kernel(
                    kernel_entry=k,
                    solvers=solvers,
                    timeout_ms=timeout_ms,
                    determinism_trials=determinism_trials,
                    seeds=seeds,
                    expected_toolchain=expected_toolchain,
                    actual_toolchain=esso_checkout,
                    evidence_bundle_base=bundle_base,
                    produce_proofs=bool(args.produce_proofs),
                    require_no_trust_proofs=bool(args.require_no_trust_proofs),
                    fingerprint_proofs=bool(args.fingerprint_proofs),
                )
            )
    except Exception as exc:
        report["ok"] = False
        report["error"] = str(exc)
        report["kernels"] = out_kernels
        sys.stdout.write(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
        sys.stdout.write("\n")
        return 2

    report["kernels"] = out_kernels
    sys.stdout.write(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
