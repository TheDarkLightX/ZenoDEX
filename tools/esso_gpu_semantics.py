#!/usr/bin/env python3
"""
Shared GPU semantics helpers for private-toolchain kernels (Torch MPS/CUDA).

This module powers `tools/esso_gpu_semantic_check.py` and can be imported by other
tools (e.g., hint ranking) to evaluate many candidate terms against a reference
model efficiently.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, MutableMapping, Optional, Sequence, Union


REPO_ROOT = Path(__file__).resolve().parents[1]
ESSO_ROOT = REPO_ROOT / "external" / "ESSO"


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise ValueError(msg)


def ensure_esso_on_path() -> None:
    if not ESSO_ROOT.exists():
        raise FileNotFoundError(f"toolchain not found at {ESSO_ROOT} (clone/update external/ESSO).")
    esso_str = str(ESSO_ROOT)
    if esso_str not in sys.path:
        sys.path.insert(0, esso_str)


def load_yaml(path: Path) -> Any:
    import yaml  # local import

    return yaml.safe_load(path.read_text(encoding="utf-8"))


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _try_import_torch() -> Optional[Any]:
    try:
        import torch  # type: ignore
    except Exception:
        return None
    return torch


@dataclass(frozen=True)
class TorchBackend:
    torch: Any
    device: Any
    name: str

    def synchronize(self) -> None:
        if self.name == "torch:mps":
            self.torch.mps.synchronize()
        elif self.name == "torch:cuda":
            self.torch.cuda.synchronize()


def pick_torch_backend(*, prefer_gpu: bool) -> TorchBackend:
    torch = _try_import_torch()
    _require(torch is not None, "torch is required (install PyTorch to use GPU semantics tooling)")

    if prefer_gpu and bool(getattr(torch.backends, "mps", None)) and torch.backends.mps.is_available():
        return TorchBackend(torch=torch, device=torch.device("mps"), name="torch:mps")
    if prefer_gpu and bool(getattr(torch, "cuda", None)) and torch.cuda.is_available():
        return TorchBackend(torch=torch, device=torch.device("cuda"), name="torch:cuda")
    return TorchBackend(torch=torch, device=torch.device("cpu"), name="torch:cpu")


def torch_full(be: TorchBackend, batch: int, *, value: Union[int, bool], dtype: Any) -> Any:
    return be.torch.full((batch,), value, device=be.device, dtype=dtype)


def torch_int(be: TorchBackend, batch: int, *, low: int, high_inclusive: int) -> Any:
    high = int(high_inclusive) + 1  # randint upper bound is exclusive
    return be.torch.randint(int(low), int(high), (batch,), device=be.device, dtype=be.torch.int64)


def torch_bool(be: TorchBackend, batch: int) -> Any:
    return (be.torch.randint(0, 2, (batch,), device=be.device, dtype=be.torch.int64) != 0)


def torch_euclid_div(be: TorchBackend, n: Any, d: Any) -> Any:
    torch = be.torch
    d0 = d == 0
    d_safe = torch.where(d0, torch.ones_like(d), d)
    q = torch.div(n, d_safe, rounding_mode="floor")
    r = n - q * d_safe
    q = torch.where(r < 0, q + 1, q)
    return torch.where(d0, torch.zeros_like(q), q)


def torch_mod(be: TorchBackend, n: Any, d: Any) -> Any:
    torch = be.torch
    ad = torch.abs(d)
    d0 = ad == 0
    ad_safe = torch.where(d0, torch.ones_like(ad), ad)
    r = torch.remainder(n, ad_safe)
    return torch.where(d0, torch.zeros_like(r), r)


def torch_eval_expr(be: TorchBackend, expr: Any, *, batch: int, state: Mapping[str, Any], params: Mapping[str, Any]) -> Any:
    """
    Evaluate a toolchain `Expr` over a batch of environments.

    Supported subset (DEX kernels):
    - literals, vars, params
    - ite
    - ops: not, and/or/xor/=>, =/!=/< <=/> >=, + - * min max, div, mod
    """

    torch = be.torch

    k = expr.kind
    if k == "var":
        name = expr.name or ""
        v = state.get(name)
        if v is None:
            raise ValueError(f"unknown var {name!r}")
        return v
    if k == "param":
        name = expr.name or ""
        v = params.get(name)
        if v is None:
            raise ValueError(f"unknown param {name!r}")
        return v
    if k == "bool":
        if not isinstance(expr.bool_value, bool):
            raise ValueError("invalid bool literal")
        return torch_full(be, batch, value=bool(expr.bool_value), dtype=torch.bool)
    if k == "const":
        if not isinstance(expr.const, int) or isinstance(expr.const, bool):
            raise ValueError("invalid int literal")
        return torch_full(be, batch, value=int(expr.const), dtype=torch.int64)
    if k == "enum":
        raise ValueError("enum not supported in batched evaluator")
    if k == "ite":
        if expr.cond is None or expr.then is None or expr.else_ is None:
            raise ValueError("malformed ite")
        c = torch_eval_expr(be, expr.cond, batch=batch, state=state, params=params).to(dtype=torch.bool)
        t = torch_eval_expr(be, expr.then, batch=batch, state=state, params=params)
        e = torch_eval_expr(be, expr.else_, batch=batch, state=state, params=params)
        return torch.where(c, t, e)
    if k != "op":
        raise ValueError(f"unsupported expr kind {k!r}")

    op = (expr.op or "").strip()
    args = list(expr.args or ())

    if op == "not":
        _require(len(args) == 1, "not expects 1 arg")
        a = torch_eval_expr(be, args[0], batch=batch, state=state, params=params).to(dtype=torch.bool)
        return torch.logical_not(a)

    if op in {"and", "or", "xor", "=>"}:
        if op == "=>" and len(args) != 2:
            raise ValueError("=> expects 2 args")
        if op != "=>" and len(args) < 2:
            raise ValueError(f"{op} expects >=2 args")
        vals = [torch_eval_expr(be, a, batch=batch, state=state, params=params).to(dtype=torch.bool) for a in args]
        if op == "and":
            out = vals[0]
            for v in vals[1:]:
                out = torch.logical_and(out, v)
            return out
        if op == "or":
            out = vals[0]
            for v in vals[1:]:
                out = torch.logical_or(out, v)
            return out
        if op == "xor":
            out = vals[0]
            for v in vals[1:]:
                out = torch.logical_xor(out, v)
            return out
        return torch.logical_or(torch.logical_not(vals[0]), vals[1])

    if op in {"=", "!=", "<", "<=", ">", ">="}:
        _require(len(args) == 2, f"{op} expects 2 args")
        a0 = torch_eval_expr(be, args[0], batch=batch, state=state, params=params)
        a1 = torch_eval_expr(be, args[1], batch=batch, state=state, params=params)
        if op == "=":
            return torch.eq(a0, a1)
        if op == "!=":
            return torch.ne(a0, a1)
        a0 = a0.to(dtype=torch.int64)
        a1 = a1.to(dtype=torch.int64)
        if op == "<":
            return torch.lt(a0, a1)
        if op == "<=":
            return torch.le(a0, a1)
        if op == ">":
            return torch.gt(a0, a1)
        return torch.ge(a0, a1)

    if op == "div":
        _require(len(args) == 2, "div expects 2 args")
        n = torch_eval_expr(be, args[0], batch=batch, state=state, params=params).to(dtype=torch.int64)
        d = torch_eval_expr(be, args[1], batch=batch, state=state, params=params).to(dtype=torch.int64)
        return torch_euclid_div(be, n, d)

    if op == "mod":
        _require(len(args) == 2, "mod expects 2 args")
        n = torch_eval_expr(be, args[0], batch=batch, state=state, params=params).to(dtype=torch.int64)
        d = torch_eval_expr(be, args[1], batch=batch, state=state, params=params).to(dtype=torch.int64)
        return torch_mod(be, n, d)

    if op in {"+", "-", "*", "min", "max"}:
        _require(len(args) >= 2, f"{op} expects >=2 args")
        vals = [torch_eval_expr(be, a, batch=batch, state=state, params=params).to(dtype=torch.int64) for a in args]
        if op == "+":
            out = vals[0]
            for v in vals[1:]:
                out = out + v
            return out
        if op == "-":
            out = vals[0]
            for v in vals[1:]:
                out = out - v
            return out
        if op == "*":
            out = vals[0]
            for v in vals[1:]:
                out = out * v
            return out
        if op == "min":
            out = vals[0]
            for v in vals[1:]:
                out = torch.minimum(out, v)
            return out
        out = vals[0]
        for v in vals[1:]:
            out = torch.maximum(out, v)
        return out

    raise ValueError(f"unsupported op {op!r}")


def torch_sample_env(be: TorchBackend, model: Any, act: Any, *, batch: int) -> tuple[dict[str, Any], dict[str, Any]]:
    nt = model.named_types()
    state: dict[str, Any] = {}
    for v in model.state_vars:
        t = v.type.resolved(nt) if v.type.kind == "ref" else v.type
        if t.kind == "int":
            _require(t.min is not None and t.max is not None, f"missing int bounds for state var {v.id!r}")
            state[v.id] = torch_int(be, batch, low=int(t.min), high_inclusive=int(t.max))
        elif t.kind == "bool":
            state[v.id] = torch_bool(be, batch)
        else:
            raise ValueError(f"unsupported state var type for {v.id!r}: {t.kind}")

    params: dict[str, Any] = {}
    for p in act.params:
        t = p.type.resolved(nt) if p.type.kind == "ref" else p.type
        if t.kind == "int":
            _require(t.min is not None and t.max is not None, f"missing int bounds for param {p.id!r}")
            params[p.id] = torch_int(be, batch, low=int(t.min), high_inclusive=int(t.max))
        elif t.kind == "bool":
            params[p.id] = torch_bool(be, batch)
        else:
            raise ValueError(f"unsupported param type for {p.id!r}: {t.kind}")
    return state, params


def find_action(model: Any, action_id: str) -> Any:
    for a in model.actions:
        if a.id == action_id:
            return a
    raise ValueError(f"unknown action {action_id!r} in model")


def find_field_expr(model: Any, action_id: str, field: str) -> Any:
    act = find_action(model, action_id)
    for e in act.effects:
        if e.id == field:
            return e.expr
    for u in act.updates:
        if u.var == field:
            return u.expr
    raise ValueError(f"field {field!r} not found in action {action_id!r} (effect or update)")


def rewrite_vars_to_params(expr: Any, *, param_ids: set[str]) -> Any:
    ensure_esso_on_path()
    from ESSO.cgs.sygus import _rewrite_vars_to_params as _rw  # type: ignore

    return _rw(expr, params=param_ids).canonicalized()


def parse_term_to_expr(*, model: Any, synth: Any, hole_id: str, term: str) -> Any:
    ensure_esso_on_path()
    from ESSO.cgs.llm_hints import InfixParseError, SexpParseError, parse_infix, parse_one  # type: ignore
    from ESSO.cgs.sygus import _hole_arg_order, _parse_define_fun_solution  # type: ignore

    hole = next((h for h in synth.holes if h.hole_id == hole_id), None)
    if hole is None:
        raise ValueError(f"unknown hole_id {hole_id!r} in synth spec")

    try:
        body = parse_one(term)
    except SexpParseError:
        try:
            body = parse_infix(term)
        except InfixParseError as e:
            raise ValueError(f"failed to parse term: {e}") from e

    args = _hole_arg_order(hole=hole, model=model)
    constants = {"BPS_DENOM": 10000}
    expr = _parse_define_fun_solution(hole_id=hole_id, args=args, body=body, constants=constants).canonicalized()
    return expr


def self_check_against_esso_interpreter(
    *,
    model: Any,
    expr: Any,
    state_t: Mapping[str, Any],
    params_t: Mapping[str, Any],
    expected_out_t: Any,
    indices: Sequence[int],
) -> None:
    ensure_esso_on_path()
    from ESSO.kernel.interpreter import eval_expr as esso_eval_expr  # type: ignore

    for i in indices:
        s = {k: int(v[i].detach().to("cpu").item()) for k, v in state_t.items()}
        p = {k: int(v[i].detach().to("cpu").item()) for k, v in params_t.items()}
        out = esso_eval_expr(expr, state=s, params=p, ir=model, expected=None)
        if getattr(out, "code", None) is not None:
            raise RuntimeError(f"toolchain interpreter error during self-check at i={i}: {out.code} {out.message}")
        want = int(expected_out_t[i].detach().to("cpu").item())
        got = int(out)  # type: ignore[arg-type]
        if got != want:
            raise RuntimeError(f"batched evaluator mismatch at i={i}: torch={want} esso={got}")


@dataclass(frozen=True)
class Counterexample:
    idx: int
    state: dict[str, int]
    params: dict[str, int]
    expected: int
    got: int


@dataclass(frozen=True)
class TermCheckResult:
    term: str
    ok: bool
    mismatch_count: int
    mismatch_rate: float
    counterexample: Optional[Counterexample]
    error: Optional[str]


@dataclass(frozen=True)
class SemanticCheckResult:
    ok: bool
    backend: str
    samples: int
    mismatch_count: int
    mismatch_rate: float
    counterexample: Optional[Counterexample]


@dataclass
class PreparedSemanticCheck:
    backend: TorchBackend
    reference: Any
    model: Any
    synth: Any
    action_id: str
    field: str
    hole_id: str
    state: Mapping[str, Any]
    params: Mapping[str, Any]
    ref_out: Any

    def check_term(self, term: str, *, self_check: bool = False) -> TermCheckResult:
        try:
            act_ref = find_action(self.reference, self.action_id)
            raw_expr = parse_term_to_expr(model=self.model, synth=self.synth, hole_id=self.hole_id, term=term)
            cand_expr = rewrite_vars_to_params(raw_expr, param_ids={p.id for p in act_ref.params})

            want = int(self.ref_out.shape[0])
            cand_out = torch_eval_expr(
                self.backend, cand_expr, batch=want, state=self.state, params=self.params
            ).to(dtype=self.backend.torch.int64)
            self.backend.synchronize()

            mismatch = self.backend.torch.ne(self.ref_out, cand_out)
            mismatch_count = int(mismatch.sum().detach().to("cpu").item())

            ce: Optional[Counterexample] = None
            if mismatch_count > 0:
                first = int(mismatch.nonzero(as_tuple=False)[0].detach().to("cpu").item())
                ce_state = {k: int(v[first].detach().to("cpu").item()) for k, v in self.state.items()}
                ce_params = {k: int(v[first].detach().to("cpu").item()) for k, v in self.params.items()}
                ce = Counterexample(
                    idx=first,
                    state=ce_state,
                    params=ce_params,
                    expected=int(self.ref_out[first].detach().to("cpu").item()),
                    got=int(cand_out[first].detach().to("cpu").item()),
                )

            if self_check:
                indices = list(range(0, min(10, want)))
                self_check_against_esso_interpreter(
                    model=self.reference,
                    expr=cand_expr,
                    state_t=self.state,
                    params_t=self.params,
                    expected_out_t=cand_out,
                    indices=indices,
                )

            return TermCheckResult(
                term=term,
                ok=(mismatch_count == 0),
                mismatch_count=mismatch_count,
                mismatch_rate=(float(mismatch_count) / float(want)),
                counterexample=ce,
                error=None,
            )
        except Exception as exc:
            return TermCheckResult(
                term=term,
                ok=False,
                mismatch_count=0,
                mismatch_rate=1.0,
                counterexample=None,
                error=str(exc),
            )


def prepare_semantic_check(
    *,
    model: Any,
    synth: Any,
    reference: Any,
    hole_id: str,
    action_id: str,
    field: str,
    samples: int,
    chunk: int,
    prefer_gpu: bool,
    seed: Optional[int] = 0,
    self_check: bool = False,
) -> PreparedSemanticCheck:
    be = pick_torch_backend(prefer_gpu=prefer_gpu)
    if seed is not None:
        be.torch.manual_seed(int(seed))

    act_ref = find_action(reference, action_id)
    ref_expr = find_field_expr(reference, action_id, field)

    want = int(samples)
    chunk = int(chunk)

    states_chunks: MutableMapping[str, list[Any]] = {}
    params_chunks: MutableMapping[str, list[Any]] = {}

    kept = 0
    rounds = 0
    max_rounds = 50
    while kept < want and rounds < max_rounds:
        rounds += 1
        st, pa = torch_sample_env(be, reference, act_ref, batch=chunk)

        ok = torch_full(be, chunk, value=True, dtype=be.torch.bool)
        for inv in reference.invariants:
            ok = be.torch.logical_and(ok, torch_eval_expr(be, inv.expr, batch=chunk, state=st, params=pa).to(dtype=be.torch.bool))
        ok = be.torch.logical_and(ok, torch_eval_expr(be, act_ref.guard, batch=chunk, state=st, params=pa).to(dtype=be.torch.bool))

        idx = ok.nonzero(as_tuple=False).flatten()
        if idx.numel() <= 0:
            continue
        take = min(want - kept, int(idx.numel()))
        idx = idx[:take]

        for k, v in st.items():
            states_chunks.setdefault(k, []).append(v.index_select(0, idx))
        for k, v in pa.items():
            params_chunks.setdefault(k, []).append(v.index_select(0, idx))

        kept += take

    _require(kept >= want, f"failed to collect enough applicable samples: got {kept}, want {want}")

    state = {k: be.torch.cat(vs, dim=0)[:want] for k, vs in states_chunks.items()}
    params = {k: be.torch.cat(vs, dim=0)[:want] for k, vs in params_chunks.items()}

    ref_out = torch_eval_expr(be, ref_expr, batch=want, state=state, params=params).to(dtype=be.torch.int64)
    be.synchronize()

    if self_check:
        indices = list(range(0, min(10, want)))
        self_check_against_esso_interpreter(
            model=reference,
            expr=ref_expr,
            state_t=state,
            params_t=params,
            expected_out_t=ref_out,
            indices=indices,
        )

    return PreparedSemanticCheck(
        backend=be,
        reference=reference,
        model=model,
        synth=synth,
        action_id=action_id,
        field=field,
        hole_id=hole_id,
        state=state,
        params=params,
        ref_out=ref_out,
    )


def semantic_check_single(
    *,
    model_path: Path,
    synth_path: Path,
    reference_path: Path,
    hole_id: str,
    action_id: str,
    field: str,
    term: str,
    samples: int,
    chunk: int,
    prefer_gpu: bool,
    seed: Optional[int] = 0,
    self_check: bool = False,
) -> SemanticCheckResult:
    ensure_esso_on_path()
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.cgs.schema import SynthIR  # type: ignore

    model = CandidateIR.from_json_dict(load_yaml(model_path)).canonicalized()
    synth = SynthIR.from_json_dict(load_json(synth_path))
    reference = CandidateIR.from_json_dict(load_yaml(reference_path)).canonicalized()

    prep = prepare_semantic_check(
        model=model,
        synth=synth,
        reference=reference,
        hole_id=hole_id,
        action_id=action_id,
        field=field,
        samples=samples,
        chunk=chunk,
        prefer_gpu=prefer_gpu,
        seed=seed,
        self_check=self_check,
    )
    term_res = prep.check_term(term, self_check=self_check)
    ce = term_res.counterexample
    return SemanticCheckResult(
        ok=term_res.ok,
        backend=prep.backend.name,
        samples=samples,
        mismatch_count=term_res.mismatch_count,
        mismatch_rate=term_res.mismatch_rate,
        counterexample=ce,
    )
