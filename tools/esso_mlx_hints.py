#!/usr/bin/env python3
"""
ESSO Neural Hint Generator - MLX Edition (Apple Silicon)

Uses local MLX models (Qwen 7B/80B) to generate high-quality synthesis hints.
Fully local, no API calls. Supports batch processing and two-stage model selection.

Usage:
    # Single spec
    python esso_mlx_hints.py hints-only src/kernels/dex/fee_calculator_hole.yaml \\
        src/kernels/dex/fee_calculator_hole.synth.json

    # Batch all specs with two-stage selection
    python esso_mlx_hints.py batch src/kernels/dex --samples 3 --two-stage

    # Report on run results
    python esso_mlx_hints.py report runs/ngs/<run_id>
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import Optional


# Model configurations
MODEL_7B = "/Users/danax/projects/TCEModel/models/Qwen2.5-7B-Instruct"
MODEL_80B = "/Users/danax/projects/TCEModel/models/Qwen3-Next-80B-A3B-Instruct-qx64-mlx"
DEFAULT_MLX_MODEL = MODEL_80B


@dataclass
class CandidateResult:
    """Result from a single candidate generation."""
    spec_name: str
    hole_id: str
    model: str
    sample_idx: int
    candidate_idx: int
    term: str
    gen_ms: float
    valid_cheap: Optional[bool] = None
    valid_full: Optional[bool] = None
    valid_examples: Optional[bool] = None
    examples_mismatch_rate: Optional[float] = None
    examples_backend: Optional[str] = None
    error: Optional[str] = None


@dataclass
class HoleResult:
    """Aggregated result for a single hole."""
    spec_name: str
    hole_id: str
    best_term: Optional[str]
    best_model: Optional[str]
    candidates_tried: int
    valid_cheap_count: int
    valid_full_count: int
    total_gen_ms: float


def load_mlx_model(model_path: str = DEFAULT_MLX_MODEL):
    """Load MLX model from local path."""
    from mlx_lm import load
    print(f"Loading MLX model: {model_path}")
    model, tokenizer = load(model_path)
    return model, tokenizer


def generate_text(model, tokenizer, prompt: str, max_tokens: int = 300,
                  temp: float = 0.7, top_p: float = 0.9) -> str:
    """Generate text with MLX model using temperature sampling."""
    from mlx_lm import generate
    from mlx_lm.sample_utils import make_sampler

    sampler = make_sampler(temp=temp, top_p=top_p)
    response = generate(
        model, tokenizer,
        prompt=prompt,
        max_tokens=max_tokens,
        verbose=False,
        sampler=sampler,
    )
    return response


def build_synthesis_prompt(hole: dict, model_yaml: str, synth_spec: dict) -> str:
    """Build prompt for synthesis model."""
    grammar = None
    for g in synth_spec.get("grammars", []):
        if g.get("grammar_id") == hole.get("grammar_id"):
            grammar = g
            break

    productions = json.dumps(grammar["productions"], indent=2) if grammar else "{}"

    return f"""<|im_start|>system
You are an expert in formal verification and program synthesis. You generate expressions that satisfy formal specifications.<|im_end|>
<|im_start|>user
I need to synthesize an expression for a formal verification kernel.

## Hole Specification
- Hole ID: {hole['hole_id']}
- Type: {hole.get('type', 'Int')}
- Used in fields: {hole.get('used_in', [])}
- Semantic constraints: {hole.get('semantic_constraints', [])}

## Grammar (expressions MUST match these productions)
{productions}

## Kernel Context (YAML)
```yaml
{model_yaml[:1500]}
```

## Task
Generate exactly 5 candidate expressions that:
1. STRICTLY follow the grammar productions
2. Satisfy all semantic constraints
3. Are likely correct for formal verification

Output ONLY a JSON array of 5 strings, no explanation:
["expr1", "expr2", "expr3", "expr4", "expr5"]<|im_end|>
<|im_start|>assistant
"""


def extract_candidates(response: str) -> list[str]:
    """Extract candidate expressions from model response."""
    match = re.search(r'\[.*?\]', response, re.DOTALL)
    if match:
        try:
            parsed = json.loads(match.group())
            if isinstance(parsed, list):
                return [str(x) for x in parsed[:5]]
        except json.JSONDecodeError:
            pass
    candidates = re.findall(r'"([^"]+)"', response)
    return candidates[:5]


def compute_esso_hashes(model_path: str, synth_path: str) -> tuple[str, str]:
    """Compute ESSO model and synth hashes."""
    import yaml
    try:
        from ESSO.evolve import ir_hash
        from ESSO.cgs.schema import SynthIR, synth_hash
        from ESSO.ir.schema import CandidateIR

        with open(model_path) as f:
            model = CandidateIR.from_json_dict(yaml.safe_load(f)).canonicalized()
        with open(synth_path) as f:
            synth = SynthIR.from_json_dict(json.load(f))
        return ir_hash(model), synth_hash(synth)
    except ImportError:
        esso_dir = Path(__file__).parent.parent / "external" / "ESSO"
        venv_python = esso_dir / ".venv" / "bin" / "python"
        result = subprocess.run(
            [str(venv_python), "-c", f"""
import json, yaml
from ESSO.evolve import ir_hash
from ESSO.cgs.schema import SynthIR, synth_hash
from ESSO.ir.schema import CandidateIR
with open('{model_path}') as f:
    model = CandidateIR.from_json_dict(yaml.safe_load(f)).canonicalized()
with open('{synth_path}') as f:
    synth = SynthIR.from_json_dict(json.load(f))
print(ir_hash(model))
print(synth_hash(synth))
"""],
            capture_output=True, text=True,
            cwd=str(Path(__file__).parent.parent),
            env={**os.environ, "PYTHONPATH": str(esso_dir)}
        )
        if result.returncode == 0:
            lines = result.stdout.strip().split('\n')
            return lines[0], lines[1]
        raise RuntimeError(f"Failed to compute hashes: {result.stderr}")


def validate_cheap(term: str, model_path: str, synth_path: str, hole_id: str) -> tuple[bool, str]:
    """
    Cheap validation: parse + grammar check via ESSO hint loader.
    Returns (valid, error_message).
    """
    esso_dir = Path(__file__).parent.parent / "external" / "ESSO"
    venv_python = esso_dir / ".venv" / "bin" / "python"

    # Create temporary hints file
    import tempfile
    model_hash, synth_hash_val = compute_esso_hashes(model_path, synth_path)
    hints = {
        "schema": "esso-llm-hints/v1",
        "model_hash": model_hash,
        "synth_hash": synth_hash_val,
        "holes": {hole_id: {"term": term, "source": "validation", "rank": 0}}
    }

    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(hints, f)
        hints_path = f.name

    try:
        result = subprocess.run(
            [str(venv_python), "-c", f"""
import json, yaml
from ESSO.cgs.llm_hints import load_llm_hints
from ESSO.cgs.schema import SynthIR
from ESSO.ir.schema import CandidateIR
with open('{model_path}') as f:
    model = CandidateIR.from_json_dict(yaml.safe_load(f))
with open('{synth_path}') as f:
    synth = SynthIR.from_json_dict(json.load(f))
hints = load_llm_hints('{hints_path}', model, synth)
print('OK' if hints else 'FAIL')
"""],
            capture_output=True, text=True, timeout=10,
            env={**os.environ, "PYTHONPATH": str(esso_dir)}
        )
        if result.returncode == 0 and 'OK' in result.stdout:
            return True, ""
        return False, result.stderr or result.stdout
    except subprocess.TimeoutExpired:
        return False, "Validation timeout"
    except Exception as e:
        return False, str(e)
    finally:
        os.unlink(hints_path)


def validate_full(term: str, model_path: str, synth_path: str, hole_id: str,
                  timeout_ms: int = 5000) -> tuple[bool, str]:
    """
    Full validation: run ESSO synth in hint-only mode with limited search.
    Returns (valid, error_message).
    """
    esso_dir = Path(__file__).parent.parent / "external" / "ESSO"
    venv_python = esso_dir / ".venv" / "bin" / "python"

    import tempfile
    model_hash, synth_hash_val = compute_esso_hashes(model_path, synth_path)
    hints = {
        "schema": "esso-llm-hints/v1",
        "model_hash": model_hash,
        "synth_hash": synth_hash_val,
        "holes": {hole_id: {"term": term, "source": "validation", "rank": 0}}
    }

    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(hints, f)
        hints_path = f.name

    with tempfile.TemporaryDirectory() as out_dir:
        try:
            cmd = [
                str(venv_python), "-m", "ESSO", "synth",
                model_path, synth_path,
                "--llm-hints", hints_path,
                "--output", out_dir,
                "--timeout-ms", str(timeout_ms),
            ]
            result = subprocess.run(
                cmd,
                capture_output=True, text=True,
                timeout=timeout_ms / 1000 + 5,
                env={**os.environ, "PYTHONPATH": str(esso_dir)}
            )
            if result.returncode == 0:
                return True, ""
            return False, result.stderr or result.stdout
        except subprocess.TimeoutExpired:
            return False, "ESSO synth timeout"
        except Exception as e:
            return False, str(e)
        finally:
            os.unlink(hints_path)


def infer_reference_model_path(model_path: str) -> Optional[str]:
    """
    Infer a reference model YAML path for a given hole model YAML.

    Convention: <prefix>_hole*.yaml -> <prefix>_ref.yaml
    Example: cpmm_output_amount_hole_v2.yaml -> cpmm_output_amount_ref.yaml
    """
    p = Path(model_path)
    name = p.name
    if "_hole" not in name:
        return None
    prefix = name.split("_hole", 1)[0]
    ref = p.with_name(prefix + "_ref.yaml")
    return str(ref) if ref.exists() else None


def validate_examples_terms(
    *,
    model_path: str,
    synth_path: str,
    reference_path: str,
    hole_id: str,
    action_id: str,
    field: str,
    terms: list[str],
    samples: int = 50_000,
    chunk: int = 100_000,
    prefer_gpu: bool = True,
) -> tuple[dict[str, bool], dict[str, float], str, Optional[str]]:
    """
    Example-based semantic validation against a reference kernel.

    Returns:
      - ok_by_term: term -> bool (zero mismatches)
      - mismatch_rate_by_term: term -> mismatch_rate
      - backend_name
      - error (if the whole validation step failed)
    """
    try:
        from esso_gpu_semantics import ensure_esso_on_path, load_json as _load_json, load_yaml as _load_yaml, prepare_semantic_check  # type: ignore

        ensure_esso_on_path()
        from ESSO.cgs.schema import SynthIR  # type: ignore
        from ESSO.ir.schema import CandidateIR  # type: ignore

        model = CandidateIR.from_json_dict(_load_yaml(Path(model_path))).canonicalized()
        synth = SynthIR.from_json_dict(_load_json(Path(synth_path)))
        reference = CandidateIR.from_json_dict(_load_yaml(Path(reference_path))).canonicalized()

        prep = prepare_semantic_check(
            model=model,
            synth=synth,
            reference=reference,
            hole_id=hole_id,
            action_id=action_id,
            field=field,
            samples=int(samples),
            chunk=int(chunk),
            prefer_gpu=bool(prefer_gpu),
            seed=0,
            self_check=False,
        )
        ok_by_term: dict[str, bool] = {}
        mismatch_rate_by_term: dict[str, float] = {}
        for term in terms:
            res = prep.check_term(term, self_check=False)
            ok_by_term[term] = bool(res.ok)
            mismatch_rate_by_term[term] = float(res.mismatch_rate)
        return ok_by_term, mismatch_rate_by_term, prep.backend.name, None
    except Exception as exc:
        return {}, {}, "unknown", str(exc)


def generate_hints_single(model_path: str, synth_path: str, mlx_model_name: str,
                          samples: int = 1, temp: float = 0.7, top_p: float = 0.9,
                          validate: str = "none") -> dict:
    """
    Generate hints for a single spec with optional multi-sampling.
    Returns ESSO-compatible hints dict.
    """
    with open(model_path) as f:
        model_yaml = f.read()
    with open(synth_path) as f:
        synth_spec = json.load(f)

    model, tokenizer = load_mlx_model(mlx_model_name)
    model_hash, synth_hash_val = compute_esso_hashes(model_path, synth_path)

    hints = {
        "schema": "esso-llm-hints/v1",
        "model_hash": model_hash,
        "synth_hash": synth_hash_val,
        "holes": {}
    }

    all_candidates: dict[str, list[CandidateResult]] = {}

    reference_path = infer_reference_model_path(model_path) if validate == "examples" else None
    if validate == "examples" and reference_path is None:
        print("  Note: no *_ref.yaml found; skipping example validation.")

    for hole in synth_spec.get("holes", []):
        hole_id = hole['hole_id']
        print(f"\n{'='*50}")
        print(f"Generating hints for: {hole_id} (samples={samples})")
        print(f"{'='*50}")

        prompt = build_synthesis_prompt(hole, model_yaml, synth_spec)
        all_candidates[hole_id] = []

        for sample_idx in range(samples):
            start = time.time()
            response = generate_text(model, tokenizer, prompt, max_tokens=200,
                                     temp=temp, top_p=top_p)
            gen_ms = (time.time() - start) * 1000

            candidates = extract_candidates(response)
            print(f"  Sample {sample_idx+1}: {candidates[:2]}...")

            for cand_idx, term in enumerate(candidates):
                result = CandidateResult(
                    spec_name=Path(model_path).stem,
                    hole_id=hole_id,
                    model=Path(mlx_model_name).name,
                    sample_idx=sample_idx,
                    candidate_idx=cand_idx,
                    term=term,
                    gen_ms=gen_ms / len(candidates),
                )

                if validate in ("cheap", "full", "examples"):
                    valid, err = validate_cheap(term, model_path, synth_path, hole_id)
                    result.valid_cheap = valid
                    if not valid:
                        result.error = err

                if validate == "full" and result.valid_cheap:
                    valid, err = validate_full(term, model_path, synth_path, hole_id)
                    result.valid_full = valid
                    if not valid:
                        result.error = err

                all_candidates[hole_id].append(result)

        if validate == "examples" and reference_path is not None:
            used_in = hole.get("used_in", [])
            if not used_in:
                print(f"  Note: hole {hole_id} has no used_in; skipping example validation.")
            else:
                action_id = used_in[0].get("action")
                field = used_in[0].get("field")
                if not action_id or not field:
                    print(f"  Note: hole {hole_id} missing action/field in used_in; skipping example validation.")
                else:
                    cheap_ok_terms = [c.term for c in all_candidates[hole_id] if c.valid_cheap]
                    if cheap_ok_terms:
                        ok_by_term, mismatch_rate_by_term, backend_name, err = validate_examples_terms(
                            model_path=model_path,
                            synth_path=synth_path,
                            reference_path=reference_path,
                            hole_id=hole_id,
                            action_id=str(action_id),
                            field=str(field),
                            terms=cheap_ok_terms,
                            samples=50_000,
                            chunk=100_000,
                            prefer_gpu=True,
                        )
                        if err is not None:
                            print(f"  Example validation failed: {err}")
                        else:
                            for c in all_candidates[hole_id]:
                                if not c.valid_cheap:
                                    continue
                                c.valid_examples = ok_by_term.get(c.term)
                                c.examples_mismatch_rate = mismatch_rate_by_term.get(c.term)
                                c.examples_backend = backend_name

        # Aggregate: pick best candidate
        best = aggregate_candidates(all_candidates[hole_id])
        if best:
            hints["holes"][hole_id] = {
                "term": best.term,
                "source": f"mlx:{best.model}",
                "rank": 0,
            }
            print(f"  Best: {best.term}")

    return hints


def aggregate_candidates(candidates: list[CandidateResult]) -> Optional[CandidateResult]:
    """
    Aggregate candidates and pick the best one.
    Strategy: prefer validated > frequent > simple > first.
    """
    if not candidates:
        return None

    # Group by term
    term_counts: dict[str, list[CandidateResult]] = {}
    for c in candidates:
        term_counts.setdefault(c.term, []).append(c)

    def score(term: str, results: list[CandidateResult]) -> tuple:
        # Higher is better: (full_valid, examples_valid, cheap_valid, frequency, -mismatch_rate, -complexity, -first_seen)
        any_full = any(r.valid_full for r in results)
        any_examples = any(r.valid_examples for r in results)
        any_cheap = any(r.valid_cheap for r in results)
        mismatch_rate = min((r.examples_mismatch_rate for r in results if r.examples_mismatch_rate is not None), default=1.0)
        freq = len(results)
        complexity = len(term)
        first_idx = min(r.sample_idx * 10 + r.candidate_idx for r in results)
        return (any_full, any_examples, any_cheap, freq, -mismatch_rate, -complexity, -first_idx)

    best_term = max(term_counts.keys(), key=lambda t: score(t, term_counts[t]))
    return term_counts[best_term][0]


def discover_specs(spec_dir: str) -> list[tuple[str, str]]:
    """Discover all hole specs in a directory."""
    spec_path = Path(spec_dir)
    specs = []
    for yaml_file in sorted(spec_path.glob("*_hole.yaml")):
        synth_file = yaml_file.with_suffix(".synth.json")
        if synth_file.exists():
            specs.append((str(yaml_file), str(synth_file)))
    return specs


def run_batch(spec_dir: str, samples: int = 3, two_stage: bool = False,
              validate: str = "cheap", output_dir: Optional[str] = None) -> dict:
    """
    Batch process all specs in directory.
    Two-stage: try 7B first, escalate to 80B on failure.
    """
    specs = discover_specs(spec_dir)
    print(f"Discovered {len(specs)} hole specs")

    run_id = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = Path(output_dir or f"runs/ngs/{run_id}")
    out_path.mkdir(parents=True, exist_ok=True)

    results = {
        "run_id": run_id,
        "specs_count": len(specs),
        "samples": samples,
        "two_stage": two_stage,
        "validate": validate,
        "specs": {},
        "summary": {"success": 0, "failed": 0, "total_ms": 0}
    }

    for model_yaml, synth_json in specs:
        spec_name = Path(model_yaml).stem
        print(f"\n{'#'*60}")
        print(f"# Processing: {spec_name}")
        print(f"{'#'*60}")

        spec_result = {"model_yaml": model_yaml, "synth_json": synth_json}
        start = time.time()

        if two_stage:
            # Stage 1: Try 7B
            print(f"\n[Stage 1] Trying 7B model...")
            hints = generate_hints_single(
                model_yaml, synth_json, MODEL_7B,
                samples=samples, validate=validate
            )

            # Check if all holes have valid hints
            all_valid = all(
                h.get("term") for h in hints.get("holes", {}).values()
            )

            if not all_valid:
                # Stage 2: Escalate to 80B
                print(f"\n[Stage 2] Escalating to 80B model...")
                hints = generate_hints_single(
                    model_yaml, synth_json, MODEL_80B,
                    samples=max(1, samples // 2), validate=validate
                )
                spec_result["model_used"] = "80B"
            else:
                spec_result["model_used"] = "7B"
        else:
            # Single model run
            hints = generate_hints_single(
                model_yaml, synth_json, DEFAULT_MLX_MODEL,
                samples=samples, validate=validate
            )
            spec_result["model_used"] = Path(DEFAULT_MLX_MODEL).name

        elapsed_ms = (time.time() - start) * 1000
        spec_result["elapsed_ms"] = elapsed_ms
        spec_result["holes"] = hints.get("holes", {})
        spec_result["success"] = bool(hints.get("holes"))

        # Save individual hints
        hints_path = out_path / f"{spec_name}.hints.json"
        with open(hints_path, 'w') as f:
            json.dump(hints, f, indent=2)
        spec_result["hints_path"] = str(hints_path)

        results["specs"][spec_name] = spec_result
        results["summary"]["total_ms"] += elapsed_ms
        if spec_result["success"]:
            results["summary"]["success"] += 1
        else:
            results["summary"]["failed"] += 1

    # Save summary
    summary_path = out_path / "summary.json"
    with open(summary_path, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\n{'='*60}")
    print(f"BATCH COMPLETE")
    print(f"{'='*60}")
    print(f"Success: {results['summary']['success']}/{len(specs)}")
    print(f"Total time: {results['summary']['total_ms']/1000:.1f}s")
    print(f"Output: {out_path}")

    return results


def run_esso_synth(model_path: str, synth_path: str, hints_path: str, output_dir: str) -> bool:
    """Run ESSO synthesis with hints."""
    esso_path = Path(__file__).parent.parent / "external" / "ESSO"
    venv_python = esso_path / ".venv" / "bin" / "python"

    cmd = [
        str(venv_python), "-m", "ESSO", "synth",
        model_path, synth_path,
        "--llm-hints", hints_path,
        "--ice",
        "--output", output_dir,
    ]

    print(f"\nRunning ESSO: {' '.join(cmd)}")
    env = os.environ.copy()
    env["PYTHONPATH"] = str(esso_path)

    result = subprocess.run(cmd, env=env, capture_output=True, text=True)
    print(result.stdout)
    if result.stderr:
        print(result.stderr)

    return result.returncode == 0


def generate_report(run_dir: str) -> None:
    """Generate report from batch run results."""
    run_path = Path(run_dir)
    summary_path = run_path / "summary.json"

    if not summary_path.exists():
        print(f"No summary.json found in {run_dir}")
        return

    with open(summary_path) as f:
        results = json.load(f)

    print(f"\n{'='*60}")
    print(f"BATCH RUN REPORT: {results['run_id']}")
    print(f"{'='*60}")
    print(f"Specs: {results['specs_count']}")
    print(f"Samples per spec: {results['samples']}")
    print(f"Two-stage: {results['two_stage']}")
    print(f"Validation: {results['validate']}")
    print()

    print(f"{'Spec':<40} {'Model':<10} {'Time':<10} {'Status'}")
    print("-" * 70)
    for spec_name, spec_result in results["specs"].items():
        model = spec_result.get("model_used", "?")[:8]
        time_s = spec_result.get("elapsed_ms", 0) / 1000
        status = "OK" if spec_result.get("success") else "FAIL"
        holes = len(spec_result.get("holes", {}))
        print(f"{spec_name:<40} {model:<10} {time_s:>6.1f}s   {status} ({holes} holes)")

    print()
    print(f"Summary: {results['summary']['success']}/{results['specs_count']} succeeded")
    print(f"Total time: {results['summary']['total_ms']/1000:.1f}s")


def main():
    parser = argparse.ArgumentParser(
        description="ESSO MLX Hint Generator (Apple Silicon)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Single spec with 80B model
    python esso_mlx_hints.py hints-only model.yaml model.synth.json

    # Batch all specs with two-stage (7B first, 80B fallback)
    python esso_mlx_hints.py batch src/kernels/dex --samples 3 --two-stage

    # Report on previous run
    python esso_mlx_hints.py report runs/ngs/20240101_120000
        """
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # hints-only command
    hints_parser = subparsers.add_parser("hints-only", help="Generate hints for single spec")
    hints_parser.add_argument("model", help="Path to model.yaml")
    hints_parser.add_argument("synth", help="Path to synth.json")
    hints_parser.add_argument("--mlx-model", default=DEFAULT_MLX_MODEL)
    hints_parser.add_argument("--samples", type=int, default=1)
    hints_parser.add_argument("--temp", type=float, default=0.7)
    hints_parser.add_argument("--top-p", type=float, default=0.9)
    hints_parser.add_argument("--validate", choices=["none", "cheap", "full", "examples"], default="none")
    hints_parser.add_argument("--hints-out", default=None)

    # synth command
    synth_parser = subparsers.add_parser("synth", help="Generate hints and run ESSO synthesis")
    synth_parser.add_argument("model", help="Path to model.yaml")
    synth_parser.add_argument("synth", help="Path to synth.json")
    synth_parser.add_argument("--mlx-model", default=DEFAULT_MLX_MODEL)
    synth_parser.add_argument("--samples", type=int, default=1)
    synth_parser.add_argument("--hints-out", default=None)
    synth_parser.add_argument("--output", default=None)

    # batch command
    batch_parser = subparsers.add_parser("batch", help="Batch process all specs in directory")
    batch_parser.add_argument("spec_dir", help="Directory containing *_hole.yaml specs")
    batch_parser.add_argument("--samples", type=int, default=3)
    batch_parser.add_argument("--two-stage", action="store_true",
                              help="Try 7B first, escalate to 80B on failure")
    batch_parser.add_argument("--validate", choices=["none", "cheap", "full", "examples"], default="cheap")
    batch_parser.add_argument("--output", default=None)

    # report command
    report_parser = subparsers.add_parser("report", help="Generate report from batch run")
    report_parser.add_argument("run_dir", help="Path to batch run directory")

    args = parser.parse_args()

    if args.command == "hints-only":
        hints = generate_hints_single(
            args.model, args.synth, args.mlx_model,
            samples=args.samples, temp=args.temp, top_p=args.top_p,
            validate=args.validate
        )
        hints_path = args.hints_out or f"runs/mlx_hints_{Path(args.model).stem}.json"
        os.makedirs(Path(hints_path).parent, exist_ok=True)
        with open(hints_path, 'w') as f:
            json.dump(hints, f, indent=2)
        print(f"\nSaved hints: {hints_path}")
        print(f"Total hints: {len(hints['holes'])}")

    elif args.command == "synth":
        hints = generate_hints_single(args.model, args.synth, args.mlx_model, samples=args.samples)
        hints_path = args.hints_out or f"runs/mlx_hints_{Path(args.model).stem}.json"
        os.makedirs(Path(hints_path).parent, exist_ok=True)
        with open(hints_path, 'w') as f:
            json.dump(hints, f, indent=2)
        print(f"\nSaved hints: {hints_path}")

        output_dir = args.output or f"runs/mlx_synth_{Path(args.model).stem}"
        success = run_esso_synth(args.model, args.synth, hints_path, output_dir)
        sys.exit(0 if success else 1)

    elif args.command == "batch":
        run_batch(
            args.spec_dir,
            samples=args.samples,
            two_stage=args.two_stage,
            validate=args.validate,
            output_dir=args.output
        )

    elif args.command == "report":
        generate_report(args.run_dir)


if __name__ == "__main__":
    main()
