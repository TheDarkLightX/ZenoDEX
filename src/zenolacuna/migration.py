"""Source-bound omission search on the real finite AutoTrader metadata codec.

The relation contexts are five aggregate checks, each exhaustively evaluated
over the stated byte domain. Mutants remain in memory and have no runtime mount.
"""

from __future__ import annotations

import ast
import hashlib
from dataclasses import asdict, dataclass, replace
from pathlib import Path

from src.tau_workbench.programs import Program

from .check import close_model
from .engine import analyze
from .model import Candidate, Hypothesis, Outcome, OutcomeKind, Requirement, Scope, SourceRef
from .ports.programs import pipeline_outputs
from .proposals import membership_questions

ENCODER = "src/kernels/python/external_signal_profile_encode_v2.py"
DECODER = "src/kernels/python/external_signal_profile_decode_v2.py"
MASKS = (0, 1, 2, 4, 8, 16, 32, 64)


@dataclass(frozen=True, slots=True)
class CodecTrial:
    mask: int
    encoder_sha256: str
    decoder_sha256: str
    self_mismatches: tuple[int, ...]
    producer_mismatches: tuple[int, ...]
    consumer_mismatches: tuple[int, ...]
    reserved_mismatches: tuple[int, ...]


def _mutants(encoder: Program, decoder: Program, mask: int) -> tuple[Program, Program]:
    # Validate source grammar before using AST only to prepare a proposal.
    pipeline_outputs((encoder,), 8)
    pipeline_outputs((decoder,), 8)
    encoder_tree, decoder_tree = ast.parse(encoder.source), ast.parse(decoder.source)
    encoder_function, decoder_function = encoder_tree.body[0], decoder_tree.body[0]
    if not isinstance(encoder_function, ast.FunctionDef) or not isinstance(decoder_function, ast.FunctionDef):
        raise ValueError("source_shape")
    encoder_return, decoder_return = encoder_function.body[0], decoder_function.body[0]
    if not isinstance(encoder_return, ast.Return) or not isinstance(decoder_return, ast.Return):
        raise ValueError("source_shape")
    if encoder_return.value is None or decoder_return.value is None:
        raise ValueError("source_shape")
    enc = ast.unparse(encoder_return.value)

    class Substitute(ast.NodeTransformer):
        def visit_Name(self, node: ast.Name) -> ast.expr:
            if node.id == "x":
                return ast.BinOp(left=ast.Name(id="x", ctx=ast.Load()), op=ast.BitXor(),
                                 right=ast.Constant(value=mask))
            return node

    dec = ast.unparse(Substitute().visit(decoder_return.value))
    enc_source = f"def transform(x): return (({enc}) ^ {mask}) if x < 128 else 255\n"
    dec_source = f"def transform(x): return ({dec}) if x < 128 else 255\n"
    return Program(f"encoder_xor{mask}", enc_source.encode()), Program(f"decoder_xor{mask}", dec_source.encode())


def _trial(original: tuple[Program, Program], mutant: tuple[Program, Program], mask: int) -> CodecTrial:
    enc, dec = original
    enc_new, dec_new = mutant
    same = pipeline_outputs((enc_new, dec_new), 8)
    producer = pipeline_outputs((enc_new, dec), 8)
    consumer = pipeline_outputs((enc, dec_new), 8)
    reserved_tables = tuple(pipeline_outputs((p,), 8) for p in (enc, dec, enc_new, dec_new))
    return CodecTrial(mask, enc_new.sha256, dec_new.sha256,
                      tuple(x for x in range(128) if same[x] != x),
                      tuple(x for x in range(128) if producer[x] != x),
                      tuple(x for x in range(128) if consumer[x] != x),
                      tuple(x for x in range(128, 256) if any(t[x] != 255 for t in reserved_tables)))


def codec_scope(root: Path) -> tuple[Scope, tuple[CodecTrial, ...]]:
    """Read only fixed known kernels; arbitrary candidate paths are never imported."""
    sources = tuple((path, (root / path).read_bytes()) for path in (ENCODER, DECODER))
    original = tuple(Program(name, source) for name, (_, source) in zip(("encoder", "decoder"), sources, strict=True))
    encoder, decoder = original
    trials = tuple(_trial((encoder, decoder), _mutants(encoder, decoder, mask), mask) for mask in MASKS)
    outcomes = (
        Outcome("correct", "every valid metadata word decodes to its original value", OutcomeKind.ACCEPT),
        Outcome("misdecode", "at least one valid metadata word decodes to another value", OutcomeKind.ACCEPT),
        Outcome("reserved", "every reserved byte returns the reserved sentinel", OutcomeKind.REJECT),
    )
    contract = ((0,), (0,), (0, 1), (0, 1), (2,))
    required = ((0,), (0,), (), (), (2,))
    protected = (Requirement("roundtrip-and-reserved", (0, 1, 4), contract, required),)
    old_roundtrip_ok = pipeline_outputs((encoder, decoder), 8)[:128] == tuple(range(128))
    hypotheses = tuple(Hypothesis(f"xor-{trial.mask}", (
        (0,) if old_roundtrip_ok else (1,),
        (0,) if not trial.self_mismatches else (1,),
        (0,) if not trial.producer_mismatches else (1,),
        (0,) if not trial.consumer_mismatches else (1,),
        (2,) if not trial.reserved_mismatches else (),
    )) for trial in trials)
    scope = Scope("autotrader-codec-compatibility", (
        "legacy self roundtrip over 0..127", "candidate self roundtrip over 0..127",
        "candidate producer to legacy consumer over 0..127",
        "legacy producer to candidate consumer over 0..127", "reserved bytes 128..255",
    ), outcomes, (0, 1, 2, 3, 4), contract, protected, hypotheses, (),
        sources=tuple(SourceRef(path, hashlib.sha256(source).hexdigest()) for path, source in sources),
        omission_family=tuple(f"paired-xor-{mask}" for mask in MASKS[1:]))
    return replace(scope, questions=membership_questions(scope)), trials


def migration_report(root: Path) -> dict[str, object]:
    scope, trials = codec_scope(root)
    before = analyze(scope)
    candidate = Candidate("preserve-existing-wire-map", scope.hypotheses[0].allowed, scope.assumptions)
    # Demonstration of a simulated selected contract; no real-owner receipt is minted.
    after = close_model(scope, (0,), candidate)
    return {
        "schema": "zenolacuna/codec-migration-v1", "authority": "NONE",
        "authorization_profile": "SIMULATED", "scope": scope, "before": before,
        "after_simulated_compatibility_decision": after, "trials": tuple(asdict(trial) for trial in trials),
        "concrete_domain": {"valid_words": 128, "reserved_words": 128, "candidate_pairs": len(trials)},
        "scope_claim": "five aggregate observations computed over all byte inputs; no queued-message graph claim",
    }


def byte_roundtrip_scope(root: Path) -> tuple[Scope, Candidate]:
    """Full concrete byte-domain contract for the unchanged restricted codec pipeline."""
    names = tuple(map(str, range(256)))
    allowed = tuple((x if x < 128 else 255,) for x in range(256))
    sources = tuple(SourceRef(path, hashlib.sha256((root / path).read_bytes()).hexdigest())
                    for path in (ENCODER, DECODER))
    # All observations are successful integer returns. The value 255 is checked
    # as a sentinel; application-level rejection needs its own runtime adapter.
    outcomes = tuple(Outcome(name, name, OutcomeKind.ACCEPT) for name in names)
    requirement = Requirement("all-byte-roundtrip-and-reserved", tuple(range(256)), allowed, allowed)
    scope = Scope("full-byte-roundtrip", names, outcomes, tuple(range(256)), allowed,
                  (requirement,), (Hypothesis("canonical-byte-roundtrip", allowed),), (),
                  sources=sources, max_work=1_000_000)
    return scope, Candidate("real-codec-pipeline", allowed, scope.assumptions)
