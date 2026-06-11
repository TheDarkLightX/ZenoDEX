"""Top-level conftest for mechanism_design_math_v1.

Adapted from experiments/research_program_v2/conftest.py.

After all tests complete, normalizes evidence/results.json files to the
canonical schema expected by validate_evidence.py, and injects per-hypothesis
test counts collected via pytest_runtest_logreport.

Program-specific differences from research_program_v2:
- Hypothesis IDs are three-segment: H-MD-<DOM>-NNN with DOM in
  {SS, SB, PT, VM, XD, FV}. Test-name extraction patterns match
  ``TestHMDSS001`` / ``test_h_md_ss_001`` style names.
- The formal-verification lane prefix is H-MD-FV- (proof_file required).
- v2's legacy normalization cases (results arrays, hypotheses_tested,
  wave-specific special formats) and v2-specific override tables are
  dropped: this program writes canonical evidence from day one, and the
  override tables start empty.
"""
from __future__ import annotations

import collections
import json
import re
from pathlib import Path

BASE = Path(__file__).parent

PROGRAM_REL = "experiments/mechanism_design_math_v1"

# ── Session test count collection ─────────────────────────────────────────
# Tracks {wave_dir: {hyp_id: {"passed": int, "failed": int}}}
_session_counts: dict[str, dict[str, dict[str, int]]] = collections.defaultdict(
    lambda: collections.defaultdict(lambda: {"passed": 0, "failed": 0})
)

# Patterns to extract hypothesis ID from test nodeid.
# Three-segment program IDs: TestHMDSS001 → H-MD-SS-001;
# test_h_md_ss_001 → H-MD-SS-001.
_TEST_HYP_PATTERNS = [
    re.compile(r"TestHMD([A-Z]{2})(\d{2,3})"),
    re.compile(r"test_h_md_([a-z]{2})_(\d{2,3})"),
]


def _extract_hyp_id_from_nodeid(nodeid: str) -> str | None:
    """Extract hypothesis ID (e.g. H-MD-SS-001) from a pytest nodeid."""
    for pat in _TEST_HYP_PATTERNS:
        m = pat.search(nodeid)
        if m:
            dom = m.group(1).upper()
            num = m.group(2).zfill(3)
            return f"H-MD-{dom}-{num}"
    return None


def _extract_wave_dir(nodeid: str) -> str | None:
    """Extract wave directory name from a pytest nodeid."""
    m = re.search(r"(wave\d+_[^/]+)/", nodeid)
    return m.group(1) if m else None

# ── Canonical verdict mapping ──────────────────────────────────────────────

_VERDICT_MAP: dict[str, str] = {
    "CORROBORATED": "SUPPORTED",
    "INFORMATIONAL": "NOT_APPLICABLE",
    "SAFE": "SUPPORTED",
    "PASS": "SUPPORTED",
    "REFUTED": "FALSIFIED",
    "SUPPORTED": "SUPPORTED",
    "FALSIFIED": "FALSIFIED",
    "PARTIALLY_FALSIFIED": "PARTIALLY_FALSIFIED",
    "INCONCLUSIVE": "INCONCLUSIVE",
    "NOT_APPLICABLE": "NOT_APPLICABLE",
}

_CONF: dict[str, float] = {
    "SUPPORTED": 0.9,
    "FALSIFIED": 0.95,
    "PARTIALLY_FALSIFIED": 0.7,
    "INCONCLUSIVE": 0.5,
    "NOT_APPLICABLE": 0.5,
}

_HYP_ID_RE = re.compile(r"^H-[A-Z]{2}(-[A-Z]+)*-\d{2,3}.*$")

# Popperian polarity overrides (hypothesis "X is safe" falsified = safety
# proven). Empty at program start; populated only with reviewed entries.
_POLARITY_OVERRIDES: dict[str, str] = {}

# Cross-wave ID overrides: (domain, old_id) → new_id, first wave keeps the
# original ID. Empty at program start.
_CROSS_WAVE_ID_OVERRIDES: dict[tuple[str, str], str] = {}

# Domain-scoped proof links for formal-verification hypotheses.
_FV_PROOF_FILE_BY_DOMAIN: dict[str, dict[str, str]] = {}

FV_PREFIX = "H-MD-FV-"


def _map_verdict(raw: str) -> str:
    return _VERDICT_MAP.get(raw, "INCONCLUSIVE")


def _infer_wave(dir_name: str) -> int:
    m = re.match(r"wave(\d+)", dir_name)
    return int(m.group(1)) if m else 0


def _infer_domain(dir_name: str) -> str:
    m = re.match(r"wave\d+_(.*)", dir_name)
    return m.group(1) if m else dir_name


def _make_canonical_hyp(
    raw: dict,
    *,
    reproduction: str = "",
) -> dict:
    """Convert a raw hypothesis dict to canonical form (safety net only)."""
    hid = raw.get("id", raw.get("hypothesis", "H-MD-XX-000"))
    raw_v = raw.get("verdict", raw.get("status", "INCONCLUSIVE"))
    verdict = _map_verdict(raw_v)

    trials = raw.get("trials", raw.get("n_trials", raw.get("tested", 0)))
    failed = raw.get("violations", raw.get("failures", 0))
    passed = max(0, trials - failed)

    desc = raw.get("description", raw.get("title", raw.get("name", hid)))
    finding = raw.get("key_finding", raw.get("evidence", raw.get("detail", desc)))

    out = {
        "id": hid,
        "description": desc,
        "verdict": verdict,
        "tests_passed": raw.get("tests_passed", passed),
        "tests_failed": raw.get("tests_failed", failed),
        "confidence": raw.get("confidence", _CONF[verdict]),
        "key_finding": finding,
        "reproduction": raw.get("reproduction", reproduction),
    }
    for opt_key in ("proof_file", "obligation"):
        val = raw.get(opt_key)
        if isinstance(val, str) and val.strip():
            out[opt_key] = val
    return out


def _is_canonical(data: dict) -> bool:
    """Quick check if file already matches canonical schema."""
    if not isinstance(data.get("wave"), int):
        return False
    if not isinstance(data.get("domain"), str):
        return False
    if not isinstance(data.get("hypotheses"), list):
        return False
    if not isinstance(data.get("total_tests"), int):
        return False
    hyps = data.get("hypotheses", [])
    if not hyps:
        return False
    h0 = hyps[0]
    if not isinstance(h0, dict):
        return False
    for key in ("id", "description", "verdict", "tests_passed",
                "tests_failed", "confidence", "key_finding", "reproduction"):
        if key not in h0:
            return False
    for h in hyps:
        if not _HYP_ID_RE.match(h.get("id", "")):
            return False
    valid_verdicts = {"SUPPORTED", "FALSIFIED", "PARTIALLY_FALSIFIED",
                      "INCONCLUSIVE", "NOT_APPLICABLE"}
    for h in hyps:
        if h.get("verdict") not in valid_verdicts:
            return False
    return True


def _apply_polarity_overrides(data: dict) -> bool:
    """Fix known polarity mismatches. Returns True if any changes were made."""
    changed = False
    for h in data.get("hypotheses", []):
        hid = h.get("id", "")
        if hid in _POLARITY_OVERRIDES and h.get("verdict") != _POLARITY_OVERRIDES[hid]:
            h["verdict"] = _POLARITY_OVERRIDES[hid]
            h["confidence"] = _CONF[_POLARITY_OVERRIDES[hid]]
            changed = True
    return changed


def _inject_fv_proof_files(hyps: list[dict], domain: str) -> None:
    """Backfill proof_file for FV hypotheses when source formats omit it."""
    domain_map = _FV_PROOF_FILE_BY_DOMAIN.get(domain, {})
    if not domain_map:
        return
    for hyp in hyps:
        hid = hyp.get("id", "")
        if not isinstance(hid, str) or not hid.startswith(FV_PREFIX):
            continue
        proof_file = hyp.get("proof_file")
        if isinstance(proof_file, str) and proof_file.strip():
            continue
        mapped = domain_map.get(hid)
        if mapped:
            hyp["proof_file"] = mapped


def _dedup_in_file(hyps: list[dict]) -> None:
    """Rename in-file duplicate IDs by incrementing the numeric suffix."""
    seen: set[str] = set()
    for h in hyps:
        hid = h.get("id", "")
        if hid in seen:
            m = re.match(r"^(H-[A-Z]{2}(-[A-Z]+)*-)(\d{2,3})(.*)$", hid)
            if m:
                prefix, _, num_str, suffix = m.groups()
                num = int(num_str)
                while True:
                    num += 1
                    new_id = f"{prefix}{str(num).zfill(len(num_str))}{suffix}"
                    if new_id not in seen:
                        h["id"] = new_id
                        seen.add(new_id)
                        break
            else:
                h["id"] = f"{hid}-b"
                seen.add(h["id"])
        else:
            seen.add(hid)


def _normalize_file(path: Path) -> None:
    """Normalize a single evidence file to canonical schema."""
    with open(path) as f:
        data = json.load(f)

    dir_name = path.parent.parent.name  # waveN_domain
    rel_repro = f"python3 -m pytest {PROGRAM_REL}/{dir_name}/ -v"

    if _is_canonical(data):
        changed = _apply_polarity_overrides(data)
        ids = [h.get("id", "") for h in data.get("hypotheses", [])]
        if len(ids) != len(set(ids)):
            _dedup_in_file(data["hypotheses"])
            changed = True
        for h in data.get("hypotheses", []):
            repro = h.get("reproduction", "")
            if "/home/" in repro or repro.startswith("cd "):
                h["reproduction"] = rel_repro
                changed = True
        if changed:
            with open(path, "w") as f:
                json.dump(data, f, indent=2)
                f.write("\n")
        return

    # Safety net: hypotheses as a list of non-canonical entries.
    wave = _infer_wave(dir_name) if not isinstance(data.get("wave"), int) else data["wave"]
    domain = data.get("domain", _infer_domain(dir_name))
    timestamp = data.get("timestamp", "2026-06-10T00:00:00Z")

    raw_hyps = data.get("hypotheses")
    if not isinstance(raw_hyps, list) or not raw_hyps:
        return  # Cannot normalize; validator will flag it.

    hyps = [_make_canonical_hyp(h, reproduction=rel_repro) for h in raw_hyps
            if isinstance(h, dict)]
    if not hyps:
        return

    _inject_fv_proof_files(hyps, domain)
    _dedup_in_file(hyps)

    tp = sum(h["tests_passed"] for h in hyps)
    tf = sum(h["tests_failed"] for h in hyps)

    out = {
        "wave": wave,
        "domain": domain,
        "timestamp": timestamp,
        "hypotheses": hyps,
        "total_tests": tp + tf,
        "total_passed": tp,
        "total_failed": tf,
    }
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
        f.write("\n")


def _apply_cross_wave_overrides_to_file(path: Path) -> None:
    """Rename cross-wave duplicate hypothesis IDs based on domain."""
    wave_dir = path.parent.parent.name
    domain = _infer_domain(wave_dir)

    applicable = {
        old_id: new_id
        for (d, old_id), new_id in _CROSS_WAVE_ID_OVERRIDES.items()
        if d == domain
    }
    if not applicable:
        return

    with open(path) as f:
        data = json.load(f)

    changed = False
    for h in data.get("hypotheses", []):
        hid = h.get("id", "")
        if hid in applicable:
            h["id"] = applicable[hid]
            changed = True

    if changed:
        _apply_polarity_overrides(data)
        _inject_fv_proof_files(data.get("hypotheses", []), domain)
        with open(path, "w") as f:
            json.dump(data, f, indent=2)
            f.write("\n")


def pytest_runtest_logreport(report):
    """Collect per-hypothesis test counts from test results."""
    if report.when != "call":
        return
    hid = _extract_hyp_id_from_nodeid(report.nodeid)
    wave_dir = _extract_wave_dir(report.nodeid)
    if not hid or not wave_dir:
        return
    if report.passed:
        _session_counts[wave_dir][hid]["passed"] += 1
    elif report.failed:
        _session_counts[wave_dir][hid]["failed"] += 1


def pytest_sessionfinish(session, exitstatus):
    """Normalize all evidence files after test session completes."""
    patterns = [
        "wave*_*/evidence/results.json",
        "wave*_formal/results.json",
    ]
    for pattern in patterns:
        for path in BASE.glob(pattern):
            try:
                _normalize_file(path)
                _inject_session_counts(path)
                _apply_cross_wave_overrides_to_file(path)
            except Exception as e:
                import warnings
                warnings.warn(f"Evidence normalization failed for {path}: {e}")


def _inject_session_counts(path: Path) -> None:
    """Inject collected pytest session counts into normalized evidence file.

    For any hypothesis where the file has tests_passed=0 and tests_failed=0
    but the session collected actual counts, update the counts.
    """
    wave_dir = path.parent.parent.name
    if wave_dir not in _session_counts:
        return
    counts = _session_counts[wave_dir]
    if not counts:
        return

    with open(path) as f:
        data = json.load(f)

    changed = False
    for h in data.get("hypotheses", []):
        hid = h.get("id", "")
        if hid not in counts:
            continue
        if h.get("tests_passed", 0) == 0 and h.get("tests_failed", 0) == 0:
            if h.get("verdict") == "NOT_APPLICABLE":
                continue
            h["tests_passed"] = counts[hid]["passed"]
            h["tests_failed"] = counts[hid]["failed"]
            changed = True

    if changed:
        tp = sum(h.get("tests_passed", 0) for h in data["hypotheses"])
        tf = sum(h.get("tests_failed", 0) for h in data["hypotheses"])
        data["total_tests"] = tp + tf
        data["total_passed"] = tp
        data["total_failed"] = tf
        with open(path, "w") as f:
            json.dump(data, f, indent=2)
            f.write("\n")
