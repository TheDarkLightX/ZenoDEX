#!/usr/bin/env python3
"""
PopperPad: Falsification-Gated Collective Knowledge System

A Popper-inspired append-only knowledge base where agents record:
- HYPOTHESIS: Testable conjectures (must be falsifiable)
- FALSIFIED: Hypotheses disproven by counterexample
- CORROBORATED: Hypotheses that survived severe tests (not proven!)
- DEAD_END: Approaches that failed (with reason)
- KNOWLEDGE: Established facts with evidence
- INSIGHT: Useful observations (non-falsifiable)

Key Popperian principles:
1. Hypotheses MUST be falsifiable (testable)
2. One counterexample kills a universal claim
3. Corroboration ≠ proof (bold conjectures + severe tests = progress)
4. Record negative results - they're as valuable as positive ones

Usage:
    # Add a hypothesis
    python3 tools/popper_pad.py add-hypothesis \
        --claim "Hybrid curve with dynamic alpha preserves K monotonicity" \
        --test "SMT: ∀ valid swap, K_after >= K_before" \
        --domain "hybrid-curve" \
        --agent "H4-ESSO"

    # Falsify a hypothesis
    python3 tools/popper_pad.py falsify H001 \
        --counterexample "{x:2, y:3, dx:5, dy:2} -> K decreases" \
        --agent "H4-ESSO"

    # Record a dead end
    python3 tools/popper_pad.py dead-end \
        --approach "Dynamic alpha blending in invariant" \
        --reason "Alpha changes during swap invalidates K comparison" \
        --agent "H4-ESSO"

    # Query before starting work
    python3 tools/popper_pad.py query --domain "hybrid-curve"
    python3 tools/popper_pad.py check-falsified "dynamic alpha"
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional
import hashlib
import re

# Default pad location
DEFAULT_PAD_PATH = Path(__file__).parent.parent / "knowledge" / "popper_pad.jsonl"


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _hash_content(content: str) -> str:
    """Short hash for entry ID generation."""
    return hashlib.sha256(content.encode()).hexdigest()[:8]


def _generate_id(entry_type: str, content: str) -> str:
    """Generate unique entry ID."""
    prefix = {
        "HYPOTHESIS": "H",
        "FALSIFIED": "F",
        "CORROBORATED": "C",
        "DEAD_END": "D",
        "KNOWLEDGE": "K",
        "INSIGHT": "I",
    }.get(entry_type, "X")
    return f"{prefix}{_hash_content(content)}"


def _load_pad(pad_path: Path) -> list[dict[str, Any]]:
    """Load all entries from the pad."""
    if not pad_path.exists():
        return []
    entries = []
    with open(pad_path, "r") as f:
        for line in f:
            line = line.strip()
            if line:
                entries.append(json.loads(line))
    return entries


def _append_entry(pad_path: Path, entry: dict[str, Any]) -> str:
    """Append a single entry (append-only!)."""
    pad_path.parent.mkdir(parents=True, exist_ok=True)
    entry_id = entry.get("id", _generate_id(entry["type"], json.dumps(entry)))
    entry["id"] = entry_id
    entry["timestamp"] = _now_iso()

    with open(pad_path, "a") as f:
        f.write(json.dumps(entry) + "\n")

    return entry_id


def _validate_falsifiability(claim: str, test: str) -> tuple[bool, str]:
    """Check if a hypothesis is properly falsifiable."""
    issues = []

    # Must have a testable claim
    if len(claim) < 10:
        issues.append("Claim too vague - must be specific and testable")

    # Must specify how to test
    if not test or len(test) < 5:
        issues.append("Must specify a concrete test/experiment")

    # Warn about unfalsifiable language
    unfalsifiable_patterns = [
        (r"\bshould\b", "Avoid 'should' - use concrete predictions"),
        (r"\bmight\b", "Avoid 'might' - make definite claims"),
        (r"\bcould\b", "Avoid 'could' - state what WILL happen"),
        (r"\bprobably\b", "Avoid 'probably' - be precise"),
    ]
    for pattern, msg in unfalsifiable_patterns:
        if re.search(pattern, claim, re.IGNORECASE):
            issues.append(msg)

    if issues:
        return False, "; ".join(issues)
    return True, "OK"


class PopperPad:
    """Falsification-gated knowledge system."""

    def __init__(self, pad_path: Path = DEFAULT_PAD_PATH):
        self.pad_path = pad_path
        self._entries: Optional[list[dict]] = None

    @property
    def entries(self) -> list[dict[str, Any]]:
        if self._entries is None:
            self._entries = _load_pad(self.pad_path)
        return self._entries

    def reload(self) -> None:
        """Force reload from disk."""
        self._entries = None

    # ─────────────────────────────────────────────────────────────
    # WRITE OPERATIONS (append-only)
    # ─────────────────────────────────────────────────────────────

    def add_hypothesis(
        self,
        claim: str,
        test: str,
        domain: str,
        agent: str,
        confidence: float = 0.5,
        references: Optional[list[str]] = None,
    ) -> str:
        """
        Add a falsifiable hypothesis.

        Args:
            claim: The testable conjecture (must be falsifiable!)
            test: How to test/falsify this hypothesis
            domain: Knowledge domain (e.g., "hybrid-curve", "batch-auction")
            agent: Who proposed this (e.g., "H4-ESSO", "human")
            confidence: Prior confidence [0,1] (will be updated by tests)
            references: Related entry IDs or file paths
        """
        valid, msg = _validate_falsifiability(claim, test)
        if not valid:
            raise ValueError(f"Hypothesis not falsifiable: {msg}")

        entry = {
            "type": "HYPOTHESIS",
            "status": "OPEN",  # OPEN -> FALSIFIED | CORROBORATED
            "claim": claim,
            "test": test,
            "domain": domain,
            "agent": agent,
            "confidence": confidence,
            "references": references or [],
            "tests_survived": 0,
            "tests_attempted": 0,
        }
        entry_id = _append_entry(self.pad_path, entry)
        self._entries = None  # Invalidate cache
        return entry_id

    def falsify(
        self,
        hypothesis_id: str,
        counterexample: str,
        agent: str,
        evidence_path: Optional[str] = None,
    ) -> str:
        """
        Record falsification of a hypothesis.

        One counterexample is sufficient to kill a universal claim!
        """
        # Find the hypothesis
        hyp = self.get_entry(hypothesis_id)
        if not hyp:
            raise ValueError(f"Hypothesis {hypothesis_id} not found")
        if hyp["type"] != "HYPOTHESIS":
            raise ValueError(f"{hypothesis_id} is not a hypothesis")

        entry = {
            "type": "FALSIFIED",
            "hypothesis_id": hypothesis_id,
            "hypothesis_claim": hyp["claim"],
            "counterexample": counterexample,
            "evidence_path": evidence_path,
            "agent": agent,
            "domain": hyp.get("domain", "unknown"),
        }
        entry_id = _append_entry(self.pad_path, entry)
        self._entries = None
        return entry_id

    def corroborate(
        self,
        hypothesis_id: str,
        test_description: str,
        agent: str,
        severity: str = "medium",  # low, medium, high, extreme
        evidence_path: Optional[str] = None,
    ) -> str:
        """
        Record that a hypothesis survived a test.

        NOTE: Corroboration ≠ proof! Bold conjectures that survive
        severe tests gain credibility but are never "proven".
        """
        hyp = self.get_entry(hypothesis_id)
        if not hyp:
            raise ValueError(f"Hypothesis {hypothesis_id} not found")

        # Check if already falsified
        if self.is_falsified(hypothesis_id):
            raise ValueError(f"Cannot corroborate {hypothesis_id} - already falsified!")

        entry = {
            "type": "CORROBORATED",
            "hypothesis_id": hypothesis_id,
            "hypothesis_claim": hyp["claim"],
            "test_description": test_description,
            "severity": severity,
            "evidence_path": evidence_path,
            "agent": agent,
            "domain": hyp.get("domain", "unknown"),
        }
        entry_id = _append_entry(self.pad_path, entry)
        self._entries = None
        return entry_id

    def dead_end(
        self,
        approach: str,
        reason: str,
        domain: str,
        agent: str,
        time_spent: Optional[str] = None,
        references: Optional[list[str]] = None,
    ) -> str:
        """
        Record an approach that failed.

        This is VALUABLE - saves others from wasting time!
        """
        entry = {
            "type": "DEAD_END",
            "approach": approach,
            "reason": reason,
            "domain": domain,
            "agent": agent,
            "time_spent": time_spent,
            "references": references or [],
        }
        entry_id = _append_entry(self.pad_path, entry)
        self._entries = None
        return entry_id

    def knowledge(
        self,
        fact: str,
        evidence: str,
        domain: str,
        agent: str,
        confidence: float = 0.9,
        references: Optional[list[str]] = None,
    ) -> str:
        """
        Record established knowledge with evidence.
        """
        entry = {
            "type": "KNOWLEDGE",
            "fact": fact,
            "evidence": evidence,
            "domain": domain,
            "agent": agent,
            "confidence": confidence,
            "references": references or [],
        }
        entry_id = _append_entry(self.pad_path, entry)
        self._entries = None
        return entry_id

    def insight(
        self,
        observation: str,
        context: str,
        domain: str,
        agent: str,
    ) -> str:
        """
        Record a useful observation (may not be falsifiable).
        """
        entry = {
            "type": "INSIGHT",
            "observation": observation,
            "context": context,
            "domain": domain,
            "agent": agent,
        }
        entry_id = _append_entry(self.pad_path, entry)
        self._entries = None
        return entry_id

    # ─────────────────────────────────────────────────────────────
    # QUERY OPERATIONS (read-only)
    # ─────────────────────────────────────────────────────────────

    def get_entry(self, entry_id: str) -> Optional[dict[str, Any]]:
        """Get entry by ID."""
        for e in self.entries:
            if e.get("id") == entry_id:
                return e
        return None

    def is_falsified(self, hypothesis_id: str) -> bool:
        """Check if a hypothesis has been falsified."""
        for e in self.entries:
            if e["type"] == "FALSIFIED" and e.get("hypothesis_id") == hypothesis_id:
                return True
        return False

    def get_falsification(self, hypothesis_id: str) -> Optional[dict[str, Any]]:
        """Get the falsification entry for a hypothesis."""
        for e in self.entries:
            if e["type"] == "FALSIFIED" and e.get("hypothesis_id") == hypothesis_id:
                return e
        return None

    def query_domain(self, domain: str) -> dict[str, list[dict]]:
        """Get all entries for a domain, organized by type."""
        result: dict[str, list[dict]] = {
            "hypotheses_open": [],
            "hypotheses_falsified": [],
            "corroborations": [],
            "dead_ends": [],
            "knowledge": [],
            "insights": [],
        }

        falsified_ids = {
            e["hypothesis_id"] for e in self.entries
            if e["type"] == "FALSIFIED"
        }

        for e in self.entries:
            if e.get("domain") != domain:
                continue

            if e["type"] == "HYPOTHESIS":
                if e["id"] in falsified_ids:
                    result["hypotheses_falsified"].append(e)
                else:
                    result["hypotheses_open"].append(e)
            elif e["type"] == "CORROBORATED":
                result["corroborations"].append(e)
            elif e["type"] == "DEAD_END":
                result["dead_ends"].append(e)
            elif e["type"] == "KNOWLEDGE":
                result["knowledge"].append(e)
            elif e["type"] == "INSIGHT":
                result["insights"].append(e)

        return result

    def search_falsified(self, keyword: str) -> list[dict[str, Any]]:
        """Search for falsified hypotheses matching keyword."""
        results = []
        for e in self.entries:
            if e["type"] == "FALSIFIED":
                claim = e.get("hypothesis_claim", "")
                cex = e.get("counterexample", "")
                if keyword.lower() in claim.lower() or keyword.lower() in cex.lower():
                    results.append(e)
        return results

    def search_dead_ends(self, keyword: str) -> list[dict[str, Any]]:
        """Search for dead ends matching keyword."""
        results = []
        for e in self.entries:
            if e["type"] == "DEAD_END":
                approach = e.get("approach", "")
                reason = e.get("reason", "")
                if keyword.lower() in approach.lower() or keyword.lower() in reason.lower():
                    results.append(e)
        return results

    def get_corroboration_count(self, hypothesis_id: str) -> int:
        """Count how many tests a hypothesis has survived."""
        count = 0
        for e in self.entries:
            if e["type"] == "CORROBORATED" and e.get("hypothesis_id") == hypothesis_id:
                count += 1
        return count

    def summary(self) -> dict[str, Any]:
        """Get summary statistics."""
        stats = {
            "total_entries": len(self.entries),
            "hypotheses": 0,
            "falsified": 0,
            "corroborations": 0,
            "dead_ends": 0,
            "knowledge": 0,
            "insights": 0,
            "domains": set(),
        }

        for e in self.entries:
            t = e["type"]
            if t == "HYPOTHESIS":
                stats["hypotheses"] += 1
            elif t == "FALSIFIED":
                stats["falsified"] += 1
            elif t == "CORROBORATED":
                stats["corroborations"] += 1
            elif t == "DEAD_END":
                stats["dead_ends"] += 1
            elif t == "KNOWLEDGE":
                stats["knowledge"] += 1
            elif t == "INSIGHT":
                stats["insights"] += 1

            if "domain" in e:
                stats["domains"].add(e["domain"])

        stats["domains"] = sorted(stats["domains"])
        return stats

    def format_briefing(self, domain: Optional[str] = None) -> str:
        """
        Generate a briefing document for agents starting work.

        This is the key output - tells agents what NOT to try.
        """
        lines = [
            "=" * 60,
            "POPPERPAD BRIEFING",
            "=" * 60,
            "",
        ]

        if domain:
            lines.append(f"Domain: {domain}")
            data = self.query_domain(domain)
        else:
            lines.append("All domains")
            data = {
                "hypotheses_falsified": [e for e in self.entries if e["type"] == "FALSIFIED"],
                "dead_ends": [e for e in self.entries if e["type"] == "DEAD_END"],
                "knowledge": [e for e in self.entries if e["type"] == "KNOWLEDGE"],
                "hypotheses_open": [e for e in self.entries if e["type"] == "HYPOTHESIS" and not self.is_falsified(e["id"])],
            }

        lines.append("")

        # DEAD ENDS - Most important for avoiding wasted work
        lines.append("─" * 40)
        lines.append("⛔ DEAD ENDS (Do NOT retry these approaches)")
        lines.append("─" * 40)
        if data["dead_ends"]:
            for de in data["dead_ends"]:
                lines.append(f"  [{de['id']}] {de['approach']}")
                lines.append(f"      Reason: {de['reason']}")
                lines.append(f"      Agent: {de['agent']}")
                lines.append("")
        else:
            lines.append("  (none recorded)")
        lines.append("")

        # FALSIFIED HYPOTHESES
        lines.append("─" * 40)
        lines.append("❌ FALSIFIED HYPOTHESES (Proven false)")
        lines.append("─" * 40)
        if data.get("hypotheses_falsified"):
            for f in data["hypotheses_falsified"]:
                if f["type"] == "FALSIFIED":
                    lines.append(f"  [{f['hypothesis_id']}] {f['hypothesis_claim']}")
                    lines.append(f"      Counterexample: {f['counterexample']}")
                    lines.append(f"      Falsified by: {f['agent']}")
                else:
                    # It's the hypothesis entry itself
                    fentry = self.get_falsification(f["id"])
                    if fentry:
                        lines.append(f"  [{f['id']}] {f['claim']}")
                        lines.append(f"      Counterexample: {fentry['counterexample']}")
                lines.append("")
        else:
            lines.append("  (none)")
        lines.append("")

        # ESTABLISHED KNOWLEDGE
        lines.append("─" * 40)
        lines.append("✓ ESTABLISHED KNOWLEDGE")
        lines.append("─" * 40)
        if data["knowledge"]:
            for k in data["knowledge"]:
                lines.append(f"  [{k['id']}] {k['fact']}")
                lines.append(f"      Evidence: {k['evidence']}")
                lines.append("")
        else:
            lines.append("  (none)")
        lines.append("")

        # OPEN HYPOTHESES
        lines.append("─" * 40)
        lines.append("? OPEN HYPOTHESES (untested or corroborated)")
        lines.append("─" * 40)
        if data["hypotheses_open"]:
            for h in data["hypotheses_open"]:
                corr_count = self.get_corroboration_count(h["id"])
                status = f"survived {corr_count} tests" if corr_count else "untested"
                lines.append(f"  [{h['id']}] {h['claim']}")
                lines.append(f"      Test: {h['test']}")
                lines.append(f"      Status: {status}")
                lines.append("")
        else:
            lines.append("  (none)")

        lines.append("")
        lines.append("=" * 60)

        return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────

def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="PopperPad: Falsification-gated knowledge system",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--pad", type=Path, default=DEFAULT_PAD_PATH,
        help="Path to pad file (default: knowledge/popper_pad.jsonl)"
    )

    subparsers = parser.add_subparsers(dest="command", required=True)

    # add-hypothesis
    p_hyp = subparsers.add_parser("add-hypothesis", help="Add a falsifiable hypothesis")
    p_hyp.add_argument("--claim", required=True, help="The testable conjecture")
    p_hyp.add_argument("--test", required=True, help="How to test/falsify")
    p_hyp.add_argument("--domain", required=True, help="Knowledge domain")
    p_hyp.add_argument("--agent", required=True, help="Who proposed this")
    p_hyp.add_argument("--confidence", type=float, default=0.5)
    p_hyp.add_argument("--refs", nargs="*", default=[], help="Reference IDs or paths")

    # falsify
    p_fals = subparsers.add_parser("falsify", help="Falsify a hypothesis")
    p_fals.add_argument("hypothesis_id", help="ID of hypothesis to falsify")
    p_fals.add_argument("--counterexample", required=True, help="The counterexample")
    p_fals.add_argument("--agent", required=True, help="Who found this")
    p_fals.add_argument("--evidence", help="Path to evidence file")

    # corroborate
    p_corr = subparsers.add_parser("corroborate", help="Record a passed test")
    p_corr.add_argument("hypothesis_id", help="ID of hypothesis")
    p_corr.add_argument("--test", required=True, help="Description of test")
    p_corr.add_argument("--agent", required=True, help="Who ran the test")
    p_corr.add_argument("--severity", choices=["low", "medium", "high", "extreme"], default="medium")
    p_corr.add_argument("--evidence", help="Path to evidence")

    # dead-end
    p_dead = subparsers.add_parser("dead-end", help="Record a failed approach")
    p_dead.add_argument("--approach", required=True, help="What was tried")
    p_dead.add_argument("--reason", required=True, help="Why it failed")
    p_dead.add_argument("--domain", required=True, help="Knowledge domain")
    p_dead.add_argument("--agent", required=True, help="Who tried this")
    p_dead.add_argument("--time-spent", help="How much time was spent")
    p_dead.add_argument("--refs", nargs="*", default=[])

    # knowledge
    p_know = subparsers.add_parser("knowledge", help="Record established fact")
    p_know.add_argument("--fact", required=True, help="The established fact")
    p_know.add_argument("--evidence", required=True, help="Evidence/proof")
    p_know.add_argument("--domain", required=True, help="Knowledge domain")
    p_know.add_argument("--agent", required=True, help="Who established this")
    p_know.add_argument("--confidence", type=float, default=0.9)
    p_know.add_argument("--refs", nargs="*", default=[])

    # insight
    p_ins = subparsers.add_parser("insight", help="Record an observation")
    p_ins.add_argument("--observation", required=True)
    p_ins.add_argument("--context", required=True)
    p_ins.add_argument("--domain", required=True)
    p_ins.add_argument("--agent", required=True)

    # query
    p_query = subparsers.add_parser("query", help="Query by domain")
    p_query.add_argument("--domain", help="Domain to query (all if omitted)")
    p_query.add_argument("--format", choices=["json", "briefing"], default="briefing")

    # check-falsified
    p_check = subparsers.add_parser("check-falsified", help="Check if keyword matches falsified claims")
    p_check.add_argument("keyword", help="Keyword to search")

    # check-dead-ends
    p_dead_check = subparsers.add_parser("check-dead-ends", help="Check for dead ends")
    p_dead_check.add_argument("keyword", help="Keyword to search")

    # summary
    subparsers.add_parser("summary", help="Show summary statistics")

    # briefing
    p_brief = subparsers.add_parser("briefing", help="Generate agent briefing")
    p_brief.add_argument("--domain", help="Domain (all if omitted)")

    args = parser.parse_args(argv)
    pad = PopperPad(args.pad)

    try:
        if args.command == "add-hypothesis":
            entry_id = pad.add_hypothesis(
                claim=args.claim,
                test=args.test,
                domain=args.domain,
                agent=args.agent,
                confidence=args.confidence,
                references=args.refs,
            )
            print(f"Added hypothesis: {entry_id}")

        elif args.command == "falsify":
            entry_id = pad.falsify(
                hypothesis_id=args.hypothesis_id,
                counterexample=args.counterexample,
                agent=args.agent,
                evidence_path=args.evidence,
            )
            print(f"Falsified {args.hypothesis_id}: {entry_id}")

        elif args.command == "corroborate":
            entry_id = pad.corroborate(
                hypothesis_id=args.hypothesis_id,
                test_description=args.test,
                agent=args.agent,
                severity=args.severity,
                evidence_path=args.evidence,
            )
            print(f"Corroborated {args.hypothesis_id}: {entry_id}")

        elif args.command == "dead-end":
            entry_id = pad.dead_end(
                approach=args.approach,
                reason=args.reason,
                domain=args.domain,
                agent=args.agent,
                time_spent=args.time_spent,
                references=args.refs,
            )
            print(f"Recorded dead end: {entry_id}")

        elif args.command == "knowledge":
            entry_id = pad.knowledge(
                fact=args.fact,
                evidence=args.evidence,
                domain=args.domain,
                agent=args.agent,
                confidence=args.confidence,
                references=args.refs,
            )
            print(f"Recorded knowledge: {entry_id}")

        elif args.command == "insight":
            entry_id = pad.insight(
                observation=args.observation,
                context=args.context,
                domain=args.domain,
                agent=args.agent,
            )
            print(f"Recorded insight: {entry_id}")

        elif args.command == "query":
            if args.format == "json":
                data = pad.query_domain(args.domain) if args.domain else {"entries": pad.entries}
                print(json.dumps(data, indent=2, default=str))
            else:
                print(pad.format_briefing(args.domain))

        elif args.command == "check-falsified":
            results = pad.search_falsified(args.keyword)
            if results:
                print(f"⚠️  Found {len(results)} falsified hypothesis matching '{args.keyword}':")
                for r in results:
                    print(f"  [{r['hypothesis_id']}] {r['hypothesis_claim']}")
                    print(f"      Counterexample: {r['counterexample']}")
                return 1  # Non-zero = found falsified (warn the agent!)
            else:
                print(f"✓ No falsified hypotheses match '{args.keyword}'")
                return 0

        elif args.command == "check-dead-ends":
            results = pad.search_dead_ends(args.keyword)
            if results:
                print(f"⚠️  Found {len(results)} dead ends matching '{args.keyword}':")
                for r in results:
                    print(f"  [{r['id']}] {r['approach']}")
                    print(f"      Reason: {r['reason']}")
                return 1
            else:
                print(f"✓ No dead ends match '{args.keyword}'")
                return 0

        elif args.command == "summary":
            stats = pad.summary()
            print(json.dumps(stats, indent=2, default=list))

        elif args.command == "briefing":
            print(pad.format_briefing(args.domain))

        return 0

    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
