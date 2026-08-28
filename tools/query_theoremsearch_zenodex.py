#!/usr/bin/env python3
"""Query TheoremSearch for ZenoDEX's highest-value proof obligations.

This is a research helper, not a consensus dependency.  It records the exact
queries and raw theorem-level responses so a literature review can be replayed
without turning semantic-search output into an authority source.
"""

from __future__ import annotations

import argparse
import json
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

SEARCH_URL = "https://api.theoremsearch.com/search"
GRAPH_URL = "https://api.theoremsearch.com/graph/embedding"
SCHEMA = "zenodex.theoremsearch.query_bundle.v1"

QUERIES: tuple[tuple[str, str], ...] = (
    (
        "parser_unique_decode",
        "a deterministic typed parser has a unique full-consumption parse and a decoder left inverse makes the encoder injective",
    ),
    (
        "parser_disjoint_choice",
        "disjoint FIRST sets imply an unambiguous deterministic parser choice with one token lookahead",
    ),
    (
        "parallel_commuting_updates",
        "pairwise commuting independent state updates are invariant under permutation of the execution schedule",
    ),
    (
        "parallel_disjoint_writes",
        "disjoint write sets and no read write conflicts imply parallel execution is equivalent to sequential execution",
    ),
    (
        "linearizable_atomic_commit",
        "compare and swap gives a linearizable atomic state transition with no partial effects on root mismatch",
    ),
    (
        "canonical_batch_auction",
        "a canonical batch auction clearing rule is order independent and maximizes a lexicographic welfare objective",
    ),
    (
        "double_auction_efficiency",
        "repeated double auction clearing converges to an individually rational Pareto efficient allocation",
    ),
    (
        "cfmm_axioms",
        "independence and scale invariance characterize the constant product market maker",
    ),
    (
        "amm_transaction_splitting",
        "an automated market maker fee rule is invariant to splitting one transaction into multiple transactions",
    ),
    (
        "amm_equilibrium",
        "existence of an equilibrium price vector for limit orders and automated market makers",
    ),
    (
        "rounding_conservation",
        "floor rounded pro rata allocation conserves the total after deterministic remainder assignment",
    ),
    (
        "merkle_bisection",
        "Merkle commitment bisection locates an invalid state transition with logarithmic communication",
    ),
)


def _request_json(request: urllib.request.Request, *, retries: int = 4) -> Any:
    delay = 1.0
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(request, timeout=45) as response:
                return json.loads(response.read().decode("utf-8"))
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError):
            if attempt + 1 == retries:
                raise
            time.sleep(delay)
            delay *= 2
    raise AssertionError("unreachable")


def theorem_search(query: str, *, n_results: int) -> Any:
    payload = json.dumps(
        {
            "query": query,
            "n_results": n_results,
            "sources": ["arXiv", "Stacks Project", "ProofWiki"],
            "citation_weight": 0.05,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    request = urllib.request.Request(
        SEARCH_URL,
        data=payload,
        headers={"Content-Type": "application/json", "User-Agent": "ZenoDEX-TheoremLedger/1"},
        method="POST",
    )
    return _request_json(request)


def graph_search(query: str, *, n_results: int) -> Any:
    params = urllib.parse.urlencode({"query": query, "n_results": n_results, "formality": "both"})
    request = urllib.request.Request(
        f"{GRAPH_URL}?{params}",
        headers={"User-Agent": "ZenoDEX-TheoremLedger/1"},
        method="GET",
    )
    return _request_json(request)


def build_bundle(*, n_results: int) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    for query_id, query in QUERIES:
        results.append(
            {
                "id": query_id,
                "query": query,
                "theorem_search": theorem_search(query, n_results=n_results),
                "theorem_graph": graph_search(query, n_results=n_results),
            }
        )
    return {
        "schema": SCHEMA,
        "service": {
            "search_url": SEARCH_URL,
            "graph_url": GRAPH_URL,
        },
        "n_results_per_query": n_results,
        "queries": results,
        "authority": "research_retrieval_only",
        "non_claims": [
            "semantic similarity is not proof relevance",
            "retrieved theorem text is not a verified ZenoDEX theorem",
            "formal informal matches require human review",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--n-results", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.n_results <= 50:
        raise SystemExit("--n-results must be in [1, 50]")
    bundle = build_bundle(n_results=args.n_results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
