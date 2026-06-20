# Verification: FairTraDEX & "Maximal Extractable Value in Batch Auctions"

**Date:** 2026-06-19 · **Method:** fetched both source PDFs directly (arxiv.org +
the author's site), extracted text, and checked every specific theorem number,
figure, and claim against the actual papers. This corrects a search-derived
summary whose Zhang half was self-flagged as unverified (garbled PDF).

## Bottom line

The summary's **substance holds up on both papers** — including the Zhang half it
admitted was reconstructed from snippets. The required fixes are **citation
precision** (wrong theorem labels, a missing assumption, a missed stronger
result) and **applicability grounding to ZenoDEX** (which the summary over-reached
on). Net: a good lead, now citation-safe, with the ZenoDEX mapping made honest.

| Claim in the summary | Verified? | Correction |
|---|---|---|
| FairTraDEX = real, WSFBA, $665M/98% EEV, escrow commit-reveal | ✅ | — |
| FairTraDEX equilibrium "Theorem 4.1" | ⚠️ substance ✅, label ❌ | It is **Theorem 1** |
| FairTraDEX main result "Theorem 5.1" | ⚠️ substance ✅, label ❌ | It is **Theorem 2** |
| FairTraDEX "Observation 0.D.2" | ⚠️ substance ✅, label ❌ | It is **Observation 5** |
| Zhang Fisher = poly-time MEV (Thm 3.13) | ✅ | "almost-linear" → **polynomial time** (the stated bound) |
| Zhang Arrow-Debreu Batch-MEV NP-hard (Thm 3.14) | ✅ | — (reduction from Max Acyclic Subgraph) |
| Zhang "50.01% approximation is NP-hard" | ⚠️ ✅ but incomplete | It is **Theorem 3.17** and **assumes the Unique Games Conjecture** (omitted) |
| (missed entirely) | ➕ | **Theorem 4.4**: for an **AMM with swap fees**, even a **0.01%-approximation is NP-hard, unconditionally** (reduction from Partition) — stronger, and the most ZenoDEX-relevant |

## G10 — FairTraDEX (verified)

**Cite:** Conor McMenamin, Vanesa Daza, Matthias Fitzi, Padraic O'Donoghue,
*FairTraDEX: A Decentralised Exchange Preventing Value Extraction*,
arXiv:2202.06384v2 [cs.GT], 4 Aug 2022. (No journal-ref in arXiv metadata; confirm
the DeFi/AFT venue before any formal citation — the summary's "AFT 2021" is
unconfirmed.)

**Verified in the PDF:** WSFBA = **Definition 1**; **Theorem 1** is the strict-Nash
equilibrium — *N=1*: clients submit market orders of width `fmcf`, the monopolistic
MM shows a market of width ≤ `fmcf` at the MIFP; *N≥2*: clients width > 1, MMs
width 1 at MIFP. **Theorem 2** is the protocol result (≥`nψ` `Register()` calls ⇒
implements a WSFBA in strict Nash, via `CommitClient`/`CommitMM`/`RevealClient`/
`RevealMM`). **Lemma 1**, **Lemmas 2–6**, **Corollary 1**, **Observation 5** all as
the summary described — only the labels drifted. The `$665M`/`98%`/Flashbots EEV
figures, `fmcf`, `Qnot`, MIFP are real.

**ZenoDEX applicability (the summary over-reached):** FairTraDEX is a
**market-maker-quote** mechanism — clients trade against MMs posting two-sided
markets. **ZenoDEX is CFMM (pools) + CoW (peer netting), with no MM-quote layer**,
so the paper's *core* contribution — the WSFBA width *equilibrium* (Theorem 1),
which governs MM quoting — **does not transfer**. What transfers is the
*scaffolding*: FBA batching, **ZK set-membership order privacy**, and
**escrow-enforced commit-reveal** — the last is the same family as the
commit-reveal seed source already built (`experiments/neutral_tiebreak_v1/seed_source.py`).
Also note FairTraDEX *assumes* a censorship-resistant chain with instant finality +
a trusted NIZK setup — those are **Tau-substrate** assumptions, not ZenoDEX
guarantees.

## G11 — Maximal Extractable Value in Batch Auctions (verified)

**Cite:** Mengqian Zhang (Yale), Yuhao Li (Columbia), Xinyuan Sun (Flashbots),
Elynn Chen (NYU), Xi Chen (NYU), *Maximal Extractable Value in Batch Auctions*,
ACM EC 2025. PDF: `mengqian-zhang.github.io/papers/batch.pdf`.

**Verified in the PDF (the half the summary couldn't read — it checks out):**
- **Theorem 3.13** — if the batch forms a **Fisher market** (all trades between a
  hub token `τ1` and each `τj`, none among the `τj`), optimal MEV is computable in
  **polynomial time** (Algorithm 1). *(Use "polynomial time," not "almost-linear" —
  that is the stated bound.)*
- **Theorem 3.14** — for a general **Arrow-Debreu** market, the **Batch-MEV**
  problem is **NP-hard** (reduction from Maximum Acyclic Subgraph).
- **Theorem 3.17** — no **(1/2+ε)-approximation** unless P=NP, **assuming the
  Unique Games Conjecture**. *This is the "50.01%" result; the UGC assumption is
  load-bearing and was omitted.*
- **Theorem 4.4 (summary missed this)** — for an **AMM with swap fees**, it is
  **NP-hard to compute even an ε-approximation for any constant ε** (i.e. even
  0.01% of optimal), **unconditionally** (reduction from Partition), sharpening the
  prior no-fee poly-time result of ref [3].

**ZenoDEX applicability (grounded, and subtler than the summary's "design toward
Arrow-Debreu"):**
- ZenoDEX's **single-pool** batch is structurally a **Fisher market** (a star: every
  trade is trader-vs-pool, none trader-vs-trader) — i.e. **Theorem 3.13's
  poly-time / efficiently-extractable case**, *not* the protected Arrow-Debreu
  case. The summary's "complexity as a defense" is therefore *weaker* than implied
  for the base CPMM path.
- BUT ZenoDEX charges **swap fees** (`fee_bps`), and **Theorem 4.4** says optimal
  MEV against a *fee-charging AMM* is inapproximable. So fees may *restore*
  hardness even in the single-pool case. **Whether ZenoDEX's single-pool-CPMM +
  CoW model lands in the easy (Fisher/3.13) or hard (fee-AMM/4.4, multi-asset/3.14)
  regime is an open modeling question** — not settled by "favor Arrow-Debreu."
- In all cases the hardness is **worst-case**: a mediator needs only *good-enough*
  extraction on the small, structured instances a real batch presents, so
  computational hardness is at best a **supplementary** layer behind the
  cryptographic (order privacy) and economic defenses — not a primary guarantee.

## Corrections to fold back into the summary
1. FairTraDEX: `Theorem 4.1 → Theorem 1`, `Theorem 5.1 → Theorem 2`,
   `Observation 0.D.2 → Observation 5`. Drop the unconfirmed "AFT 2021" venue.
2. Zhang: the 50.01% result is **Theorem 3.17, assuming the Unique Games
   Conjecture**; add the stronger **Theorem 4.4** (0.01%-inapproximable for
   fee-charging AMMs, unconditional).
3. Reframe "complexity as a defense": ZenoDEX's single-pool path is **Fisher
   (efficiently extractable)**; the hardness results are worst-case and apply to
   general multi-asset/fee settings — a supplementary layer, not Layer-3-as-solid.
4. FairTraDEX's WSFBA *equilibrium* does **not** map to ZenoDEX (no MM-quote
   layer); only the FBA + ZK-privacy + escrow-commit-reveal scaffolding transfers.
