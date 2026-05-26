# N1 (revised): Research Plan — Characterizing the CDCL-vs-Beame-Liew Gap

## Status

**Premise update (May 2026).** Beame and Liew~\cite{beame2017towards,beame2019toward} have *refuted* the exponential-resolution conjecture that motivated the original N1. They give polynomial-size regular resolution proofs for any degree-2 ring identity (commutativity, distributivity) on array, diagonal, and Booth multipliers, and quasi-polynomial-size ($n^{O(\log n)}$) proofs for Wallace tree multipliers. The original N1 plan (prove an exponential lower bound) is therefore obsolete. This document replaces it.

## Revised goal

**Close the CDCL-vs-Beame-Liew gap**: formally characterize why current CDCL heuristics do not find the polynomial-size regular resolution proofs of commutativity that Beame-Liew proved to exist, and under what formula-level transformations CDCL does find them.

Beame and Liew explicitly identify this as an open engineering problem in JACM 2019:

> "The observed scaling of SAT solver performance on these problems suggests that they do not currently find proofs matching even these upper bounds. An important direction for improving SAT solvers is to find the right guiding information to add, either to the formulas derived from the circuits or to CDCL SAT solver heuristics, to help them find shorter proofs."

Paper 1's controlled N2 experiment is an empirical data point consistent with this gap (integer commutativity is ≥1000× harder than GF(2) under shift-add at BW ≥ 10, despite the polynomial proof's existence). Our encoding-selection contribution is one answer to "what guiding information to add." N1 asks: can we turn this into a *characterization* rather than a point estimate?

## Three concrete sub-questions

### Q1. Which encoding transformations preserve / destroy the Beame-Liew proof?

Beame-Liew's construction uses the standard shift-add bit-matrix structure of a multiplier, "critical strips" of width $\log(2n)$, and a branching program that scans each strip. Their construction relies on specific properties of the partial-product grid.

- **Q1a.** Does the construction transfer to carry-save encodings (Dadda, combacs)? Our empirical evidence (Paper 1, Table tab:scaling) suggests yes — combacs solves commutativity at BW=256 in 4.7 ms. But does Beame-Liew's proof translate mechanically, or does carry-save need a different critical-strip argument?
- **Q1b.** Does the construction transfer to Booth encoding? Booth's partial-product structure is different (signed digits). A Beame-Liew-like proof for Booth multipliers is an open question the JACM paper does not cover directly.
- **Q1c.** Does the construction transfer to sorting-network encodings, block-multiplier encodings, or other non-standard forms? These have different grid structures.

### Q2. What is the shortest polynomial proof that CDCL actually finds on the encoding in practice?

- **Q2a.** Given a CDCL solver (CaDiCaL) with its standard heuristics and a specific encoding (e.g., combacs), measure the empirical proof length (DRAT proof size, resolution proof length) as BW grows. Compare to Beame-Liew's upper bound ($O(N^3 \log N)$ where $N = O(n^2)$).
- **Q2b.** Identify the specific heuristic decisions that lead CDCL to short vs long proofs. This could use existing tools (e.g., MaxSAT on conflict-driven heuristic traces).
- **Q2c.** Characterize "CDCL-reachable" proofs within the polynomial-proof class: a subset of regular resolution proofs that standard CDCL heuristics can construct in polynomial time. This may or may not include Beame-Liew's proofs.

### Q3. Can we construct a formal characterization?

- **Q3a.** Formal definition: under what encoding properties is CDCL's running time within a polynomial factor of the Beame-Liew proof size?
- **Q3b.** Is there a formula-transformation family $T$ such that for any CNF $\varphi$ encoding a degree-2 ring identity, $T(\varphi)$ is a formula on which CDCL reaches a short proof?
- **Q3c.** Alternative: is there an equivalent CDCL variant (e.g., with XOR-aware reasoning~\cite{danner2025sat}) whose standard heuristics find Beame-Liew-size proofs on standard encodings, without explicit guidance?

## Three proposed approaches

### Approach A: Empirical characterization (engineering-heavy)

1. Take Beame-Liew's construction from the JACM paper (Section 3, Array multipliers) and implement it as a proof generator that produces a DRAT proof directly from a multiplier CNF.
2. Compare to the DRAT proof produced by CaDiCaL on the same CNF.
3. Analyze where the two proofs diverge: which resolution steps does Beame-Liew's proof make that CaDiCaL does not, and vice versa.
4. Identify heuristic decisions (variable order, clause-learning strategy) that would steer CaDiCaL toward Beame-Liew-style proofs.

**Effort:** substantial engineering; Beame-Liew's construction has never been successfully implemented (prior attempt by Paul Beame's student failed — reviewer communication). See also companion plan N3 ("Practical CDCL-guided execution of Beame-Liew"), which focuses on this implementation challenge as a standalone effort.

**Risk:** The construction may not admit an efficient implementation — the BDD-based branching program has $O(n^6 \log n)$ nodes in its parameters, which at 16 bits is $\approx 10^7$ nodes, manageable; but at 32 bits it's $\approx 10^9$, borderline.

### Approach B: Via interpolation (theory-heavy)

Use the Craig interpolation framework: a CDCL execution of $\varphi_{\text{comm}}^{\text{Array}}$ produces a regular resolution refutation, which is a read-once branching program. The key property of the encoding under which CDCL reaches a short proof can potentially be characterized via *interpolant circuit complexity*~\cite{krajicek1997interpolation}: if the interpolant's natural circuit representation matches the encoding structure, CDCL can find a small one.

**Effort:** Moderate theoretical effort. Tight technical work but builds on established machinery.

**Risk:** Interpolation gives *size* bounds, not time bounds; the result may be "proofs of size $S$ exist but CDCL may still take $S \cdot \text{poly}$ decisions to find them."

### Approach C: Empirical-theoretical hybrid

Combine parts of A and B:
1. Run CaDiCaL on many encodings + benchmarks; record whether the DRAT proof has Beame-Liew-style critical-strip structure.
2. Correlate presence/absence of that structure with running time.
3. Formalize: "An encoding $E$ is CDCL-friendly for commutativity iff CaDiCaL's proof on $\varphi_E$ admits a decomposition into $O(\log n)$-width critical strips, each of polynomial size."

**Effort:** Realistic; grows the empirical dataset already collected in Paper 1 with proof-structure analysis.

**Risk:** The definition may be hard to verify algorithmically.

## Relation to companion research plans

- **N2 (controlled carry-causation experiment)**: already executed; empirically supports the existence of the gap. N1 asks the theoretical question N2 could not.
- **N3 (implement Beame-Liew)**: focused engineering plan to turn the JACM construction into executable code; independent of N1 but a possible input to Approach A.
- **N4 (multi-encoding experiments)**: empirical exploration of whether CDCL benefits from seeing multiple encodings simultaneously; relevant to Q1 (does the Beame-Liew proof transfer to multi-encoding conjunctions?).

## Deliverables

| Month | Deliverable |
|---|---|
| 1–2 | Literature survey beyond what Paper 1 already cites; identification of Beame-Liew's construction internals; decision on Approach A/B/C. |
| 3–4 | First result: either empirical characterization (Approach C) or an interpolation bound (Approach B) or an implementation (Approach A). |
| 5–6 | Writeup; target venues: proof-complexity track of CCC / ICALP-B if theoretical; SAT / FMCAD / CADE if empirical. |

## Why this matters

- **Theoretical**: closing Beame-Liew's open problem directly.
- **Practical**: characterization would inform encoding-selection heuristics (Paper 1's contribution) with formal backing rather than empirical lottery.
- **Contextual**: Danner 2025 and Pollitt et al. 2026 both address the same broad question from different angles (solver generalization, inprocessing). N1 would add a proof-complexity characterization to the picture.

## What this plan is NOT

- Not a lower-bound proof (the lower bound is false, per Beame-Liew).
- Not a proof that CDCL is inherently weak (Beame-Liew note that regular resolution, which CDCL produces, contains their short proofs).
- Not a plan to build a better solver (that's N3 or the Pollitt/Danner line).

---

*This document supersedes the earlier N1 plan which aimed to prove an exponential resolution lower bound for integer multiplication commutativity. That lower bound is false.*
