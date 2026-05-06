# N1: Research Plan — Formal Proof of Exponential Resolution Lower Bound for Integer Multiplication Commutativity

## Goal

Prove (or refute) that proving integer multiplication commutativity (`x*y = y*x` over `N`-bit bitvectors) via CDCL requires resolution proofs of length exponential in `N`, while the analogous GF(2) commutativity has polynomial-length proofs.

The paper currently states empirical causation (§3 controlled experiment, §N2 results: carry presence drives hardness at least 1000× on commutativity). A formal proof-complexity result would upgrade this from "empirical causation at BW ≤ 16" to "proven exponential separation for all N."

## Background and prior art

1. **Haken 1985** ("The Intractability of Resolution") — pigeonhole principle has exponential resolution lower bounds. Technique: Size-width lower bound via the "bottleneck method."

2. **Ben-Sasson and Wigderson 2001** ("Short Proofs are Narrow") — size-width trade-off: any proof of width `w` has size at least `2^{Ω(w^2/n)}`.

3. **Urquhart 1987** — exponential lower bounds for Tseitin formulas over expander graphs.

4. **Buss 1995** ("Bounded Arithmetic and Propositional Proof Complexity", survey) — canonical reference for the bounded-arithmetic → propositional-proof translations. Key results relevant to N1:
   - **Theorem 44-47 (Craig interpolation for resolution, and limited-extension resolution)**: If a set of clauses `{A_i(p,q)} ∪ {B_j(p,r)}` has a resolution refutation of `n` inferences, there is a circuit of size `O(n)` that serves as an interpolant (a function of the shared variables `p` that separates the two half-refutations). Therefore, if we can show that any such interpolant must have superpolynomial circuit complexity, resolution proofs must be superpolynomial.
   - **Translation from `S_2^1` to Extended Frege (eF)**: basic arithmetic axioms, including associativity and commutativity of multiplication, have polynomial-size eF-proofs (Theorem 30, case 2: BASIC axioms). This tells us Frege-with-extension can do commutativity in polynomial size, but does **not** say the same about resolution.
   - **Razborov 1995 (Theorem 49)**: `S_2^2(α)` cannot prove superpolynomial circuit lower bounds on `NP` predicates unless the SPRNG conjecture fails (Razborov–Rudich natural proofs obstacle). This is an obstacle to any interpolation-based strategy that tries to invoke circuit lower bounds on `Sat` or other general `NP` functions — *but it does not apply to lower bounds on polynomial-time functions like multiplication itself*.

5. **Biere and Kauers 2019** ("New Challenges for Automated Reasoning in Multiplication Verification") — conjecture exponential lower bounds for integer multiplier verification; explicitly calls this open.

6. **Kojevnikov and Kulikov 2010** — bounds on SAT encodings of specific arithmetic problems.

7. **Brain 2021** — conjectures PC multiplier encoding is exponential size.

8. **Krajíček 1997** ("Interpolation theorems, lower bounds for proof systems, and independence results for bounded arithmetic") — the foundational paper that made resolution-via-interpolation concrete. Connects lower bounds on circuit complexity to resolution proof lengths.

## What is known vs unknown

- **Known**: Any *propagation-complete* (PC) encoding of `N`-bit integer multiplication requires exponentially many clauses (Brain 2021 conjecture, partially supported).
- **Known**: Some related arithmetic problems (pigeonhole, parity over linear equations) have exponential resolution lower bounds (Haken; Urquhart).
- **Known**: Commutativity of integer multiplication has polynomial-size eF-proofs (Buss 1995 Theorem 30, case 2 BASIC axioms).
- **Open**: Whether resolution proofs of `x·y - y·x = 0` over `N`-bit bitvectors are exponential in `N`.
- **Open**: Whether the empirical gap between integer and GF(2) multiplication commutativity reflects a provable proof-complexity separation.
- **Known (our §3 N2 experiment)**: Empirically, integer is ≥1000× harder than GF(2) on identical-topology formulas for commutativity at BW ≥ 10, with the gap widening with BW. This is compatible with a proof-complexity separation but does not prove one.

## The Buss-1995-informed strategy: interpolation

The most promising framework comes directly from Buss's presentation of Krajíček's interpolation theorem (Theorem 44-47). The strategy has three moves:

1. **Split the commutativity formula Φ_N into two halves.** Choose auxiliary variables carefully so the two halves share only the "observable" interface:
   - A-half: encodes the assertion `z₁ = x·y` using internal multiplier variables `q` (partial products, carries).
   - B-half: encodes `z₂ ≠ y·x` using internal multiplier variables `r` (a disjoint set).
   - Shared (observable) variables `p = {x, y, z₁, z₂}`.
   - The full formula `A ∪ B ∪ {z₁ = z₂}` is unsatisfiable iff multiplication commutes (always), so any refutation proves commutativity.

2. **Derive the interpolant.** By Buss's Theorem 45, any resolution refutation of `n` clauses gives an interpolant circuit `C(p)` of size `O(n)` such that:
   - if `τ(C) = False`, then A is unsatisfiable under τ (i.e., `z₁ ≠ x·y`);
   - if `τ(C) = True`, then B is unsatisfiable under τ (i.e., `z₂ = y·x` after all).

   Interpreting `C`: fed with `(x, y, z₁, z₂)`, `C` must decide whether `z₁` is the correct product of `x` and `y`. In other words, **`C` computes a version of multiplication verification**.

3. **Bound the interpolant's circuit complexity from below.**
   - If we can show any circuit that computes or verifies multiplication of `N`-bit numbers has size `ω(poly(N))`, then by Krajíček's theorem the resolution refutation has size `ω(poly(N))`.
   - *This is where N1 is hard.* Multiplication of `N`-bit integers is in polynomial-size circuits (trivially in `O(N^2)`, sub-quadratic with Karatsuba/FFT). So a direct "multiplication is hard to compute" argument does not work.
   - **The promising direction**: the interpolant must compute multiplication *relative to a fixed subset of input bits* (determined by the split). For suitable splits, this restricted form may be harder than general multiplication — e.g., if the split forces the interpolant to handle a carry-chain that crosses the A/B boundary. This is where the technical depth of N1 lies.

## Proposed strategy (revised after Buss 1995)

### Approach 1': Interpolation-based lower bound (refined)

**Target theorem (T1'):** For all `N`, every resolution proof of the canonical CNF encoding `Φ_N` of `N`-bit unsigned multiplication commutativity has size `n^{ω(1)}` (superpolynomial in `N`).

**Plan:**
1. Formalize `Φ_N` with partial-product and carry variables explicit.
2. Construct a split `A ∪ B` where the shared variables are `{x, y, z₁, z₂}` and the interpolant must compute a *carry-chain-crossing* predicate.
3. Show this predicate (a restricted form of multiplication verification) requires circuit size `n^{ω(1)}`, e.g., via a reduction from a known hard-for-small-circuits predicate (e.g., parity or inner-product mod 2 — but these are easy; better candidates needed).
4. Apply Krajíček's interpolation theorem (Buss Theorem 45).

**Risk:** Step 3 is likely the place where this approach either succeeds or reveals fundamental obstacles. If the "restricted multiplication predicate" is also in polynomial circuit size, this strategy fails. We would then need to appeal to more sophisticated models (monotone circuits, restricted depth, GF(2) arithmetic circuits) for the lower bound.

### Approach 2': Reduction from a known-hard resolution problem

**Target theorem (T2'):** There is a polynomial-size reduction from `PHP_n` (or Tseitin over an expander) to `Φ_N` such that any resolution proof of `Φ_N` yields a resolution proof of the source problem with a polynomial-size blowup.

**Plan:**
1. Identify a copy of `PHP_n` or a Tseitin formula embedded in `Φ_N`. The commutativity formula has `O(N²)` partial-product variables and `O(N²)` carry variables — enough degrees of freedom to embed an `N`-pigeon / `N-1`-hole structure.
2. Prove the embedding preserves resolution proof size.
3. Use Haken's `2^{Ω(n)}` lower bound on `PHP_n`.

**Risk:** Finding the explicit embedding is non-trivial. Multiplication's partial products are AND gates, not arbitrary relations, so the "pigeon" structure is not obviously there. This approach may need an intermediate step (e.g., embedding via a Tseitin formula that comes from a graph whose edges correspond to carry dependencies).

### Approach 3': GF(2) upper bound as a provable separation

**Target theorem (T3'):** There is a polynomial-size family of resolution proofs for GF(2) multiplication commutativity.

**Plan:**
1. Give an explicit polynomial-size resolution refutation for the GF(2) commutativity formula `Ψ_N`.
2. Technique: exploit the fact that GF(2) partial-product accumulation is *linear* in GF(2), so each output bit is an XOR of ANDs. Use the standard resolution proof of linear identities, which is polynomial in `N`.
3. This, combined with either Approach 1' or 2' on the integer side, would yield the provable separation.

**Payoff:** Even without proving T1' or T2', T3' alone is publishable: a polynomial-size proof for the GF(2) case, combined with our empirical evidence that integer is exponentially harder at BW ≥ 10, would be a substantial partial result.

### Approach 4': Obstacles and meta-theorem

Check whether the interpolation approach is blocked by natural-proof-style obstacles:
- **Natural proofs (Razborov-Rudich) do not obviously apply** here because multiplication is in `P/poly`, so lower bounds on multiplication-verification are not constrained by SPRNG. This is an important *negative* observation: the Razborov 1995 meta-obstacle does *not* rule out the approach.
- The approach could still be blocked by more subtle obstacles (e.g., algebraic natural proofs [Grochow et al. 2017]). Worth investigating.

## Deliverables and timeline (revised)

| Month | Deliverable |
|---|---|
| 1 | Formalize `Φ_N` CNF family in Lean 4; state T1', T2', T3' precisely. |
| 2 | Attempt T3' (GF(2) polynomial-size resolution upper bound). This is the most concrete and likely most tractable goal. |
| 3 | Attempt T1' (interpolation) or T2' (reduction), whichever looks more promising after T3'. |
| 4 | Formalize the relevant portions in Lean 4 / Isabelle / Coq as a verification step. |
| 5-6 | Write up. Target venues: CCC (Computational Complexity Conference), ICALP (Track B), STACS. |

## Tools

- **Lean 4 / Mathlib** for any formal proof (the algebraic paper already formalizes part of this; extending is natural).
- **Krajíček's textbook** "Proof Complexity" (Cambridge 2019) for technical details on interpolation.
- **Buss 1995** (this document) for the overall framework.
- **Chu, Krajíček** "Proof complexity and cryptography" for additional tooling on natural-proof obstacles.

## Expected outcome

A paper of one of the following forms:
- **Best case**: "Exponential separation between integer and GF(2) multiplication commutativity in resolution" (T1' + T3').
- **Realistic**: "A polynomial-size resolution proof for GF(2) multiplication commutativity" (T3' alone, with empirical evidence for the integer side from our current paper).
- **Fallback**: "Obstacles to proving exponential lower bounds for integer multiplication via interpolation" (a meta-result clarifying what techniques cannot work, guiding future research).

## Explicit connection to Paper 1

Paper 1 currently presents the empirical causation result (§3 Table tab:n2: carry presence is the dominant causal factor, ≥1000× at BW ≥ 10). The N1 result, in any of the three forms above, would upgrade this to a proof-theoretic separation. The narrative would then be: "empirically observed in our controlled experiment; provably an exponential gap." This is the single most impactful theoretical improvement possible for this line of work.
