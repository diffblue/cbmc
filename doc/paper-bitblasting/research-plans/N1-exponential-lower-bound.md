# N1: Research Plan — Formal Proof of Exponential Resolution Lower Bound for Integer Multiplication Commutativity

## Goal

Prove (or refute) that proving integer multiplication commutativity (`x*y = y*x` over `N`-bit bitvectors) via CDCL requires resolution proofs of length exponential in `N`, while the analogous GF(2) commutativity has polynomial-length proofs.

The paper currently states this only as empirical observation. A formal result would significantly strengthen the contribution.

## Background and prior art

1. **Haken 1985** ("The Intractability of Resolution") — pigeonhole principle has exponential resolution lower bounds. Technique: Size-width lower bound via the "bottleneck method."

2. **Ben-Sasson and Wigderson 2001** ("Short Proofs are Narrow") — size-width trade-off: any proof of width `w` has size at least `2^{Ω(w^2/n)}`.

3. **Urquhart 1987** — exponential lower bounds for Tseitin formulas over expander graphs.

4. **Beame et al.** — various lower bounds for graph pigeonhole and counting principles.

5. **Biere and Kauers 2019** — "New Challenges for Automated Reasoning in Multiplication Verification." Conjectures (but does not prove) exponential lower bounds for integer multiplier verification. Explicitly calls this an open question.

6. **Kojevnikov and Kulikov 2010** — bounds on SAT encodings of specific arithmetic problems.

7. **Brain 2021** — conjectures PC multiplier encoding is exponential size.

## What is known vs unknown

- **Known**: Any _propagation-complete_ (PC) encoding of `N`-bit integer multiplication requires exponentially many clauses (Brain 2021 conjecture, partially supported).
- **Known**: Some related arithmetic problems (pigeonhole, parity over linear equations) have exponential resolution lower bounds.
- **Open**: Whether resolution proofs of `x*y - y*x = 0` over `N`-bit bitvectors are exponential in `N`.
- **Open**: Whether the gap between integer and GF(2) multiplication commutativity is provable.

## Proposed strategy

### Approach 1: Direct size-width lower bound

**Target theorem (T1):** For all `N`, every resolution proof of commutativity of `N`-bit unsigned integer multiplication has size at least `2^{Ω(N)}` on the canonical shift-add CNF encoding.

**Plan:**
1. Formalize the commutativity formula as a CNF family `Φ_N`:
   - Encode `z₁ = x·y` and `z₂ = y·x` using standard shift-add.
   - Negate the equality: `¬(z₁ = z₂)` becomes a set of clauses.
2. Define a "bottleneck" random variable over partial assignments:
   - Consider a random assignment of `x` drawn from a specific distribution.
   - Show any sub-formula on fewer than `w` variables (for suitable `w = Ω(N)`) has high probability of being simultaneously satisfiable.
3. Apply the Ben-Sasson–Wigderson size-width theorem:
   - Width lower bound `w(Φ_N ⊢ ⊥) ≥ Ω(N)` plus formula width `O(1)` gives size `2^{Ω(N^2/N)} = 2^{Ω(N)}`.
4. Key technical step: reducing to a known hard problem (e.g., pigeonhole or a counting problem) via an affine embedding.

**Risk:** The reduction may not be straightforward because shift-add CNF has specific structure that doesn't obviously contain pigeonhole as a minor.

### Approach 2: Reduction from parity / linear algebra over GF(2)

**Target theorem (T2):** There is a polynomial-time reduction from `N`-bit _integer_ multiplication commutativity to a related problem known to have exponential resolution lower bounds.

**Candidate target problems:**
- Urquhart formulas (Tseitin over expander)
- `MOD_p` counting principles for `p > 2` (parity won't work directly because it's in GF(2))

**Plan:**
1. Observe that in integer multiplication, the high-order bit of `x·y` is a degree-`N` multilinear function of the input bits (with specific coefficients from integer addition).
2. Show that deciding the value of this high-order bit reduces (in the CNF representation) to a problem with known exponential lower bound.
3. Since the commutativity formula includes this high-order bit agreement as a constraint, the exponential lower bound carries over.

**Risk:** The reduction must preserve CNF size polynomially and clause width; these constraints are non-trivial.

### Approach 3: Lower bound relative to a specific encoding family

**Target theorem (T3):** For any encoding in a certain family (that we characterize algebraically), the resolution proof length of integer multiplication commutativity is exponential in `N`.

**Plan:**
1. Define a class of "carry-propagation-faithful" encodings: encodings where the carry bit at position `i` is represented by a variable that can be resolved to either 0 or 1 by the solver.
2. Show that any such encoding must include a gadget isomorphic to a known hard sub-formula.
3. Apply existing lower bounds.

**Advantage:** This weaker statement is easier to prove and still useful (captures shift-add, Dadda, Comba, combacs, Booth).

**Risk:** The characterization "carry-propagation-faithful" may be technical.

### Approach 4: GF(2) upper bound as a separating oracle

**Target theorem (T4):** GF(2) multiplication commutativity has resolution proofs of polynomial size (we know it does empirically).

**Plan:**
1. Explicitly construct a polynomial-size resolution proof for GF(2) commutativity.
2. This establishes the existence of a provable separation between integer and GF(2), conditional on proving the integer side exponential.
3. The construction: use the fact that GF(2) multiplication's bit-level circuit is a collection of XOR trees; prove commutativity one bit at a time via small local arguments.

**Payoff:** Even without proving T1, T4 gives a concrete witness of why the two problems are fundamentally different, strengthening the empirical observation.

## Deliverables and timeline

| Month | Deliverable |
|---|---|
| 1 | Literature review and identification of most promising reduction target |
| 2 | Formal statement of `Φ_N` family and the separation theorem, written in Lean 4 |
| 3 | Attempt Approach 4 (GF(2) upper bound) — formal construction |
| 4 | Attempt Approach 3 (restricted encoding family lower bound) |
| 5-6 | Write up results, submit to a proof complexity venue (STACS, CCC, ICALP) |

## Tools

- **Lean 4 / Mathlib** for any formal proof (the algebraic paper already formalizes part of this; extending is natural).
- **CaDiCaL / CakeML** for machine-checked proof verification of any explicit constructions.
- **PRADA / RaMus** for automated proof complexity lower bound research tools.

## Expected outcome

A paper of the form:
- **Theorem:** Resolution proof length of integer multiplication commutativity is `2^{Ω(N)}` (under `<caveat>`).
- **Separation:** GF(2) commutativity has polynomial proofs.
- **Implication:** The exponential-scaling phenomenon observed empirically in SAT solvers for multiplication is proof-theoretic, not solver-heuristic. This closes an open question posed by Biere and Kauers (2019).

## Fallback

If a full lower bound is not provable in the available time:
1. Prove a conditional lower bound (e.g., "assuming Hypothesis H, the integer case is `2^{Ω(N)}`").
2. Prove a weaker "no short polynomial calculus proof" result, which is typically easier and still publishable.
3. Formalize the GF(2) upper bound (Approach 4) alone as a separation result, which is itself a contribution.

## Connection to Paper 1

A proof, even conditional or restricted, would be cited from Paper 1 Section 3 to upgrade "carry propagation correlates strongly with SAT hardness" to "carry propagation provably causes exponential resolution length in specific encoding families (Theorem X)." This is the single most impactful improvement a reviewer would ask for.
