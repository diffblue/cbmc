# N3: Research Plan — Practical CDCL-Guided Execution of Beame-Liew's Critical-Strip Construction

## Status

**Phase 1 prototype (2026-05-11): partial.** A case-analysis DRAT proof
generator for array-multiplier commutativity is implemented in
`bench-multiplication/n3-beame-liew/`. The generator:

- emits a DIMACS CNF for `a*b = b*a` on an `n`-bit array multiplier
  (`generate_array_mul_comm.py`);
- emits a DRAT refutation by flat case-split on the `2^(2n)` input
  assignments, followed by a binary resolution tree over the `2n`
  input bits (`beame_liew_phase1_v2.py`);
- the DRAT proof is validated by `drat-trim` at `n = 1..11`;
- on equal CNFs, the prototype's DRAT proof is 4--10x smaller than
  CaDiCaL's DRAT output at `n <= 8` and remains smaller at `n = 9, 10`
  (though CaDiCaL starts timing out there).

What this does NOT yet achieve: the Beame-Liew polynomial-size
critical-strip refutation. The prototype's proof is
`O(2^(2n) * poly(n))`, dominated by the flat enumeration; the
Beame-Liew construction folds the `2^(2n)` leaves into a read-once
branching program whose size is `O(n^6 log n)` by exploiting the
`Delta = log(2n)` strip decomposition. Implementing that branching
program and the Krajicek-Prop.-2.6 translation from branching
program to DRAT is Phase 2-3.

See `bench-multiplication/n3-beame-liew/README.md` for details and
reproduction instructions.

## Goal

Turn the *theoretical* polynomial-size regular resolution proof of multiplier commutativity due to Beame and Liew~\cite{beame2017towards,beame2019toward} into an *executable* procedure that a SAT solver (or a DRAT proof checker) can produce and verify on real multiplier CNFs.

Their construction is well-defined mathematically but has never been implemented as a working tool. An earlier attempt by Beame's PhD student is reported to have failed (reviewer communication). Closing this gap would:

1. **Empirically validate** Beame-Liew's upper-bound claim on concrete instances.
2. Provide a **reference DRAT proof** that researchers can compare CDCL output against (directly addresses N1's Approach A).
3. Potentially enable a **CDCL heuristic** that guides clause-learning and decision-making toward Beame-Liew-style proofs, closing the CDCL-vs-proof-existence gap empirically.

## Background

### The Beame-Liew construction (summary)

For an $N$-bit unsigned integer multiplier using the array architecture, the SAT instance
$\varphi_{\text{Comm}}^{\text{Array}}(n)$ encodes the negation of $a \cdot b = b \cdot a$.

The construction in JACM 2019, §3:

1. **Critical strips.** Divide the bits of the assertion `e = (a·b) - (b·a)` into strips of width $\Delta = \log(2n)$. Each strip $\varphi_{\text{Strip}}(k)$ is a restriction of the full CNF to a narrow band of $\Delta$ consecutive bits.
2. **Branching program per strip.** For each strip, construct a read-once branching program (equivalent to a regular resolution proof via Krajíček's Prop. 2.6) of size $O(n^5 \log n)$ that refutes the strip. The branching program branches on the tableau variables, with a "sliding window" of $\Delta$ input bits.
3. **Global refutation.** The overall SAT formula is refuted by branching on the inequality-constraint assignments $\sigma_e(k)$ for $k \in [0, 2n-1]$. Each branch contains the clauses $\varphi_{\text{Strip}}(k)$, so we attach the branching program for that strip.
4. **Total size.** $O((n+1) \cdot n^5 \log n) = O(n^6 \log n)$, which in the full formula size $N = O(n^2)$ becomes $O(N^3 \log N)$.

The construction extends to diagonal and Booth multipliers (§4). For Wallace tree multipliers, an alternative algorithm (Algorithm 1, §5) gives a quasi-polynomial proof of size $2^{8 \log^2 n + O(\log n)}$.

### Why this has not been implemented

We know the following from the literature and the reviewer's communication:

- The construction is presented in terms of branching programs, not directly in CNF-resolution form. Translating branching-program nodes to resolution steps requires careful bookkeeping.
- The proof size is polynomial but the constants are large: $O(N^3 \log N)$ at $N = n^2 = 256$ (for $n = 16$) is already $\sim 10^8$ steps, producing a $\sim 1$ GB DRAT file.
- Beame's student (unnamed in correspondence) attempted implementation and was unsuccessful; the failure mode is not documented publicly.

The theoretical simplicity of the construction suggests the practical difficulty is implementation-level (bookkeeping, memory management, intermediate-size blowup during construction) rather than algorithmic. This is exactly the kind of problem where a careful engineering effort can succeed even after earlier ones have not.

## Proposed approach

### Phase 1: Implement the branching program for a single critical strip (2–3 weeks)

- Input: CNF for $\varphi_{\text{Strip}}(k)$ at a specific bit-width $n$ and strip position $k$.
- Output: a read-once branching program in an in-memory DAG representation.
- Validation: on small bit-widths ($n = 4, 6, 8$), verify that the branching program indeed refutes the strip (i.e., the empty clause is reachable).

### Phase 2: Translate branching program to DRAT proof (1–2 weeks)

- Use Krajíček's Prop. 2.6 construction: each branching-program node corresponds to a resolution step.
- Output: DRAT lines that a standard checker (DRAT-trim, GRAT) accepts.
- Validation: run DRAT-trim on the generated proof against the original CNF; confirm acceptance.

### Phase 3: Combine per-strip proofs into a full refutation (1 week)

- Branch on the inequality-constraint assignments $\sigma_e(k)$.
- For each branch, emit the Phase 2 DRAT for the corresponding strip.
- Validate DRAT on the full CNF.

### Phase 4: Scaling experiments (2–3 weeks)

- Run the implementation at $n = 8, 12, 16, 20, 24, 32$.
- Measure: construction time, DRAT file size, DRAT-trim verification time.
- Compare to: CaDiCaL's own DRAT proof on the same CNFs.

### Phase 5: Heuristic extraction (2–4 weeks, stretch goal)

- From the branching-program structure, extract a variable-ordering and clause-learning heuristic that steers a CDCL solver toward the same proof.
- Implement as a CaDiCaL plugin or custom restart/branch policy.
- Measure: does a CaDiCaL run with this heuristic find proofs closer to Beame-Liew's size than the default configuration?

## Risks

1. **Intermediate blowup.** Even if the final proof is $O(N^3 \log N)$, constructing it may require intermediate data structures (e.g., the full branching program expanded out) that are much larger. Mitigation: careful streaming output, on-the-fly BDD-like reduction.

2. **Engineering complexity.** The JACM construction has many case analyses (different multiplier architectures, different identity shapes). Mitigation: start with the simplest case (array multiplier, commutativity only) and extend incrementally.

3. **Negative result.** The implementation might simply not scale beyond small $n$, reproducing the earlier failure. Mitigation: at minimum, produce a correct-but-slow implementation that validates Beame-Liew's construction at $n \leq 12$; this alone is publishable as empirical validation.

4. **Tooling friction.** DRAT-trim has hard limits on proof size; GRAT is more modern. Need to pick the right checker. Mitigation: test early with small proofs, verify toolchain compatibility.

## Deliverables

| Month | Deliverable |
|---|---|
| 1 | Prototype: branching program for single strip at $n = 4, 6, 8$. |
| 2 | Full refutation: DRAT output for single strip, validated by DRAT-trim. |
| 3 | Full proof: multi-strip refutation for $\varphi_{\text{Comm}}^{\text{Array}}$ at $n = 8, 12$. |
| 4 | Scaling: results at $n = 16, 24, 32$; comparison with CaDiCaL. |
| 5–6 | Heuristic extraction (if Phase 4 succeeds); paper writeup. |

## Target venues

- **Tool paper / artifact**: SAT 2026 (tool paper track), CADE, or FMCAD.
- **If heuristic extraction succeeds**: main track of the same venues.
- **If implementation is publishable standalone**: CAV tool demo, or supplementary material to a theoretical follow-up.

## Why this is worth trying

- **Scientific gap**: an important theoretical result from 2019 has no implementation, creating a reproducibility hole that an interested research group can fill.
- **Direct impact on our Paper 1**: a working implementation would let us compare our empirical CDCL DRAT proofs against a gold-standard Beame-Liew proof on the same instances, potentially validating encoding-selection as a heuristic proxy.
- **Low downside**: even a partial success at small $n$ advances the literature; a full success at $n = 32$ would be a substantial contribution.

## Relation to companion plans

- **N1 (CDCL-vs-Beame-Liew gap characterization)**: an implementation enables Approach A of N1 directly.
- **N2 (controlled carry-causation experiment, executed)**: the present plan asks the orthogonal question "given the gap, can we close it with explicit construction?"
- **N4 (multi-encoding experiments)**: multi-encoding is an empirical shortcut that may approximate Beame-Liew's proof structure on particular instances; N3 would give the canonical reference.

## What this plan is NOT

- Not a plan to improve SAT solvers directly (that is N1's Phase 5 or the Pollitt et al.~\cite{pollitt2026factoring} line).
- Not a plan to prove a new theorem (Beame-Liew's theorems are already proven; we are executing them).
- Not a negative-result plan: we aim for a correct, reproducible implementation, and accept a restricted-scope result if scaling is the bottleneck.

---

*The reviewer's communication that Paul Beame's student attempted and failed is valuable context but not a deterrent: the failure mode is undocumented, and 7 years of improvements in SAT infrastructure (DRAT-trim, GRAT, LRAT, efficient CNF-to-circuit converters) may change what is practically feasible.*
