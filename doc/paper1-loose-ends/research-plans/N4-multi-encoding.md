# N4: Research Plan — Multi-Encoding Experiments

## Status

**Executed (May 2026).** Implementation complete; ablation sweep over
9 benchmarks × 4 primary encodings × 7 secondary encodings (including
singleton baseline) completed. Headline findings:

- **Portfolio-like outcome** (Outcome N from the plan below).
- Median multi/min(A, B) = 1.31; geometric mean 1.23.
- Median multi/max(A, B) = 0.14 (multi is on median 7× faster than the slower singleton).
- 44 "rescue" cases where one singleton timed out and the multi-encoding solved within 60s.
- 42% of multi runs within 1.25× of min(A, B); 40% more than 1.5× slower than min(A, B).
- Integrated into Paper 1 as new Section~\ref{sec:multi-encoding}
  ("Multi-Encoding Combinations") after the Alternative Encodings section.

Raw data: `doc/paper1-loose-ends/data/multi-encoding-results.tsv`
(216 measurements).

## Goal

Answer the empirical question: does a SAT solver benefit from seeing *multiple* encodings of the same multiplication simultaneously, sharing inputs and outputs? Specifically, if we encode $z = a \cdot b$ both with encoding $E_A$ (e.g., shift-add) and encoding $E_B$ (e.g., comba-cs), with shared input and output bitvectors, and the two encodings' internal variables kept separate with $\mathrm{output}(E_A) = \mathrm{output}(E_B)$ constraints — does CDCL reach the correct answer faster, slower, or indistinguishably compared to using either encoding alone?

The intuition that this might help:
- The conjunction $\mathrm{enc}_A(a,b,z) \wedge \mathrm{enc}_B(a,b,z)$ provides **two structural handles** for CDCL to derive facts about $a, b, z$. If encoding $A$ is CDCL-friendly on benchmark family $X$ and encoding $B$ on family $Y$, the multi-encoding formula potentially inherits the union.
- This is philosophically related to **Extended Resolution**: each additional encoding introduces fresh "definition" variables, strictly more derivable clauses than either encoding alone. Pollitt et al.~\cite{pollitt2026factoring} obtain similar benefits retroactively through learned-clause factoring; we are doing it a priori at the encoding level.
- **BVE interaction** may clean up whichever encoding is less useful per instance, effectively giving an "encoding portfolio" at the formula level.

The intuition that it might hurt:
- **Formula bloat**: $\sim 2\times$ variables and clauses for the multiplier block. BVE may not recover the cost.
- **Heuristic confusion**: CDCL decision heuristics might spread focus across both encodings instead of committing to one.
- **Inprocessing interference**: what makes encoding $A$ effective may be undermined by $B$'s presence.

Empirical evidence already in Paper 1 points both ways: `g-only` redundancy helps (a clear win), BVA-style blowup hurts (a clear loss).

## Implementation

Complete as of May 2026 on `features/adder` branch.

### Scheme

`bv_utilst::unsigned_multiplier(a, b)` now accepts a `secondary_encoding` string setter. When non-empty:

1. Compute the primary output $z_A = \mathrm{enc}_A(a, b)$ using current flags.
2. Temporarily clear flags and set the secondary encoding's flags.
3. Compute $z_B = \mathrm{enc}_B(a, b)$.
4. Assert `set_equal(z_A, z_B)` bit-by-bit.
5. Restore primary flags; return $z_A$.

The caller receives a single output bitvector of the usual shape; internally the SAT formula contains both encodings' clauses plus the tie constraints.

### Interface

Env var `CBMC_MULTI_ENCODING=<name>` read by `smt2_solver`'s `configure_encodings`, passed to `boolbv.set_secondary_encoding()`. Accepted names: `shift-add`, `comba`, `comba-cs`, `dadda`, `dadda-cs`, `wallace`, `booth`, `block4`, `sortnet`.

### Sanity check

On `comm_12` (algebraic disabled):

| Configuration                     | Time    | Variables | Clauses |
|-----------------------------------|---------|-----------|---------|
| Single shift-add                  | 533 s   | 568       | 2,257   |
| Single comba-cs                   | 1.04 s  | 1,022     | 4,007   |
| Multi comba-cs + shift-add        | **1.08 s** | 1,552    | 6,239   |

The multi-encoding runs at essentially the speed of the faster encoding: 4% overhead vs comba-cs alone, 500× speedup vs shift-add alone. Bloat is ≈50% in variables and clauses (not 2× because partial products and I/O are shared).

## Experimental plan

### Ablation grid

- **Benchmarks** (algebraic pre-solver disabled to isolate encoding effect): `comm_8`, `comm_10`, `comm_11`, `comm_12`, `comm_14`, `strength_chain_16`, `strength_16_31`, `mul_ineq_12`, `bf16_mul_comm_v2`.
- **Primary encodings**: shift-add, comba-cs, booth, block4.
- **Secondary encodings**: none (baseline), shift-add, comba-cs, comba, dadda, booth, block4.
- **Solver**: CaDiCaL.
- **Timeout**: 60 s.
- **Resource limit**: 6 GB virtual memory.

Total: 9 × 4 × 7 ≈ 250 runs. Expected wall time ≈ 30–60 min.

### Metrics per run

- Solve time
- Conflict count
- Clause/variable count (formula size)
- Result (sat / unsat / T/O)

### Derived analyses

- **Is multi strictly better than singles?** For each benchmark, compare best-single vs best-multi. If multi is ≥20% faster than the better single on a majority of benchmarks, that's a strong positive result.
- **Is multi strictly worse?** If multi is ≥20% slower than the slower single on any benchmark, that's evidence of interference.
- **Is multi close to min(single_A, single_B)?** This is the "portfolio behaviour" hypothesis: solver picks the faster encoding.
- **Formula-size overhead per multi vs single_A**: should be roughly $(|\mathrm{vars}_B| + |\mathrm{clauses}_B|) / (|\mathrm{vars}_A| + |\mathrm{clauses}_A|)$.

## Possible outcomes and their interpretation

### Outcome P (positive): multi strictly dominates singles on many benchmarks

Significance: this is a novel encoding technique. Publishable as a SAT / FMCAD paper. Folds into Paper 1 as a new subsection or as a separate short paper.

Follow-up research:
- Optimal secondary-encoding selection per benchmark pattern.
- Three-way multi-encoding (primary + two secondaries)?
- Variable-sharing tricks (share more than just I/O)?

### Outcome N (neutral/portfolio): multi ≈ min(single_A, single_B) most of the time

Significance: gives a solver a free portfolio without explicit solver orchestration. Useful for deployment when the "right" encoding is unknown a priori.

Follow-up: compare multi-encoding to a portfolio solver (run both encodings in parallel, take first). Identify when multi wins vs when parallel wins.

### Outcome B (bad): multi is consistently worse than at least one single

Significance: encoding-level multi is not a general technique. Publishable as a negative result paragraph in Paper 1's §10 or a short note.

Follow-up: identify the failure mechanism (BVE interaction, heuristic split, etc.) to inform better designs.

## Risks

1. **Variable-sharing too aggressive**: if we accidentally share internal variables between encodings, one may contaminate the other. Our current implementation only shares inputs and outputs; this is the safest design.
2. **Timeout skews the picture**: 60s timeout may hide subtle differences at smaller scale. Mitigation: re-run interesting cases at 300s.
3. **Only one solver**: results may not generalize. Mitigation: re-run on MiniSat / CryptoMiniSat / Kissat if time permits.

## Deliverables

- [x] Implementation: `set_secondary_encoding` in `bv_utils.h`, wrapper in `unsigned_multiplier`, env-var wiring (`CBMC_MULTI_ENCODING`) in `smt2_solver.cpp`.
- [ ] Ablation sweep over the 250-run grid.
- [ ] Analysis and per-outcome writeup (Outcome P / N / B).
- [ ] Integration into Paper 1 (new subsection in §5 or §7 if outcome is P/N; paragraph in §10 if outcome is B).

## Relation to companion plans

- **N1 (CDCL-vs-Beame-Liew gap)**: multi-encoding is an empirical test of whether multiple concurrent structural handles help CDCL find short proofs. Not a direct answer to N1 but a data point.
- **N2 (carry-causation experiment, done)**: used different families of encodings to isolate carry propagation; N4 uses multiple encodings at once.
- **N3 (Beame-Liew implementation)**: orthogonal. Multi-encoding is an a-priori technique; Beame-Liew is a-posteriori construction.

## Why this is cheap and high-value

- Implementation effort: ~2 hours (done).
- Experimental wall time: ~1 hour (background).
- Analysis effort: ~1 hour.
- Writeup: ~2 hours (scales with outcome).
- Total: ~6 hours for a possibly publishable result.

The early sanity-check result (comm_12: multi close to the faster single) is already encouraging. Full results will determine whether to spin this out as its own paper or fold into Paper 1's encoding-selection narrative.
