# N2: Research Plan — Controlled Experiment to Isolate Carry Propagation as SAT Hardness Driver

## Status

**EXECUTED (2026-05-06).** A simplified SMT-LIB-generator variant
of this experiment was run. Benchmarks and raw data:
- Generator: `bench-multiplication/n2-controlled/generate.py`
- Benchmarks: `bench-multiplication/n2-controlled/*.smt2`
- Raw data: `doc/paper-bitblasting/data/n2-controlled-experiment.tsv`
- Integrated into Paper 1 Section 3 (Table tab:n2).

Five variants were implemented (E0-E4) as pure SMT-LIB macro
expansions with identical partial-product topology; the
accumulator (bvadd vs. bvxor, sequential vs. parallel-tree,
binary vs. ternary) was the only variable. The primary finding:
at BW=8, integer sequential takes 6.4s with 184K conflicts while
the structurally identical GF(2) sequential formula solves in
38ms with 2.9K conflicts. Topology variations (parallel-tree vs.
sequential) change time by <5x; carry presence changes it by
orders of magnitude (>1000x at BW>=10). Carry propagation is
the dominant causal factor.

The original plan below is retained for reference; the extended
program it describes (E5 CSA-only variant, paired benchmarks
with tautology padding to match formula size, multi-solver
confirmation) remains future work.

---

## Goal

Provide empirical evidence that **carry propagation** specifically (not XOR structure, clause count, clause width, or variable count) is the dominant driver of SAT hardness for multiplication. The current paper shows correlation between carry propagation and hardness; this plan aims to turn correlation into isolated causation via a controlled experiment.

## Motivation

The GF(2) vs integer comparison in Section 3 of Paper 1 changes three things simultaneously:

1. Carry propagation: present (integer) vs. absent (GF(2))
2. Clause structure: 3-CNF gate encodings of (AND, OR, XOR of carry bits) vs. XOR-only
3. Variable interactions: sequential carry chain vs. independent columns

A reviewer can reasonably object: "Maybe it's the XOR-only structure that makes GF(2) easy, not the absence of carries."

## Proposed experimental design

We construct a family of "hybrid" encodings that independently vary these three dimensions:

| Encoding | Carry chain | Main op | Variable structure |
|---|---|---|---|
| E0 (integer baseline) | Yes | Add | Sequential |
| E1 (GF(2) baseline) | No | XOR | Parallel |
| E2 (integer, parallel-adder) | Yes but masked by CSA | Add | Parallel |
| E3 (GF(2), sequential) | No | XOR | Sequential |
| E4 (ternary carries) | Yes | 3-input add (mod 2^N) | Sequential |
| E5 (carry-save-only integer) | Partial (only last pass) | Add | Parallel |

The key insight: by comparing pairs that differ on one axis only, we can isolate the effect of each.

## Required pairs to establish causation

### C1: "Does parallel structure alone explain easy-ness?"

Compare E0 (sequential integer) vs. E2 (parallel integer).

- If E2 is easy and E0 is hard → parallel structure matters independently.
- If both hard → carry chain matters (not parallel-ness).

### C2: "Does absence of carries alone explain easy-ness?"

Compare E1 (parallel GF(2)) vs. E3 (sequential GF(2)).

- If both easy → absence of carries is sufficient, structure doesn't matter.
- If E3 is hard → sequential structure + some-operation is what's hard.

### C3: "Does carry chain in isolation cause hardness?"

Compare E0 (sequential integer) vs. E3 (sequential GF(2)) at same formula size.

- Structural analog: sequential in both cases. Only difference: carries.
- If E0 hard, E3 easy → carries are the cause.

### C4: "Do 3-input carries (more carrying) make it worse?"

Compare E0 (2-input carry) vs. E4 (3-input ternary carry).

- If E4 even harder → more carrying = more hardness. Supports monotone carry-effect.

## Implementation plan

### Phase 1: Build the encoding variants (1 week)

In CBMC's `src/solvers/flattening/bv_utils.cpp`:

1. **E1 (GF(2) parallel)**: already exists as carry-less variant via XOR gates. Formalize.
2. **E2 (integer parallel)**: carry-save-only integer multiplier (exists as `combacs`). Use with adaptive heuristic disabled.
3. **E3 (GF(2) sequential)**: new. Replace each `a⊕b` in GF(2) formula with a ripple-equivalent sequential structure: `t_i = t_{i-1} ⊕ a_i ⊕ b_i` (same variables, just ordered sequentially).
4. **E4 (ternary carries)**: new. Replace binary addition with `a + b + c (mod 2^N)` unit, where `c` is fed from a third multiplicand.
5. **E5 (CSA-only)**: carry-save adder tree, final ripple-propagate added as separate layer.

Each variant implemented as a `use_<name>` flag on `bv_utilst`.

### Phase 2: Construct paired benchmarks (1 week)

For each pair (Eᵢ, Eⱼ) of interest:
- Commutativity: `x*y = y*x` at BW=8,10,12,14,16,18,20,24.
- Associativity: `(x*y)*z = x*(y*z)` at BW=8,10,12.
- Matched formula size: if Eᵢ produces `k` clauses, pad Eⱼ with unit tautologies to match (so clause count is not a confound).

### Phase 3: Run experiment (2-3 weeks wall time)

For each (Eᵢ, benchmark) pair:
- 5 runs on CaDiCaL, collect median time and conflict count.
- DRAT proof size.
- Confidence intervals (5 runs should give ~1% CV based on our existing variance data).
- Machine: same as Paper 1 (Intel Xeon Platinum 8124M, 68 GB RAM).

### Phase 4: Analysis (1 week)

For each comparison C1-C4:
- Compute ratio of medians.
- Plot on log-scale as BW grows.
- Formal test: geometric-mean ratio across benchmarks with Wilcoxon signed-rank (one-sided).

## Expected results and scientific value

### Outcome A: Carries cause hardness (most likely)

Expected: E0 >> E3 on conflicts (at matching formula size); E2 ≈ E0 (CSA alone doesn't help without carry absence); E4 >> E0 (more carrying = more hardness).

**Publication:** "Controlled experiment isolating carry propagation as the hardness driver in SAT encodings of multiplication." Short paper at SAT or FMCAD.

### Outcome B: Structure matters too

Expected: E2 < E0 (parallel integer significantly easier); E3 ≈ E1 (parallelness doesn't matter for GF(2)).

**Publication:** "Both carry propagation and encoding structure drive SAT hardness." Still publishable; more nuanced story.

### Outcome C: Carries don't matter

Unlikely given existing data, but if E3 is hard, then our entire hardness hypothesis is wrong. In that case:

**Publication:** "Negative result: carry propagation alone does not explain SAT hardness of multiplication; the dominant factor is <X> (TBD from data)." This would also be valuable.

## Risks and mitigations

1. **E3 (sequential GF(2)) may not solver-behave like standard GF(2)**. Mitigation: carefully instrument the encoding to match variable ordering exactly.
2. **Formula size confounds**. Mitigation: pad with tautologies for matching, and also report "per-clause" conflict rate.
3. **Solver idiosyncrasies**. Mitigation: run on CaDiCaL, MiniSat, Kissat, and verify patterns hold cross-solver.
4. **Preprocessor effects**. Mitigation: run both with and without BVE; report both.

## Deliverables

1. CBMC patch implementing encoding variants E3, E4, E5 (E0-E2 already exist).
2. Benchmark suite with paired instances.
3. Experimental scripts in `doc/paper-bitblasting/data/N2-experiments/`.
4. Results TSV + Jupyter notebook for plots.
5. Short paper manuscript (SAT or FMCAD short paper track).

## Timeline estimate

- Phase 1 (implementation): 1 week
- Phase 2 (benchmarks): 1 week
- Phase 3 (run experiments): 2-3 weeks wall time (10-20 hours human time)
- Phase 4 (analysis and write-up): 1-2 weeks

**Total: ~6-8 weeks for a short paper.**

## Integration with Paper 1

Paper 1's conclusion already mentions this as future work. The result, once obtained, would upgrade Section 3's language from "carry propagation correlates strongly with SAT hardness" to "carry propagation causes SAT hardness (Theorem/Experiment X)."

Alternatively, if the controlled experiment reveals that structure matters too, Paper 1's thesis can be refined (not refuted): "encoding choice affects SAT hardness through two mechanisms: carry propagation depth and variable-dependency structure; combacs addresses both."
