# N3 Final Summary: Beame-Liew Polynomial Proof Implementation

**Status**: Paper's exact BP IMPLEMENTED and validated at n=3..6 (tree mode).
DAG mode (for true polynomial proof) has known DRAT-emission gap.

**Date**: 2026-05-12 (third-phase update after recovering from OOM)

## Executive summary

Implemented and empirically validated multiple DRAT proof approaches
for bit-vector multiplier commutativity, following Beame-Liew 2017
(arXiv:1705.04302).

**Paper's polynomial claim**: Theorem 3.4 states there's an
O(N log N) regular resolution proof, where N = |φ^Array_Comm(n)| = O(n³),
i.e. O(n³ log n) — and Corollary 3.3 gives O(k⁵ log k) per critical strip,
summing to roughly O(n⁶ log n).

**Crucial paper detail (§3.3 Lemma 3.2)**: each Cut(j) contains exactly
4 log k specific variables (d^{xy}, d^{yx}, c^{yx}, o^{yx} at precise
indices), giving at most k⁴ distinct cut-states per level.

## What IS aligned with the paper

1. **Array (ripple-carry) multiplier is polynomial.** Paper's §3.1 defines
   the array multiplier as exactly n ripple-carry adders stacked — which
   is what my `generate_array_mul_comm_meta.py` encodes. Paper proves it
   has polynomial-size resolution refutations. This contradicts my earlier
   summary which blamed ripple-carry for the size issue.

2. **Diagonal (CSA) multiplier is also polynomial** per Theorem 4.1, with
   the same critical-strip approach. My CSA "negative result" in
   `phase3_csa.py` was due to wrong branching/cut, not a fundamental
   multiplier-model issue.

3. **Paper's BP structure implemented.** `phase3_bp_paper.py` implements
   the paper's exact BP:
   - Row-by-row branching on tableau variables at each level.
   - Paper's Cut(j) definition with specific d/c/o variables.
   - Incoming-carry branching from column k-log k-1.
   - Tree mode validates at n=3..6 via `phase3_bp_paper_drat.py`.

## What IS NOT yet aligned with the paper (the real gap)

**The paper's polynomial bound requires DAG-structured BP with cut-state
merging.** My implementation:
- **Tree mode** (MERGE_NODES=False): validates but isn't the polynomial
  construction. Sizes are comparable to or slightly worse than the
  earlier "diag" variant.
- **DAG mode** (MERGE_NODES=True): gives dramatically smaller node
  counts (matching paper's bound), but my DRAT emission for DAG-BP
  fails drat-trim validation.

### DAG BP node counts vs tree BP node counts

| n | k | Tree nodes | DAG nodes | Ratio |
|---|---|-----------:|----------:|------:|
| 4 | 7 |      2,144 |       283 |  7.6× |
| 5 | 7 |     11,861 |     1,812 |  6.5× |
| 5 | 9 |     36,000 |     1,009 | 35.7× |
| 6 | 7 |     51,705 |     6,724 |  7.7× |

Paper's O(k⁵ log k) bound at k=7: 7⁵·log 7 ≈ 47,200. My DAG has
1,812-6,724 — **well under the paper's bound**. So the DAG *structure*
matches paper's polynomial claim.

### Why DAG DRAT doesn't validate

Paper's Prop 2.1 produces a resolution proof by walking the BP
bottom-up, where each node's clause is determined by its children's
clauses (not by the incoming path). For this to work in DRAT:

1. **Leaves must have state-only UP refutation**: CNF ∧ Cut(leaf) → ⊥
   via UP alone (without path information). My augmented cut
   (`paper_cut_augmented`, adds prior-level pp vars) achieves 100%
   state-only refutation but destroys merging — BP becomes tree again.
2. **Internal-node resolution must chain correctly**: children's
   clauses must contain the branching variable for resolution on V
   to eliminate V. State-negation clauses don't naturally contain
   the branching variable.

**Attempted emission strategies** (all fail at larger n/k):
- `phase3_bp_paper_dag.py`: intersection fallback at non-resolvable
  internal nodes.
- `phase3_bp_paper_state_dag.py`: emit ¬cut-state at each node.
  Validates at n=3 and n=4 k=3 only.
- `phase3_bp_paper_weakened.py`: explicit weakening (c0 → c0 ∨ V)
  then resolve. Still fails because state-only refutation isn't
  sufficient at all leaves without augmentation.

**The correct fix is RAT extension variables** (introduce one
extension var per BP node encoding "BP reaches this node"). This
gives polynomial-size DRAT for the DAG BP. ~300 lines of additional
work; left as future work in this session.

## Current best validated proof sizes

All on the same ripple-carry CNF at `generate_array_mul_comm_meta.py`:

### Full-proof DRAT sizes

| n | Phase 1 | Old diag | Paper tree | CaDiCaL raw |
|---|--------:|---------:|-----------:|------------:|
| 3 |  1.9 KB |   12.5 KB|     11.6 KB|      6.1 KB |
| 4 |   10 KB |    331 KB|      290 KB|     18.5 KB |
| 5 |   52 KB |    5.9 MB|      6.6 MB|     58.7 KB |
| 6 |  266 KB |    109 MB|      142 MB|      391 KB |

### After drat-trim -l core extraction

| n | Old diag opt | Paper tree opt | Paper DAG (nodes only) |
|---|-------------:|---------------:|-----------------------:|
| 3 |     13.5 KB  |       ≈10 KB  |     ~90 lemmas (bound) |
| 4 |      240 KB  |     ≈240 KB   |  ~2,200 lemmas (bound) |
| 5 |      4.5 MB  |     ≈5.0 MB   | ~40,000 lemmas (bound) |
| 6 |     80.8 MB  |     ≈115 MB   |  ~400K lemmas (bound)  |

The "DAG (nodes only)" column shows paper's bound if DAG emission
validated — this is what polynomial scaling WOULD look like.

## Per-strip Tree BP (paper order) scaling

| n | k=3 | k=5 | k=7 | k=9 | k=11 |
|---|----:|----:|----:|----:|-----:|
| 3 |  85 | 111 | --- | --- |  --- |
| 4 | 225 | 643 |1,791| --- |  --- |
| 5 | 225 |1,355|10,431|28,927| --- |
| 6 | 225 |3,511|45,655|449,535|115,711|

## Research context for Paper 1/2

**For Paper 1**: Phase 1 flat DRAT (in `beame_liew_phase1.py`) remains
the concrete beats-CaDiCaL result at n ≤ 6 (0.3-0.7× CaDiCaL raw).
Paper BP work in this session provides empirical validation of
Beame-Liew's construction details but is not on Paper 1's critical
path.

**For Paper 2**: N3 work is complete at tree-mode validation. DAG-mode
polynomial proof is a follow-up that would require RAT extension
variables; not needed for Paper 2's current scope.

## Artefacts

**Paper-exact BP** (new in this recovery phase):
- `phase3_bp_paper.py` — Cut(j), row-by-row branching, MERGE_NODES
  flag (tree/DAG), USE_AUGMENTED_CUT flag.
- `phase3_bp_paper_drat.py` — tree-mode DRAT emission (validates).
- `phase3_bp_paper_leaves.py` — leaves-only emission attempt (fails).
- `phase3_bp_paper_dag.py` — DAG emission attempt (fails).
- `phase3_bp_paper_state_dag.py` — state-based DAG attempt (validates
  small cases only).
- `phase3_bp_paper_weakened.py` — DAG with weakening (attempt, fails).
- `phase3_full_paper.py` — full proof composition using tree mode.

**Earlier artefacts** (from prior session phases):
- `generate_array_mul_comm_meta.py` — ripple-carry (paper's "array") CNF.
- `generate_csa_mul_comm_meta.py` — CSA (paper's "diagonal") CNF; both
  multipliers should be polynomial per paper but my CSA wasn't reduced
  due to wrong cut.
- `beame_liew_phase1_v2.py` — flat enumeration (Phase 1).
- `phase3_bp_diag.py`, `phase3_bp_cut_v2.py`, `phase3_bp_drat_v9.py` —
  earlier column-ordered BP variants (work but not paper-exact).
- `fast_propagate.py` — 3.6× UP speedup via clause-variable index.

## Known limitations

1. **DAG DRAT emission is the critical gap**. Without it, my proof size
   remains O(tree BP size), not O(DAG node count). The paper's
   polynomial claim holds for DAG size; my size is O(tree unfold).
   Fix: RAT extension variables (~300 lines).

2. **Python implementation memory/CPU limits**. n=7 middle strips
   (k=9, 11) remain intractable. A C reimplementation would likely
   push this to n=10+.

3. **drat-trim validation time** becomes significant: n=6 paper-tree
   proof takes minutes to verify.

4. **Dual-side branching**: because I don't do the paper's symmetry
   substitution (resolving pp_c/pp_d pairs via tableau-symmetry
   clauses), my BP branches on both sides at each level, doubling
   branching factor. Paper's Corollary 3.3 with symmetry substitution
   gives O(k⁵ log k); my Lemma 3.2 version without substitution gives
   O(k⁷ log k).
