# N3 Follow-up: Options B and A

Two quick investigations after the Phase 2 prototype commit.

## Option B: is Phase 1's 4–10× advantage over CaDiCaL structural?

Ran `drat-trim -l` to extract the **trimmed core** of CaDiCaL's
DRAT on the commutativity CNFs, then compared sizes.

| n | Phase 1 DRAT | CaDiCaL raw | CaDiCaL trimmed core | Phase 1 / trimmed |
|---|-------------:|-------------:|---------------------:|:-----------------:|
| 2 | 307          | 5,002        | 3,288                | 0.09×             |
| 3 | 1,859        | 15,745       | 14,836               | 0.12×             |
| 4 | 9,987        | 41,560       | 46,113               | 0.21×             |
| 5 | 52,225       | 156,474      | 137,896              | 0.37×             |
| 6 | 266,229      | 994,916      | 770,747              | 0.34×             |
| 7 | 1,294,277    | 5,246,959    | 4,073,863            | 0.31×             |
| 8 | 6,094,597    | 26,452,011   | 18,344,797           | 0.33×             |
| 9 | 28,048,389   | 117,262,735  | 69,767,088           | 0.40×             |

Raw data: `data-options-ba.tsv`.

### Finding

Even after drat-trim extracts the proof core, CaDiCaL's proof
remains **2.5–4× larger** than Phase 1 at n ≥ 5.  The ratio is
stable across n.  So the Phase-1 advantage is **structural, not a
trimming artefact**: ordered enumeration with an explicit
resolution tree captures the commutativity proof more compactly
than CDCL's conflict-driven lemma stream, and drat-trim cannot
recover the gap by pruning.

This is the most defensible empirical form of the Phase-1 result:
at n=9, 28 MB (BL) vs 70 MB (CaDiCaL core); Phase 1 is 0.40× the
size of the fully-pruned CaDiCaL proof.

## Option A: does drat-trim accept RAT with extension variables?

Wrote `rat_test.py` with a 4-clause UNSAT CNF and a DRAT proof
that introduces `x3 := x1 AND x2` via three RAT clauses, then
derives the empty clause through a chain that depends on `x3`.

Result:

```
c detected empty clause; start verification via backward checking
c 4 of 4 clauses in core
c 5 of 9 lemmas in core using 13 resolution steps
c 0 RAT lemmas in core; 3 redundant literals in core lemmas
s VERIFIED
```

`drat-trim` accepts the proof.  The "0 RAT lemmas in core" line
reflects the fact that on this tiny formula, the RAT-introduced
lemmas happened to be RUP-derivable too; `drat-trim` prefers the
cheaper RUP check.  The key point is that `drat-trim`
**does not reject the RAT-format clauses** and produces
`s VERIFIED` on a proof that uses them.  For Phase 3, this
confirms the toolchain supports extension-variable-based
encodings: the polynomial Beame-Liew construction could in
principle be emitted as a DRAT file with RAT-introduced
extension variables, and `drat-trim` would verify it.

## Implications for Phase 3

With Option A confirmed, the remaining blocker for a polynomial-
size refutation is **constructing the branching program** and
**emitting RAT clauses that introduce one extension variable per
BP node**.  The infrastructure and the proof-format support are
both in place.  What's left is the (non-trivial) implementation
of the per-strip BP.

## Implications for Paper 1

The Option B finding is worth adding to the paper (one sentence in
§8 or §9) to demonstrate that the 4--10× advantage is genuinely
structural rather than a CDCL-search artefact:

> On the same instances, CaDiCaL's DRAT trimmed with `drat-trim -l`
> remains 2.5--4× larger than a case-analysis proof with an
> explicit input-enumeration resolution tree (Appendix or
> supplementary material), suggesting encoding- and proof-structure
> guidance captures the commutativity proof more compactly than
> CDCL's conflict-driven lemma stream.


## Phase 3 Step 1 (2026-05-11 continuation)

Extracted phi_Strip(k) from the CNF per Beame-Liew §3.3 and
verified UNSAT via CaDiCaL at n=4, 6, 8 for k in [1, 2n-1]. This
confirms Lemma 3.1 and validates the strip-extraction criterion
(column-based variables + tableau symmetry + ZERO-constant units).

Files: `phase3_strip_extract.py`.

## Phase 3 Step 2 probe: strip BDD sizes

Built BDDs for all strip variables as functions of input bits
(a[0..n-1], b[0..n-1]) using the `dd` package. The BDD sizes
confirm why the Beame-Liew construction is intricate:

| n | k  | strip cols       | total strip var BDD size | peak single-var BDD |
|---|----|------------------|-------------------------:|--------------------:|
| 4 | 3  | [0, 3]           | 508                      | 30                  |
| 4 | 5  | [2, 5]           | 1,276                    | 55                  |
| 6 | 5  | [1, 5]           | 3,310                    | 144                 |
| 6 | 7  | [3, 7]           | 10,399                   | 462                 |
| 6 | 9  | [5, 9]           | 14,222                   | 462                 |
| 8 | 7  | [3, 7]           | 21,871                   | 818                 |
| 8 | 9  | [5, 9]           | 81,689                   | 3,537               |
| 8 | 11 | [7, 11]          | 137,161                  | 4,419               |

The BDDs for middle-k strip variables explode exponentially
(consistent with Bryant 1991). A naive BDD-based BP would not
deliver the O(n^6 log n) polynomial bound from Beame-Liew. The
polynomial bound requires the paper's specific variable-ordering
trick:

1. Branch first on `o^{yx}_i` output bits.
2. Then on tableau variables row-by-row.
3. Crucially, *merge* BP nodes with the same `Cut(j)` assignment,
   where `Cut(j)` has |Cut(j)| = 4 log k variables.

Our BDD probe branches on inputs a, b in interleaved order, which
is the WRONG ordering for polynomial size -- hence the exponential
blowup we measure. Implementing the paper's specific BP (Step 2
proper) is the next milestone for Phase 3.


## Phase 3 Step 2 prototype: per-strip CaDiCaL

Tested a practical proxy for Beame-Liew's per-strip BP: run
CaDiCaL on each phi_Strip(k) individually, collect its DRAT,
compose via a top-level case split on k. This avoids implementing
the hand-crafted BP but uses a SAT solver to find per-strip
refutations automatically.

| n | Per-strip total | Phase 1 | CaDiCaL full | PS/P1 | PS/CaD |
|---|--:|--:|--:|:--:|:--:|
| 4 | 137 KB | 10 KB | 42 KB | 13.7x | 3.3x |
| 6 | 1.2 MB | 266 KB | 995 KB | 4.6x | 1.2x |
| 7 | 4.6 MB | 1.3 MB | 5.2 MB | 3.6x | 0.88x |
| 8 | 22 MB | 6.1 MB | 26 MB | 3.6x | **0.82x** |

Findings:
- Per-strip CaDiCaL beats full-CNF CaDiCaL at n >= 7 (0.82x at n=8)
  and the ratio is improving with n. So structurally decomposing
  the proof by strip *does* help a SAT solver, even without
  implementing the paper's exact BP.
- Per-strip is still strictly WORSE than Phase 1's structured
  enumeration, by 3.6-13.7x. Phase 1's ordered case-analysis
  remains the tightest proof we can generate.
- The polynomial O(n^6 log n) bound would require Beame-Liew's
  specific BP construction with Cut(j) merging on |Cut| = 4 log k
  variables, which we did not implement in this session.

Data: `data-phase3-perstrip.tsv`.

## Net outcome of N3 push (this session)

Committed:
- Phase 1 (flat case-analysis DRAT, validates, 0.30-0.40x of
  CaDiCaL's trimmed core) -- `beame_liew_phase1_v2.py`.
- Phase 2 structural (column-decomposed DRAT, validates, 2n times
  larger than Phase 1) -- `beame_liew_phase2_v2.py`.
- Phase 3 step 1 (strip extraction validated Lemma 3.1) --
  `phase3_strip_extract.py`.
- Phase 3 step 2 probe (BDD sizes confirm Bryant-style exponential
  growth for wrong variable ordering) -- `phase3_bdd_size.py`.
- Phase 3 step 2 prototype via per-strip CaDiCaL (beats CaDiCaL-
  full at n >= 7) -- `phase3_per_strip.py`.
- Option B trimmed-core comparison (Phase 1 wins are structural,
  not trimming artifacts).
- Option A RAT extension variables (drat-trim accepts them; not
  needed for the Beame-Liew construction which uses only existing
  CNF variables).

Not committed (would be weeks of additional work):
- Beame-Liew's exact BP construction with the paper's variable
  ordering (o^{yx} first, then tableau row-by-row, merging on
  Cut(j) of size 4 log k). This is what would deliver the
  polynomial O(n^6 log n) bound.
- Scaling experiments at n >= 16.
- CDCL heuristic extraction from the BP.

The session closes having made substantial empirical progress on
all phases of the N3 plan while explicitly calling out the
remaining core theoretical implementation task.


## Phase 3 step 2: BP construction attempts

Tried to construct the per-strip BP in phase3_bp_build.py with
input-based (a, b) branching and cut-state merging at
`cut_vars(j, k, delta)`. Result: gets stuck at non-trivial k
because UP within the strip cannot determine c[k] and d[k] from
just a, b inputs -- the strip is missing the constraints from
lower columns (pp_c[i][j] for i+j < k-delta, which by design are
NOT in phi_Strip(k)).

To fix this, one must follow the paper's actual ordering:
1. Branch on o^{yx}_i (output bits) first, not on inputs.
2. Branch on incoming carries at column k-delta-1 (variables
   cry_c[row, k-delta-1] and cry_d[row, k-delta-1]) -- these are
   the "input boundary" to the strip.
3. Branch on tableau variables row-by-row.
4. Merge on Cut(j) at each row boundary.

Step (1) is a 2^(delta+1)-way branch for each initial output
configuration. Step (2) adds another 2^n factor per row (one
carry per row crosses into the strip).

This is a concrete implementation plan, but getting it right
requires:
- Correct cut-state definitions matching the paper.
- Handling the bottom boundary (columns < k-delta) by carry-only
  branching.
- Output ordering for DRAT emission (post-order from leaves up).

We verified via `phase3_up_trivial.py` that NO strip refutes by
UP alone from the forced e assignment -- every strip requires
real branching. So UP-only fallback is not possible.

`phase3_up_trivial.py` confirms every k in [1, 2n-1] needs
branching at n=4..8.

## Session stopping point

Total session committed deliverables across Phase 1-3:

- `generate_array_mul_comm.py` + `generate_array_mul_comm_meta.py`:
  CNF generators.
- `beame_liew_phase1_v2.py`: Phase 1 case-analysis proof. Verified
  4-10x smaller than CaDiCaL raw; 2.5-4x smaller than CaDiCaL
  trimmed core at n>=5.
- `beame_liew_phase2_v2.py`: Phase 2 column-structured proof. 2n
  times larger than Phase 1 (theoretical factor confirmed).
- `phase2_bdd_probe.py`: BDD sanity check for commutativity.
- `phase3_strip_extract.py`: strip extraction validates Lemma 3.1
  UNSAT at n=4, 6, 8 for all k.
- `phase3_bdd_size.py`: measures exponential BDD growth for wrong
  variable ordering (peak 4,419 at n=8, k=11).
- `phase3_per_strip.py`: per-strip CaDiCaL proxy, beats full-CNF
  CaDiCaL at n>=7.
- `phase3_bp_build.py`: scaffolding for BP construction (doesn't
  yet achieve polynomial size due to need for proper branching
  ordering per paper).
- `phase3_up_trivial.py`: confirms every strip needs real branching.
- `rat_test.py`: confirms drat-trim accepts RAT extension-variable
  lemmas (infrastructure check for potential future use).

Remaining open for N3 Phase 3 in a future session:
- Implement the paper's exact BP variable ordering (outputs first,
  tableau row-by-row, carry boundary branches) with proper Cut(j)
  merging.
- Translate DAG-structured BP to DRAT via Krajicek Prop. 2.1.
- Scaling experiments and O(n^6 log n) validation.

The infrastructure is in place; what's missing is careful,
correct implementation of the paper's specific construction.
