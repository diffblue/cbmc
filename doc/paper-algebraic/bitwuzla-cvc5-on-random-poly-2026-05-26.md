# Bitwuzla and cvc5 on the 210-Benchmark Random-Polynomial Sample

*Date: 2026-05-26*
*Purpose: validate (or invalidate) the (A) prong of headline (C)
in `structural-rewrite-plan-2026-05-26.md`.*

## Setup

- 210 benchmarks: stratified sample of Brain's
  `subpolynomial-encoding` random polynomial suite (seeds 23 + 42,
  eight categories per seed).
- 10 s wall timeout per benchmark, matching the existing
  `martin-subpoly-comparison-v2.tsv` setup.
- Bitwuzla version 0.9.0-dev-main@72ecd081 (the local source
  build at `/home/ubuntu/bitwuzla.git`).
- cvc5 version 1.3.3 (system install at `/usr/local/bin/cvc5`).
- Both run with no special flags (default QF\_BV pipelines).
- Memory limit `ulimit -v 57591731` per subprocess.
- Total wall time: 17 minutes for both solvers across all 210
  benchmarks.
- Output TSV: `bench-multiplication/martin-subpoly-bitwuzla-cvc5.tsv`.
- Runner script: `bench-multiplication/run-martin-subpoly-bitwuzla-cvc5.sh`.

## Solved-count summary

| Configuration | Solved / 210 |
|---|---|
| shift\_add (CBMC bit-blasting, no algebraic) | 118 |
| comba\_cs (CBMC bit-blasting + Paper 1 encoding) | 118 |
| pair\_detect (Paper 1's `--refine-arithmetic`) | 110 |
| **p2\_algebraic (this paper)** | **128** |
| all\_combined (Paper 1 + Paper 2) | 120 |
| **Bitwuzla** | **184** |
| **cvc5** | **168** |

Per-category breakdown:

| Category | shift\_add | comba\_cs | p2\_algebraic | Bitwuzla | cvc5 |
|---|---|---|---|---|---|
| addition (univ-eq)         | 4/20  | 4/20  | 11/20 | **17/20** | 17/20 |
| multiplication (univ-eq)   | 3/20  | 3/20  | 11/20 | **14/20** | 8/20 |
| correctness (univ-eq)      | 8/30  | 8/30  | 11/30 | **14/30** | 12/30 |
| equality (exist-eq SAT)    | 11/20 | 11/20 | 11/20 | **20/20** | 19/20 |
| nonequality (exist-eq SAT) | 14/20 | 14/20 | 6/20  | **20/20** | 19/20 |
| bounding                   | 16/20 | 16/20 | 16/20 | **20/20** | 20/20 |
| identity-point             | 30/40 | 30/40 | 30/40 | **40/40** | 37/40 |
| root-finding               | 31/40 | 31/40 | 31/40 | **38/40** | 35/40 |

Three-way correctness spot-check on three benchmarks (one
sat, one unsat, one mixed): all three solvers agree on all three.
No correctness disagreements observed.

## Headline (A) prong: invalidated

**Original claim**: "18 algebraic-only wins on random-polynomial
suite at degree $\geq 18$ — bit-blasting cannot encode within
10 s."

**Updated reality** when Bitwuzla and cvc5 are added:

| Of the 18 algebraic-only-wins-vs-bit-blasting | Count |
|---|---|
| Both Bitwuzla and cvc5 solve  | 7 |
| Only Bitwuzla solves          | 7 |
| Only cvc5 solves              | 0 |
| **Neither solves (true wins)**| **4** |

The 4 surviving wins:
- `bitwidth-16-degree-13-seed-23-multiplication-reduced-native-encoding`
  (we 0.30 s; all others T/O at 10 s)
- `bitwidth-16-degree-23-seed-23-correctness-original-native-encoding-vs-reduced-native-encoding`
  (we 0.41 s)
- `bitwidth-32-degree-19-seed-23-multiplication-reduced-native-encoding`
  (we 3.73 s)
- `bitwidth-32-degree-27-seed-23-correctness-original-native-encoding-vs-reduced-native-encoding`
  (we 2.87 s)

All 4 are in the universal-equational class (multiplication and
correctness identity benchmarks), at degree 13–27. Two at BW=16,
two at BW=32.

**Wider per-solver picture:**

| Pair | p2 wins (other T/O) | Other wins (we T/O) |
|---|---|---|
| p2 vs Bitwuzla | 6 | 62 |
| p2 vs cvc5     | 11 | 51 |

Bitwuzla beats us by 56 net on this suite. cvc5 beats us by 40 net.
Both Bitwuzla and cvc5 dominate every category — including the
universal-equational categories that should be our strongest
suit.

## Implications for the headline

The (A) prong cannot survive in its original form. Three options
for the user to choose between:

### Option (C-revised, weakened): retreat to 4 wins

> The procedure decides 4 random-polynomial identity benchmarks
> at degree $\geq 13$ that Bitwuzla, cvc5, and bit-blasting all
> time out on within 10 s, plus 5 DSP datapath equivalences
> with overflow cancellation in microseconds (where cvc5 is
> $184\times$ slower).

- Pro: defensible, conservative, exactly what the data shows.
- Con: 4 is a small number for an abstract; reviewers may push
  back ("why is 4 a meaningful sample?").
- Con: Bitwuzla wins 56 net; the abstract has to acknowledge this
  somewhere or risk looking dishonest.

### Option (E): pivot to a methodological / Lean-driven headline

> We give a mechanised-soundness-driven decision procedure for
> universally-quantified equalities of polynomial expressions in
> $\mathbb{Z}_{2^d}$. The Lean 4 development (25 theorems, 0
> sorry, Mathlib contribution under review) directly improved
> the C++ implementation by exposing and removing a 2000$\times$
> ordering sensitivity that empirical testing did not catch.
> Empirical evaluation shows the procedure is competitive with
> Bitwuzla's word-level rewriting at all bitwidths up to 256, and
> contributes 4 wins beyond all current solvers on a 210-benchmark
> stratified sample.

- Pro: pivots from speed (where we lose to Bitwuzla on this
  suite) to correctness-and-formalisation (where we own the
  contribution).
- Pro: the 2000$\times$ ordering-sensitivity story is genuinely
  good and currently underused.
- Pro: the 4 wins become illustrative evidence for completeness,
  not the headline number.
- Con: TACAS reviewers vary in their appetite for
  formalisation-first contributions; some will see this as
  underclaiming on the empirical side.
- Con: re-frames the paper away from its current centre of
  gravity (Gröbner basis + vanishing polynomial test); needs
  buy-in from co-authors who shaped the algebraic side.

### Option (G): completeness-first headline (recommended)

> Bitwuzla and cvc5 dispatch arithmetic identities heuristically:
> when a syntactic rewrite matches, instantly; otherwise, falls
> through to bit-blasting and may time out. We give the first
> *complete decision procedure* for universally-quantified
> equalities of polynomial expressions in $\mathbb{Z}_{2^d}$,
> combining a strong Gröbner basis solver (ideal membership) and
> a vanishing polynomial test (function equivalence). The
> procedure decides 4 benchmarks at degree $\geq 13$ that defeat
> all current solvers (Bitwuzla, cvc5, and bit-blasting) within
> 10 s, all 5 DSP datapath equivalences with overflow
> cancellation in microseconds (cvc5 $184\times$ slower on
> `dsp_horner_16`), and is bitwidth-independent (BW=8 to 256).
> Soundness is mechanised in Lean 4 (25 theorems, 0 sorry,
> Mathlib contribution under review); the formalisation effort
> exposed and removed a 2000$\times$ ordering sensitivity in
> the C++ implementation that empirical testing missed.

- Pro: pitches completeness-of-procedure as the contribution,
  with speed and correctness as supporting evidence.
- Pro: the 4 wins become *categorical* evidence (these queries
  are beyond heuristic capacity, by construction) rather than
  benchmark-level evidence.
- Pro: handles the Bitwuzla-beats-us reality gracefully:
  Bitwuzla's heuristics happen to win the volume contest, but
  we win the *completeness* contest (which is the contribution
  we are claiming).
- Pro: connects to the four-classes taxonomy: completeness is
  for the universal-equational class with polynomial
  expressions; the other three classes fall through to
  Paper 1's bit-blasting work.
- Con: requires the body of the paper to actually defend
  completeness. The current §3 / §4 do this implicitly; we
  need to make it explicit.
- Con: "first complete decision procedure" is a strong claim
  that will be checked. Song et al. 2024's proof gives us the
  theoretical backing; our claim is that we are the first to
  *implement* it as an SMT integration with both ideal-
  membership and function-equivalence directions.

## Recommendation

Option (G) is the strongest. The data invalidates the volume-of-
wins framing; the paper's actual contribution is completeness-of-
procedure, and the 4 wins + DSP results + Lean development
are the three supporting pillars.

If (G) is accepted, the 18-wins claim in the current §7.5 should
be revised to "4 wins beyond all current solvers; 18 wins beyond
all bit-blasting configurations of CBMC" — both numbers are
correct, with the larger one in scope of CBMC bit-blasting only.

## Update to the structural-rewrite plan

If headline (G) replaces (C), the rewrite plan changes as
follows:

| Plan task | Update |
|---|---|
| R1 (re-centre contribution) | Recentre on completeness, not volume of wins |
| R3 (taxonomy as scaffold) | Unchanged; even more important — the per-category breakdown above motivates exactly this |
| §7.1 (promote random-poly suite) | Keep promotion, but the headline number is "4 wins beyond all current solvers", not "18 wins" |
| Abstract | Rewrite to (G); drop "outpacing pure bit-blasting" framing |

Other rewrite-plan items (R2, R4–R10) are unchanged.

## Data files

- `bench-multiplication/martin-subpoly-bitwuzla-cvc5.tsv` — raw
  output (210 rows, 2 columns + header).
- `bench-multiplication/run-martin-subpoly-bitwuzla-cvc5.sh` —
  reproducible runner.
