# Item 12 — Ablation re-audit of all claimed algebraic wins

Date: 2026-06-01. Method: run every benchmark behind a paper
claim twice — algebra ON vs `DISABLE_ALGEBRAIC=1` — and, for
each verdict, cross-check against an independent oracle
(declared `:status`, z3, Bitwuzla, or CBMC's own bit-blaster).
Single-threaded / low-parallelism to avoid the contention
artifact documented in `float-fp2bv/RESULTS.md`.

Classes: **NEEDS_ALGEBRA** (ON solves, OFF times out — genuine);
**ALGEBRA_FASTER** (both solve, ON ≥3× faster and saves ≥5 s);
**ARTIFACT** (both solve, comparable — bit-blasting alone
suffices); **BOTH_TO**; **ONLY_OFF** (algebra harmful).

Harness: `/home/ubuntu/bench-staging/ablation.sh` (smt2),
`ablation-cbmc.sh` (C via cbmc).

## ★ Headline: the audit found TWO soundness bugs

These were prompted by — and vindicate — the audit. Both are in
the *dangerous* direction: our tool reports **no bug when a bug
exists**.

| benchmark | algebra ON | bit-blast OFF | z3 | correct | status |
|-----------|-----------|---------------|----|---------|--------|
| `assoc.c` (BW=9) | SUCCESSFUL | FAILED | sat | **FAILED** | **UNSOUND** |
| `mul_zero_factor.c` (BW=8) | SUCCESSFUL | FAILED | sat | **FAILED** | **UNSOUND** |

Both are custom-suite benchmarks. Bit-blasting and z3 agree
(independently) that the assertion is violable; the algebraic
path wrongly reports it holds.

**Two distinct root causes:**

1. **`assoc` — integer promotion not modelled.** The C source
   asserts `(a*b)*c == a*(b*c)` on `__CPROVER_bitvector[9]`. The
   SSA shows the assertion operands are
   `cast(..., signedbv[32])`: C integer promotion widens the
   products to 32 bits *after* `ab`, `bc` were truncated to 9
   bits. The identity holds in the 9-bit ring (mod 512 mult is
   associative) but **not** at 32 bits — e.g.\ a=39, b=461,
   c=352 gives ab·c = 20768 ≠ 18720 = a·bc. The algebraic
   extractor reasons in the 9-bit ring and ignores the cast,
   "proving" a false identity.

2. **`mul_zero` — zero divisors in Z/2ⁿ.** The source asks
   whether `a*b==0` with `a≠0, b≠0` is reachable (8-bit). It is:
   16·16 = 256 ≡ 0 (mod 256). The algebraic path refutes the
   disequality system `{a·b=0, a≠0, b≠0}` — valid over an
   integral domain / field, **invalid** over Z/2⁸, which has
   zero divisors. The disequality handling assumes no zero
   divisors.

Tracked as **Item 13** in `remaining-work.md` (a real code fix,
not a benchmark reclassification). Until fixed, the algebraic
path is unsound on (a) any property whose asserted expression is
promoted to a wider type than the ring the extractor uses, and
(b) any disequality system relying on zero-divisor-freeness.

## The headline numbers — genuine vs artifact

### SMT-COMP 66-sample (the "41/66" figure)

| class | count |
|-------|------:|
| NEEDS_ALGEBRA (genuine unlock) | **10** |
| ARTIFACT (bit-blasting also solves) | 31 |
| BOTH_TO (unsolved either way) | 25 |

Honest decomposition: **bit-blasting alone solves 31/66; algebra
adds 10 genuine unlocks → 41/66.** No ONLY_OFF (algebra never
lost a benchmark here). The "41/66" is correct but should be
read as "31 bit-blast + 10 algebra", not "41 by algebra". The
paper already frames this pool as a *complement*, so this is
consistent — but the text should state the 10/31 split
explicitly.

The 10 genuine unlocks: cohencu.c_0/1/2/3, geo3.c_5 (the 5
claimed unlocks — **all confirmed genuine**), plus ecrw
bw512_1, wienand Commute_commute08/16/32, Distrib_distrib08.
All return `unsat`; the wienand four match their declared
`:status unsat` (sound).

### 5 claimed SMT-COMP unlocks — ALL GENUINE

cohencu.c_0/1/2/3 and geo3.c_5: each is NEEDS_ALGEBRA (algebra
ON `unsat`, OFF times out at 60 s). Validated.

### 4 wins-beyond-all-solvers (Brain's sample) — ALL GENUINE

All four NEEDS_ALGEBRA (ON 0.3–3.1 s, OFF 60 s timeout).
Soundness: bw16-deg-13 confirmed `unsat` by both z3 and
Bitwuzla; bw32-deg-19 is unverifiable by z3/Bitwuzla (both time
out) — which is exactly the "beyond all solvers" claim. No
unsoundness found.

### SABER (31) — overwhelmingly genuine

| class | count |
|-------|------:|
| NEEDS_ALGEBRA | 26 |
| ALGEBRA_FASTER | 1 |
| ARTIFACT | 4 |

27/31 materially benefit from algebra; 26 are unsolvable by
bit-blasting within 90 s. Cross-checked n16/n8 `unsat` against
z3 and Bitwuzla (agree). SABER is the cleanest genuine result.

### Custom suite / DSP / div-mod (C via cbmc)

| benchmark | class | note |
|-----------|-------|------|
| mac_equiv (DSP/MAC comm) | ALGEBRA_FASTER | 0.14 s vs 45.8 s; sound (z3 unsat) |
| comm_64 | NEEDS_ALGEBRA | sound (z3 unsat) |
| mul_overflow | NEEDS_ALGEBRA | sound (z3 unsat) |
| matrix_mul | NEEDS_ALGEBRA | sound (z3 unsat) |
| hash_mul | NEEDS_ALGEBRA | sound (z3 unsat) |
| mul_square_nonneg | (SUCCESSFUL) | sound (z3 unsat) |
| div_roundtrip (div/mod) | ARTIFACT | bit-blasting also fast |
| distrib | ARTIFACT | z3 inconclusive (TO); both cbmc paths SUCCESSFUL |
| **assoc** | **UNSOUND** | see headline |
| **mul_zero_factor** | **UNSOUND** | see headline |

Note: the div/mod *identity* scaling claim (Plan A.3, bit-widths
8→256) is a separate generated benchmark, not `div_roundtrip.c`;
it should be ablation-checked too when located (the
`div_roundtrip.c` artifact result does NOT bear on that claim).

## Net effect on paper claims

- **4 wins-beyond-all-solvers (Brain)**: ✓ validated, sound.
- **5 SMT-COMP unlocks**: ✓ validated, genuine.
- **41/66**: ✓ correct, but restate as 31 bit-blast + 10
  algebra.
- **SABER**: ✓ strongest genuine result (27/31 benefit).
- **DSP (mac_equiv)**: ✓ genuine (ALGEBRA_FASTER).
- **Custom suite "39/39 validates correctness"**: ✗ **two
  members (assoc, mul_zero) are unsound** — the suite was scored
  against assumed-correct expected verdicts that bit-blasting and
  z3 contradict. This claim must be withdrawn/qualified and the
  soundness bug fixed (Item 13).

## Methodology note

The audit's value: every "win" is now classified as genuine or
artifact against an independent oracle, and the two soundness
bugs would otherwise have shipped in the paper. This is the
discipline that the float episode showed was missing.

## ADDENDUM (2026-06-01, after the Item 13 fixes): broad
## unsoundness scan reveals the problem is SYSTEMIC

After committing the two targeted fixes (assoc, mul_zero), a
broad scan ran the solver (algebra ON) on **4,361 SAT
bvmul benchmarks** from the full QF\_BV corpus (declared
`:status sat`) and flagged any returned `unsat` — the dangerous
direction. Of the 3,677 under 2 MB, **76 were wrongly reported
`unsat`**. Re-running each with `DISABLE_ALGEBRAIC=1` splits
them:

- **41 ALGEBRA-CAUSED** (Sage2 ×40, sage ×1): algebra-OFF does
  not return `unsat`, so our algebraic pre-solver is the cause.
  These are genuine unsoundness and are **NOT fixed** by the two
  committed targeted guards. Lists:
  `bench-multiplication/ablation-audit/sat-scan-algebra-unsound.txt`.
- **35 PRE-EXISTING** (all `float`): algebra-OFF *also* returns
  `unsat`, so the CBMC bit-blaster/SMT2 front-end itself
  disagrees with z3 (which says `sat` on the ones it decides)
  on these declared-sat FP-as-BV benchmarks. This is a separate,
  pre-existing issue **outside the algebraic pre-solver** (it
  reproduces with `DISABLE_ALGEBRAIC=1`) — flagged for separate
  investigation, not part of Item 13. List:
  `.../sat-scan-preexisting-bitblast.txt`.

  > **CORRECTION (2026-06-03):** the "pre-existing" / "the CBMC
  > bit-blaster itself" characterisation here is **wrong**. These
  > `float` (and `mcm`) wrong-`unsat` results reproduce with
  > `DISABLE_ALGEBRAIC=1` because they are *not* in the algebraic
  > layer — but they are **not** pre-existing upstream either. A
  > merge-base baseline build returns the correct `sat`, and
  > `git bisect` identified them as **branch-introduced** by
  > commit `d06d50c678` (an unsound "adjacent equality
  > implications" SAT-encoding optimisation in
  > `bv_utils::equal()`). Fixed in commit `8a6f7b2ef1`. See
  > `soundness-sweep-findings-2026-06-03.md`.

### Root cause is systemic, across ≥4 refutation paths

The 41 algebra-caused failures are the **Rabinowitsch
unit-trick over ZMod(2^d)**, the same root cause as Bug B but
manifesting beyond the narrow zero-divisor pattern the committed
guard detects. Encoding `diff != 0` as `diff*e - 1 = 0` asserts
`diff` is a *unit*; over ZMod(2^d) a non-zero element need not be
invertible, so `UNSAT_rabinowitsch` does NOT imply
`UNSAT_original`. This trick is used at (at least) three call
sites in `try_algebraic_solve` (`__rabinowitsch` main system,
`__rab` per-disequality, `__rab_disj` disjunctive), plus there is
a **second, distinct** unsound mechanism: 4 of the 41
(`Sage2/bench_{12880,5552,13209,8135}`) remain wrongly `unsat`
even with all three Rabinowitsch sites gated off — refuted by the
`is_zero()` / gb-on-equalities path (normalisation reporting a
spurious zero, or the predicate/equality ideal being found
inconsistent unsoundly).

### Feasibility data for a sound-only mode

An experimental `DISABLE_RABINOWITSCH` gate (reverted; not
committed) over the three unit-trick sites showed:

- Fixes **37/41** algebra-caused failures.
- **SABER and the 4 Brain wins survive** (they refute via the
  sound vanishing/ideal-membership test, not Rabinowitsch).
- **cohencu_0..3 and geo3.c_5 regress to timeout** — they
  genuinely depend on the Rabinowitsch path. So a naive
  sound-only mode costs ~5 SMT-COMP unlocks.
- **4 residual** remain unsound (the second mechanism above),
  so even gating all Rabinowitsch sites does not fully restore
  soundness.

### Status / consequence

The two committed targeted fixes (assoc, mul_zero) are correct,
tested, and harmless, but they are a **down payment**, not a
resolution. The algebraic disequality refutation is **unsound by
default over ZMod(2^d)** on ~41 real SMT-LIB benchmarks. This is
a CRITICAL, submission-blocking issue requiring a proper
redesign rather than per-site guards. Tracked as the expanded
Item 13 + new Item 14 in `remaining-work.md`. The headline
soundness claim of the paper cannot stand until this is
resolved.

### RESOLUTION (Item 14, 2026-06-01)

Fixed. The Rabinowitsch unit-trick was **removed** at all three
sites; disequalities are now refuted only by the sound routes
(per-disequality vanishing test, and reduction of `diff` modulo
the Gröbner basis of the equalities — `diff ∈ ⟨F⟩`). A residual
third mechanism was diagnosed: a single tree-walk leaf equality
containing bit-decomposition operators (`bitand`/`lshr`) was
overconstraining the equality system `F` and tripping the
equality-system-inconsistency check on 3 SAT benchmarks
(`Sage2/bench_{12880,13209,5552}`); a `contains_bit_decomp`
filter excludes such equalities from `F` (sound — underconstraint
never turns SAT into UNSAT).

Re-running the **broad SAT scan** after the fix: **0 non-float
wrong-unsat** (down from 41). The 35 `float` wrong-unsat persist
and are confirmed pre-existing (reproduce with
`DISABLE_ALGEBRAIC=1`) — a separate CBMC bit-blaster/SMT2
front-end issue, not the algebraic pre-solver.
<!-- CORRECTION (2026-06-03): "pre-existing ... CBMC bit-blaster"
is wrong; these float wrong-unsat are branch-introduced by commit
d06d50c678 (unsound adjacent-equality clause in bv_utils::equal()),
not upstream, and are fixed in 8a6f7b2ef1. See
soundness-sweep-findings-2026-06-03.md. -->
Genuine wins:
SABER 4/4 and Brain 4/4 preserved; cohencu_0/1 preserved via the
sound ideal-membership path (Bitwuzla confirms unsat). **Lost:
cohencu_2, cohencu_3, geo3.c_5** (3 SMT-COMP unlocks) — the
accepted soundness cost. The proof gap is closed by
`formal-proofs/DisequalityRefutation.lean` and the coverage check
`scripts/check_proof_traceability.py`. Remaining: rewrite the
paper's Rabinowitsch methodology (Item 14b).
