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
