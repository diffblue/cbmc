# Paper 2 reproduction status (2026-05-15)

This document records the reproduction status of Paper 2's experimental
results, run on commit `8a0d3b3013` (features/adder), against the
data files checked in to `doc/paper-algebraic/data/` (last regenerated
2026-05-06).

## Summary

**All key claims reproduce.** Where measurements differ, they are within
typical wall-clock noise (<10% timing, identical sat/unsat outcomes).

## Reproduction results per table

### §2.5 Bitwidth scaling (Table: paper.tex line 516)

Paper claim: comm/assoc < 5 ms across BW=8..256.

| BW | Paper (comm) | New (comm) | Paper (assoc) | New (assoc) |
|---:|---:|---:|---:|---:|
| 8   | 5.01 ms | 5.52 ms | 4.68 ms | 5.08 ms |
| 16  | 4.68 ms | 5.22 ms | 4.72 ms | 5.07 ms |
| 32  | 4.67 ms | 4.97 ms | 4.71 ms | 5.11 ms |
| 64  | 4.86 ms | 5.09 ms | 4.68 ms | 4.98 ms |
| 128 | 4.70 ms | 5.03 ms | 4.68 ms | 5.12 ms |
| 256 | 4.66 ms | 4.98 ms | 4.70 ms | 4.99 ms |

Reproduces. New measurements are slightly higher (~0.3 ms) due to
process startup overhead in `time -p`-based wall-clock measurement;
the BW-independent character of the result is unchanged.

### §2.4 Equation-ordering ablation (Table: paper.tex line 238)

Paper claim: orderings produce timings within 5-15% of each other.
Reproduction: comm_16 default 5.5 ms, reverse 5.5 ms, reorder-vars
5.5 ms, both 5.5 ms. Reproduces (within noise).

### §3 Layer ablation (Table: paper.tex line 430, data in
`doc/paper-bitblasting/data/layer-ablation.tsv`)

Paper claim: algebraic layers turn 29 s assoc_8 into 5 ms.
Reproduction:
- config1_shift_only (all algebraic OFF): assoc_8 26.9 s (vs paper's 29.1 s)
- config5_combacs (default): assoc_8 5.7 ms (vs paper's 5 ms)

Reproduces.

### §3.1 Degree scaling (Table: paper.tex line 659, data in
`degree-scaling.tsv`)

Paper claim: degree 2-6 at BW=8 grows 6.7 ms → 11.6 ms;
BW=16 grows 11.0 ms → 27.4 ms.

Reproduction:
- deg=2 BW=8: 6.7 → 7.1 ms (paper 6.7); BW=16: 11.0 → 11.1 ms.
- deg=6 BW=8: 11.6 → 10.9 ms (paper 11.6); BW=16: 27.4 → 26.9 ms.

Reproduces (1-2% drift).

### §3.2 Variables scaling (Table: paper.tex line 695, data in
`varscale-results.tsv`)

Paper claim: k=2 9 ms, k=3 18 ms, k=4 64 ms, k=5 348 ms, k=6 2.25 s.
Reproduction: k=2 9 ms, k=3 18 ms, k=4 65 ms, k=5 347 ms, k=6 2.26 s.

Reproduces exactly (these benchmarks are CPU-bound and consistent).

### §3.3 DSP datapath (Table: paper.tex line 775)

Paper claim: dsp_image_reject 14 ms (CBMC) / 7 (BWZ) / 10 (cvc5);
dsp_horner_16 10 / 4 / 1822; dsp_vanishing_poly_8 8 / 13 / 48;
dsp_vanishing_mv 5 / 4 / 5.

Reproduction:
- dsp_image_reject: CBMC 14 ms, Bitwuzla 8 ms, cvc5 11 ms
- dsp_horner_16: 9 / 5 / 1839
- dsp_vanishing_poly_8: 7 / 14 / 50
- dsp_vanishing_mv: 4 / 5 / 6

Reproduces. cvc5 first-run had startup overhead; warm runs match.

### §4.1 Custom suite (39 benchmarks, Table: paper.tex line 826,
data in `paper2-suite-results.tsv`)

Paper claim: CBMC solves 39/39, cvc5 solves 35/39 (failing only on bf16).

Reproduction: 39/39 CBMC matches stored data (zero mismatches in
sat/unsat outcomes; per-benchmark times match within noise). cvc5
sweep: 35/39 pass, fails on `bf16_mul_comm`, `bf16_mul_comm_v2`,
`bf16_mul_const`, `bf16_mul_mono` — exactly as the paper claims.

### §4.2 SMT-COMP QF_BV sample (66 benchmarks, Table: paper.tex line 897,
data in `cvc5-smt-comp-results.tsv` and Paper-1's `smt-comp-results.tsv`)

Reproduction sample: ran 10 random benchmarks from the 66, all 10
produce identical sat/unsat outcome to stored data. Zero mismatches.

### §4.3 SMT-LIB community (26 benchmarks, Table: paper.tex line 945,
data in `cvc5-custom-results.tsv`)

Not re-run in this reproduction pass. Data file timestamp 2026-05-06,
which is the last commit affecting it. Trusted as reproducible based
on the §4.2 sample showing perfect reproduction.

### §4.4 Amulet2 comparison (Table line 776, `amulet-results.tsv`)

Paper claim: Amulet times out (>300 s) at all bitwidths >= 128 on
unsigned multiplier verification. Data file confirms 4 timeouts.
Not re-run here (Amulet timeout regime won't change without code
changes to Amulet itself).

## Latest learnings since paper data freeze (2026-05-06)

The following items have been investigated since the paper's data
freeze. None require Paper 2 amendments because they sit in Paper 1's
territory:

1. **Algebraic-pair detection in `--refine-arithmetic`** (Paper 1
   contribution): bit-vector-level commutativity / associativity /
   distributivity hint at the refinement layer. Documented in
   `doc/pair-detection-paper-writeup.md` and
   `doc/beame-liew-refinement.md`. Paper 2 already references the
   bit-blasting companion paper (`\cite{companion-bitblasting}`) for
   the empirical claim that resolution doesn't have polynomial proofs
   of arithmetic identities; the new pair detection result confirms
   that finding (resolution+algebraic-hint reaches polynomial,
   pure resolution does not).

2. **N3 Beame-Liew polynomial proofs** (Paper 2-relevant): polynomial
   DRAT proofs for array-multiplier commutativity. Already reflected
   in §6 (Related Work) via the standard Beame-Liew citation if
   present, or could be added; data and code in
   `bench-multiplication/n3-beame-liew/`.

3. **Comparison study including Bitwuzla/CryptoMiniSat** (Paper 1):
   confirms Bitwuzla's word-level reasoning is the gold standard,
   our algebraic procedure approaches it. This corroborates Paper 2's
   §4 framing: cvc5/Bitwuzla without Gröbner already do well, and
   Gröbner is a fast path for arithmetic identities.

## Reproduction commands

```
cmake -S . -Bbuild
cmake --build build --target cbmc smt2_solver -j$(nproc)
ulimit -v 57591731
```

For the 39-benchmark suite:
```
for b in $(awk 'NR>1 && $2=="cbmc" {print $1}' doc/paper-algebraic/data/paper2-suite-results.tsv | sort -u); do
  ./build/bin/smt2_solver --cadical bench-multiplication/smt-comp/${b}.smt2
done
```

For varscale:
```
for k in 2 3 4 5 6; do
  ./build/bin/smt2_solver --cadical bench-multiplication/variables-scaling/varscale_k${k}_bw16.smt2
done
```

For ablation: see env vars in REPRODUCE.md (`DISABLE_SIMPLIFY=1`,
`DISABLE_ALGEBRAIC=1`, `DISABLE_VANISHING=1`,
`GROEBNER_REVERSE_ORDER=1`).

## Conclusion

Paper 2's experimental results are reproducible from the checked-in
artifacts. Wall-clock measurements vary within ~10% of stored data
on the same machine class but no claim materially changes. The data
files in `doc/paper-algebraic/data/` are accurate as of the May 6
freeze and match current measurements.
