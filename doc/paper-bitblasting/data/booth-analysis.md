# Booth Performance Analysis (algebraic solver disabled)

## Summary

Booth radix-4 is **not** uniformly faster on constant multiplication.

| Problem pattern | Booth effect | Example |
|---|---|---|
| Pure constant eq (`x*15 == 15*x`) | Booth is WORSE | const_mul_16_15: shift 0.013s, booth 0.233s |
| BW=32 const mul | Booth mostly T/Os | const_mul_32_*: 30s T/O on 6 of 8 |
| Strength reduction (`x*15 == (x<<4)-x`) | Booth is BETTER | strength_16_15: 3.5×, strength_32_63: 35.9× |
| Chained reductions | Booth is BEST | strength_chain_16: 17.1× |

## Why the asymmetry

- Pure constant mul: Both encodings find `x*c == c*x` trivially through
  variable identification. Booth's extra structure (sign bits, doubling)
  adds overhead without benefit.
- Strength reduction: shift-add must match a manually-written shift-add
  circuit, requiring detailed bit-level reasoning. Booth's compressed
  representation hides the partial products, making the equivalence
  easier for the solver to see.

## Recommended paper wording

**OLD:** "Booth is 17× faster on constant multiplication"

**NEW:** "Booth is faster (up to 17×) on strength-reduction benchmarks
where the multiplier must prove equivalence between `x*c` and a
manually-decoded shift-add implementation. On pure constant
multiplication (where both sides use `bvmul`), Booth offers no
advantage and can be slower due to its additional structure (sign
correction, pre-computed doublings)."
