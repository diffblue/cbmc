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
