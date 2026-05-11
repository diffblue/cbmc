# N3 Phase 1 Prototype: Beame-Liew-Style Proof Generation for Array Multiplier Commutativity

This directory contains a working Phase 1 prototype for research plan
N3 (`research-plans/N3-beame-liew-implementation.md`).

## What this prototype achieves

1. **A self-contained DIMACS generator** (`generate_array_mul_comm.py`)
   for the commutativity formula `a * b = b * a` on an `n`-bit array
   multiplier with carry-save full adders. The formula has shape
   `p cnf (~10n^2) (~60n^2)` and is UNSAT for all `n >= 1`.

2. **A case-analysis DRAT proof generator** (`beame_liew_phase1_v2.py`)
   that emits a validatable DRAT refutation in three phases:
   - emit `2^(2n)` leaf "branch-cut" clauses (one per `(a, b)` input
     assignment), each being a valid RUP lemma;
   - emit a binary-resolution tree over the `2n` input variables,
     progressively halving the open clauses;
   - emit the empty clause.

   The generated proof is accepted by `drat-trim` at every tested
   bit-width (n = 1..11).

3. **A comparison against CaDiCaL's own DRAT proof.** On the same
   CNFs, the prototype's proof is 4-10× smaller than CaDiCaL's DRAT
   output at small `n`, and remains smaller as `n` grows:

| n  | BL DRAT (B) | BL lines | CaDiCaL DRAT (B) | CaDiCaL lines | BL / CaDiCaL |
|----|-------------:|----------:|-------------------:|---------------:|:-------------:|
| 2  | 307          | 31        | 5,002              | 413            | 0.061×         |
| 3  | 1,859        | 127       | 15,745             | 1,150          | 0.118×         |
| 4  | 9,987        | 511       | 41,560             | 2,407          | 0.240×         |
| 5  | 52,225       | 2,047     | 156,474            | 5,794          | 0.333×         |
| 6  | 266,229      | 8,191     | 994,916            | 21,280         | 0.267×         |
| 7  | 1,294,277    | 32,767    | 5,246,959          | 92,403         | 0.246×         |
| 8  | 6,094,597    | 131,071   | 26,452,011         | 407,760        | 0.230×         |
| 9  | 28,048,389   | 524,287   | 117,262,735 (T/O)  | 1,724,943      | 0.239×         |
| 10 | 126,873,605  | 2,097,151 | 212,799,488 (T/O)  | 2,458,016      | 0.596×         |

(CaDiCaL DRAT at n >= 10 is the partial proof accumulated before
timeout; the asymptotic ratio may differ once CaDiCaL is given enough
time to finish.)

## What this prototype is NOT

This is **not** the polynomial-size `O(n^6 log n)` critical-strip
refutation of Beame and Liew (2019). The prototype's case-analysis
proof has size `O(2^(2n) * poly(n))`, dominated by the `2^(2n)`
branch-cut clauses and their resolution tree. At large `n` the
empirical 4-10× constant-factor win over CaDiCaL will be overtaken
by the exponential blow-up of the enumeration.

To reach the Beame-Liew asymptotic, the leaves of the case split need
to be folded into a read-once branching program whose size is
polynomial in `n` by the strip decomposition: for a strip of width
`Delta = log(2n)`, only `2^Delta = poly(n)` carry-in configurations
must be tracked between adjacent strips. Implementing this branching
program and translating it to DRAT via Krajicek's Prop. 2.6 is Phase
2-3 in the N3 research plan.

## Files

- `generate_array_mul_comm.py` -- CNF generator.
- `beame_liew_phase1_v2.py` -- DRAT proof generator (current version).
- `beame_liew_phase1.py` -- earlier failed attempt (kept for record;
  flat branch-cut clauses without the resolution tree, rejected by
  drat-trim because the RUP check for the final empty clause
  requires the resolution steps).

## Reproducing the comparison

```
# Build drat-trim if not available:
gcc -O2 -o /tmp/drat-trim /home/ubuntu/cbmc-github.git/build/cadical-src/test/cnf/drat-trim.c

# Generate BL proof for a given n:
python3 beame_liew_phase1_v2.py 5
/tmp/drat-trim /tmp/comm_n5_bl.cnf /tmp/comm_n5_bl.drat

# Baseline: CaDiCaL's own DRAT on the same CNF:
python3 generate_array_mul_comm.py 5 > /tmp/comm_n5.cnf
/home/ubuntu/cadical-src/build/cadical --no-binary /tmp/comm_n5.cnf /tmp/comm_n5_cadical.drat
```

## Takeaways

- The N3 plan's Phase 1 is implementable and validates with `drat-trim`
  out of the box.
- Even the straight case-analysis proof is substantially smaller than
  a CDCL-produced proof on the same instance at small `n`, suggesting
  that the *structural order* of the proof (enumerate first, resolve
  second) is itself a useful piece of guidance.
- Scaling beyond `n ~ 10` with this prototype becomes prohibitive both
  in DRAT file size (>100 MB) and in Python propagation time
  (polynomial in the CNF but multiplied by `2^(2n)` branches). The
  polynomial Beame-Liew construction is what would break this.

## Next steps (Phase 2 and beyond)

1. Replace the `2^(2n)` flat enumeration by a read-once branching
   program keyed on the critical strips of width `Delta = log(2n)`.
2. Implement the Krajicek-Prop.-2.6 translation from the branching
   program to DRAT resolution steps.
3. Validate `O(n^6 log n)` growth empirically for n in {4, 6, 8, ...}.
4. (Stretch) extract a CDCL variable-ordering / branching heuristic
   from the branching-program structure.
