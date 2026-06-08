# Variable Ordering Plan

## Background

Our experiments showed that variable numbering significantly affects
CaDiCaL's performance on adder benchmarks:

| Ordering | UNSAT time | Equiv time | Speedup |
|----------|-----------|-----------|---------|
| Original (inputs first) | 5.74s | 7.72s | 1.0x |
| Reversed (aux first) | 3.76s | 4.97s | 1.5x |
| Aux (Tseitin) first | 5.63s | 4.59s | 1.7x |

The effect comes from VSIDS tie-breaking: when two variables have
equal activity scores, the solver picks the one with the lower index.
Putting structural variables (carries, Tseitin gates) first makes the
solver prioritize reasoning about the adder structure.

## Current Allocation Order

CBMC allocates variable IDs sequentially via `cnft::new_variable()`:

1. **Phase 1 (boolbv)**: Named program variables (a, b, sum) get IDs
   when `boolbvt::convert_bv()` is first called on them. These are
   the "input" variables.

2. **Phase 2 (encoding)**: Tseitin auxiliary variables get IDs when
   Boolean operations are encoded (`cnft::land`, `cnft::lor`,
   `cnft::lxor`, `cnft::lselect`). These include carry variables
   from adders.

3. **Phase 3 (assertions)**: Guard and assertion variables.

The result: inputs get low IDs (1, 2, ...), auxiliaries get high IDs.
This is the worst ordering for VSIDS.

## Proposed Change

### Option A: Reverse numbering (simplest)

After all variables are allocated but before solving, renumber them
so that the highest-numbered variables become the lowest. This puts
the most recently allocated variables (Tseitin aux, carries) first.

**Implementation:**
- In `satcheck_cadical::do_prop_solve()`, before calling `solver->solve()`:
  1. Create a permutation map: `new_id[v] = max_var - v + 1`
  2. Re-add all clauses with remapped literals
  3. This requires buffering clauses (already done in `cnft::lcnf`)

**Pros:** Simple, no changes to allocation order.
**Cons:** Requires re-adding all clauses (O(n) extra work).
**Estimated effort:** ~50 lines in `satcheck_cadical.cpp`.

### Option B: Two-phase allocation (cleaner)

Allocate variables in two phases:
1. First pass: count how many auxiliary variables will be needed
   (by doing a dry run of the encoding)
2. Second pass: allocate aux variables starting at ID 1, then
   input variables starting at ID (num_aux + 1)

**Pros:** No clause re-adding needed.
**Cons:** Requires a dry-run pass or pre-counting, which is complex.
**Estimated effort:** ~200 lines, touches boolbv and cnf.

### Option C: Post-hoc renumbering in DIMACS (simplest for CaDiCaL)

CaDiCaL processes clauses in order. Instead of changing CBMC's
internal numbering, add a renumbering step in `satcheck_cadical`
that maps variable IDs before passing them to the solver.

**Implementation:**
- Add a `std::vector<int> var_map` to `satcheck_cadical_baset`
- In `lcnf()`, remap each literal before calling `solver->add()`
- Build the map in `do_prop_solve()` before the first `solver->add()`
  by sorting variables: aux first, then inputs
- Requires knowing which variables are "named" vs "aux" — this info
  is available from `boolbvt`'s symbol map

**Pros:** Clean, no clause buffering, no changes to allocation.
**Cons:** Requires passing variable classification from boolbv to sat.
**Estimated effort:** ~80 lines.

### Option D: CaDiCaL phase/activity hints (zero-clause approach)

Instead of renumbering, use CaDiCaL's API to set initial variable
activities. CaDiCaL supports `solver->phase(var, value)` for initial
phase and could potentially support activity hints.

**Implementation:**
- After all clauses are added, call `solver->phase(v, ...)` for
  carry/aux variables to give them higher initial activity
- Check if CaDiCaL exposes an activity-setting API

**Pros:** Zero overhead, no renumbering.
**Cons:** CaDiCaL may not expose activity control.
**Estimated effort:** ~20 lines if API exists.

## Recommendation

**Start with Option D** (check CaDiCaL API for activity/phase hints).
If not available, **implement Option C** (post-hoc renumbering in
satcheck_cadical). Option A is a fallback if C is too complex.

## Variable Classification

To implement Options B/C, we need to classify variables as:
- **Input**: allocated by `boolbvt::convert_bv()` for named symbols
- **Auxiliary**: allocated by `cnft::land/lor/lxor/lselect/carry`

This classification can be tracked by:
1. Adding a `bool is_auxiliary` flag to `cnft::new_variable()`
2. Or: recording the variable ID range at the boundary between
   boolbv symbol allocation and encoding (simpler)
3. Or: using the `boolbvt::bv_cache` to identify named variables
   (they appear as keys in the cache)

## Testing

The variable ordering change should be benchmarked on:
1. All synthetic benchmarks (10 C + 24 SMT2)
2. With and without --xor-gauss
3. With both CaDiCaL and MiniSat (MiniSat may respond differently)
4. Multiple runs for statistical significance

The expected outcome: 30-70% speedup on UNSAT benchmarks with
CaDiCaL, neutral on MiniSat, no correctness impact.
