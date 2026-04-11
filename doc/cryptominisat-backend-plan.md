# Plan: CryptoMiniSat Backend for CBMC

## Motivation

CryptoMiniSat (CMS) has native XOR constraint support with built-in
Gaussian elimination during solving. Unlike our CaDiCaL approach (which
adds derived clauses at initialization), CMS performs online Gaussian
elimination during BCP and conflict analysis. This is the approach that
provides 10-100x speedups on XOR-heavy problems in the SAT competition.

## Architecture Overview

CBMC's solver integration follows this pattern:
```
propt (interface)
  └── cnft (CNF encoding: land, lor, lxor, etc.)
        └── cnf_solvert (adds solve/get_model)
              ├── satcheck_minisat2t
              ├── satcheck_cadical_baset
              └── satcheck_cryptominisatt  ← NEW
```

Each solver backend implements:
- `lcnf(bvt)` — add a clause
- `new_variable()` — allocate a variable
- `do_prop_solve(assumptions)` — solve
- `l_get(literalt)` — get variable value after solving
- `solver_text()` — solver name string
- `is_in_conflict(literalt)` — assumption conflict check

CryptoMiniSat additionally supports:
- `add_xor_clause(vars, rhs)` — native XOR constraint (no clause encoding needed)

## Key Design Decision: Native XOR vs Clause Encoding

When `--sat-solver cryptominisat` is used:
1. `lxor(a, b)` still creates output variable `o` and calls `gate_xor(a, b, o)`
   which adds 4 clauses via `lcnf()`. This is needed for the CNF encoding.
2. `register_xor({o, a, b}, false)` is called, which stores the XOR constraint.
3. In `do_prop_solve()`, before calling `solver.solve()`, pass all stored
   XOR constraints to CMS via `add_xor_clause()`.
4. CMS uses both the clause encoding AND the native XOR constraints.
   The clause encoding ensures correctness; the XOR constraints enable
   Gaussian elimination for speed.

Alternative: skip the clause encoding entirely for XOR gates and only
use `add_xor_clause()`. This reduces clause count but requires CMS's
Gaussian elimination to handle all XOR propagation. Riskier but faster.

**Recommendation:** Start with both (clauses + XOR), then benchmark
without clauses.

## Implementation Steps

### Step 1: CMake Integration

Add CryptoMiniSat as a downloadable dependency in `src/solvers/CMakeLists.txt`:

```cmake
elseif("${SOLVER}" STREQUAL "cryptominisat")
    message(STATUS "Building solvers with cryptominisat")
    download_project(PROJ cryptominisat
        URL https://github.com/msoos/cryptominisat/archive/refs/tags/5.11.21.tar.gz
        URL_HASH SHA256=<hash>
    )
    # CMS uses CMake natively
    set(ONLY_SIMPLE OFF CACHE BOOL "" FORCE)
    set(NOZLIB ON CACHE BOOL "" FORCE)
    set(NOBREAKID ON CACHE BOOL "" FORCE)
    set(NOSTATS ON CACHE BOOL "" FORCE)
    add_subdirectory(${cryptominisat_SOURCE_DIR} ${cryptominisat_BINARY_DIR})
    target_compile_definitions(solvers PUBLIC SATCHECK_CRYPTOMINISAT HAVE_CRYPTOMINISAT)
    target_include_directories(solvers PUBLIC ${cryptominisat_SOURCE_DIR}/src)
    target_link_libraries(solvers cryptominisat5)
```

### Step 2: Solver Wrapper (`satcheck_cryptominisat.h/.cpp`)

Create `src/solvers/sat/satcheck_cryptominisat.h`:

```cpp
#include "cnf.h"
#include <cryptominisat5/cryptominisat.h>

class satcheck_cryptominisatt : public cnf_solvert {
public:
  satcheck_cryptominisatt(message_handlert &);
  ~satcheck_cryptominisatt() override;

  std::string solver_text() const override;
  tvt l_get(literalt a) const override;
  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;
  bool has_assumptions() const override { return true; }
  bool has_is_in_conflict() const override { return true; }
  bool is_in_conflict(literalt a) const override;
  void register_xor(const bvt &lits, bool rhs) override;
  literalt new_variable() override;
  bvt new_variables(std::size_t width) override;

protected:
  resultt do_prop_solve(const bvt &assumptions) override;

private:
  CMSat::SATSolver *solver;
  // XOR constraints to pass natively
  struct xor_constraintt {
    std::vector<unsigned> vars; // 0-based CMS variables
    bool rhs;
  };
  std::vector<xor_constraintt> pending_xors;
  bool xors_added = false;
};
```

### Step 3: Implementation Details

**Variable mapping:** CBMC's `literalt` uses 1-based variable numbering
(var_no() starts at 1). CryptoMiniSat uses 0-based. The mapping:
- CBMC var `v` → CMS var `v - 1` (but var 0 is the constant, skip it)
- Actually: `literalt::var_no()` returns the variable number.
  `var_no() == 0` is the constant literal. Real variables start at 1.
  CMS variable = `var_no() - 1`.

**`lcnf(bvt)`:** Convert each `literalt` to CMS `Lit`:
```cpp
std::vector<CMSat::Lit> cms_clause;
for (auto lit : bv) {
  if (lit.is_true()) return; // tautology
  if (lit.is_false()) continue; // skip
  unsigned var = lit.var_no() - 1; // 0-based
  cms_clause.push_back(CMSat::Lit(var, lit.sign()));
}
solver->add_clause(cms_clause);
```

**`register_xor(lits, rhs)`:** Store for later:
```cpp
xor_constraintt xc;
bool adjusted_rhs = rhs;
for (auto lit : lits) {
  xc.vars.push_back(lit.var_no() - 1);
  if (lit.sign()) adjusted_rhs = !adjusted_rhs;
}
xc.rhs = adjusted_rhs;
pending_xors.push_back(std::move(xc));
```

**`do_prop_solve(assumptions)`:** Add XOR constraints, then solve:
```cpp
if (!xors_added) {
  for (auto &xc : pending_xors)
    solver->add_xor_clause(xc.vars, xc.rhs);
  xors_added = true;
}
// Add assumptions
for (auto lit : assumptions) {
  std::vector<CMSat::Lit> a = {CMSat::Lit(lit.var_no()-1, lit.sign())};
  solver->add_clause(a); // CMS doesn't have assume(), use unit clause
}
// Actually CMS has set_num_threads and solve with assumptions:
// solver->solve(&cms_assumptions);
CMSat::lbool ret = solver->solve();
```

**`l_get(literalt)`:** Get model value:
```cpp
if (a.is_true()) return tvt(true);
if (a.is_false()) return tvt(false);
unsigned var = a.var_no() - 1;
CMSat::lbool val = solver->get_model()[var];
if (val == CMSat::l_True) return a.sign() ? tvt(false) : tvt(true);
if (val == CMSat::l_False) return a.sign() ? tvt(true) : tvt(false);
return tvt(tvt::tv_enumt::TV_UNKNOWN);
```

### Step 4: Runtime Selection

In `solver_factory.cpp`, add:
```cpp
else if(solver_option == "cryptominisat")
{
#if defined SATCHECK_CRYPTOMINISAT
  return make_satcheck_prop<satcheck_cryptominisatt>(message_handler, options);
#else
  emit_solver_warning(message_handler, "cryptominisat");
#endif
}
```

### Step 5: Build Configuration

Build with: `cmake -S . -Bbuild-cms -Dsat_impl="minisat2;cryptominisat"`

Or as the sole solver: `cmake -S . -Bbuild-cms -Dsat_impl=cryptominisat`

### Step 6: Testing

1. Build and run: `cbmc test.c --sat-solver cryptominisat`
2. Run full regression: same as CaDiCaL tests
3. Benchmark against CaDiCaL baseline and CaDiCaL+xor-gauss

### Step 7: Optimization — Skip Clause Encoding for XOR

Once the basic integration works, try skipping the 4-clause encoding
for XOR gates when CMS is the backend. In `cnf.cpp`'s `lxor()`:
```cpp
if (solver_has_native_xor()) {
  literalt o = new_variable();
  // Don't call gate_xor() — skip the 4 clauses
  register_xor({o, a, b}, false); // CMS handles this natively
  return o;
}
```

This reduces clause count by ~4x for XOR-heavy problems but requires
CMS's Gaussian elimination to handle all XOR propagation.

## Risks and Mitigations

1. **CMS build complexity:** CMS has many dependencies (boost, zlib, etc.).
   Mitigate by disabling optional features (NOZLIB, NOBREAKID, NOSTATS).

2. **Variable numbering:** Off-by-one errors between CBMC (1-based) and
   CMS (0-based). Mitigate with careful mapping and assertion checks.

3. **Incremental solving:** CBMC calls solve() multiple times with
   different assumptions. CMS supports this via `solve(&assumptions)`.

4. **XOR constraint timing:** XOR constraints must be added before the
   first solve(). The `register_xor` → `do_prop_solve` flow handles this.

## Expected Performance

Based on CryptoMiniSat's SAT competition results:
- XOR-heavy problems (crypto, checksums): 10-100x speedup expected
- Non-XOR problems: comparable to MiniSat/CaDiCaL
- The native Gaussian elimination handles exactly the cases where our
  CaDiCaL approach (offline derived clauses) provides only 1.4x

## Files to Create/Modify

New files:
- `src/solvers/sat/satcheck_cryptominisat.h`
- `src/solvers/sat/satcheck_cryptominisat.cpp`

Modified files:
- `src/solvers/CMakeLists.txt` — add CMS download and build
- `CMakeLists.txt` — add "cryptominisat" to sat_impl options
- `src/goto-checker/solver_factory.cpp` — add runtime selection
- `src/goto-checker/solver_factory.h` — add help text
