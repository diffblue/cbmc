# Investigation: Why Are 4 CI Tests Extremely Slow on Certain Platforms?

Tracking PR: https://github.com/diffblue/cbmc/pull/8868

These tests were moved from CORE to THOROUGH in commit 6e616e96 to reduce
CI wall-clock time. This investigation determines the root cause of the
slowness: is it the operating system, the SAT/SMT solver, or a specific
CBMC mode?

## Tests Under Investigation

| # | Test | Reported slowness |
|---|------|-------------------|
| 1 | `jbmc-strings/StringSubstring/test.desc` | macOS-14: 1950s, Linux: 3s (650×) |
| 2 | `book-examples/pid/C11.desc` | macOS-14: 1069s, Linux: 28s (38×) |
| 3 | `contracts-dfcc/assigns-local-composite/test.desc` | macOS-14: 90s, Win: 78–114s, Linux: 8s |
| 4 | `cbmc-incr-smt2/structs/large_array_of_struct_nondet_index.desc` | Win VS2022: 472s, Linux: fast |

## Round 1: Normal Pass — {Linux, macOS} × {minisat2, cadical}

Tests 1–3 with the default SAT backend (no `--symex-driven-lazy-loading`,
no `--cprover-smt2`). Test 4 with incremental SMT2 on {Linux, Windows}.

### Results

| Test | Linux minisat2 | Linux cadical | macOS minisat2 | macOS cadical |
|------|---------------|--------------|----------------|---------------|
| StringSubstring | 2s | 4s | 2s | 3s |
| pid/C11 | 3s | 19s | 5s | 15s |
| assigns-local-composite | 4s | 5s | 7s | 5s |

| Test | Linux z3 | Linux cvc5 | Windows z3 | Windows cvc5 |
|------|---------|-----------|-----------|-------------|
| large_array_of_struct | 3s | 3s | **473s** | **472s** |

### Round 1 Conclusions

1. **No OS difference for tests 1–3.** macOS-14 ARM and Linux x86_64
   produce identical times for the same solver. The OS is not the cause.

2. **CaDiCaL is moderately slower** for pid/C11 (~5× vs minisat2) and
   StringSubstring (~2×), but all times are under 20 seconds. This does
   not explain the reported 1950s / 1069s.

3. **assigns-local-composite** shows no difference (4–7s everywhere) in
   the normal SAT pass.

4. **Test 4 is a Windows platform issue.** 473s on Windows vs 3s on
   Linux, identical across z3 and cvc5. The solver is irrelevant. This
   is likely due to Windows pipe/IPC overhead in the incremental SMT2
   pipeline. **Root cause identified — inherent to Windows.**

5. **The extreme slowness is NOT in the normal pass.** The reported times
   (1950s, 1069s, 90s) must come from other test configurations:
   `--symex-driven-lazy-loading` or `--cprover-smt2`.

## Round 2: Specific Slow Configurations (pending)

Based on Round 1, the extreme times come from specific CBMC modes, not
the default SAT pass. Round 2 tests:

- **StringSubstring with `--symex-driven-lazy-loading`** across
  {Linux, macOS} × {minisat2, cadical} — the 1950s was reported in the
  `jbmc-strings-symex-driven-lazy-loading-CORE` suite.

- **pid/C11 with `--cprover-smt2`** across {Linux, macOS} × {minisat2,
  cadical} — the 1069s was reported in `book-examples-cprover-smt2-CORE`.

- **assigns-local-composite with `--cprover-smt2`** across {Linux, macOS}
  × {minisat2, cadical} — the 90s macOS / 78–114s Windows times may come
  from the cprover-smt2 pass.

### Expected Outcomes

If the slowness is solver-dependent (e.g., cadical + lazy-loading is
pathological), we can fix it by changing the default solver on macOS or
adding solver-specific exclusion tags.

If the slowness is inherent to the mode (e.g., `--symex-driven-lazy-loading`
is slow regardless of solver), the THOROUGH classification is correct and
no further action is needed beyond the existing CI configuration.

## CI Configuration Notes

- macOS-14 CI uses `-Dsat_impl=cadical` (CaDiCaL only)
- Linux make builds use minisat2 (default)
- Linux cmake builds use `-Dsat_impl="minisat2;cadical"` (both, minisat2 default)
- The `--cprover-smt2` backend uses the `smt2_solver` binary via pipes
- The `--symex-driven-lazy-loading` mode uses a different class-loading
  strategy for Java bytecode (JBMC only)
