# Dog-fooding: compiling CBMC's own source tree with goto-cc

**Goal**: end-to-end, goto-cc should be able to produce a goto binary
from every `.cpp` file in CBMC's own source tree.  Progress towards
that goal is a practical measure of C++ front-end maturity.

**Why**: CBMC's source uses a realistic subset of modern C++ (STL
containers, templates, lambdas, polymorphism, RAII).  A bug that
breaks goto-cc on `src/util/dstring.cpp` is almost certainly the same
bug that breaks goto-cc on user code that uses `std::unordered_map`.

## Current baseline (2026-05-11)

Sampled on the 15 smallest files in `src/util/` (by line count), with
the compile flags from `build/compile_commands.json`:

| Status | Count | Files |
|--------|-------|-------|
| **OK** (produces .gb, exit 0, no errors) | **1** | `irep_hash.cpp` |
| Front-end error | 12 | 9 × `unordered_map` + 3 × `__stoa` (see below) |
| Crash (SIGSEGV) | 2 | `ref_expr_set.cpp`, `output_file.cpp` |

### Recurring root causes

1. **`std::unordered_map` instantiation through `rebind`**
   — 9 files fail here, all via `src/util/string_container.h`
   line 96's
   `std::unordered_map<string_ptrt, unsigned, string_ptr_hash>`.
   The failure surfaces as
   ```
   template scope 'rebind' is ambiguous
       __void_t<typename _Tp::template rebind<_Up>::other>>
   ```
   in libstdc++'s `__alloc_rebind` alias
   (`/usr/include/c++/13/bits/hashtable_policy.h` line 892).  Per
   [allocator.requirements], `std::allocator<pair<const K, V>>::rebind`
   is uniquely defined; CBMC's resolution incorrectly finds it
   ambiguous.

2. **`std::__stoa` variadic helper** — 3 files fail
   (`threeval.cpp`, `string_hash.cpp`, `get_base_name.cpp`) when any
   header pulls in `std::stof/stoi/stoul/...`.  The libstdc++ helper
   at `ext/string_conversions.h` line 56 is a variadic function
   template that takes a function-pointer parameter, and CBMC's
   overload resolution fails to deduce the function-pointer template
   argument.  Related to the KNOWNBUG test
   `cpp11_deduct_funcaddr` in `regression/cbmc-cpp/`.

3. **`address_of error` with `irep::pretty()` dump** — CBMC uses
   `std::max<size_t>(__builtin_floor(x) + 1, …)` at
   `hashtable_policy.h` line 687 and fails with a prvalue/reference
   materialization error.  The diagnostic embeds a full
   `irep::pretty()` dump rather than a clean message (same UX bug
   class as the SFINAE leak that was fixed in `e7080a017e`, but at
   a different code path — probably
   `c_typecheck_expr::typecheck_expr_address_of`).

## Approach

Start small, scale up:

1. **Layer 0** (done): `irep_hash.cpp` — 12 lines, minimal includes.
2. **Layer 1**: small files in `src/util/` that only pull in
   `util/irep.h`-shaped headers (no STL containers beyond
   `std::vector`, `std::list`).  Need to fix the `unordered_map`
   + custom-hash bug to unlock these.
3. **Layer 2**: files that use `dstring.h`, `symbol_table_base.h`.
4. **Layer 3**: entire `libutil.a` target.
5. **Layer 4**: language front-ends and `goto-programs`.
6. **Layer 5**: full CBMC executable.

Once Layer 1 is reachable, add a new `regression/goto-cc-cbmc/` entry
that actually invokes goto-cc on a representative CBMC source file;
the current crashes (`SIGSEGV` on 2 of 15 files) mean we cannot
confidently test at that scale yet.

## Tooling

* `scripts/dogfood_goto_cc.sh` — dog-food harness.  Classifies each
  file as OK / OK_NOISY / FAIL / CRASH.  Three modes:
  * `--baseline` (CI gate): just the files that must compile
    cleanly; exits non-zero if any do not.
  * default: the 30 smallest `.cpp` files under `src/util/`.
  * `--expand`: every `.cpp` under `src/util/`.
* `.github/workflows/pull-request-checks.yaml` job
  `check-dogfood-goto-cc`: runs the baseline as a gate and the
  default sample for visibility.

## Progress

| Date | Sample (30 smallest src/util/*.cpp) | OK | OK_NOISY | FAIL | CRASH | Notes |
|------|-------------------------------------|----|----------|------|-------|-------|
| 2026-05-11 (initial)   | 15 smallest | 1 | 0 | 12 | 2 | baseline after SFINAE fix `e7080a017e` |
| 2026-05-11 (alignment) | 15 smallest | 1 | 0 | 13 | 1 | cycle guard `424da3ca32` — 1 crash eliminated |
| 2026-05-11 (rebind)    | 15 smallest | 1 | 3 | 10 | 1 | `87d40979a3` — unordered_map + custom hash unblocks 3 files (noisy) |
| 2026-05-11 (invariants)| 30 smallest | 1 | 5 | 24 | 0 | `bb36504ba4` — two invariants softened; 0 crashes on the 30-file sample |

## Fixes that have landed (in order)

1. `e7080a017e` — SFINAE substitution-failure leak absorbed per
   [temp.deduct]/7-8.  (Pre-dog-food context; large front-end
   ripple effect.)
2. `424da3ca32` — `alignment()` cycle guard for pathological
   type-graph cycles, removing one SIGSEGV class.
3. `87d40979a3` — class-inheritance dominance rule in
   `disambiguate_template_classes`, fixing
   `std::unordered_map<K, V, CustomHash>` `rebind is ambiguous`.
4. `bb36504ba4` — soften two invariants
   (`member_offset::bit_field_bits == 0` and destructor-body
    precondition) to graceful failure, eliminating the remaining
    crashes seen in the 30-file sample.

## Remaining recurring errors (30-file sample)

| # files | First error | Root cause (hypothesis) |
|---------|-------------|-------------------------|
| ≥8 | `invalid implicit conversion from 'char [1l]' to 'struct basic_string'` | Default argument `std::string x = ""` on a constructor of a class that inherits from another — implicit conversion pathway not finding the `basic_string(const char*)` constructor. |
| ≥5 | cascade from `std::unordered_map` instantiation | Downstream of the basic_string / __stoa failures: many files cascade when `std::string` operations fail. |
| ≥3 | `found no match for symbol '__stoa'` | libstdc++ `ext/string_conversions.h` variadic template with function-pointer parameter.  Candidate does deduce `<float, float, char>` but outer lookup still fails. |
| 1 | `instantiating 'nfat' with <char>` | CBMC-internal template `nfat<char>` in `src/util/edit_distance.h` — needs investigation. |

*Updated: 2026-05-11*
