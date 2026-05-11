# CI Known Failures — `cpp11-parser-rework-squashed`

This document tracks all known CI failures on the `cpp11-parser-rework-squashed`
branch that we carry as pre-existing technical debt.  Each item is a TODO
we will eventually need to resolve before the branch is merged upstream.

Snapshot taken against GitHub Actions run for commit [`ac830e7ef6`](
https://github.com/diffblue/cbmc/pull/.../commits/ac830e7ef6) (2026-05-10).
See [the CI run index](
https://github.com/diffblue/cbmc/actions/runs/25620772992) for the source
logs.

### Progress since ac830e7ef6

The following issues have already been addressed on this branch
*after* the CI snapshot above.  They will be reflected once CI is
re-triggered:

* **Array member initializer `: _Buf() {}`** (MSVC `<xstring>` SSO
  buffer) — fixed in `b10e77f534`.
* **`reinterpret_cast<T&>(x)` and `&reference`** (MSVC `<atomic>`
  `_Atomic_lock_acquire`) — fixed in `311dd6e68a`.
* **Clang `__c11_atomic_*` intrinsics** (macOS libc++ `<atomic>`
  primitives) — declared in `e255c90e72`.
* **`cpp_scope suppress_cache_invalidation` stale-lookup bug** —
  fixed in `b4f40b57b3`.  Affected class-scope lookups across
  both MSVC and libc++ (e.g. MSVC `_Iterator_base12::_Myproxy`).
* **Silent SFINAE for unassigned template args** — fixed in
  `368b07d6ea`.  `cpp_typecheck::instantiate_template` emitted
  `"internal error: template parameter without instance"` as a
  hard error; per [temp.deduct]/8 it should be a silent
  substitution failure.
* **Per-member catch during template instantiation** — fixed in
  `97f5d81455`.  Per [temp.inst]/11, a failed type-check of one
  member should not abort processing of sibling members; added
  try/catch around `convert_template_declaration` and
  `typecheck_compound_declarator` inside class-body processing
  when we are currently instantiating a template.

### Preprocessed-header test results after these fixes

Locally, against `/tmp/macos-pp-new/` and `/tmp/msvc-pp-new/`:

* **macOS (Xcode 16.4 libc++)**: 5 of 7 preprocessed-header tests
  now report VERIFICATION SUCCESSFUL on the CBMC output —
  `Address_of_Method1`, `STL1`, `STL2`, `Vector1`,
  `cpp11_vector_size`.  Only `cpp17_any_basic` and
  `cpp20_coroutine_types` still fail (both for reasons outside the
  basic_string cascade: `std::any` method bodies and libstdc++-
  internal `std::__n4861` respectively).  Note: on the *real* CI
  runner these tests still fail their test.desc assertion match
  because `main()` doesn't reach the goto model — see "Remaining
  work" below.
* **MSVC (VC 14.44.35207)**: 12 of 26 preprocessed-header tests
  now pass: Vector1, cpp11_condition_variable_header,
  cpp11_shared_ptr, cpp17_filesystem_basic,
  cpp17_filesystem_path_ops, cpp17_mutex_basic,
  cpp17_numeric_basic, cpp17_shared_ptr, cpp17_string_view(_basic),
  cpp17_thread_basic, cpp20_iostream_basic.

### Remaining work (not yet fixed)

The remaining MSVC and macOS failures all reduce to one deeper
issue: **using an uninstantiated class template as the type of a
data member or the underlying type of a typedef**.  Examples:

* macOS libc++ `basic_string` — `typedef typename __alloc_traits::
  pointer pointer;` fails because `allocator_traits<allocator<T>>`
  isn't eagerly instantiated; after this typedef fails, sibling
  typedefs (`__is_long`, `__fits_in_sso`, `npos`) also fail to
  register in the instantiated class scope, and out-of-class
  method bodies then emit `symbol 'pointer' is unknown`.  With the
  per-member catch in place, errors no longer cascade, but the
  member still doesn't register.
* MSVC `atomic_flag::_Storage` — type is `atomic<long>` which is
  a class template that hasn't been instantiated when
  `atomic_flag` is elaborated; the data member declaration throws
  during `typecheck_type(declaration.type())` (the type-check of
  the declaration's *type* itself, before reaching
  `typecheck_compound_declarator`).  Wrapping that call in a
  try/catch makes the member name register but suppresses real
  errors for 30+ regression tests.
* MSVC `_Rebind_alloc_t` / `allocator_traits` deduction cycle —
  same shape, deeper call graph.

#### Phase 1 diagnosis (2026-05-10)

Detailed investigation of the MSVC `atomic_flag::_Storage` case
was done using runtime instrumentation of `typecheck_compound_body`,
`elaborate_class_template`, and `resolve`.  Findings:

* `atomic_flag` is a non-template struct, processed via the normal
  `convert_non_template_declaration → typecheck_compound_body`
  path.  Its body has 6 member declarations: 4 methods
  (`test_and_set x2`, `clear x2`), 1 default constructor, and the
  data member `atomic<long> _Storage;` at the end.
* The first 5 declarations process successfully; `_Storage`'s type
  declaration reaches `typecheck_type(declaration.type())` at
  `cpp_typecheck_compound_type.cpp:1337` (as `cpp_name{atomic,
  template_args{long}}`).
* `typecheck_type` dispatches to `resolve(atomic<long>, TYPE, ...)`.
  `resolve` triggers `elaborate_class_template(atomic<long>)` which
  cascades through 22+ sub-elaborations (remove_cv, is_same,
  disjunction, _Disjunction, _Select, _Atomic_integral_facade,
  _Atomic_integral<long,4>, _Atomic_storage<long,4>,
  remove_reference, etc.).  The elaboration *chain runs to
  completion* — none of the sub-elaborations throw at class-body
  time.
* Nevertheless, `typecheck_type(atomic<long>)` throws `int 0`
  with exactly one error added to the message handler during the
  call.  The error's source_location is `atomic_flag::test_and_set`
  line 2811 (`return _Storage.exchange(true, _Order) != 0;`) and
  the text is `symbol '_Storage' is unknown`.
* The backtrace of the `_Storage unknown` emission goes through
  `typecheck_method_bodies()` → `convert_function` → ... →
  `resolve`.  That path runs at top-level, *after*
  `typecheck_compound_body`.  So the error is emitted much later,
  yet its presence is reflected in the error counter at class-body
  time.  This suggests CBMC's method-body deferral queue is being
  flushed eagerly during `resolve` (probably via
  `deferred_method_bodies` promotion in `typecheck_expr.cpp`),
  which in turn pulls out atomic_flag's 4 methods and tries to
  type-check them in a scope where `_Storage` isn't yet registered.
* The throw from `typecheck_type` then propagates up, aborting the
  remainder of `typecheck_compound_body` for atomic_flag.  Because
  `_Storage`'s declarator is the last in the body, at least no
  sibling members are dropped, but `_Storage` itself never
  registers.

The root cause is therefore twofold and mutually reinforcing:
 1. `resolve` (or `elaborate_class_template` or a sub-step)
    promotes methods of atomic_flag out of `deferred_method_bodies`
    *before* atomic_flag's class body is complete.
 2. When those methods are type-checked, they can't find
    `_Storage` and emit an error, which aborts atomic_flag's class
    body mid-way (so `_Storage` never gets registered).

A proper fix needs to break this deadlock: either (A) the
method-body deferral queue must not be flushed while any enclosing
class body is still being processed, or (B) data-member
declarations must be registered in the class scope (by name, even
with a placeholder type) *before* any sub-elaboration that might
flush the queue.  Option (B) is likely simpler and less invasive.

The isolated reproducers added in `regression/cbmc-cpp/cpp11_
template_member_data/`, `.../cpp11_template_nested_typedef/`, and
`.../cpp11_template_diamond_inst/` currently pass because they
don't trigger the deferred-queue flush — the real failure requires
the full `_Atomic_storage`/`_Atomic_integral`/`atomic` inheritance
chain plus SFINAE cascades that exist in the live MSVC headers.
Extending one of those reproducers to also trigger the premature
flush is a useful next step for the fix work.

The "Performance Benchmarking" job (perf-benchcomp) fails at the end of the
AWS C Common comparison with exit code 1 on otherwise-successful metrics; by
agreement with the branch owner it is tracked separately and not part of this
list.  The `include-what-you-use` job is also outside the scope of this
document.

Legend:
- 🆕 introduced on this branch (pre-existing on parent commit would be 🅿️)
- 🅿️ pre-existing before this branch
- 🔄 intermittent / flaky on the platform
- 📐 toolchain/stdlib compatibility gap (requires CBMC front-end work)
- 🪲 CBMC type-check or goto-conversion bug (reproducible on smaller inputs)

---

## 1. macOS — libc++ (Xcode 15.4 on macOS 14, Xcode 16.4 on macOS 15)

Job IDs: `check-macos-14-cmake-clang`, `check-macos-15-intel-make-clang`

| Test | Status | Root cause |
|------|--------|------------|
| `regression/cbmc-cpp/Vector1` | 🅿️ 📐 | libc++ `__libcpp_operator_new(_Args&&...)` is a variadic function template; CBMC's `--cpp11` deduction cannot deduce `_Args = {size_t}` from a single `size_t` argument, so the call at `new:296` fails with `found no match for symbol '__libcpp_operator_new'`.  This cascades: `std::logic_error`/`std::runtime_error` constructors fail, `__cxx_atomic_*` primitives are missing, `std::basic_string::append` and `__system_error::error_category`/`error_code` operators misresolve, main() never reaches the goto model, and the assertion at line 35 is never verified. |
| `regression/cbmc-cpp/cpp11_vector_size` | 🅿️ 📐 | Same `__libcpp_operator_new` / libc++ cascade as above.  Was incorrectly untagged in `9ab95889af` based on a flawed `--cpp14` verification; re-tagged `gcc-only` in `b12307a216` as a holding action until CBMC properly parses the libc++ allocator helpers. |

### What to do

1. Fix the variadic-template argument deduction path in
   `src/cpp/cpp_typecheck_resolve.cpp::guess_function_template_args` so that
   `template <class... Args> void f(Args... args)` correctly deduces `Args =
   {T}` when called with a single argument of type `T` — *including the case
   where the function is within a class/namespace with `abi_tag`/visibility
   attributes applied*.  Minimal reproducer:
   ```cpp
   typedef unsigned long size_t;
   namespace std {
     template <class... A>
     __attribute__((__abi_tag__("ne190102")))
     void *op_new(A... a) { return 0; }
     inline void *alloc(size_t s) { return op_new(s); }
   }
   ```
   Works on Linux today but fails when the full libc++ preamble is included
   (presumably an interaction with earlier SFINAE failures poisoning the
   candidate set).
2. Once (1) is done, drop `gcc-only` from `cpp11_vector_size` again (and any
   other tests on the libc++ path).
3. Repeat the audit that `be467fbd92` started for the remaining tests that
   pass *structurally* on the `.ii` artifact but fail at verification on real
   macOS.

### Reproducing locally

The macOS CI uploads `macos-preprocessed-headers` artifacts; download them
with `gh run download <run-id> --name macos-preprocessed-headers` and run
CBMC locally with the test.desc flags (typically `--cpp11`).  Do **not**
rely on the final `VERIFICATION SUCCESSFUL` line alone — look for a
`main.cpp function main` section in the output; if it is missing, the
test.pl assertion match will still fail.

---

## 2. Windows — MSVC VS2022 (cl 14.44.35207) and VS2025

Job IDs: `check-vs-2022-make-build-and-test`, `check-vs-2025-cmake-build-and-test`

### 2.1 MSVC STL header compatibility (deterministic)

Both VS2022 and VS2025 share the same 14 cbmc-cpp failures; all trace back
to one of three MSVC-STL-specific construct families that CBMC's parser
does not yet handle.

| Test | Root cause |
|------|------------|
| `STL2` | 🅿️ 📐 MSVC `<vector>` / `<xmemory>`: `std::_Rebind_alloc_t<Alloc, T>` alias template (uses `__t` helper) / `_Normal_allocator_traits` specialization path.  CBMC repeatedly instantiates `std::vector<int, allocator>` and cycles through the same `allocator_traits`/`_Normal_allocator_traits` instantiation without reaching a concrete answer. |
| `cpp11_vector_size` | 🅿️ 📐 Same MSVC `_Rebind_alloc_t` / `allocator_traits` issue as STL2. |
| `cpp11_vector_front_body` | 🅿️ 📐 Same. |
| `cpp11_vector_probe` | 🅿️ 📐 Same. |
| `cpp11_vector_push_back` | 🅿️ 📐 Same. |
| `cpp11_vector_pushback` | 🅿️ 📐 Same. |
| `cpp11_vector_verify` | 🅿️ 📐 Same. |
| `cpp17_vector_basic` | 🅿️ 📐 Same. |
| `cpp11_map_insert` | 🅿️ 📐 MSVC `<xmemory>` / `<xstring>`: `_Myproxy` control block, plus `"direct assignments to arrays not permitted"` in `<xstring>` at line 493 (SSO buffer assignment via `_Bx._Buf`). |
| `cpp11_condition_variable_header` | 🅿️ 📐 MSVC `<atomic>` line 472 `_Atomic_lock_acquire`: address-of a built-in atomic operation that CBMC cannot represent. |
| `cpp11_future_header` | 🅿️ 📐 Same atomic-lock issue as `cpp11_condition_variable_header`. |
| `cpp14_chrono_basic` | 🅿️ 📐 MSVC `<chrono>` uses `_Rebind_alloc_t` / `allocator_traits` paths. |
| `cpp17_filesystem_basic` | 🅿️ 📐 MSVC `<filesystem>` uses `<xstring>` SSO array assignment. |
| `cpp17_filesystem_path_ops` | 🅿️ 📐 Same. |
| `cpp17_mutex_basic` | 🅿️ 📐 Same `_Atomic_lock_acquire` root as condition_variable. |
| `cpp17_thread_basic` | 🅿️ 📐 MSVC `<utility>` line 137 `forward` / `move` template resolution with constrained `_Remove_reference_t`. |
| `cpp17_valarray_basic` | 🅿️ 📐 MSVC `<valarray>` (allocator traits path). |

### 2.2 Non-cpp VS2022-only failures (likely flaky / Makefile-driver issue)

Three non-STL regression suites have new VS2022 failures that are not seen
on VS2025:

| Test | Status | Notes |
|------|--------|-------|
| `regression/acceleration/array_safe4` | 🔄 🪲 | Failed on ac830e7; was passing on 7c68e97 and 894e427.  Error text not captured by the Makefile test driver — needs a dedicated re-run with `-p` to see stdout/stderr. |
| `regression/contracts-dfcc/assigns_enforce_havoc_object` | 🔄 | Same (Makefile suppresses detail). |
| `regression/contracts-dfcc/dont_skip_cprover_prefixed_vars_pass` | 🔄 | Same. |
| `regression/goto-harness/pointer-function-parameters-struct-mutual-recursion` | 🔄 | Same. |
| `regression/cbmc/overflow/leftshift_overflow-c89` | 🆕 | Newly failing at ac830e7 vs 7c68e97.  Possibly affected by `config.cpp.cpp_standard` default change in `config.cpp::1289`.  Needs investigation. |

### 2.3 VS2025-only unit-test noise (not build-blocking)

The `unit` binary on VS2025 prints `FAILED:` lines from
`unit/solvers/smt2_incremental/smt_to_smt2_string.cpp:{256,257,258}`,
`unit/util/irep.cpp:311`, and `unit/util/irep_sharing.cpp:{33,138}`, plus
a large volume of `jbmc/unit/java_bytecode/.../convert_invoke_dynamic.cpp`
failures.  All of these test cases still report "All tests passed" at the
suite level, so they are Catch2 `CHECK_FALSE`/`SECTION` lines inside
passing tests — cosmetic but worth auditing (and probably removing the
`CHECK(false)` lines if they are meant to be negative-path assertions).

### What to do

1. Start with the smallest reproducers: `cpp11_condition_variable_header`
   and `cpp17_mutex_basic` both fail on MSVC `<atomic>` line 472
   `_Atomic_lock_acquire`.  This is likely solvable with a CBMC library
   stub for MSVC's `_Atomic_*` intrinsics (we already stub GCC's
   `__atomic_*`).
2. Next tackle `<xstring>` SSO assignment — add support for direct
   assignment to in-class `char[N]` members (currently rejected with
   `"direct assignments to arrays not permitted"`).  This probably needs
   work in `cpp_typecheck_expr::typecheck_expr_binary` for `=` with
   array lvalue.
3. The `_Rebind_alloc_t` / `allocator_traits` cycle is the big one —
   half the vector/chrono/filesystem tests share it.  Needs deep
   investigation of MSVC's `_Normal_allocator_traits`
   specialization pattern.
4. For the flaky non-cpp tests on VS2022 (§2.2): re-run the CI job and
   see whether the set is stable.  If it is, get them tagged
   `broken-msvc` or similar so the makefile test runner prints detail.

---

## 3. Linux — newer libstdc++ (GCC 15 on Ubuntu 26.04)

Not in the GitHub Actions matrix, but **will be** when Ubuntu 26.04
joins.  Discovered by running the cbmc-cpp regression in a
`ubuntu:26.04` container.

| Test | Root cause |
|------|------------|
| `cpp20_sort_cpp20` | 🅿️ 📐 libstdc++ 15 `<bits/max_size_type.h>`: `__max_size_type` is a struct wrapping `unsigned __int128` with implicit arithmetic conversions (`operator*=`, `/=`, `<<=`, etc.).  CBMC rejects struct↔integer implicit conversions and emits a cascade of `"conversion from 'unsigned __int128' to 'struct __max_size_type': implicit arithmetic conversion not permitted"` / `"conversion from 'struct __max_size_type' to 'unsigned long int': implicit arithmetic conversion not permitted"`. |
| `cpp23_optional_monadic` | 🅿️ 📐 libstdc++ 15 `<optional>` line 495 `_Optional_payload`: uses `auto` return types in member templates that CBMC cannot resolve (`"member operator requires struct/union type on left hand side but got 'auto'"`), and the subsequent `_Optional_payload` lookup fails. |
| `cpp11_vector_front_body` | 🅿️ 🪲 | Cascades: libstdc++ 15 `stl_vector.h` line 501 `_S_nothrow_relocate` → `"unexpected ID_code expression"` → `__builtin_operator_new` / `__uninitialized_move_if_noexcept_a` template instantiation fails → symex invariant violation `"level0: failed to find this"`. |
| `cpp17_vector_basic` | 🅿️ 🪲 Same cascade as `cpp11_vector_front_body`. |
| `cpp20_optional_basic` | 🔄 | Times out on Ubuntu 26.04 at the 60 s limit (runs to VERIFICATION SUCCESSFUL within 30 s if invoked directly — so it is a scheduler / timeout configuration issue, not a correctness bug).  Bumping the per-test timeout or enabling `--unwind` caps should recover it. |

### What to do

1. Implement implicit struct↔integer conversions for types flagged with
   a libstdc++-internal marker (or, better, detect the `__abi_tag_`
   tagged struct wrappers over `unsigned __int128`).  This is the root
   cause of both `__max_size_type` and many future integer-extension
   types.
2. Extend `auto` return-type deduction to class-template member
   functions that are evaluated as part of operand types (currently
   only works for function *definitions*).
3. Investigate `"unexpected ID_code expression"` during type-checking
   of `_S_nothrow_relocate` — likely a `noexcept(auto)` or concept
   predicate path that the type-checker does not expect.

Note that none of these are *regressions* — they are new failures
because the toolchain is new.  When Ubuntu 26.04 (or an equivalent
GCC 15 container) enters the CI matrix, every one of these tests will
need a matching `gcc<15` or `libstdc++<15` exclusion **or** a fix.

---

## Summary of forthcoming work (rough ordering)

1. **Small (DONE)**: Stub `__c11_atomic_*` intrinsics for libc++ and
   `_Atomic_lock_acquire`/array-member-init for MSVC `<xstring>` —
   fixed in b10e77f534, 311dd6e68a, e255c90e72.
2. **Medium**: Deep out-of-class template-member-scope lookup: both
   macOS `basic_string::operator=` (`pointer`, `__is_long`, `npos`,
   `__fits_in_sso`) and MSVC `_Iterator_base12::operator=` (`_Myproxy`)
   and `atomic_flag::test_and_set` (`_Storage`) fail with
   `"symbol 'X' is unknown"`.  CBMC's class-scope lookup for unqualified
   identifiers inside a template-member-function body defined outside
   the class does not find members that are declared later in the
   class or come from dependent base classes.  Both platforms share
   this root cause.  A minimal reproducer that reliably breaks would
   speed up the fix substantially.
3. **Medium**: SFINAE `enable_if_t<V, int> = 0` with uninstantiated
   value template parameter — see MSVC `system_error:174` and libc++
   `error_code.h:55` ("instantiating 'std::enable_if_t' with <FALSE,
   signed int>").  Value-template-parameter evaluation during
   deduction needs to produce the actual bool, not FALSE as a
   fallback.
4. **Medium**: libstdc++ 15 struct-wrapped-integer implicit conversions
   — unlocks `cpp20_sort_cpp20` and the `__max_size_type` cascade.
5. **Large**: MSVC `_Rebind_alloc_t` / `allocator_traits` path — 8+
   vector/chrono tests on Windows.
6. **Ongoing**: flaky contract tests on VS2022 (§2.2) — need per-test
   detail in the Makefile runner to know what's actually going wrong.

---

*Last updated: 2026-05-10 (after c_typecheck and clang-intrinsic fixes)*
