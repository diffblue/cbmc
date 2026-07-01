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
| Crash (SIGSEGV) | 2 | `ref_expr_set.cpp` (**fixed 2026-06-30, reference-NTTP — see fix #10**), `output_file.cpp` |

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

| Date | Sample | OK | OK_NOISY | FAIL | CRASH | Notes |
|------|--------|----|----------|------|-------|-------|
| 2026-05-11 (initial)   | 15 smallest   | 1 | 0 | 12  | 2 | baseline after SFINAE fix `e7080a017e` |
| 2026-05-11 (alignment) | 15 smallest   | 1 | 0 | 13  | 1 | cycle guard `424da3ca32` — 1 crash eliminated |
| 2026-05-11 (rebind)    | 15 smallest   | 1 | 3 | 10  | 1 | `87d40979a3` — unordered_map + custom hash unblocks 3 files (noisy) |
| 2026-05-11 (invariants)| 30 smallest   | 1 | 5 | 24  | 0 | `bb36504ba4` — two invariants softened; 0 crashes on the 30-file sample |
| 2026-05-11 (expand)    | all src/util/ | 1 | 7 | 109 | 0 | `6b09016f4a` — vtable type-mismatch invariant + cleaner `expr2c` fallback (replaces megabyte-long irep dumps with `<<expr:ID>>` placeholders) |
| 2026-05-12 (string)    | all src/util/ | 1 | 7 | 109 | 0 | `9cbd9daef9` — `char[N]`→`std::string` fallback; eliminates 35 `invalid implicit conversion from 'char [1l]' to 'struct basic_string'` errors (cascades, same count) |
| 2026-05-12 (using)     | all src/util/ | 1 | 7 | 109 | 0 | `9537b6bfc5` — class-member `using Base::X` with unresolved lookup silently dropped; eliminates 31 `using identifier 'remove' not found` errors (cascades, same count) |
| 2026-05-12 (syshdr)    | all src/util/ | **7** | **1** | 109 | 0 | `a760f05e84` — null message handler around system-header function body + default template args; eliminates 27 `__stoa` leaks and moves 6 files from OK_NOISY to OK_CLEAN |
| 2026-05-12 (destr)     | all src/util/ | 7 | 5 | 105 | 0 | `5e7efee580` + `7a9154a46e` + `56c27ea9d3` — destructor fallback + silent fallbacks for uninitialised constexpr + bare `enum class X;` forward declaration; eliminates 64 `'' is not static member of 'const struct basic_string'` errors |
| 2026-05-12 (tmpl-no-match) | all src/util/ | **10** | **4** | 103 | 0 | `01507a3e6d` — resolve: silently discard template-only no-match per [temp.deduct]/8; eliminates the `invariant_violated_structured` cascade that had been emitted by 60+ files and moves 3 files to OK_CLEAN + 1 to OK_NOISY-to-OK_CLEAN |
| 2026-05-12 (funcaddr+SIGSEGV) | all src/util/ | 10 | 4 | 103 | 0 | `d612fe6dac` (plain function-pointer target-type deduction per [temp.deduct.funcaddr]; promotes `cpp11_deduct_funcaddr` KNOWNBUG→CORE) + `df5f5d955e` (guard empty declarator-name sub on trailing-return-decltype path; eliminates MSVC `cpp11_future_header` SIGSEGV on preprocessed-header runs) |
| 2026-05-13 (duration) | all src/util/ | 10 | 4 | 103 | 0 | `2e8e74f8ed` — skip self-referential `common_type_t<duration>` member during class elaboration; unlocks `_MyRep` + constructors + operators on `std::chrono::duration<...>`, MSVC `cpp14_chrono_basic` preprocessed-header run now VERIFIES SUCCESSFUL |
| 2026-06-30 (variadic) | all src/util/ | **36** | **59** | **22** | 0 | cumulative variadic-pack-expansion + std::function rework (layers 1, 2a/2b/2c-i/2c-ii, 3a, 3b, 3c-i): multi-argument std::function now constructs AND invokes soundly; 95/117 files now produce a goto binary (was 14/117 on 2026-05-13) |
| 2026-06-30 (adl) | all src/util/ | **38** | **60** | **19** | 0 | suppress ADL when ordinary lookup finds a class member (N5008 [basic.lookup.argdep]/3.1); unblocks the xml.h `find(element)` vs `std::basic_string::find` ambiguity (3 files) |

## Fixes that have landed (in order)

1. `e7080a017e` — SFINAE substitution-failure leak absorbed per
   [temp.deduct]/7-8.  (Pre-dog-food context; large front-end
   ripple effect.)
2. `424da3ca32` — `alignment()` cycle guard for pathological
   type-graph cycles, removing one SIGSEGV class.
3. `87d40979a3` — class-inheritance dominance rule in
   `disambiguate_template_classes`, fixing
   `std::unordered_map<K, V, CustomHash>` `rebind is ambiguous`.
4. `bb36504ba4` — harness + soften `member_offset` and
   `convert_function` destructor preconditions; add CI gate
   harness.
5. `4648a540b8` — CI job `check-dogfood-goto-cc` added to
   `pull-request-checks.yaml`.
6. `6b09016f4a` — soften vtable type-mismatch invariant; replace
   irep-dump fallback in `convert_norep` with a compact
   placeholder.
7. `9cbd9daef9` — `implicit_typecast`: `char[N]` → `std::string`
   fallback synthesising the 3-arg basic_string ctor, since
   libstdc++'s convenience ctor
   `basic_string(const _CharT*, const _Alloc& = _Alloc())` is a
   SFINAE-guarded member template not elaborated into the struct
   components list.
8. `9537b6bfc5` — `cpp_typecheck_using`: base-class walk + silent
   drop of class-member `using Base::X` when lookup fails
   (access-control-only, no goto-conversion effect).
9. `a760f05e84` — null message handler around system-header
   function bodies (existing error-recovery already clears the
   body) and default template args (per [temp.deduct]/7-8).
   Removes 27 leaked `__stoa` errors from dog-food output.
10. `15ec1832dc` + `8dd999d43e` — reference/pointer **non-type
    template parameters**.  `template <typename T, const T &empty
    = T::blank>` (the shape of `src/util/reference_counting.h`)
    was mishandled: the declarator's `&` was dropped
    (`typecheck_template_parameters` used `declaration.type()`
    alone), so the reference parameter became a value parameter of
    type `T`, the reference argument (`&T::blank`) was valuified,
    and `template_suffix` aborted in `to_constant_expr` while
    naming the instance.  Fixed in three cooperating parts, per
    N5008 [temp.param]/6, [dcl.meaning]/1, [temp.arg.nontype]/2:
    (a) build the parameter symbol from
    `declarator.merge_type(declaration.type())` so it keeps its
    reference/pointer type; (b) do not valuify a reference/pointer
    argument in `typecheck_template_args`; (c) build the
    instance-name suffix of an address-of-object argument from the
    object's identity.  **`ref_expr_set.cpp` now compiles to a
    goto binary (was a SIGSEGV/abort).**  CORE tests:
    `cpp11_reference_nontype_template_param`,
    `cpp11_reference_nontype_template_param_distinct`,
    `cpp11_pointer_nontype_template_param`.  (`rename_symbol.cpp`
    and `replace_symbol.cpp` still fail, but on a distinct
    `std::unordered_map<dstringt, …>` instantiation issue.)
11. `37577e13b4` + `9132564dbe` — **explicit class template
    specialization named with a qualified-id** (N5008
    [temp.expl.spec]/2).  `template <> struct ns::G<char> {...}`
    (and `template <> struct std::hash<T> {...}`, the standard way
    to make a user type an unordered-container key) was silently
    skipped by `convert_template_declaration` — mistaken for an
    out-of-class nested definition — so the primary template was
    used instead of the specialization.  Fixed by distinguishing on
    the final name component (a specialization's final component
    carries template arguments; a nested definition's does not) and
    resolving the qualified name via `resolve_scope` in
    `convert_class_template_specialization`.  CORE tests:
    `cpp11_qualified_class_template_specialization`,
    `cpp11_std_hash_user_specialization`.
12. `40c2118140` — **incomplete class template instance elaborated
    at its construction site** (N5008 [temp.inst]/2).  When a class
    has a member `std::unordered_map<K,V>`, libstdc++ references the
    non-const `std::pair<K,V>` (distinct from the value_type
    `std::pair<const K,V>`) from a typedef type-checked while
    `skip_typechecking_elaborate` is set, leaving `std::pair<K,V>`
    registered but INCOMPLETE and never later elaborated; a
    subsequent explicit `std::pair<K,V>(a,b)` then found only the
    implicit members of an incomplete class (`found no match for
    symbol 'pair'`).  Fixed in `cpp_typecheck_resolvet::resolve` by
    elaborating an incomplete `template_class_instance` immediately
    before `make_constructors` (want == VAR) — i.e. at the actual
    construction site, not while elaboration is suppressed, so the
    deferred elaboration of `std::basic_string` is undisturbed.
    CORE test `cpp11_pair_incomplete_member_unordered_map`.  This
    removes the `found no match for symbol 'pair'` cascade from
    `rename_symbol.cpp` / `replace_symbol.cpp` (they now progress to
    distinct downstream errors: `depth_iterator_baset` instantiation
    and `std::unordered_map<dstringt, exprt>` respectively).
13. `9a8e231654` — **function type with a pointer/reference return
    and empty parameter list** (N5008 [dcl.decl]/4,
    [dcl.ambig.res]).  `rDeclarator` only re-parsed an empty `()` as
    a function parameter-list when there was no leading ptr-operator,
    so `int*()` / `int&()` were mis-parsed as `int*` / `int&` (the
    `()` dropped).  Such a type then failed to match a function-type
    partial specialization `X<R(A...)>` — the shape of
    `std::function<R&()>`.  Fixed by also backtracking when the
    nested declarator is empty (regardless of a ptr-operator), while
    leaving non-empty groupings such as `int(*)()` untouched.  This
    was the `depth_iterator_baset` layer of the `rename_symbol.cpp`
    cascade: `util/expr_iterator.h`'s
    `std::function<exprt &()> mutate_root; ... if(mutate_root)` had
    its explicit `operator bool` looked up on the mis-parsed type.
    CORE tests `cpp11_function_type_ptr_ref_return`,
    `cpp11_explicit_bool_function_ref_return`.  `rename_symbol.cpp`
    now progresses to a distinct `operand of unary * ... is not a
    pointer` error in `expr_iterator.h`.
14. `307e4cabf7` — **brace-construct a temporary from a reference
    member** (N5008 [dcl.init.aggr]/1, [dcl.init.list]/3).  `It{arg}`
    for a class with a user-declared converting constructor must call
    that constructor, and a reference-member argument must be
    dereferenced exactly once.  Two fixes:
    typecheck_expr_explicit_constructor_call classified any 2-param
    constructor with a reference 2nd parameter as copy/move, so a
    converting constructor `It(const S&)` was mistaken for one and
    `It{arg}` did (ill-formed) aggregate initialization — now only a
    parameter of the class's OWN type counts as copy/move; and the
    already-type-checked braced operands are marked
    already_typechecked before new_temporary, so cpp_constructor does
    not re-type-check (and double-dereference) a reference-member
    access `*this->root`.  This was the `expr_iterator.h` range-
    adapter layer of `rename_symbol.cpp`.  CORE test
    `cpp11_brace_construct_reference_member`.  **`rename_symbol.cpp`
    now compiles to a goto binary.**
15. `25f4b86590` — **reference direct-initialization with
    parentheses/braces** (N5008 [dcl.init.ref], [dcl.init]/16).
    `T &r(init)` binds the reference like `T &r = init`, but the
    parser stores the initializer as init_args and a reference is not
    an object a constructor initializes, so it was reported "declared
    as reference but is not initialized".  Fixed in convert_new_symbol
    by attaching the single init_args operand as the reference's value
    (and clearing init_args).  This was the `replace_symbol.cpp` layer
    (`const exprt &const_dest(dest);`).  CORE test
    `cpp11_reference_paren_init`.  **`replace_symbol.cpp` now compiles
    to a goto binary.**
16. `a02982c4e7` — **member template operators in operator overload
    resolution** (N5008 [over.match.oper]/3.2, [over.match.best]/2).
    operator_is_overloaded detected member operator candidates only
    among ID_code components, missing a member operator that is a
    function template (util/message.h's
    `mstreamt::template<class T> operator<<(const T&)`), so `a @ b`
    fell through to a free operator (or reported the operator
    undefined).  Detect template members via a SCOPE_ONLY lookup, and
    prefer a free non-template operator over the member template only
    when the free operator's object parameter is an EXACT match (per
    [over.match.best]/2) -- not when it needs a derived-to-base
    conversion (so `mstreamt::operator<<`, exact object, wins over a
    free `operator<<(std::ostream&, …)`).  CORE test
    `cpp11_member_template_operator_overload`.  Clears the
    `_Require_derived_from_ios_base` cluster on ui_message.cpp /
    parser.cpp / typecheck.cpp (which now progress to distinct
    downstream errors).

## Remaining recurring errors (full src/util/ sample, 117 files)

Dog-food re-baselined 2026-07-01: **42 OK-clean / 64 OK-noisy / 11 FAIL / 0
CRASH** (was 19 FAIL at the start of the cpp11 front-end work).  Remaining FAIL
clusters:

| # files | First error | Files |
|---------|-------------|-------|
| 2 | `symbol 'read' is unknown` (parser.h:48) | `parser.cpp`, `lispexpr.cpp` |
| 2 | CONVERSION ERROR on a `virtual_table::messaget/message_handlert` member | `typecheck.cpp`, `ui_message.cpp` |
| 1 | `found no match for symbol 'optional'` | `simplify_utils.cpp` |
| 1 | `found no match for symbol 'resize'` | `irep_serialization.cpp` |
| 1 | `found no match for symbol 'insert'` | `pointer_predicates.cpp` |
| 1 | `found no match for symbol 'remove'` | `tempfile.cpp` |
| 1 | parse error before `virtual bool __do_upcast (` | `invariant.cpp` |
| 1 | `mallinfo` does not uniquely resolve | `memory_info.cpp` |
| 1 | `std::unique_ptr<console_message_handlert>` instantiation | `parse_options.cpp` |

*Updated: 2026-07-01*

### 2026-05-13 filesystem stack-overflow fix

Follow-up to the 2026-05-13 (duration) row: the additional duration
members elaborated by `2e8e74f8ed` triggered a previously-masked
mutual-recursion cycle in `resolve_template_alias` on MSVC's
`<filesystem>` preprocessed-header run.  Commit `09e5625681` adds a
thread-local active-set guard that breaks the cycle
deterministically, restoring the two filesystem tests to PASS and
bringing the MSVC preprocessed-header pass rate to **26/26**.
