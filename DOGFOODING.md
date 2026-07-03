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

17. `8e6dd4afc7` — **lambda parameter with a concrete class-name
    type** (N5008 [expr.prim.lambda.general]/4).
    typecheck_expr_lambda treated any lambda parameter whose type is
    a bare name (cpp_name) as a generic `auto` parameter and replaced
    it with `signed int`.  An ordinary class-name parameter such as
    `E &` was therefore replaced, so a lambda body accessing a member
    of a class-typed parameter failed ("member operator requires
    struct/union ... but got 'signed int'") and the enclosing body
    was dropped.  This silently stubbed util/expr.cpp's `exprt::visit`
    to a no-op (SKIP) -- a reachable soundness loss found via the
    noisy-file triage.  Fixed by resolving a cpp_name parameter: only
    an unresolved name or a dependent template parameter is generic; a
    concrete type is an ordinary parameter.  CORE test
    `cpp11_lambda_class_reference_parameter`.  NOTE: `exprt::visit`'s
    outer body is restored, but its traversal (visit_pre_template,
    which uses `std::stack<exprt*>`) is still dropped because CBMC
    *eagerly* instantiates an UNUSED allocator-extended `std::stack`
    constructor template (stl_stack.h:201) whose instantiation fails
    and aborts visit_pre_template -- a [temp.inst]/2 non-conformance
    (member/ctor TEMPLATE definitions instantiated without odr-use).
    Full `exprt::visit` soundness needs the lazy-instantiation work.

18. `f7e6f5fd89` — **guess_template_args recursion guard**.  A
    depth guard stops cpp_typecheck_resolvet::guess_template_args from
    exhausting the stack on a cyclic type graph (e.g. std::error_category
    reached during deduction).  Defensive; mirrors the alignment() cycle guard.
19. `56643fec6b` — **__is_constructible with an empty argument pack**
    (N5008 [meta.unary.prop], [temp.variadic]/5).  is_constructible<T> written
    as the empty-pack form `bool_constant<__is_constructible(T, Args...)>` (how
    libstdc++ writes is_default_constructible<T> and std::stack's default-ctor
    SFINAE) was mis-evaluated: the empty pack became the empty type (not nil),
    so the trait took the "construct from void" branch and returned false.  This
    broke std::stack and hence exprt::visit's std::stack<exprt*> traversal
    (visit_pre_template) -- a silent soundness loss found via the cvise-reduced
    std::stack repro.  Fixed to treat an empty-pack second argument as the
    default-constructibility query, evaluated accurately.  CORE test
    `cpp11_is_constructible_empty_pack`.  `exprt::visit`'s traversal is restored
    (std::stack<class*> now verifies non-vacuously; expr.cpp / rename_symbol.cpp
    / replace_symbol.cpp compile clean).  Side effect: `cpp11_regex_match`
    downgraded to KNOWNBUG -- the correct trait value exposes a separate latent
    guess_template_args deduction cascade on std::error_category (guarded from
    crashing, but deduction incomplete).

20. `3077ecc7c0` — **constructor templates in braced-init-list overload
    resolution** (N5008 [over.match.list]/2.2, [over.match.ctor], [temp.deduct]).
    `brace_init_is_viable` scanned only ordinary constructor components and
    missed constructor *templates* (a class stores those behind a
    `has_template_constructor` flag), so passing a braced-init-list whose
    parameter's matching constructor is a template -- e.g. constructing a
    std::pair (element-wise ctor is a template) from `{a, b}` in
    `map.insert({k, v})` -- was rejected as "found no match for symbol '...'".
    This was the ROOT of the dominant "no match for symbol 'insert'" dog-food
    cluster (found by cvise-reducing the noisy preprocessed source; the earlier
    "eager instantiation" and "member call" framings were both incorrect -- the
    free-function path fails identically).  Fixed by declaring a non-empty
    braced-init-list viable when the class has a constructor template, deferring
    deduction/substitution to implicit_typecast's SFINAE-guarded template-ctor
    path.  CORE test `cpp11_braced_init_constructor_template`.  Verified: the
    "no match for 'insert'" noise is cleared across the util dog-food (0 of 30
    sampled files, was ~47).  A separate braced-default-member-initializer bug
    uncovered en route is tracked as KNOWNBUG
    `cpp11_class_member_default_brace_init` (a `pair stored{-1, 7}` class member
    with no default ctor is default-constructed instead of using the braced
    initializer).

21. `c0aac6156e` — **class member initialized from its braced default
    member initializer** (N5008 [class.base.init]/9).
    `full_member_initialization` synthesised BOTH a default-construction
    member-initializer (for any non-POD member the ctor did not explicitly
    initialize) AND a separate initializer carrying the default member
    initializer's value.  For a class-typed member with a braced default member
    initializer but no default constructor -- `pair stored{-1, 7}` where `pair`
    has only `pair(int, int)` -- the default-construction one failed with "found
    no match for symbol 'pair'".  Fixed by excluding a member that has its own
    default member initializer from the default-construction branch.  CORE test
    `cpp11_class_member_default_brace_init`.  A separate pre-existing bug found
    en route -- a *scalar* member's braced default member initializer
    (`int x{42}`) leaks a raw initializer_list and aborts the bit-vector
    flattener -- is tracked as KNOWNBUG `cpp11_scalar_member_default_brace_init`.

22. `02cecd4437` — **member list-initialized from a non-empty braced default
    member initializer** (N5008 [dcl.init.list], [dcl.init.aggr]).  A braced
    default member initializer of a scalar member (`int x{42}`) left a raw
    initializer_list in the model, aborting the bit-vector flattener
    (unimplemented `boolbv_widtht::get_entry`); pointer/floating members got
    wrong values and POD sub-struct members aborted.  Two sites fixed: the POD
    default-member-initialization path now delegates to cpp_constructor
    (forwarding the braced-init-list's elements), and cpp_constructor's
    single-operand POD assignment now unwraps a single-element braced-init-list
    to its element for a scalar target ([dcl.init.list]/3.9).  Flips the
    KNOWNBUG `cpp11_scalar_member_default_brace_init` to CORE.

23. `c44adf9046` — **alias-template argument deduction terminates**
    (N5008 [temp.alias]/2, [temp.deduct.type]).  guess_template_args detected an
    alias-template pattern by an *unqualified* base-name lookup that ignored
    qualification.  After expanding a member alias template to its qualified
    underlying type (libstdc++ regex's `_BracketMatcher<I,C>` ->
    `__detail::_BracketMatcher<_TraitsT,I,C>`), it re-looked-up the expansion's
    base name unqualified, re-found the member alias, and re-expanded until the
    stack overflowed (a crash exposed once fix #19 enabled the deduction path
    reaching this alias).  Fixed by alias-expanding only unqualified
    template-ids; deduction now terminates and binds arguments correctly.  CORE
    test `cpp11_alias_template_deduction` (found by cvise-reducing the regex
    crash to 43 lines).  `cpp11_regex_match`'s guess_template_args cascade is
    resolved (its "regex match" assertion now verifies SUCCESSFUL); it stays
    KNOWNBUG only for a separate, now-reachable libstdc++ locale-facet
    dereference-modelling gap.

### 2026-07-02 dog-food re-baseline (after fixes #18-23)

`--expand` sweep of all 117 src/util/*.cpp: **83 clean / 23 noisy / 11 FAIL /
0 CRASH** (was 42 / 64 / 11 / 0 on 2026-07-01).  The session's fixes -- notably
#20 (braced-init constructor templates) clearing the dominant "no match for
symbol 'insert'" cluster -- nearly doubled the clean count and cut noise 64->23.
No regressions, no crashes.

Next-target triage: the remaining FAILs/noise are now diverse.  The highest-
impact FAIL cluster is `enable_if_t<false>` during `std::unique_ptr` member
elaboration (parse_options.cpp, irep_serialization.cpp, ui_message.cpp).  Root
cause diagnosed (backtrace + probe): CBMC concretizes unique_ptr's =delete'd
deleter constructor *template* during class-template instantiation -- the
member function template loses its template-ness (is_template=0) and its
enable_if_t<false> signature is eagerly evaluated -- violating N5008
[temp.inst]/2 (member function templates stay dependent until odr-used).  This
is a concrete instance of the deferred lazy member-function-template
instantiation work; a partial fix leaves a malformed model.  Captured as
KNOWNBUG `cpp11_unique_ptr_member_enable_if`; the proper fix (keep member
function templates dependent during class-template instantiation) is scoped as
a dedicated follow-up rather than rushed.

### 2026-07-02 smaller-target triage (both deeper than surface)

Investigated the two smaller dog-food noise clusters:

* **`<< eom` operator resolution** (message.h, ~15 including files): `m << eom`
  picks the member template `operator<<(const T&)` over the non-member friend
  `operator<<(mstreamt&, eomt)`.  NOT self-contained: minimal repros (member
  template vs friend, incl. enclosing-class friend + ADL + a base class) all
  resolve correctly; the failure needs the full std::ostringstream inheritance
  context (mstreamt : std::ostringstream).  A related crash surfaced en route:
  `std::ostringstream o; o << "hello"` aborts with a padding invariant (heavy
  ostringstream modelling; separate issue).  Left untracked pending a
  reproducible minimal case.

* **`codet` "does not uniquely resolve"** (std_code.h, 11 errors): a
  braced-init-list argument to an overloaded constructor
  (`codet(ID_assume, {std::move(expr)})`) is ambiguous.  Root diagnosed
  (probe): list-initializing a class from `{x}` gives the direct value
  constructor and the copy/move constructor an equal args_distance (4), so
  overload resolution ties, violating [over.ics.rank] (the value ctor should
  win; the copy ctor's ICS from the list is a user-defined conversion).
  Captured as KNOWNBUG `cpp11_braced_init_overload_rank` (minimal, header-free).
  The fix touches the delicate overload-ranking code and is deferred to a
  focused, well-validated effort.

Both "smaller" targets are genuine front-end issues but not quick wins.

*Updated: 2026-07-01*

### 2026-07-02 codet cluster fixed (fixes #24, #25) + re-baseline 85/21/11/0

Tackled the `codet` "does not uniquely resolve" cluster (11 errors in
std_code.h; std_code.cpp now compiles with **0** errors).  It had **two**
distinct root causes, both fixed:

* **#24 rank pollution** (`cpp_typecheck_conversions.cpp`,
  `implicit_conversion_sequence`): on the path where both the standard and the
  user-defined conversion attempts fail, `rank` was returned without being
  restored to its saved `backup_rank`, leaking `user_defined_conversion_sequence`'s
  `+4` penalty.  `cpp_typecheck_fargst::match` tries alternative conversions in
  sequence sharing one `rank`, so a failed init-list->scalar attempt inflated
  the next viable single-element conversion's rank — mis-ranking a value
  constructor's identity element conversion (rank 0) as user-defined (4) and
  tying it with the copy constructor, violating N5008 [over.ics.rank]/(3.1)
  (standard beats user-defined).  CORE `cpp11_braced_init_overload_rank`
  (was KNOWNBUG).

* **#25 inherited base ctors as brace-init candidates**
  (`cpp_typecheck_fargs.cpp`, `brace_init_is_viable` fallback loop): the loop
  iterated `from_base` constructor components.  Since `exprt` and
  `source_locationt` both derive from `irept`, `source_locationt` carried
  irept's inherited `irept(const irept&)` / `irept(const sharing_treet&)` copy
  constructors, and `exprt -> const irept&` is a derived-to-base binding — so
  `source_locationt` looked constructible from an `exprt`, tying
  `codet(dstringt, source_locationt)` with `codet(dstringt, operandst)`.  Per
  N5008 [over.match.ctor]/1 + [namespace.udecl]/3 base ctors are not candidates
  unless inherited via `using` (CBMC materialises those as non-`from_base`
  components).  Skip `from_base` ctors in the loop.  CORE
  `cpp11_braced_init_base_ctor` (reproduces pre-fix as ambiguous).

Both fixes: BOTH regression suites green (cbmc-cpp -X libcxx; cbmc -j4),
clang-format clean.  Dog-food `--expand` re-baseline: **85 clean / 21 noisy /
11 FAIL / 0 CRASH** (was 83/23/11/0).  The 11 FAILs are the deeper deferred
issues (enable_if/unique_ptr lazy instantiation, parser 'read', optional/lookup/
remove "found no match", CONVERSION ERROR).

*Updated: 2026-07-02*

### 2026-07-02 using-declared overload fix (fix #26) + re-baseline 88/19/10/0

Fixed the "found no match for symbol 'lookup'" FAIL (pointer_predicates.cpp,
plus lookup noise in many files).

* **#26 using-declared base overloads hidden in member lookup**
  (`cpp_typecheck_resolve.cpp`, `cpp_typecheck_resolvet::resolve`): the
  [class.member.lookup]/4 hiding block dropped a candidate whose declaring
  class is a base of another candidate's declaring class.  That is meant to
  prune base members that ADL (`resolve_with_arguments`) conservatively adds,
  but it also ran over ordinary-lookup candidates -- where a base-declared
  candidate is present only because a using-declaration imported it into the
  derived class (members merely inherited become flattened `from_base`
  components whose declaring class is the *derived* class, so they never trip
  the base-of test).  So `namespacet`'s `using namespace_baset::lookup;`
  one-argument `const symbolt &lookup(const irep_idt&)` was discarded and
  `ns.lookup("x")` failed.  Per N5008 [namespace.udecl]/16 a using-declared
  base member joins the derived class's overload set and is not hidden.  Fix:
  snapshot the ordinary-lookup candidate set before ADL augments it, and never
  hide a candidate that was in it.  CORE `cpp11_using_decl_overload`
  (reproduces pre-fix as "found no match for symbol 'look'").

BOTH regression suites green (cbmc-cpp -X libcxx; cbmc -j4), clang-format clean.
Dog-food `--expand` re-baseline: **88 clean / 19 noisy / 10 FAIL / 0 CRASH**
(was 85/21/11/0).  Remaining FAILs: 2 enable_if/unique_ptr (deferred lazy
instantiation), simplify_utils 'optional', tempfile std::filesystem 'remove',
parser std::istream 'read', + scattered CONVERSION ERROR.

*Updated: 2026-07-02*

### 2026-07-02 __restrict-qualified reference fix (fix #27)

Fixed the `invariant.cpp` parse error (and any translation unit that
transitively includes <typeinfo>).

* **#27 __restrict on a reference declarator** (`cpp/parse.cpp`,
  `Parser::optPtrOperator`): the parser consumed a cv-qualifier sequence after
  `*` (so `T * __restrict` parsed) but nothing after `&` / `&&`.  libstdc++'s
  <cxxabi.h> declares `__class_type_info::__do_upcast` with an
  `__upcast_result& __restrict __result` parameter -- a GCC/Clang extension
  ([dcl.ref]/1 forbids cv-qualified references, but both compilers accept a
  restrict-qualifier on a reference).  So invariant.cpp failed with
  "parse error before 'virtual bool __do_upcast ('".  Fix: accept and ignore a
  `__restrict` token after `&` / `&&`; `const` / `volatile` on a reference
  remain ill-formed and are still rejected.  CORE `cpp11_restrict_reference`
  (reproduces pre-fix as a parse error; covers lvalue- and rvalue-ref).

Verified directly: invariant.cpp went from parse error to a clean goto binary.
BOTH regression suites green, clang-format clean.  Note: typecheck.cpp and
ui_message.cpp remain FAIL with a *pre-existing* messaget/message_handlert
virtual-table "member not found" error (confirmed identical before and after
this fix -- it is the messaget/`<< eom` cluster, not a regression).  Dog-food
aggregate count fluctuates run-to-run for the largest files (typecheck.cpp,
ui_message.cpp) near the memory/time caps; invariant.cpp is a confirmed,
reproducible fix.

*Updated: 2026-07-02*

### 2026-07-02 derived-introduced virtual dispatch fix (fix #28) + 88/20/8/1

Fixed the messaget/`typecheckt` virtual-table "member not found" cluster
(ui_message.cpp, cout_message.cpp now compile).

* **#28 virtual dispatch through the wrong vtable pointer**
  (`cpp_typecheck_expr.cpp`, `typecheck_side_effect_function_call`): CBMC models
  each class introducing virtual functions with its own `virtual_table::<class>`
  struct + vtable pointer, so a derived class adding NEW virtuals carries
  several vtable pointers (inherited + own).  Virtual-call lowering selected the
  *first* vtable pointer and looked up the slot there; for a virtual newly
  introduced by the derived class that first pointer is a base's, whose vtable
  lacks the slot -> "member 'virtual_table::<base>::<fn>()' of 'struct' not
  found".  This broke CBMC's own message.h hierarchy (`typecheckt : messaget`
  adds `typecheck()`; `message_handlert::get_ui()`).  N5008 [class.virtual]/2.
  Fix: select the vtable pointer whose vtable struct actually contains the
  called function's virtual-name entry.  CORE `cpp11_derived_new_virtual`
  (override-through-base-ptr + new derived virtual + override-through-derived-ptr;
  reproduces pre-fix as "member ... not found").

BOTH regression suites green, clang-format clean.  Dog-food re-baseline:
**88 clean / 20 noisy / 8 FAIL / 1 CRASH** (was 88/19/10/0): ui_message.cpp and
cout_message.cpp cleared; typecheck.cpp moved from the vtable FAIL to a distinct,
newly-exposed invariant violation (generic "Precondition") -- a separate deeper
bug to investigate next, not a regression of this fix.

*Updated: 2026-07-02*

### 2026-07-02 pointer exception-handler fix (fix #29) + 88/21/8/0 (0 crashes)

Fixed the invariant-violation CRASH newly exposed in typecheck.cpp by fix #28.

* **#29 pointer catch-handler type-id computation** (`cpp_exception_id.cpp`,
  `cpp_exception_list_rec`): a C++ reference is represented internally as a
  pointer with ID_C_reference; the code extracted the pointee/referent type
  with `to_reference_type` in BOTH the reference and the plain-pointer branches.
  `to_reference_type` asserts ID_C_reference, so a genuine pointer handler such
  as `catch(int *)` tripped its precondition
  (`can_cast_type<reference_typet>`) and aborted goto-cc.  N5008 [except.handle].
  Fix: extract the base type with `to_pointer_type` (valid for references too);
  only the "_ptr" exception-id marker still differs.  CORE `cpp11_catch_pointer`
  (reproduces pre-fix as an invariant violation).

BOTH regression suites green, clang-format clean.  Dog-food re-baseline:
**88 clean / 21 noisy / 8 FAIL / 0 CRASH** (was 88/20/8/1): typecheck.cpp no
longer crashes -- it now compiles to a goto binary, leaving only the
pre-existing `<< eom` message.h noise.  The 8 remaining FAILs are the deferred
enable_if/lazy-instantiation work (irep_serialization, parse_options), the
SFINAE converting-ctor cases (simplify_utils 'optional', tempfile
std::filesystem 'remove'), std::istream member registration (parser/lispexpr
'read'), std::basic_regex (interval_union), and memory_info 'mallinfo'.

*Updated: 2026-07-02*

### 2026-07-02 function-hides-type fix (fix #30) + 89/21/7/0

Fixed the memory_info.cpp 'mallinfo' "does not uniquely resolve".

* **#30 a function hides a same-named type in value lookup**
  (`cpp_typecheck_resolve.cpp`, `cpp_typecheck_resolvet::resolve`): resolving a
  value (want == VAR) ran make_constructors over every candidate, turning a type
  candidate into constructors even when a same-named function was also found, so
  `S()` was ambiguous between the function and the type's constructor.  This is
  the C-library struct-tag/function pattern: glibc `struct mallinfo`/`mallinfo()`
  (`struct mallinfo m = mallinfo();`), POSIX `struct stat`/`stat()`.  N5008
  [basic.scope.hiding]/2: the function hides the type.  Fix: before building
  constructors, drop type candidates when a genuine same-named function is also
  present.  Care was taken to identify the *hiding* entity precisely -- an
  ID_code symbol whose return type is NOT ID_constructor -- so the type's own
  constructors (base_name == class name) and uninstantiated ctor templates
  (cpp_declaration) do NOT count; an initial too-broad "any non-type" predicate
  regressed `allocator`/`basic_string` construction (caught via dog-food:
  piped_process.cpp `can_receive(0)`), fixed before landing.  CORE
  `cpp11_function_hides_type` (reproduces pre-fix as "does not uniquely
  resolve").

BOTH regression suites green, clang-format clean.  Dog-food re-baseline:
**89 clean / 21 noisy / 7 FAIL / 0 CRASH** (was 88/21/8/0).  Remaining FAILs:
deferred enable_if/lazy-instantiation (irep_serialization, parse_options),
SFINAE converting-ctors (simplify_utils 'optional', tempfile/parser
std::filesystem 'remove'/_Path), std::istream member registration (lispexpr
'read'), std::basic_regex (interval_union).

*Updated: 2026-07-02*

### 2026-07-03 __is_constructible value-category fix (fix #31)

Fixed a genuine `is_constructible` correctness bug (the optional/reference_wrapper
cluster).  Count unchanged (89/21/7/0) because the fix advances simplify_utils
past the optional issue to the separate, pre-existing unordered_map/_Hashtable
cluster.

* **#31 __is_constructible drops the argument value category**
  (`cpp_typecheck_expr.cpp`): N5008 [meta.unary.prop] defines the trait via
  `declval<Args>()`, whose value category is an lvalue iff Arg is an
  lvalue-reference.  The intrinsic built its source expression from the
  de-referenced argument type without recording the value category, so an
  lvalue-reference argument was treated as an rvalue.  For
  std::reference_wrapper<const T> -- converting ctor guarded by an overload set
  that deletes the rvalue form -- the forwarding reference then deduced the
  rvalue form and picked the deleted overload, so
  is_constructible<reference_wrapper<const int>, int&> was wrongly false,
  breaking std::optional<std::reference_wrapper<const array_exprt>>
  (simplify_utils.cpp).  Fix: mark the source expression as an lvalue when the
  argument type is an lvalue reference (rvalue-ref / non-ref stay rvalues, so
  reference_wrapper remains correctly non-constructible from T&&/T).  CORE
  `cpp11_is_constructible_value_category` (reproduces pre-fix as assertion.1
  FAILURE).

BOTH regression suites green, clang-format clean.  Verified directly that the
intrinsic now matches g++ for int& (true) / int&& (false) / int (false), and
that simplify_utils's optional error is gone (it now stops at the unordered_map
cluster instead).  Note: a *separate* latent bug was observed while testing --
two `__is_constructible` queries on the same SFINAE-deleted-overload type inside
one function body drop that function's goto body; the single-query CORE test
avoids it.  Left for a future investigation.

*Updated: 2026-07-03*

### 2026-07-03 lvalue-ref-does-not-bind-rvalue fix (fix #32)

Fixed the latent bug that fix #31 exposed (the two-query main-drop).

* **#32 non-const lvalue reference must not bind an rvalue argument**
  (`cpp_typecheck_conversions.cpp`, `user_defined_conversion_sequence`): the
  converting-constructor scan skipped an rvalue-reference parameter for an
  lvalue argument but had no symmetric check, so it stripped the reference from
  a non-const lvalue-reference parameter (`X&`) and ran a standard conversion on
  the referent, treating a `T(X&)` constructor as viable for an rvalue argument
  and then aborting when the binding failed.  This became reachable once #31
  preserved value category: is_constructible<T, X&> instantiates the concrete
  `T(X&)` converting constructor as a class member, and a following
  is_constructible<T, X&&> query reached it with an rvalue, aborting
  type-checking ("invalid implicit conversion from X to X&") and dropping the
  enclosing function body.  N5008 [dcl.init.ref]/5.  Fix: a non-const
  lvalue-reference constructor parameter is not viable for an rvalue argument.
  CORE `cpp11_is_constructible_lvalue_rvalue` (two queries lvalue-then-rvalue;
  reproduces pre-fix by silently dropping main).

BOTH regression suites green, clang-format clean.  Dog-food count unchanged
(89/21/7/0): this hardens the front-end (no dog-food file was gated on it), and
confirms fix #31 no longer risks dropping function bodies in code that queries
is_constructible on one type with both value categories.

*Updated: 2026-07-03*

### 2026-05-13 filesystem stack-overflow fix

Follow-up to the 2026-05-13 (duration) row: the additional duration
members elaborated by `2e8e74f8ed` triggered a previously-masked
mutual-recursion cycle in `resolve_template_alias` on MSVC's
`<filesystem>` preprocessed-header run.  Commit `09e5625681` adds a
thread-local active-set guard that breaks the cycle
deterministically, restoring the two filesystem tests to PASS and
bringing the MSVC preprocessed-header pass rate to **26/26**.
