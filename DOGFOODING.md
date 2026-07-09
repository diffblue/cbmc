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

### 2026-07-03 istream 'read' root-caused; KNOWNBUG captured (no fix landed)

Root-caused the `symbol 'read' is unknown` failures (lispexpr.cpp, parser.cpp).
Using **cvise on a preprocessed <istream> TU** (predicate: goto-cc reports
"read is unknown" AND g++ accepts), reduced to a **7-line header-free** repro:
a class template referenced (`other(S<char>)`) while only forward-declared, then
defined with a member, then `g_in.read()` -> "unknown".  This mirrors <iosfwd>
forward-declaring std::basic_istream before <istream> defines it.

Root cause: CBMC eagerly elaborates `S<char>` at the early reference from the
not-yet-defined primary template ([temp.inst]/1, [temp.point] are violated),
producing an empty-but-complete class and dropping the instance's template link,
so the later definition's members are permanently masked.

Two fix attempts were made and **reverted** (both regressed other tests):
* Deferring when the *primary* template has no class body regressed
  std::function etc. (primary `function<T>` is bodyless; only the partial
  specialization is defined).
* Deferring when the *best-matched* template has no body fixed lispexpr and
  the previously-regressed pack/function tests, but then left library types
  incomplete and crashed cpp20 <iostream> with the std::ostringstream bit-field
  padding invariant (`member_offset_expr`).

A correct fix needs reliable "definition seen" tracking (so a forward-declared-
then-defined template is distinguished from a bodyless primary whose partial
specialization carries the definition, and so incomplete instances are never
used for layout).  Captured as KNOWNBUG `cpp11_fwd_decl_template_member`.
Dog-food count unchanged (89/21/7/0).

*Updated: 2026-07-03*

### 2026-07-03 definition-seen tracking (fix #33): istream 'read' resolved

Landed the fix the previous entry deferred.  A class template specialization is
implicitly instantiated -- and completed -- only from a *definition* of the
template (N5008 [temp.inst]/1, [temp.point]).  The eager elaboration of a
specialization referenced while the template was only forward-declared is the
root of the lispexpr.cpp / parser.cpp `symbol 'read' is unknown` failures
(<iosfwd> forward-declares std::basic_istream before <istream> defines it).

Fix, three parts:
* `cpp_typecheckt::defined_class_templates` (a side set, not an irep marker)
  records each class template -- primary or partial specialization -- for which
  a class body has been seen; populated in typecheck_class_template.
* elaborate_class_template defers instantiation of a specialization whose
  selected template (`best_match`, post specialization matching) is not yet in
  that set, leaving it incomplete until the definition is available.  Keyed on
  best_match, not the primary, so std::function (bodyless primary, defined
  partial specialization) is not wrongly deferred.  Kept off the declaration
  irep so recording a definition never perturbs template argument matching /
  specialization ordering (an earlier irep-marker attempt flipped the
  ambiguous partial-spec selection in cpp20_concepts_ordering).
* member_offset_expr now degrades gracefully (returns "offset not known")
  instead of aborting when a class with virtual bases exposes its unpadded
  1-bit `@most_derived` flag ([class.mi]); giving basic_istream its real members
  had exposed this latent layout invariant.  Mirrors the sibling member_offset().

Verified: nv/min forward-decl repro resolves the member (assertion.2 gives
non-vacuity); genuinely-empty defined templates and std::function unaffected;
cpp20_iostream_basic, cpp20_concepts_ordering, cpp11_function_basic all pass.
Both regression suites green; KNOWNBUG `cpp11_fwd_decl_template_member` promoted
to CORE.

Dog-food improved **89/21/7/0 -> 96/16/5/0**: lispexpr.cpp and parser.cpp
cleared from FAIL.  Remaining 5 FAILs are the deferred clusters (std::basic_regex
in interval_union; enable_if lazy instantiation in irep_serialization /
parse_options; optional->unordered_map in simplify_utils; std::filesystem in
tempfile).

*Updated: 2026-07-03*

### 2026-07-03 SFINAE: sole function-template false constraint not enforced (KNOWNBUG)

While scoping the remaining enable_if dog-food FAILs (all context-dependent
cascades not reproducible in isolation), isolated a distinct, header-free
soundness bug (the one `.kiro/std_function_converting_ctor_plan.md` flagged as a
separate pre-existing defect): a **sole** function-template candidate whose
non-deduced, defaulted template parameter carries a false `enable_if` constraint
(e.g. `template<class T, enable_if_t<always_false<T>::value,int> = 0> int f(T)`)
is **wrongly accepted** by CBMC (`f(5)` compiles) though g++/clang++ reject it --
[temp.deduct]/8: the substitution failure removes the only candidate, leaving no
viable function.  With a *competing* overload the constraint IS enforced (multi-
candidate disambiguation instantiates and rejects it), so only the sole-candidate
path is affected.

Root cause (traced): `guess_function_template_args` correctly evaluates the
defaulted parameter's `enable_if` and rejects the candidate (its SFINAE default-
argument block returns `nil_exprt()` on the substitution failure), so the
overload set ends empty.  But the downstream function-call resolution
(`typecheck_expr_cpp_name` -> `resolve`, which for an all-template empty result
does an intentional silent `throw 0` to emulate SFINAE for library support, and
elsewhere resurrects the name) does not turn the empty set into a "no viable
function" rejection for a real (non-SFINAE) call.  A safe fix must reject the
sole-candidate real call WITHOUT reintroducing the false-reject / false-accept
oscillation and std::any/std::apply regressions documented across six prior
sessions in this exact fallback chain.

Captured as KNOWNBUG `cpp11_sole_template_false_constraint` (header-free) with a
non-vacuous well-formed companion `cpp11_sole_template_true_constraint` (CORE)
guarding against over-rejecting a true constraint.  Fix (flip to CORE) deferred:
the change lives in the delicate overload-resolution fallback and must be gated
against the whole STL-heavy suite + dog-food.  No dog-food count change (this is
silent over-acceptance, not a FAIL).

*Updated: 2026-07-03*

### 2026-07-03 SFINAE enforcement fix: unrecovered no-viable-function is diagnosed

Landed the fix the previous entry deferred.  N5008 [temp.deduct]/8: when
deduction removes every candidate of a call and there is no non-template
overload, the call has no viable function and the program is ill-formed.
resolve() kept its silent `throw 0` for this case (so recoverable callers --
operator resolution, ADL, ranges pipes -- still absorb it via catch(int)), but a
new SFINAE-nesting depth (sfinae_context_depth, maintained by sfinae_contextt)
lets it record, at depth 0 only, a pending "no viable function" marker (cleared
at every resolve() entry, so it survives only an *unrecovered* propagation).
typecheck_method_bodies' catch then diagnoses that marker instead of rolling it
back as unsupported-STL leniency.

`cpp11_sole_template_false_constraint` is now correctly rejected (promoted to
CORE); `cpp11_sole_template_true_constraint` still verifies (no over-rejection).
Both regression suites pass; **dog-food unchanged 96/16/5/0**; the C suite is
unaffected.

The fix also surfaced two pre-existing latent resolution bugs that had been
silently swallowed (the calls were dropped, bodies truncated, so the tests only
passed vacuously):
* Two-parameter requires-constrained `add(T,U)` is dropped -- KNOWNBUG
  `cpp20_concepts_requires_expr` (was a fully vacuous CORE pass; proven by a
  deliberately-false assertion still reporting SUCCESS).
* Empty explicit pack `make_box<>()` ([temp.arg.explicit]/4) is dropped --
  split out as KNOWNBUG `cpp11_variadic_empty_explicit_pack`; the non-empty
  cases of `cpp11_variadic_member_alias_pack` stay CORE.

*Updated: 2026-07-03*

### 2026-07-03 unsupported-construct leniency made visible (was silently masking)

Investigated the "unsupported-STL leniency" -- the `had_template_instantiation`
rollback in typecheck_method_bodies that suppresses errors and keeps going when
a *user-code* body cannot be fully type-checked because it instantiates a
template CBMC cannot model.  Findings:
* It is **not** standards-conformant (a conforming compiler accepts or rejects);
  it is a pragmatic tolerance so CBMC can verify the modellable parts of
  STL-heavy code.
* It is **not** needed for dog-food: removing it leaves the dog-food count
  unchanged (96/16/5/0).  Dog-food's own STL gaps go through the *separate*
  system-header / template-instance suppression branch, not this one.
* It was **silently masking real front-end gaps**: removing it turns 12 cbmc-cpp
  CORE tests that pass only VACUOUSLY into CONVERSION ERRORs (and one into a
  goto-symex precondition crash from aborting the body loop early).

The masked front-end gaps (roadmap -- each is a candidate to fix, after which the
leniency can be narrowed): `std::initializer_list` (cpp11_initializer_list_class),
generic-lambda types (cpp14_generic_lambda_types), `std::variant`
(cpp17_variant_basic), class NTTP brace-init (cpp20_class_nttp_brace), iterator
concept chains (cpp20_concept_iterator_chain), named/overloaded concepts
(cpp20_concepts_named/overload), concept type-requirements
(cpp20_concepts_requires_type), NTTP strings (cpp20_nttp_string), ranges pipes
(cpp20_ranges_basic), unparenthesized requires (cpp20_requires_unparenthesized),
`std::expected` (cpp23_expected_basic), pack-indexing (cpp26_pack_indexing_expr).

Decision: rather than fully remove the leniency (which would reject entire TUs
merely using an unmodelled feature -- honest but far less usable, with zero
dog-food benefit), make it **visible**: emit a warning when it fires, so the
incomplete/unsound verification is auditable instead of hidden.  Behaviour is
otherwise unchanged; both suites stay green and dog-food is unchanged.

*Updated: 2026-07-03*

### 2026-07-05 CORRECTION: leniency is load-bearing; kept; gap-by-gap instead

Earlier dog-food figures this session were unreliable (measured against stale
binaries after rebuilds).  Ground truth, re-measured rebuild-then-measure in one
step:

* Baseline (leniency present): 96 clean / 16 noisy / 5 FAIL.
* The **SFINAE-enforcement fix** ("unrecovered no-viable-function is diagnosed"
  above) itself regressed dog-food to **83 / 16 / 18**: its pending_no_viable
  path surfaces latent *no-viable* front-end gaps (`make_range`, `optional`,
  `report_invariant_failure`, ...) that the leniency had swallowed.  This was
  reported as "0 dog-food impact" -- wrong.
* **Removing** the leniency craters dog-food to **66 / 49**: it genuinely masks
  ~40 STL front-end gaps CBMC hits compiling its own source.  So it is NOT
  zero-value; it is load-bearing.  The removal commit was reverted.

Decisions (with correct data): keep the SFINAE-enforcement fix (accept 83/18 --
the surfaced no-viable errors are honest); do NOT remove the leniency until the
underlying gaps are closed (removing it now would make CBMC unable to compile
~40% of its own source); proceed **gap by gap**, re-classifying to CORE as each
is closed.

First gap closed this way: `std::initializer_list<E>` object initialization
([dcl.init.list]/5) -- cpp11_initializer_list_class now verifies non-vacuously;
dog-food-neutral (83/16/18/0).

Always rebuild-then-measure in one step going forward (the staleness that caused
the bad figures).

*Updated: 2026-07-05*

### 2026-07-05 gap closed: decltype nested in a trailing return type (make_range)

N5008 [dcl.fct]/[expr.type]: a function template whose trailing return type
nests a decltype in a template-id -- util/range.h's
`template <typename C> auto make_range(C &c) -> ranget<decltype(c.begin())>` --
was removed from the candidate set ("found no match for make_range").
guess_function_template_args scopes the parameters so a trailing-return decltype
resolves, but only when the return type *was* a decltype, not when a decltype was
nested inside it.  Fixed by scanning the trailing return type for any nested
decltype (cpp_typecheck_resolve.cpp).  Header-free non-vacuous CORE test
cpp11_trailing_return_decltype_template_arg.

Dog-food **83/16/18 -> 84/19/14**: make_range no longer blocks options.cpp
(now clean), simplify_expr_if.cpp, std_expr.cpp, xml.cpp (out of FAIL; residual
non-make_range issues make them noisy).  structured_data.cpp still FAILs on a
separate make_range gap (the `.map(...).collect<...>()` chain over
`data.children()`), left for a follow-up.  Both suites green.

*Updated: 2026-07-05*

### 2026-07-05 gap closed: function template with a fixed class param + user conversion

N5008 [over.match.funcs]/[over.ics.user]: a function template with a non-deduced
(fixed) parameter of class type S is viable for an argument convertible to S via
a user-defined conversion (const char* -> S).  This is util/invariant.h's
`report_invariant_failure(const std::string&, ..., D&&...)` called with
`__FILE__` / string literals.  guess_function_template_args ended with a
post-deduction compatibility check that rejected the candidate whenever a struct
parameter got a non-struct argument -- ignoring user conversions.  Fixed to
reject only when no implicit conversion sequence exists (leaving ranking to
disambiguate_functions).  Header-free non-vacuous CORE test
cpp11_template_converting_fixed_param.

Dog-food **84/19/14 -> 89/19/9**: closes the report_invariant_failure cluster
(lower_byte_operators, replace_expr, simplify_expr, symbol_table) plus one more.
Side effect: cpp23_expected_basic (a *vacuous* pass -- std::expected is not
modelled) now instantiates more of std::expected and surfaces a real void->int
gap, so it fails honestly; reclassified KNOWNBUG (flip to CORE once std::expected
is modelled).  Both suites green.

*Updated: 2026-07-05*

### 2026-07-05 gap closed: CTAD for functional-notation C(args)

N5008 [over.match.class.deduct]: `C(args)` naming a class template without a
template-argument-list is class template argument deduction (e.g.
`std::optional(x)`), not a function call.  The parser emits a function call (C is
only a template-name), which failed with "found no match for C".  Fixed by
routing a class-template callee to the explicit-constructor-call / CTAD path in
typecheck_side_effect_function_call (via deduce_class_template_arguments, which
returns nullopt for non-class-templates so ordinary calls are unaffected), and
by resolving *qualified* class-template-ids (std::optional) to their scope in
deduce_class_template_arguments.  Header-free non-vacuous CORE test
cpp17_ctad_functional_notation.

Dog-food **89/19/9 -> 90/19/8**: fixes CTAD in simplify_expr_int.cpp.
simplify_utils.cpp still FAILs on a *separate* std::optional gap
(is_trivially_destructible_v<basic_string> in _Optional_base), left for a
follow-up.  Both suites green.

*Updated: 2026-07-05*

### 2026-07-05 gap closed: NSDMI referencing a non-type template parameter

N5008 [class.mem]/[temp.inst]: a default member initializer (NSDMI) may refer to
the enclosing class template's parameters, e.g. `template<bool B> struct Z { int
t = B ? 1 : 2; };`.  The NSDMI is stored unparsed as the component's
`C_default_value` (cpp_typecheck_compound_type.cpp) and type-checked only later,
when the implicit default constructor is generated -- by which time the
instance's template_map bindings are gone.  So a non-type parameter in the
initializer was left unresolved: at namespace scope the member took the wrong
value, and a *function-body* instantiation (`Z<true> z;` inside a function)
failed to type-check and was then silently swallowed by the unsupported-
construct leniency (vacuous pass).  Fixed by eagerly type-checking the NSDMI
while instantiating (template_map populated), under a message-suppressing
`sfinae_contextt` guard, falling back to the unparsed form on any failure.  The
suppression matters: a plain (un-guarded) early type-check emitted spurious
diagnostics that turned 73 dog-food files clean->noisy; the sfinae guard keeps
them clean.  Header-free non-vacuous CORE test
`cpp11_nsdmi_nontype_template_param` (covers an explicit non-type argument and
one defaulted from a variable template).

Dog-food unchanged at **90/19/8** (no FAIL closed, no regression): this is a
distinct front-end gap discovered while investigating simplify_utils.cpp, whose
own FAIL is a *different* bug -- `is_trivially_destructible_v<basic_string>` as a
**default template argument** of `_Optional_base` (optional:327), i.e.
default-non-type-*argument* evaluation, not an NSDMI.  That remains open.  Both
suites green.

*Updated: 2026-07-05*

### 2026-07-06 gap closed: NSDMI on a value-less namespace-scope / static object

N5008 [class.default.ctor]/3 + [basic.start.static]: a default member
initializer (NSDMI) gives a class a non-trivial default constructor, so a
namespace-scope or file-static object defined without an initializer must run
that constructor and receive its declared member defaults -- e.g.
`struct Q { int t = 5; }; Q g;` must leave `g.t == 5`, not 0.  CBMC's
`static_and_dynamic_initialization` treated such an object as a plain POD and
merely zero-initialized it (`g.t == 0`), because `cpp_is_pod` ignores NSDMIs.
The same class used as a *local* was already correct (the default-constructor
path applies the NSDMI); only the static-init path skipped it.  Fixed by routing
a value-less definition whose class has a direct NSDMI to that default-
constructor path; members without an NSDMI keep their static zero-initialization
([basic.start.static]/2), and objects with an explicit initializer are
unaffected.  `cpp_is_pod` itself is left unchanged -- it also governs aggregate
initialization, which legitimately permits NSDMIs since C++14.  Header-free
non-vacuous CORE test `cpp11_global_nsdmi`.

Dog-food unchanged at **90/19/8** (no FAIL closed, no regression).  Remaining
adjacent gaps, still open: a nested (member-subobject) NSDMI is not applied even
for a *local* (`struct O { Q q; }; O o;` leaves `o.q.t != 5`), and an
array-of-NSDMI global (`Q a[3];`) is likewise not defaulted.  Both suites green.

*Updated: 2026-07-06*

### 2026-07-06 gap closed: nested / array-element member NSDMIs (subobject default construction)

Follow-up closing the "remaining adjacent gaps" noted in the previous entry.
N5008 [class.base.init]/9-10 + [class.default.ctor]/3: a class-type member not
named by a mem-initializer is default-constructed by the enclosing class's
implicit default constructor, applying the member class's NSDMI.  This failed
even for a *local*: `struct inner { int t = 5; }; struct outer { inner q; };
outer o;` left `o.q.t == 0`.  Root cause: CBMC default-constructs a value-less
object through `cpp_constructor`'s POD branch, which applied only the object's
*direct* default member initializers and never recursed into class-type members;
and because `cpp_is_pod` (correctly, for aggregate purposes) ignores NSDMIs, no
real constructor was generated for `outer` either, so the constructor's own
member-init logic never ran.

Fixed surgically without touching `cpp_is_pod` (so C++14 braced aggregate
initialization with NSDMIs is preserved): a new predicate
`has_default_member_initializer` reports whether a class -- or a subobject, or an
array element -- carries an NSDMI, i.e. whether its default construction is
non-trivial.  `cpp_constructor` now (a) lets an array of such elements fall
through to its element-wise constructor loop rather than short-circuiting, and
(b) recurses into such members during default construction; the static-init path
uses the same predicate so value-less globals are covered too.  This closes the
nested-local, nested-global, two-level, array-of-NSDMI (local and member), cases
in one go.  Header-free non-vacuous CORE test `cpp11_nested_member_nsdmi`
(includes assertions confirming aggregate initialization is unaffected).

Dog-food unchanged at **90/19/8** (no FAIL closed, no regression).  Both suites
green.

*Updated: 2026-07-06*

### 2026-07-06 faithful reproducer captured: out-of-line member breaks a user-defined conversion (tempfile.cpp)

Applied the "reduce with the real headers kept" strategy (cvise on the raw
`.cpp` with the goto-cc `-I` flags, so libstdc++ stays external and is never
mangled into an artifact -- unlike a preprocessed reduction).  This turned the
`tempfile.cpp` dog-food FAIL into a **faithful, minimal, reliable** reproducer:

```cpp
#include <string>
struct T { std::string name; ~T(); };
#include <filesystem>
T::~T(){ std::filesystem::remove(name); }   // "found no match for symbol 'remove'"
```

Precise characterisation (all verified): CBMC wrongly rejects
`std::filesystem::remove(name)` (name : `std::string`) with "found no match" ->
CONVERSION ERROR **iff** the call sits inside an OUT-OF-LINE, qualified function
definition -- a class member (`T::~T`, `T::f`, static or not), a namespace
member (`N::f`), or a nested one (`N::M::f`).  The identical call in a free
function at namespace scope resolves fine; an explicit `path(name)` works; a
plain (non-templated) converting constructor works.  So the trigger is: overload
resolution forms the user-defined `std::string`->`std::filesystem::path`
conversion through path's *templated, SFINAE-guarded* converting constructor,
and that resolution fails when the current scope is a nested
(out-of-line-definition) scope.  Per N5008 [over.ics.user]/[temp.deduct] a
conversion's viability depends only on source/destination types, not the
call-site scope.

Ruled out: resetting the scope around the template-converting-constructor
fallback in `user_defined_conversion_sequence` (that path is not the one taken).

**Fixed** (follow-up, same day): further tracing showed the failure is not a
scope-lookup issue at all.  During type-checking of the deferred out-of-line
body, `new_temporary`/`cpp_constructor` builds the `std::string`->`path`
conversion but finds **no constructor component** on `path` -- its constructor
components are materialised only after `path` is first constructed in an
*eager* (non-deferred) context, which never happens here -- and so throws "non-
POD type has no constructor", which the SFINAE-guarded conversion turns into
"no viable conversion".  A free function at namespace scope is type-checked
eagerly, so `path`'s constructor is already materialised there.  Fix in
`cpp_constructor` ([class.ctor.general]/1): when the ctor-component loop finds
nothing for a non-POD class being constructed with arguments, resolve the
constructor by the class's own name in the (already-entered) class scope, where
overload resolution finds it -- including constructor *templates*, which are
never stored as plain components.  A genuinely constructor-less class still
fails with the ordinary "no match".

`cpp17_out_of_line_udc_conversion` is now a **CORE** test.  It keeps the
out-of-line body (so the front-end fix is exercised) but does not call it, so
BMC stays trivial (the property is a front-end one).  Dog-food **90/19/8 ->
91/19/7**: `tempfile.cpp` now compiles.  Both suites green; clang-format clean.

*Updated: 2026-07-06*

### 2026-07-06 gap closed: heterogeneous forwarding-reference parameter pack (+ const-enum KNOWNBUG)

Reduce-with-real-headers cvise on `validate_expressions.cpp` (120 -> 7 lines,
then narrowed header-free) pinned its `call_on_expr<...>(ns, vm)` "found no
match" to a variadic FORWARDING-REFERENCE parameter pack `A&&...` called with
HETEROGENEOUS arguments.  The template-template parameter and the incomplete
`namespacet` were red herrings; the minimal reproducer is just
`template<typename... A> void call_on(A&&...); call_on(i, d);` with `i`, `d` of
different types.

Root cause: `guess_function_template_args` deduced the pack correctly (e.g.
`A = {int&, double&}`) but, when expanding the single instantiated pack
parameter into `pack_size` function parameters, it inserted `pack_size` copies
of the FIRST element's parameter.  That is only valid for a homogeneous pack;
for a forwarding-reference pack it makes every parameter the first element's
reference type, so a later argument of a different type cannot bind (no implicit
conversion) and the call is rejected as "no match".  Fixed per N5008
[temp.deduct.call]/[temp.variadic] by assigning each expanded parameter its
corresponding deduced pack-element type.  Header-free non-vacuous CORE test
`cpp11_variadic_fwd_ref_heterogeneous`.

`validate_expressions.cpp` still FAILs: it also hits a *second, independent*
defect -- a forwarding reference `T&&` deducing from a **const enum** lvalue
(its `call_on_expr` forwards a `const validation_modet`, an `enum class`).
Minimal: `enum class E{}; template<typename T> void f(T&&); const E e; f(e);` ->
"found no match" (const scalar and non-const enum both work; the deduced
`const E&` parameter is dropped in overload resolution).  Captured as KNOWNBUG
`cpp11_fwd_ref_const_enum` for a follow-up.

Dog-food unchanged at **91/19/7** (fix #1 is a real correctness fix but does not
by itself close validate_expressions, which needs the const-enum fix too; no
regression).  Both suites green; clang-format clean.

*Updated: 2026-07-06*

### 2026-07-06 gap closed: const-qualified enum forwarding-reference (2 dog-food FAILs)

Follow-up fixing the const-enum defect captured as KNOWNBUG in the previous
entry.  N5008 [temp.deduct.call]/3: a forwarding reference `T&&` deduces `T` as
"lvalue reference to A" from an lvalue argument, for any A -- so a const enum
lvalue gives a `const E&` parameter.  CBMC rejected this ("found no match" ->
CONVERSION ERROR) for a const enum only.

Traced through the full pipeline with probes: deduction produced the correct
`const E&`, and `template_map.apply` kept it (`base.const=1`), but
`typecheck_type(function_type)` dropped it (`base.const=0`).  `typecheck_type`
begins with `cpp_convert_plain_type(type)`, whose "leave-as-is" list included
`c_enum`, `struct_tag`, and `union_tag` but **omitted `c_enum_tag`**.  A
cv-qualified `c_enum_tag` therefore fell through to the general conversion path,
which rebuilds the type and drops its cv-qualifiers (struct/union tags were
spared), so the deduced parameter became a non-const `E&` that a const enum
lvalue could not bind.

Fix (N5008 [dcl.enum]/[basic.type.qualifier]): treat `c_enum_tag` as the tag
reference it is -- add it to the leave-as-is list alongside `struct_tag`/
`union_tag`.  One line, no rebuild of the type.  Flipped
`cpp11_fwd_ref_const_enum` KNOWNBUG -> **CORE**.

Dog-food **91/19/7 -> 93/19/5**: both `validate_expressions.cpp` (its
`call_on_expr<...>(ns, vm)` forwards a `const validation_modet`) and
`validate_types.cpp` (a `std::optional` construction that likewise forwards a
const enum) now compile.  Both suites green; clang-format clean.

*Updated: 2026-07-06*

### 2026-07-07 gap closed: stale synthetic parameter poisoned decltype-return overload resolution (structured_data.cpp)

`structured_data.cpp`'s `make_range(components).concat(make_range(begin, end))`
was rejected with "found no match for symbol 'make_range'".  Reduce-with-real-
headers cvise narrowed it to a header-free chain
`make_range(container).concat(make_range(iter, iter))` where `make_range` has a
1-parameter *container* overload with a trailing return type using decltype
(`auto -> ranget<decltype(c.begin())>`) and a 2-parameter *iterator* overload.

Root cause: `guess_function_template_args` resolves such a trailing-return
decltype by inserting a synthetic symbol for the parameter (`c`) into the scope
so `decltype(c.begin())` resolves -- keyed by template-scope + parameter name,
and never removed.  Resolving the 2-argument iterator call speculatively tried
the 1-parameter container overload, deduced `c` from the first argument (an
`int*` iterator), and left a stale `c = int*` symbol behind.  The subsequent,
correct resolution of `make_range(container)` then found `c` already present,
skipped its own insertion, and evaluated `decltype(c.begin())` against the stale
`int*` (which has no `.begin()`) -- failing and removing the only viable
overload.

Fix (N5008 [over.match.viable]/2): a call with more arguments than a
non-variadic overload has parameters can never select it, so do not insert the
synthetic parameter symbols for it -- speculatively type-checking a non-viable
overload's return type must not pollute the shared scope.  Scoped to
free-function calls (`!fargs.has_object`) to avoid an object/`this` off-by-one
for member function templates (an earlier, broader mutate-the-stale-symbol
attempt caused unbounded recursion crashing simplify_expr.cpp / string_utils.cpp;
this narrower fix does not mutate or remove any symbol).  Header-free non-vacuous
CORE test `cpp11_decltype_return_overload_chain`.

Dog-food **93/19/5 -> 93/20/4**: `structured_data.cpp` compiles (now in the
noisy bucket).  Both suites green; clang-format clean.

*Updated: 2026-07-07*

### 2026-07-07 gap closed: reference data member in a braced-init-list function argument (irep_serialization.cpp)

`src/util/irep_serialization.cpp` was rejected with a spurious
`instantiating 'std::__enable_if_t' with <FALSE, bool>` cascade.  A probe on
`show_instantiation_stack` printing `sfinae_context_depth` showed every
`enable_if<FALSE>` frame ran at depth >= 1 (correctly SFINAE-suppressed by the
null handler): the enable_if was a **red herring**.  The only depth-0 (fatal)
error was downstream, at
`reference_convert`'s
`ireps_container.ireps_on_write.insert({h, ireps_container.ireps_on_write.size()})`:
"operand of unary * '*this->ireps_container' is not a pointer, but got 'struct
...ireps_containert'", where `ireps_container` is a **reference data member**.

Reduce-with-real-headers plus by-hand minimisation gave a header-free reproducer:

```cpp
struct vt{ unsigned long a; };
void g(const vt&){}
struct Outer{ unsigned long &ref; void f(){ g({ref}); } };
```

(`vt v{ref};` local init works; only the braced-init-list *argument* `g({ref})`
fails; a value -- non-reference -- member does not reproduce; no STL, templates
or SFINAE are needed.)

Root cause (N5008 [dcl.ref]/1, [expr.unary.op]/1: a reference denotes the object
it binds to; unary `*` on a reference operand yields that object).  A reference
lvalue -- notably a reference data member `this->ref` -- is materialised by
`add_implicit_dereference` as an implicit `dereference_exprt` whose operand keeps
the reference type.  That node is fully type-checked when built (by
`typecheck_expr_member` during name resolution), but the identical argument
sub-tree reaches `typecheck_expr` a second time: a braced-init-list call
argument is type-checked once by the operand walk and again while the call's
arguments are converted to the parameter's class type (constructing a
temporary).  The generic operand walk (`typecheck_expr_operands`, run *before*
`typecheck_expr_main`) then re-type-checked the operand `this->ref`, whose member
access re-applied its own implicit dereference; the outer `*` wrapped the
already-dereferenced value, corrupting `*this->ref` into the ill-formed
`*(*this->ref)`.

Fix: in `cpp_typecheckt::typecheck_expr`, before the operand walk, recognise an
already-elaborated implicit dereference of a reference operand (id ==
`dereference`, `C_implicit`, result type set, operand of reference type) and
leave it untouched -- it is already well-formed and must not be re-elaborated.
Header-free non-vacuous CORE test `cpp11_reference_member_braced_arg`.

Dog-food **93/20/4 -> 94/20/3, 0 crash**: `irep_serialization.cpp` compiles.
The three remaining FAILs are unrelated roots (`interval_union.cpp` regex;
`parse_options.cpp` `unique_ptr`/`default_delete` enable_if -- same dog-food
error string but a different cause; `simplify_utils.cpp` `optional`).  Both
suites green; clang-format clean.

*Updated: 2026-07-07*

### 2026-07-07 gap fixed: nested converting-constructor SFINAE across distinct types (partial for simplify_utils.cpp)

`src/util/simplify_utils.cpp` was rejected; root-causing split it into TWO
independent front-end bugs.  This entry is the first.

`std::optional<std::reference_wrapper<const array_exprt>>(char_seq)`
(simplify_utils.cpp:525) failed with "found no match for symbol 'optional'".
Header-free reduction:

```cpp
template<bool B, class T=void> struct en{}; template<class T> struct en<true,T>{ using type=T; };
template<class A,class B> constexpr bool ic_v = __is_constructible(A,B);
struct Wrap { template<class U> Wrap(U&&){} };
template<class Tp> struct opt {
  template<class Up = Tp, typename en<ic_v<Tp,Up>, bool>::type = true>
  opt(Up&&){}
};
void f(int b){ opt<Wrap> o(b); }   // error: found no match for symbol 'opt'
```

Probing showed `ic_v<Wrap,int&>` (i.e. `__is_constructible(Wrap,int&)`)
evaluated to *false* only in this nested context, though it is true in
isolation.  `__is_constructible` uses `implicit_conversion_sequence`, whose
`user_defined_conversion_sequence` reaches the converting *template*-constructor
via a fallback guarded by a single global boolean `in_template_conversion`
("prevent recursion in conversion").  Converting `int -> opt<Wrap>` (opt's
template ctor) set the flag, so the nested `int -> Wrap` conversion needed to
evaluate `is_constructible<Wrap, int&>` was skipped -> false -> every
`opt<Wrap>` ctor rejected.

Fix (N5008 [over.ics.user]: a UDCS has at most one user-defined conversion, but
a nested is_constructible query about a *different* type is a separate
sequence).  Replaced the boolean with a set keyed by destination type
(`template_conversions_in_progress`), so a distinct nested target is allowed
while same-target recursion is still cut.  Two guards keep it cheap and bounded:
nested re-entry is permitted only inside a constant-expression evaluation
(`constant_expression_context > 0`, i.e. while checking a converting ctor's
SFINAE constraint -- ordinary run-time conversions never nest here, which keeps
the expensive per-candidate `new_temporary` trial from ~doubling compile time on
numeric-heavy files such as expr.cpp / mp_arith.cpp), and a depth bound
(`size() < 2`, one nested level -- all the conforming std::optional /
std::unique_ptr patterns need).  Header-free non-vacuous CORE test
`cpp11_nested_converting_ctor_sfinae`.

Dog-food unchanged at **94/20/3, 0 crash** (verified perf-neutral: expr.cpp
40s vs 41s baseline; both suites green; clang-format clean).  simplify_utils.cpp
does NOT yet compile: it additionally hits a second, independent bug --
`is_trivially_destructible_v<std::pair<...>>` is wrongly false (the
`__is_trivially_destructible` trait counts the compiler-generated implicit
destructor of any class that has a user-declared *constructor*, and does not
recurse into members).  That is a separate triviality-semantics fix (needs a
flag distinguishing user-provided from implicit/defaulted destructors) left for
a follow-up.

*Updated: 2026-07-07*

### 2026-05-13 filesystem stack-overflow fix

Follow-up to the 2026-05-13 (duration) row: the additional duration
members elaborated by `2e8e74f8ed` triggered a previously-masked
mutual-recursion cycle in `resolve_template_alias` on MSVC's
`<filesystem>` preprocessed-header run.  Commit `09e5625681` adds a
thread-local active-set guard that breaks the cycle
deterministically, restoring the two filesystem tests to PASS and
bringing the MSVC preprocessed-header pass rate to **26/26**.

### 2026-07-07 trivial-destructor builtins + overloaded-template forward-decl match

Two coupled front-end fixes (the triviality-semantics follow-up noted above,
plus a latent overload-resolution bug it exposed):

1. `__has_trivial_destructor` / `__is_trivially_destructible` now compute the
   actual destructor triviality per [class.prop]/1 + [class.dtor]/8 (recursive
   over bases/members; a destructor is non-trivial when virtual or
   user-provided).  Implicitly-declared and `= default` destructors are marked
   `#is_implicit_dtor` (in `default_dtor` and the compound `= default` branch)
   so they are distinguished from user-provided ones.  Validated 9/9 against
   g++.  libstdc++ `std::is_trivially_destructible` is defined via
   `__has_trivial_destructor`, so this was required for correct optional/variant
   layout selection.

2. Correcting (1) changed libstdc++ instantiation ordering and exposed a latent
   bug: `instantiate_template` resolved a forward-declared function template to
   its definition by base name alone.  For `std::swap` (generic `swap(_Tp&,_Tp&)`
   vs pair `swap(pair<_T1,_T2>&, ...)`) this bound the wrong overload's parameter
   list to the deduced argument, left a template parameter unbound, and the
   dependent `pair<_T1,_T2>` threw -- silently dropping the caller's body (an
   unsound no-op).  Fixed by requiring a matching template signature
   (parameter arity + kind, and function-parameter arity) per
   [temp.over.link]/[basic.link]/11.  Non-vacuous CORE tests
   `cpp11_is_trivially_destructible` and `cpp11_swap_member_overload`;
   `cpp11_require_swap` now passes soundly.

Both suites green; clang-format clean.  Dog-food unchanged at **94/20/3,
0 crash** (no regression; verified `simplify_expr.cpp` still clean -- a coarse
tparam-only signature match had regressed it via the 3-/4-iterator `std::equal`
overloads, which the function-parameter-arity check resolves).

`simplify_utils.cpp` still does NOT compile: it hits a third, independent bug
(2b) -- instantiating `std::optional<std::pair<componentt, mp_integer>>`
recurses `optional<pair>` -> `is_trivially_destructible_v<pair>` ->
`__is_destructible_impl<pair>` -> back into `optional<pair>`, and
`is_trivially_destructible_v<pair>` resolves to `nil` ("expected constant
expression").  CBMC's incomplete-instance cycle break (cpp_instantiate_template
~3107) does not fire here because the in-progress `optional<pair>` symbol is not
yet registered when the base-class trait is evaluated.  Left for a follow-up.

*Updated: 2026-07-07*

### 2026-07-08 defaulted move constructor moves non-trivial members

A defaulted move constructor now move-constructs each base and non-static data
member from an xvalue (static_cast<T&&>) so the member's move constructor is
selected ([class.copy.ctor]/14-15).  Previously default_cpctor emitted a
memberwise *copy* initializer that was reused for the move constructor too, so
a member whose copy constructor is deleted but whose move constructor is usable
(e.g. a std::unique_ptr member) selected the deleted copy constructor -- "member
'M::M(this, ...M&...)' is not accessible" + CONVERSION ERROR dropping the
constructor body.  Fix: default_cpctor takes an is_move flag; convert_function
passes it for an rvalue-reference-parameter defaulted constructor.  Non-vacuous
CORE test cpp11_defaulted_move_ctor_member; header-free/template-free.

Both suites green; clang-format clean.  This fixes the goto-cc compilation of
CBMC's own irep_serialization.cpp and ui_message.cpp (which hold std::unique_ptr
members).  Dog-food unchanged at **94/20/3, 0 crash**: parse_options.cpp still
FAILs, but on a *distinct* remaining bug -- CBMC constructs a thrown exception
object with the class's copy constructor rather than moving/eliding from the
prvalue operand ([except.throw]/3, [class.copy.elision]/3), so throwing a
move-only exception (parse_options throws exceptions transitively holding a
move-only, unique_ptr-backed ui_message_handlert) fails.  Captured header-free
as KNOWNBUG cpp11_throw_move_only; throw/catch of a *copyable* class works, so
the gap is specifically the exception object's copy-vs-move/elision choice.

*Updated: 2026-07-08*

### 2026-07-08 catch variable nondet-initialized (not constructed from int)

A `catch(T &e)` / `catch(T e)` handler declares the exception variable; the
front-end initialized it with an `int` 0 placeholder, which for a class-typed
catch variable made convert_initializer construct the class FROM an int via
cpp_constructor -- "found no match for symbol 'X' ... argument types: signed
int" + CONVERSION ERROR -- failing for every class type without a matching int
constructor (including move-only classes, whose copy constructor is deleted).
Fix: mark the placeholder (#exception_catch_init) and nondet-initialize the
catch variable of any type in convert_initializer ([except.handle]/1-3; the
value is supplied by the exception object at runtime).  Non-vacuous CORE test
cpp11_throw_move_only.

Both suites green; clang-format clean.  Dog-food improves to **94 clean / 21
noisy / 2 FAIL / 0 CRASH** (was 94/20/3): parse_options.cpp now compiles
(it catches exceptions transitively holding a move-only, unique_ptr-backed
ui_message_handlert).  Remaining FAILs: interval_union.cpp (basic_regex) and
simplify_utils.cpp (the optional<pair> trivial-destructor instantiation cycle,
bug 2b).  (Note: CBMC still does not propagate a thrown value into the handler
body -- throw/catch of even an int leaves the handler unreachable -- a separate
exception-support limitation.)

*Updated: 2026-07-08*

### 2026-07-08 (scoping) exception-value propagation to catch handlers

Scoped the exception-propagation limitation noted with the catch-variable fix.
Root cause: goto-symex does not model C++ exception control flow.  The C++
front-end emits CATCH-PUSH / CATCH-POP / THROW instructions, but goto-symex's
symex_throw is stubbed to `assume(false)` (uncaught approximation) and
symex_catch is a no-op -- both are #if 0'd out (TODO TG-4667).  So a thrown
value never reaches the matching handler, the handler body is effectively
unreachable, and assertions in handlers pass vacuously (`try { throw 42; }
catch(int e)` proves both e==42 and e!=42) -- a soundness gap that masks bugs in
handlers and post-try code.  A separate $exception_flag+goto mechanism
(convert_CPROVER_try_catch / convert_CPROVER_throw) models control flow for the
CPROVER intrinsics but matches neither the exception type nor the value.

Captured as KNOWNBUG cpp11_throw_catch_value (header-free).  A conforming fix is
a substantial, dedicated effort (not a safe end-of-session increment to core
symex): per-frame catch stack; type-aware handler matching via cpp_exception_id
(incl. base classes and catch(...)); binding the handler parameter to the thrown
value (resolving the handler's nondet-init overwrite, e.g. via an in-flight
exception object read by the handler); control transfer to the handler with the
corresponding goto-symex dispatcher change; and, for the common cross-function
case, call-stack unwinding with destructor calls during unwinding
([except.throw]/3-4, [except.handle]/1-3,15, [except.ctor]/1-3).  The lower-risk
route is a goto-level exception-lowering pass (à la JBMC's remove_exceptions)
that runs before symex, so symex only sees ordinary gotos/assignments.

*Updated: 2026-07-08*

### 2026-07-08 goto-level C++ exception lowering (remove_cpp_exceptions)

Implemented the C++ counterpart of JBMC's remove_exceptions
(src/goto-programs/remove_cpp_exceptions.{h,cpp}), run from
process_goto_program before symex, so exception handling is no longer symex's
business.  goto-symex previously stubbed symex_throw to assume(false) and
symex_catch to a no-op, so a thrown value never reached its handler and handler
bodies were effectively unreachable (both e==42 and e!=42 provable for
`try { throw 42; } catch(int e)`).

The pass turns CATCH-PUSH/CATCH-POP/THROW into ordinary gotos/assignments: for
each THROW it matches the innermost active handler whose caught type-id is in
the thrown type's id set (cpp_exception_list already includes base classes, so
base-class matching [except.handle]/3 and catch(...) come for free), binds the
handler parameter to the thrown value (rewriting the front-end's
#exception_catch_init nondet placeholder to read a per-handler storage), and
jumps to the handler ([except.throw]/3-4, [except.handle]/1-3,15).  No-op when
there are no CATCH/THROW.

Handles intra-function try/catch: by value/reference, base-class and catch(...)
matching, and continuation after the handler.  Non-vacuous CORE tests
cpp11_throw_catch_value (was KNOWNBUG), cpp11_throw_catch_base,
cpp11_throw_catchall_continue.  Both suites green; dog-food unchanged at
94/21/2, 0 crash (the pass runs in cbmc, not goto-cc).

Follow-up: cross-function propagation (an exception unwinding to a caller's
handler) -- needs an in-flight exception object carried across returns +
per-call-site dispatch + destructor calls during unwinding; such throws
currently keep the previous (uncaught-approximation) behaviour.

*Updated: 2026-07-08*

### 2026-07-08 shared exception-lowering base + cross-function C++ propagation

Factored the language-agnostic exception-lowering structure out of JBMC's
remove_exceptions into a shared remove_exceptions_baset (src/goto-programs/):
catch-stack tracking, per-handler dispatch sequence, call-site + function-end
propagation, find_universal_exception, DEAD recomputation.  Language-specific
pieces are virtual hooks (in-flight global, match+dispatch, throw->in-flight,
handler binding).  JBMC's pass now derives from it (Java: instanceof, Throwable
reference, landingpad); WITH_JBMC enabled locally so JBMC's exception
regression tests validate the base (all pass).

remove_cpp_exceptions now derives from the base too and adds cross-function
propagation.  C++ exceptions are value types: the in-flight exception is a
pointer-to-exception-object global + an integer type tag; THROW copies the
value into a per-site static object and sets ptr+tag; a possibly-throwing CALL
is followed by a guarded dispatch; an unmatched throw falls to the function end
(propagates to the caller); a handler copies the value into its parameter and
clears the pointer.  Base-class matching (intra- and cross-function) uses the
thrown types' cpp_exception_id lists ([except.throw]/4, [except.handle]/1-3).

Verified: intra- and cross-function throw/catch deliver the value to the
matching handler (by value/reference, base-class, catch(...), multi-level
propagation, continuation after the handler); uncaught throws make subsequent
code unreachable (sound).  cbmc-cpp all pass; cbmc all pass; JBMC exception
tests all pass; dog-food unchanged at 94/21/2, 0 crash.  New CORE test
cpp11_throw_catch_cross_function (plus the intra-function tests).

*Updated: 2026-07-08*

### 2026-07-08 destructors during unwinding + rethrow; function_may_throw study

goto-conversion now runs the destructors of automatic objects during C++ stack
unwinding: on a `throw`, after the exception object is evaluated, the destructor
stack is unwound up to the innermost enclosing try (or the whole function when
there is none) before the THROW, so objects constructed in the try are destroyed
in reverse order as the stack unwinds ([except.ctor], [except.throw]/4).
Previously the destructor ran only on the normal scope-exit path.

remove_cpp_exceptions now lowers rethrow (`throw;`): the in-flight exception is
saved into "current exception" globals on handler entry and re-propagated to the
enclosing handler on a rethrow ([except.throw]/8), instead of wrapping the empty
throw side-effect into an exception object (which symex rejected).

A sound over-approximating function_may_throw (instrument only call sites of
possibly-throwing callees) was implemented and then reverted: the per-call
`inflight == null` dispatch guards prune the solver's state space on
exception-heavy STL, so dropping them blew up the deque formulas (OOM).  Kept the
conservative always-throw behaviour, rationale recorded in the pass.  (Also
noted: JBMC's uncaught_exceptions analysis assumes pointer-typed Java exceptions
and cannot be reused for C++ value exceptions.)

Verified: dtor-during-unwinding (reverse order, exactly once, scope-precise,
cross-function) and rethrow work non-vacuously; new CORE tests
cpp11_throw_dtor_unwinding and cpp11_throw_rethrow.  cbmc-cpp, cbmc and JBMC
exception tests all pass; dog-food unchanged at 94/21/2, 0 crash.

*Updated: 2026-07-08*

### 2026-07-08 unknown-bound array bound deduction (simplify_utils dog-food FIXED)

Root-caused the src/util/simplify_utils.cpp dog-food FAIL (CONVERSION ERROR
"expected constant expression, but got '<<expr:nil>>'"): an array of unknown
bound with a brace initializer, `T a[]{...}`, had its bound deduced only for
scalar/trivial element types; when T has a user-provided constructor the
initialization went through per-element construction with a nil (undeduced)
array size ([dcl.array]/1, [dcl.init.aggr]/5).  The trigger is
std::optional<std::pair<componentt, mp_integer>> (c_types.h), whose libstdc++
internals declare such an array.  Reduced with cvise (g++-validity guarded).

Fixed by completing the bound from the initializer count in
cpp_typecheck_initializer (so the declared symbol has a complete type, e.g. for
sizeof) and in cpp_constructor's array branch.  New CORE test
cpp11_array_unknown_bound_ctor.  Dog-food now 95 clean / 21 noisy / 1 FAIL / 0
crash (simplify_utils moved from FAIL to clean).

Discovered a separate, pre-existing defect (recorded as KNOWNBUG
cpp11_array_element_brace_init): per-element brace-initialization of a class
array with a user-provided constructor, `S a[N]{ {a}, {b} }`, aborts -- the
brace elements are wrapped into an untyped array expression and indexed during
construction, producing a nil-typed expression that crashes simplify_rec.  A
direct per-element construction fix was attempted but reverted because it broke
the real saj_table construction in simplify_utils (nil-typed constructor
argument); a correct fix needs to construct each element from its
initializer-clause without that regression.

Remaining dog-food FAIL: src/util/interval_union.cpp -- "symbol '_StateIdT' is
unknown" while instantiating std::__detail::_NFA<regex_traits>.  _StateIdT is a
namespace-scope typedef used as the leading return type of an out-of-line
template member definition (`_StateIdT _NFA<_TraitsT>::_M_insert_backref(...)`);
during instantiation CBMC appears to resolve that return type in the wrong scope
(the class, which has dependent bases std::vector<_State<...>> and _NFA_base)
rather than the definition's namespace, so the typedef is not found.  Not yet
fixed -- cvise plateaued on the deeply-interdependent regex trait machinery and
minimal hand-written reproducers of the pattern do not trigger it; needs deeper
investigation of out-of-line template member return-type lookup during
instantiation.

*Updated: 2026-07-08*

### 2026-07-09 per-element brace-init of a class array (bug fixed, KNOWNBUG->CORE)

Fixed the previously-recorded defect: per-element brace-initialization of an
array whose element type has a user-provided constructor, `S a[N]{ {a}, {b} }`,
aborted symex.  cpp_constructor's array brace-init branch built an array_exprt
from the raw brace elements and copy-constructed each element; for a class with a
user-provided constructor the brace elements are constructor-call list-inits left
untyped, so indexing that array yielded a nil-typed expression that crashed
simplify_rec.

Now, when the element type has a user-provided constructor (i.e. is not an
aggregate, [dcl.init.aggr]/1, [dcl.init.list]/3), each element is constructed in
place from its own initializer-clause: `{args}` forwards its elements as the
constructor arguments, a plain value/temporary is a single initializer, and a
missing clause value-initializes.  Aggregate and scalar element types keep the
array_exprt path, so an array of an aggregate `{ id, array }` (e.g.
simplify_utils.cpp's saj_table) is still initialized member-wise.  An earlier
attempt gated on non-POD-ness and broke saj_table (it has non-trivial members
but no user constructor); the correct gate is the presence of a user-provided
constructor.

cpp11_array_element_brace_init flipped KNOWNBUG->CORE; new companion
cpp11_array_element_brace_init_aggregate CORE.  cbmc-cpp, cbmc and JBMC exception
tests all pass; dog-food unchanged at 95 clean / 21 noisy / 1 FAIL / 0 crash
(remaining FAIL: interval_union.cpp regex out-of-line member lookup).

*Updated: 2026-07-09*

### 2026-07-09 interval_union regex out-of-line member return-type scope (analyzed; KNOWNBUG)

Reduced the src/util/interval_union.cpp dog-food failure ("symbol '_StateIdT' is
unknown" while instantiating std::__detail::_NFA<regex_traits>) to a minimal,
header-free, g++-valid reproducer (via cvise): a class template with an
out-of-line member whose leading return type is a namespace-scope typedef,
instantiated after a namespace-scope overload resolution of operator<< that
considers an alias-template return type (`bop<I> = I::__type`).

Root cause (pinpointed with instrumentation): when instantiating a class
template's methods, CBMC restores the scope saved at entry to
instantiate_template -- the scope that first triggered the instantiation --
before typecheck_template_parameters creates each method's template scope.  The
alias-template overload resolution makes _NFA<char> first be instantiated from a
function-body scope, so the out-of-line member's method scope is created under
that function-body scope (observed `f()::1::template::N`) instead of under the
template's own scope (`det::template::M`); the namespace-scope typedef in the
return type is then looked up in the wrong scope and not found.
([temp.inst]/2, [basic.lookup.unqual], [dcl.meaning].)

Recorded as KNOWNBUG cpp11_template_outofline_member_ns_return.  An unconditional
fix (re-enter the template scope before instantiating each method) resolves the
reproducer and passes cbmc-cpp, but has an unacceptable blast radius: it
regressed the dog-food from 95 clean/1 FAIL to 17 clean/65 FAIL by breaking
real-STL template instantiations (std::unordered_map and many others) that rely
on the restored instantiation-context scope (its using-directives / template-map
bindings).  A correct narrowly-scoped fix -- preserving the instantiation-context
using-scopes while ensuring the template's namespace is reachable during
out-of-line member return-type resolution -- is still needed; the fix attempt was
reverted.  Dog-food remains 95 clean / 21 noisy / 1 FAIL / 0 crash.

*Updated: 2026-07-09*

### 2026-07-09 interval_union out-of-line member scope FIXED (dog-food 0 FAIL)

Follow-up to the KNOWNBUG above: the fix landed.  The correct scope for
instantiating a class template's (out-of-line) members is the *instantiated
class's* scope -- its parent chain reaches both the class's own members and,
through the class's enclosing namespace, namespace-scope names ([temp.inst]/2,
[basic.lookup.unqual], [dcl.meaning]).  cpp_instantiate_template now enters that
scope before instantiating each method, instead of restoring the scope that
first triggered the instantiation.

The earlier attempt entered only the template-parameter scope, which fixed the
namespace-name case (_StateIdT) but regressed real-STL instantiations such as
std::unordered_map whose out-of-line members refer to the class's own member
aliases (e.g. __hashtable_base); the instantiated class scope covers both, so
there is no regression.  Investigating one such "regression" (as suggested) was
what revealed the template-parameter scope was itself the wrong scope.

Result: src/util/interval_union.cpp compiles; dog-food is now
96 clean / 21 noisy / 0 FAIL / 0 crash.  KNOWNBUG
cpp11_template_outofline_member_ns_return promoted to CORE.  cbmc-cpp, cbmc and
JBMC exception tests all pass.

*Updated: 2026-07-09*
