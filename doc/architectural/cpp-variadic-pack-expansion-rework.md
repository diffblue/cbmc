\file

# Unified Variadic Pack-Expansion Rework (C++ front-end)

Status: design / scoping. No behavioural change yet. This document scopes the
work needed to make C++ variadic templates ([temp.variadic]) work uniformly in
CBMC's C++ front-end, so that standard-library facilities built on parameter
packs — notably `std::__invoke` / `std::invoke_result` / `std::reference_wrapper`
and hence `std::ref`'d predicates and `std::erase_if` — verify correctly.

The regression tests named below are committed and currently KNOWNBUG; each
phase of this rework flips a specific set to CORE. A companion CORE test,
`cpp11_variadic_pack_expansion_works`, pins the contexts that already work so
the rework does not regress them.

---

## 1. Standard background ([temp.variadic])

* **[temp.variadic]/3** — a *parameter pack* is a template/function parameter
  that accepts zero or more arguments.
* **[temp.variadic]/4** — a *pack expansion* is `pattern...`; it is allowed in a
  fixed set of *expansion contexts*: function-call argument lists, template
  argument lists, brace-enclosed initializer lists, base-specifier lists,
  member-initializer lists, `sizeof...`, fold-expressions, and a few others.
* **[temp.variadic]/5** — instantiating a pack expansion `pattern...` produces a
  comma-separated list of `N` instantiations of `pattern`, where `N` is the
  common length of the packs mentioned in the pattern; in the i-th instantiation
  every such pack is replaced by its i-th element. `N` may be 0 (the list is
  then empty).
* **[temp.variadic]/8** — `sizeof...(Pack)` is `N`.

The single correctness invariant the rework must establish: **at every
expansion context, a pattern that mentions one or more packs of common length
`N` is replaced by exactly `N` substituted copies (0 when empty), per
[temp.variadic]/5.**

---

## 2. Current state (measured)

CBMC's variadic support is a collection of *independent, per-context,
single-element-oriented* code paths rather than one expansion mechanism. Their
behaviour was measured with header-free probes (see regression tests):

| Context | Probe | Status |
|---|---|---|
| Value-pack in a call, 1 / 3 / multi-layer | call1/call3/outer | ✅ works |
| Type pack forwarded as class-template arg `tup<T...>` (explicit args) | wrap | ✅ works |
| `sizeof...(T)` in a **member function body** | holder::n | ✅ works |
| `sizeof...(T)` in a **static data member initializer** | cpp11_variadic_sizeof_static_init | ❌ wrong count (multi & empty) |
| **Empty** pack in a call `f(a...)` -> `f()` | cpp11_variadic_empty_pack_call | ❌ "found no match" |
| Qualified-id `Trait<A...>::type`, **deduced** pack, simple typedef | cpp11_variadic_qualified_id_pack | ❌ body dropped / nondet |
| Qualified-id `Trait<F,A...>::type`, decltype-valued member | cpp11_decltype_pack_in_class_template | ❌ body dropped / nondet |

### Why they don't compose (relevant code)

* `src/cpp/parse.cpp` `rFunctionArguments` historically **dropped** the `...` on
  a call argument (it can instead set `ID_ellipsis` on the pattern). Without a
  preserved marker, downstream cannot tell a pack expansion from a single pack
  reference.
* `src/cpp/template_map.{h,cpp}` `template_mapt` stores packs in `pack_args_map`
  / `pack_size_map`, but for a **single-element** pack also stores a *scalar*
  `type_map` entry, and several call sites then treat the pack as that scalar.
  `template_mapt::apply(typet&)` performs **no** expression-level pack expansion
  and has **no `decltype` case**; `expand_parameter_packs` expands only function
  *parameter lists*.
* `src/cpp/cpp_typecheck_template.cpp` `typecheck_template_args` (~l.1742) *does*
  expand a template-argument pack `Trait<A...>` — but only when the argument
  arrives as an `ambiguous` `cpp_name` with `ID_ellipsis`, and only when
  `pack_args_map` is non-empty. Instrumentation shows the `A...` argument of a
  **return-type** qualified-id `Trait<F, A...>::type` never reaches this path.
* `src/cpp/cpp_typecheck_resolve.cpp` `guess_function_template_args` records a
  deduced single-element function parameter pack **only** as a scalar `type_map`
  entry (`pack_args_map` stays empty), so the (pack_args_map-gated) expansion
  machinery never fires when the function's dependent return type is elaborated.
* `sizeof...` is computed correctly where a method body is elaborated with
  `pack_size_map` populated (`cpp_typecheck_method_bodies.cpp`), but a static
  data member initializer is elaborated on a different path that lacks it.

### Member-function and constructor contexts (measured 2026-06-28)

A second, orthogonal axis of the same gap concerns *where the function lives*.
Multi-element function parameter packs (`A... a` with `N >= 2`) are expanded to
one `a$k` parameter per element **only for free function templates**, by a
self-contained expander in `instantiate_template`
(`src/cpp/cpp_instantiate_template.cpp`, ~l.4960-5260): it detects the trailing
pack parameter, builds `pack_var$0..$N-1` parameters from `full_template_args`,
replaces the pack parameter, and rewrites pack references in the body
(fold-expressions, function-call argument lists, lambda init-captures). Measured
behaviour:

| Function context | Probe | Status |
|---|---|---|
| Free function template, value pack in a call, N=3 | `call3(a...) -> g3(a...)` | ✅ works (params `a$0,a$1,a$2`) |
| Free function template, fold-expression, N>=2 | `(a + ... + 0)` | ❌ no body (fold is a stated non-goal) |
| **Member** function template, value pack in a call, N>=2 | `S::f(a...) -> g3(a...)` | ❌ vacuous (body truncated) |
| **Constructor** with a class-template pack, N>=2 | `TImpl(const Head&, const Tail&... t)` | ❌ signature collapses to one parameter; construction silently fails (see `cpp11_variadic_ctor_pack_multi`) |

Root causes (instrumented):

* The `instantiate_template` expander is reached for free function templates
  only. A member function template and a class-template-pack constructor reach
  it for *neither* (probe at the expander's entry never fires for them); they
  are elaborated on the class-member paths below.
* A class-member function/constructor signature is finalised in
  `typecheck_compound_declarator` (`src/cpp/cpp_typecheck_compound_type.cpp`).
  `pack_args_map` *is* populated there (e.g. `A -> {int,int}`), but
  `typecheck_type(final_type)` **collapses** the pack-expansion parameter
  `const A&... a` to a *single* resolved parameter (the single-element shortcut),
  rather than to `N` parameters.
* The member-function **body** is drained later in
  `cpp_typecheck_method_bodies` (`src/cpp/cpp_typecheck_method_bodies.cpp`),
  whose pack handling is **single-element only**: it maps the pack name to
  `pack_args_map[...].front()` (and only when that element is a `struct_tag`)
  and strips `ID_ellipsis`. There is no multi-element body expansion and no
  member-initializer-argument expansion (`_Inherited(t...)`).

Consequently no single-site change makes a multi-element member case verify:
the signature and the body must *both* expand to `N`, consistently named, and
member-initializer / brace-init-list pack expansions must be added. This is the
function-template expander generalised to the member contexts — see Phase 6.

### Multi-argument `std::function` (measured 2026-06-29)

Constructing **any multi-argument** `std::function<R(A,B,...)>` from a callable
fails (`std_function.h:435` "found no match for symbol 'function'") and the
proof then passes **vacuously** (unsound); a single-argument
`std::function<R(A)>` works. This is the blocker behind the dog-food
`make_bvrep` failures (`arith_tools.cpp`, `bitvector_expr.cpp`,
`bitvector_types.cpp`), which pass a lambda capturing a
`std::function<bool(bool,bool)>`.

Reduced header-free (`regression/cbmc-cpp/cpp11_decltype_pack_sfinae_ctor`):

```cpp
template <class R, class... A> struct Fn<R(A...)> {
  template <class F, class = decltype(declval<F &>()(declval<A>()...))>
  Fn(F);                         // converting ctor, SFINAE on a decltype
};                               // that expands the class pack A
Fn<bool(bool, bool)> g = lambda; // N>=2: "found no match"; N==1: works
```

This is libstdc++'s `std::function<R(A...)>` converting constructor, whose
viability is constrained by `_Callable<F> = __is_invocable_r<R, F&, A...>`
(a `decltype` over the class parameter pack `A`). Measured axis:

| Member context, default-arg `decltype(f(declval<A>()...))` | N | Status |
|---|---|---|
| Free function template (explicit class args) | 2 | ✅ works |
| Static member fn template | 2 | ✅ works |
| Non-static member fn template (called on object) | 2 | ✅ works |
| **Converting constructor template** | 2 | ❌ "found no match" → vacuous |
| Converting constructor template | 1 | ✅ works |

So this axis is **constructor-specific**: ordinary member functions deduce and
evaluate the default-argument `decltype` per call
(`template_function_instance`, `cpp_typecheck_resolve.cpp` ~l.6674, which
handles the multi-element pack correctly), but the constructor reaches a
different path. The class pack `A` inside the constructor's
default-template-argument `decltype` is never expanded for `N >= 2`: the
class-pack member expander in `template_map::apply`
(`src/cpp/template_map.cpp` ~l.363) deliberately `continue`s past
`ID_constructor`/`ID_destructor` and past template members, and no other site
expands the pack inside a constructor's default-template-argument `decltype`
operand. Grounded in N5008 [temp.variadic]/5 (pack expansion of `declval<A>()...`),
[temp.deduct]/8 and [over.ics.user] (SFINAE on the constructor's `decltype`
operand selecting the user-defined conversion). Tracked by KNOWNBUG
`cpp11_decltype_pack_sfinae_ctor`; flip to CORE once the constructor path
expands the class pack in its default-template-argument `decltype`. Belongs with
Phase 6 (member/constructor contexts).

#### Update 2026-06-29 — partial fix landed

Probing showed the constructor *does* reach `template_function_instance` and
its default-argument SFINAE evaluator (`cpp_typecheck_resolve.cpp`); the operand
`decltype(declval<F&>()(declval<A>()...))` arrives with the pack-expansion
**ellipsis discarded** — `rFunctionArguments` (`parse.cpp`) parsed `...` after a
function-call argument and dropped it (a `// TODO`). A value parameter pack
survives this (it is recovered by name during body expansion) but a type-pack
expression in a `decltype` has no such fallback, so `declval<A>()` was left as a
bare pack reference and rejected.

Fixed in two parts (commit: "expand function-call argument packs in decltype
operands"):

* `rFunctionArguments` now records the ellipsis as `ID_ellipsis` on the
  argument ([temp.variadic]/5).
* `template_mapt::apply`, when substituting into a `decltype` operand, expands
  each `ID_ellipsis`-marked call argument into one argument per deduced element
  of the referenced type pack (zero for an empty pack); arguments not
  referencing a deduced type pack are untouched, so value packs and other
  contexts are unaffected. The constructor default-argument site substitutes
  before type-checking when such a pack is present.

This resolves the **direct** form and the **nested-trait** form (the libstdc++
`__invoke_result<F,A...>::type = decltype(declval<F>()(declval<A>()...))`
shape): `cpp11_decltype_pack_sfinae_ctor` and
`cpp11_decltype_pack_nested_trait_ctor` are CORE and verify non-vacuously. Both
regression suites pass with no regressions.

**Still open** (KNOWNBUG `cpp11_decltype_pack_variadic_invoke_ctor`): real
libstdc++ routes the invocability check through the *variadic helper*
`std::__invoke`, i.e.
`__invoke_result<F,A...>::type = decltype(std::__invoke(declval<F>(), declval<A>()...))`.
After the call-argument pack is expanded, the resulting call is to a **variadic
function template** whose own pack must be deduced from the two-or-more expanded
arguments, and whose trailing-return `decltype(f(args...))` must then be
expanded — all inside an unevaluated operand during constructor SFINAE. That
nested function-template pack deduction is not yet performed for `N >= 2`, so a
real multi-argument `std::function` (and the `make_bvrep` dog-food files) still
fail. This is the next Phase-6 step.

### The motivating chain (`std::erase_if`)

`std::erase_if(v, pred)` -> `std::__remove_if(..., __ops::__pred_iter(std::ref(pred)))`.
`std::reference_wrapper::operator()(_Args&&...)` -> `std::__invoke(get(),
std::forward<_Args>(args)...)`; `std::__invoke`'s return type is
`std::__invoke_result<F, Args...>::type`, whose member is
`decltype(declval<F>()(declval<Args>()...))`. Instantiated *nested* (inside the
algorithm), the deduced pack `Args` is not propagated/expanded, the trait member
is mis-resolved, the instantiated body is dropped, and the predicate silently
never matches — so `erase_if` is a no-op. (Verified down to a header-free
reproduction; see `cpp20_vector_erase_if`, `cpp11_decltype_pack_in_class_template`.)

---

## 3. Proposed design — one representation, one primitive, applied everywhere

### 3.1 Canonical pack representation

* A parameter pack is **always** recorded in `pack_args_map` (elements) and
  `pack_size_map` (count), including length-1 and length-0 packs. The scalar
  `type_map` convenience entry may remain for length-1 packs but must never be
  the *only* record (so the expansion machinery is never starved).
* Deduction (`guess_function_template_args`) must populate `pack_args_map` /
  `pack_size_map` for every deduced function parameter pack (Phase 5).
* The pack-expansion marker `ID_ellipsis` on a *pattern* must be preserved from
  parse through substitution until the pattern is actually expanded (Phase 0).

### 3.2 One expansion primitive

Add a single routine (in `template_mapt`, the natural home) that realises
[temp.variadic]/5 for an arbitrary pattern:

```
// Returns the N expanded instantiations of `pattern` (a typet or exprt) under
// this map, where N is the common length of the packs referenced in `pattern`
// (0 if all referenced packs are empty). Each copy substitutes the i-th element
// of every referenced pack. Throws iff the referenced packs have inconsistent
// lengths ([temp.variadic]/5).
std::vector<irept> expand_pack(const irept &pattern) const;
```

It reuses the existing "collect referenced packs by suffix-match against
`pack_args_map`" logic already present (in three copied forms) in
`typecheck_template_args`, the prototype call-arg expander, and
`cpp_typecheck_method_bodies`. Those copies are replaced by calls to this one.

### 3.3 Apply the primitive at every [temp.variadic]/4 context

* **Function-call argument lists** — when type-checking a call, replace each
  argument marked `ID_ellipsis` by `expand_pack(arg)`; an empty result yields no
  argument (fixes the empty-pack call). Must run *before* the operand is
  type-checked bottom-up (the pattern alone is not well-typed).
* **Template-argument lists** — keep `typecheck_template_args`' expansion but
  drive it from `expand_pack`, and ensure dependent qualified-ids
  (`Trait<A...>::type`) route their template arguments through it (fixes the
  qualified-id paths).
* **`decltype` / unevaluated operands** — `template_mapt::apply` must recurse
  into a `decltype`'s `expr_arg` and run `expand_pack` on any pack-expansion
  sub-pattern before the operand is type-checked (fixes the decltype-trait path).
* **Brace / initializer lists, base-specifier lists, member-init lists** —
  already partly handled; reroute through `expand_pack` for uniformity.
* **`sizeof...`** — evaluate from `pack_size_map` uniformly, in *all* contexts
  including static data member initializers and empty packs (fixes the
  `sizeof...` static-init gap).

### 3.4 Substitution ordering

`expand_pack` must be invoked at the point the surrounding template is
*instantiated* (when packs are bound), before the pattern is type-checked or
resolved. The current failure mode is that some contexts type-check the pattern
(which references an unbound/scalar pack) before any expansion runs.

---

## 4. Phased implementation plan

Each phase is independently buildable and gated on **both** `regression/cbmc-cpp`
(`-X libcxx`) and `regression/cbmc`, and flips the listed KNOWNBUG tests to CORE.

* **Phase 0 — foundation.** Preserve `ID_ellipsis` on call-argument patterns in
  `rFunctionArguments`; always record deduced/instantiated packs in
  `pack_args_map`/`pack_size_map`; add `template_mapt::expand_pack`. No test
  flips yet; `cpp11_variadic_pack_expansion_works` must stay green.
* **Phase 1 — call-argument lists.** Route call-arg expansion through
  `expand_pack`, including the empty case. Flip `cpp11_variadic_empty_pack_call`.
* **Phase 2 — template-argument lists & qualified-ids.** Drive
  `typecheck_template_args` from `expand_pack`; route dependent qualified-id
  template arguments through it. Flip `cpp11_variadic_qualified_id_pack`.
* **Phase 3 — decltype / unevaluated operands.** Expand inside `decltype`
  operands during substitution. Flip `cpp11_decltype_pack_in_class_template`.
* **Phase 4 — `sizeof...` uniformity.** Evaluate `sizeof...` from
  `pack_size_map` in all contexts. Flip `cpp11_variadic_sizeof_static_init`.
* **Phase 5 — deduction propagation + end-to-end.** Ensure
  `guess_function_template_args` records deduced packs as packs, so a function
  template's dependent return type elaborated during *nested* instantiation sees
  the pack. Re-check `std::__invoke`/`std::ref`; flip `cpp20_vector_erase_if`
  (and the companion `cpp20_member_overload_converting_ctor` stays CORE).
* **Phase 6 — member-function & constructor contexts.** Generalise the
  free-function multi-element expander (`instantiate_template` ~l.4960-5260) to
  the member paths so a class-member function/constructor whose signature
  mentions a pack of length `N` expands to `N` consistently-named (`a$k`)
  parameters, and the corresponding body / member-initializer / brace-init-list
  pack expansions (`f(a...)`, `_Inherited(t...)`, `{a...}`) expand to `N`.
  Concretely: (a) replace the single-parameter collapse in
  `typecheck_compound_declarator` with `N`-parameter replication driven by
  `pack_args_map` (built from the already-resolved element types, wrapping each
  in the parameter's reference/cv structure); (b) replace the single-element
  substitution in `cpp_typecheck_method_bodies` with `expand_pack`-driven
  multi-element expansion at every [temp.variadic]/4 context reachable from a
  member body, including member-initializer argument lists. Flip
  `cpp11_variadic_ctor_pack_multi`; this also unblocks 3+-element direct
  `std::tuple` construction (`get<2>` and beyond) and the multi-element half of
  `cpp11_variadic_pack_expansion`. Depends on Phase 0 (canonical pack record +
  `expand_pack`). Highest regression risk of the phases — gate strictly on both
  suites, re-running any failure alone to rule out parallel-load flakes.

Phases 1–4 are largely independent; Phase 5 depends on 0+2+3; Phase 6 depends
on 0 and shares the `expand_pack` primitive.

---

## 5. Test strategy

Header-free, minimal, one gap per test (already committed):

* KNOWNBUG: `cpp11_variadic_empty_pack_call`, `cpp11_variadic_qualified_id_pack`,
  `cpp11_variadic_sizeof_static_init`, `cpp11_decltype_pack_in_class_template`.
* CORE guard: `cpp11_variadic_pack_expansion_works` (must never regress).
* End-to-end KNOWNBUG: `cpp20_vector_erase_if` (flips at Phase 5).
* Phase 6 (member/constructor) KNOWNBUG: `cpp11_variadic_ctor_pack_multi`
  (header-free, non-vacuous; mirrors libstdc++'s `_Tuple_impl` recursion step).

Each phase's PR flips exactly the tests it fixes from KNOWNBUG to CORE and adds
any newly-discovered edge cases as KNOWNBUG first.

---

## 6. Risks and non-goals

* **Risk: regressing the single-element machinery.** Much existing variadic
  behaviour works *because* of the single-element shortcuts. The rework keeps
  the scalar `type_map` convenience entry and adds, rather than replaces, the
  canonical record; `cpp11_variadic_pack_expansion_works` plus the full suites
  guard against regressions. Land phases incrementally.
* **Risk: pattern type-checked before expansion.** The most common current bug;
  every context must expand *before* type-checking the pattern.
* **Non-goals (initially):** fold-expressions beyond what libstdc++ needs,
  pack indexing `T...[N]` (C++26, already partially handled), and
  lambda-init-capture packs. Add as separate KNOWNBUG tests if encountered.
