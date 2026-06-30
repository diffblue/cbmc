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

#### Update 2026-06-29 (cont.) — forwarding-reference callee fixed; two layers left

Reducing the variadic `std::__invoke` chain `invk(F&& f, Args&&... a) ->
decltype(static_cast<F&&>(f)(static_cast<Args&&>(a)...))` peeled off two further
sub-gaps:

1. **Calling through a reference-typed callee** — FIXED (commit "invoke
   operator() through a reference-typed callee"; CORE
   `cpp11_forwarding_ref_callee_call`). `static_cast<F&&>(f)()` /
   `std::forward<F>(f)()` (the callee form of `std::__invoke`) was modelled as a
   pointer and mistaken for a function pointer ("expecting code as argument"),
   returning nondet. A reference-typed callee is now implicitly dereferenced
   before the call type-dispatch so a class type routes to `operator()`
   ([expr.call], [over.call.object]). Non-pack forwarding-reference arguments
   (`f(static_cast<A&&>(a))`, single or several) also work.

2. **Forwarding-reference parameter-pack expansion** — FIXED (commit "expand
   forwarding-reference parameter-pack call patterns"; CORE
   `cpp11_forwarding_ref_pack_expansion`). The body pack expander
   (`cpp_instantiate_template`) expanded a *bare* value-pack call argument
   `f(a...)` into `f(a$0, a$1)` but not a *pattern* argument that merely
   contains the pack, `f(static_cast<A&&>(a)...)`: the value pack `a` was left
   referencing a removed parameter ("symbol 'a' is unknown") and the type pack
   `A` was not substituted. The expander now expands such a pattern argument
   into one argument per element, substituting in lockstep the value pack
   (`a -> a$k`) and the type pack (`A -> ` the k-th deduced element type;
   replacing the `cpp_name A` inside `A&&` performs [dcl.ref] reference
   collapsing). The empty-pack strip path drops a pattern argument too, so
   `f(static_cast<A&&>(a)...)` with an empty pack becomes `f()`. Verified for
   N = 0..3, lvalue and rvalue.

So the remaining chain for a real multi-argument `std::function` is: (3) the
variadic helper's **trailing-return `decltype`** expansion — a
declaration-only `auto invk(F&&, Args&&...) -> decltype(static_cast<F&&>(f)
(static_cast<Args&&>(a)...))` (the declaration of `std::__invoke`) does not
expand the forwarding-reference pack in its *return type* for `N >= 2`, so the
return type fails to resolve (KNOWNBUG `cpp11_trailing_return_fwd_pack`); then
(4) re-evaluating the nested constraint during the constructor SFINAE
(`cpp11_decltype_pack_variadic_invoke_ctor`).

#### Update 2026-06-29 (cont.) — trailing-return decltype: diagnosis

Investigated layer (3).  The variadic helper's trailing-return `decltype`
elaboration happens during **deduction** (`guess_function_template_args`,
`cpp_typecheck_resolve.cpp`): `invk` is never instantiated because the call's
candidate is dropped when `typecheck_type(function_type)` throws (the function
type carries the trailing-return `decltype`).  Probing showed two facts:

* The N copies of the value parameter pack are inserted into the deduced
  function type **without distinct names** (all keep the pack name `a`), and the
  trailing-return `decltype(f(a...))` keeps the bare pack reference `a` (with its
  `...` marker).  Putting the params in scope then yields a single `a`, and the
  `a...` expansion over a non-pack fails -> the candidate is rejected.
* A prototype fix (rename the expanded params to `a$i`; expand the
  return-`decltype`'s value-pack call argument in lockstep, value pack `a -> a$i`
  and type pack `Args -> ` the i-th deduced type) makes the return type expand
  correctly at the AST level (`decltype(f(static_cast<E0&&>(a$0), static_cast<E1&&>(a$1)))`),
  and the expanded args then resolve.  But a further sub-issue remains: resolving
  the call `f(a$0, a$1)` inside the deduction-time `decltype` reports "found no
  match for operator()" (operator() resolution on the parameter callee in the
  SFINAE return-type context).  So layer (3) is itself a multi-fix sub-project
  (param renaming + value-pack return-`decltype` expansion + operator()
  resolution in the deduction `decltype`), still open.

#### Update 2026-06-29 (cont.) — conformance verdict + deeper diagnosis

**Conformance:** confirmed non-conformant (and unsound).  The construct is
well-formed standard C++ -- both GCC 13 and Clang accept it with
`-pedantic-errors` -- and matches N5008 [temp.variadic]/6 Example 5 (a
function-call argument list whose pattern contains the pack, `f(&rest ...)`) in
a trailing-return-type `decltype` ([dcl.fct], [temp.deduct.call]).  CBMC
silently drops the candidate and reports `VERIFICATION SUCCESSFUL` on a program
whose deliberately-wrong property must FAIL -- an unsoundness, the most serious
kind of non-conformance.  So it must be fixed regardless of `std::function`.

**Deeper diagnosis (second prototype):** with the param renaming + return-
`decltype` value-pack expansion applied in BOTH `guess_function_template_args`
and `instantiate_template`, the return `decltype` expands correctly end-to-end
at the AST level (`decltype(f(static_cast<c_bool&&>(a$0), static_cast<c_bool&&>(a$1)))`,
verified just before `convert_non_template_declaration`, return type resolved to
`bool`), and guess no longer throws.  But the construct STILL verifies vacuously:
the call `invk(...)` does not resolve at the call site -- the resolved `bool`
return type is not propagated from the (internally-succeeding) deduction /
instantiation to the call expression's type, and a residual `a` resolution
(during instantiation, `inst_depth=1`) is still triggered.  So layer (3) is a
genuine multi-site change spanning deduction, instantiation, AND return-type
propagation to the call expression -- i.e. it is the function-template pack
expander generalised across all three, which is the unified Phase-6 rework
rather than another ad-hoc per-site patch.  Both prototypes were reverted (they
got the expansion working but did not make the construct verify and touch the
hot deduction/instantiation paths).  KNOWNBUG `cpp11_trailing_return_fwd_pack`
remains the tracker.

**Orthogonality note:** the *real* libstdc++ `std::__invoke` does NOT use a
value-pack `decltype(...forward(args)...)` return; it uses the **type-pack
trait** return `__invoke_result_t<_Callable, _Args...>`.  A faithful model of
that shape -- `typename ir<F&, A...>::type myinvoke(F&& f, A&&... a)` with
`ir<F,A...>::type = decltype(declval<F>()(declval<A>()...))` -- already
resolves correctly (`apply` expands the type-pack trait).  So this
value-pack-trailing-return layer is a genuine standalone feature gap but is NOT
the blocker for real multi-argument `std::function`: `mf.cpp` and the
`make_bvrep` files still fail at `std_function.h:435` for a different, as-yet
unpinned reason in libstdc++'s `_Callable`/`__invoke_result` machinery, which
should be re-diagnosed directly rather than via synthetic `std::__invoke`
models.

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


---

## 7. Status update 2026-06-29 — member/constructor body expansion landed; remaining KNOWNBUGs are not expander gaps

Measured the three then-remaining KNOWNBUGs and found that, after the earlier
phases landed, they are **not** missing-`expand_pack`-primitive gaps but three
distinct deeper bugs. A single consolidated `expand_pack` primitive (section
3.2) would tidy the working duplicated logic but would not, on its own, flip
any of them.

* **`cpp11_variadic_pack_expansion` — FIXED, now CORE.** Two sub-bugs, both in
  *where* a function/member body's pack expansion happens, not in the
  expansion logic:
  1. A *free* function template's body value pack is expanded (in
     `instantiate_template` / by the call resolver), but a *member* function
     template's body is drained later in `typecheck_method_bodies`, which only
     expanded a *class* pack recorded in `#expanded_param_packs`. Its own
     deduced value pack was left unexpanded, so a recursive member call
     `sum_of(ts...)` kept its `...` and failed ("symbol 'ts' is unknown").
     Fixed by expanding the own value pack there, driven by the *instantiated
     function's actual parameters* (single param `S` ⇒ strip `...`; replicated
     `S$0..S$k` ⇒ expand; no matching param ⇒ empty-pack drop). The measured
     contrast that localised this: a member body calling a *free* variadic
     callee `g(ts...)` already worked; only a member/self callee failed.
  2. The constructor *function-call-expression* member initializer
     `sum(sum_of(rest...))` was expanded at the wrong level: the nested-search
     `mi_ref_base` (and the analogous `#expanded_param_packs` `is_arg_list`
     heuristic) treated the whole `sum_of(rest...)` initializer expression as a
     pack pattern, duplicating it to `sum(sum_of(rest$0), sum_of(rest$1))`.
     Restricted both to a *bare cpp_name* / explicit-`...` argument, so a
     nested expansion is expanded at its own inner level
     (`sum(sum_of(rest$0, rest$1))`). Grounded in N5008 [temp.variadic]/5,7.
  Commits: "expand value parameter packs in member-function-template bodies and
  function-call-expression member initializers" (src) + the CORE flip. Both
  suites green.

* **`cpp11_trailing_return_fwd_pack` — FIXED, now CORE.** The trailing-return
  `decltype(static_cast<F&&>(f)(static_cast<Args&&>(a)...))` (the declaration of
  libstdc++'s variadic `std::__invoke`) failed because the type parameter pack
  `Args` of the pack-expansion call argument sits *inside the reference type*
  `Args&&`, and `expand_call_argument_packs` (run from `template_mapt::apply` on
  decltype operands) located/substituted the pack only via a node's `ID_type`,
  so it never fired: the bare `...`/`Args` survived, `typecheck_type` rejected
  the well-formed return type, the candidate was dropped, and
  `decltype(invk(...))` silently failed. Fixed by making both the detection
  (`find`) and the substitution (`replace_type_pack_ref`) also handle a type
  parameter pack appearing as a *bare cpp_name sub-node* (not only as a node's
  `ID_type`); substituting the element type for the `cpp_name` inside `Args&&`
  yields `elem&&` ([dcl.ref] reference collapsing). Because `apply` runs in both
  deduction and instantiation, the deduced return type now both elaborates and
  *propagates* to the call expression — so this was an expander-reach gap, not a
  separate propagation gap as previously thought. Grounded in N5008
  [temp.variadic]/5,6, [dcl.fct]/2. Both suites green.

* **`cpp11_decltype_pack_variadic_invoke_ctor` — FIXED, now CORE.** The same
  enhancement makes the nested `invoke_result<F,A...>::type =
  decltype(invoke_fn(declval<F>(), declval<A>()...))` trait elaborate during the
  constructor's SFINAE, so the synthetic multi-argument-`std::function` chain
  verifies non-vacuously.

* **`cpp11_trailing_return_plain_pack` — FIXED, now CORE.** The plain by-value
  `f(a...)` trailing-return decltype, whose pattern references only the *value*
  parameter pack `a` (no type pack), is now expanded too:
  `expand_call_argument_packs`, when a `...`-marked call argument matches no
  type pack, treats it as a value-pack expansion and replicates the pattern to
  the common deduced pack length ([temp.variadic]/4,5) -- each copy referring
  to the single in-scope value parameter, whose deduced element type fixes the
  call-argument's type.  N is the unique non-zero deduced pack size; all-empty
  ⇒ drop, ambiguous ⇒ untouched.  Verified N = 1..3, plain and cast forms.

* **`cpp11_trailing_return_empty_pack` — FIXED, now CORE (N == 0).** An *empty*
  deduced parameter pack was recorded nowhere during deduction (the argument
  list is exhausted before the trailing pack is reached; the pack kept only its
  `build_unassigned` placeholder), so `f(a...)` deduced with zero pack arguments
  was not collapsed to `f()` and the return type failed to resolve.
  `guess_function_template_args` now records such an unbound trailing pack with
  `pack_size_map` size 0 (treating the `ID_unassigned` placeholder as unbound,
  per [temp.deduct.call], [temp.arg.explicit]/4 Note 1), so
  `expand_call_argument_packs` collapses the trailing-return pack expansion to
  zero arguments.  Applies to both the plain and forwarding-cast forms; verified
  for free and member function templates and that `sizeof...` stays correct.

* **Real multi-argument `std::function` (`std_function.h:435`) — root
  diagnosed; two distinct layers remain.** The `_Callable` =
  `__is_invocable_r<R, F&, A...>` constraint ("found no match for symbol
  'function'") was traced to two layers:
  1. **Partial-spec pack deduction (FIXED, CORE).** libstdc++'s
     `__result_of_impl<false, false, _Functor, _ArgTypes...>` (the base of
     `__invoke_result`) places a parameter pack *after* fixed (non-deduced)
     arguments.  When selected via the partial-specialization disambiguation
     path (`disambiguate_template_classes`, as a dependent base class), the
     deduced pack was collapsed to a single element -- `build_template_args`
     returns the scalar `type_map` convenience binding and, unlike
     `elaborate_class_template`, this path did not expand it into positional
     arguments -- so `__invoke_result` was mis-sized and the constraint failed
     to elaborate.  Isolated header-free by `cpp11_partial_spec_pack_after_fixed`
     (now CORE).  FIXED: expand the deduced pack into positional arguments via
     `pack_args_map` in `disambiguate_template_classes`, mirroring
     `elaborate_class_template` (N5008 [temp.variadic]/5).  Crucially the
     expanded list is kept SEPARATE from `matcht::specialization_args` in a new
     `matcht::instantiation_args` field: `matcht::cost` is the specialization-
     argument count and partial ordering prefers fewer arguments, so expanding
     in place inflated the cost and mis-ranked a trailing-pack specialization
     against the primary (regressing `cpp11_variadic_partial_spec_trailing_pack_
     select` / `cpp11_variadic_tuple_impl_recursion`); cost/ordering stay on the
     un-expanded form while instantiation uses the expanded one.  Both suites
     green.
  2. **`std::function` body conversion (decomposed; layer 2 fully fixed for
     single-arg).** With layer 1 fixed, single-argument `std::function`
     construction *and invocation* now verify soundly (`std::function<int(int)>
     f = g; f(x)` -- a real call with a non-vacuous wrong-assertion check).
     MULTI-argument `std::function` construction now also resolves the converting
     constructor (no more "found no match"), exposing the NEXT layer (layer 3,
     below).  Sub-roots originally found while the single-arg body was broken:
     - **2a. cv-qualifiers on a function type (FIXED, CORE).** `_M_create`'s
       first failure was `invalid conversion 'int(*)(int)' to 'int(int)'`: the
       decayed target `_Functor` was a function *type* not a function *pointer*,
       because `std::decay` missed function-to-pointer decay, because
       `std::is_function<F>` (= `!is_const<const F>`) was false, because a
       cv-qualifier applied to a function-typed template parameter via
       substitution was wrongly written onto the function type.  N5008
       [dcl.fct]/7 says such cv-qualifiers are ignored.  Fixed in
       `typecheck_type` (drop top-level cv when the resolved type is a function
       type); CORE test `cpp11_cv_qualified_function_type`.  No regressions.
     - **2b. const/non-const member-function-template overload (KNOWNBUG).**
       With the target now a function pointer, `_M_create` next selects the
       *const* `_Any_data::_M_access` overload for a non-const object, because
       const/non-const member-function-*template* overload resolution did not
       rank the implicit object parameter's cv-qualification (the non-template
       case was correct).  The const overload returns `const T&`, so
       `__dest._M_access<_Functor*>() = ...` was "not an lvalue".  FIXED, CORE
       (`cpp11_member_template_const_overload`): the deduced function type of an
       uninstantiated `template_function_instance` carries no `this` parameter,
       so the const member-qualifier is recovered from the candidate template's
       `ID_method_qualifier` and added to the cv distance
       (`member_template_const_penalty`).  No regressions.
     - **2c. `_M_manager` body (open).** With 2a and 2b fixed, single-argument
       `std::function` construction proceeds past `_M_create` to
       `_Function_base::_Base_manager::_M_manager` (the clone/destroy/type_info
       dispatcher), whose body is *silently* left nil ("no body").  Decomposed:
       - **2c-i. static_cast void* -> pointer-to-(const) function pointer
         (FIXED, CORE).** The deepest error was
         `invalid implicit conversion from 'const void *' to '__decay_t<FP> *'`
         inside `_M_get_pointer` (`__source._M_access<_Functor*>()`):
         `cast_away_constness` special-cased only a void* *target*, so a void*
         *source* cast to `const FP*` (FP a function pointer, a deeper
         subtype-chain) was mis-ranked as casting away constness and the valid
         cast ([expr.static.cast]/13) was rejected / produced a type-mismatched
         result.  Fixed by the symmetric void*-source case in
         `cast_away_constness`; CORE `cpp11_static_cast_void_to_const_funptr`.
       - **2c-ii. `_M_manager` body silently niled under system-header
       - **2c-ii. `_M_manager` body silently niled (FIXED, CORE).**  Was
         mis-attributed to system-header handling; the earlier null-handler
         diagnosis was DISPROVEN.  Real cause: a deduced cv-qualified
         function-pointer reference parameter lost its const on re-conversion
         (see ROOT CAUSE below), so the const argument could not bind and the
         body was discarded.  Fixed in `cpp_convert_typet::read_rec`'s
         `ID_pointer` branch (recover the re-converted pointer's own
         cv-qualifiers); CORE `cpp11_deduce_const_funptr_member_template`.  A
         single `std::function<int(int)> f = &fn;` now verifies (no `_M_manager`
         no-body).  Historical investigation notes follow.

         `_M_manager`'s body conversion throws a *silent* `throw 0` (no
         diagnostic is emitted, `had_template_instantiation` is set, so a nested
         instantiation is involved); `convert_function`'s `catch(int)` for
         system-header bodies then nils it -> "no body for callee" at goto
         conversion.  Findings from instrumentation + cvise this session:
         * The earlier hypothesis -- that `convert_function`'s `sfinae_contextt`
           system-header guard (a null message handler) makes a nested
           instantiation spuriously fail via error-count desync -- is **wrong**.
           Disabling the null-handler swap globally (every `sfinae_contextt`)
           leaves `_M_manager` no-body; replacing the guard with
           `typecheck_method_bodies`-style error-count save/restore (real handler
           kept throughout) *also* leaves it no-body.  So the throw is NOT caused
           by the message handler.
         * The throw is **system-header-attribution dependent**: preprocessing
           with `#line` markers (bodies attributed to `/usr/include/...`,
           `is_system_header_body == true`) reproduces the no-body; stripping all
           markers (`is_system_header_body == false` everywhere) makes the same
           code convert and verify.  So a `/usr/include` source-location gate
           (one of `convert_function:703`, `cpp_typecheck.cpp:117` top-level
           item `sfinae_contextt`+`catch(...)`, `cpp_typecheck_template.cpp:764`
           "class template not found" silent `return`, or
           `cpp_typecheck_method_bodies.cpp:596`) is what flips behaviour --
           plausibly a *swallowed* partial conversion of a system-header item
           leaving state in which `_M_manager`'s body later throws, whereas the
           un-suppressed path converts fully.  Which gate, and why suppression
           makes a success into a failure, is not yet pinned.
         * The failure is NOT reproducible with header-free hand-models: the full
           `_M_manager` switch body (typeid / `_M_access<const TI*>` /
           `_M_access<F*>` / placement-new clone / pseudo-dtor destroy),
           real `typeid(int(*)(int))`, and the individual casts all convert and
           verify in isolation and combined.  It is a deep interaction in the
           real `std::function` instantiation context.
         * cvise on the preprocessed source does NOT isolate it: "no body for
           callee" is produced identically whether a method was never defined or
           had a definition that failed to convert (its symbol value is nil
           either way), and is not distinguishable via CBMC output or even
           g++ link (cvise reaches the trivial case via an indirect call through
           an uninitialised function-pointer member).  cvise instead converges on
           tangential system-header-attribution quirks.
         NEXT: bisect the `#line` markers on the preprocessed `sf.cpp` to find
         the minimal set whose presence triggers the throw (identifying the
         responsible system-header item / gate); and/or capture the exact origin
         of the silent `throw 0` (instrument the bare `throw 0` sites that fire
         while a flag set around `_M_manager`'s `typecheck_code` is active).

         Marker-bisection results (this session) narrow it to **cumulative
         system-header suppression of *other* headers**, not `_M_manager`'s own
         gate:
         * De-systemising every header *except* `std_function.h` (rewriting its
           `#line` markers off `/usr/include`) makes the same `_M_manager` body
           convert and verify.  So `convert_function`'s own system-header guard
           (`:703`) is NOT the trigger.
         * The trigger is a *set* of other headers (binary search is
           non-monotone: no single header reproduces it with `std_function.h`
           alone), i.e. the cumulative effect of suppressing many `namespace std`
           items.
         * It is NOT the item-level `sfinae_contextt` (the null/constant-expr
           guard): removing it from both the top-level path (`cpp_typecheck.cpp`
           `:117`) and the namespace path (`cpp_typecheck_namespace.cpp` `:123`,
           which is where `namespace std` items actually go) while keeping the
           surrounding `catch(...)` leaves the bug.  Each individual effect of
           `sfinae_contextt` was ruled out separately: disabling the null-handler
           swap in *every* `sfinae_contextt` (KSF) leaves it, and *not* zeroing
           `constant_expression_context` (KCE) leaves it.
         * No system-header item is actually thrown/swallowed: instrumenting the
           `catch(...)` of both the top-level and namespace system-header paths
           shows ZERO swallowed items for `sf.cpp`.  So it is NOT a
           partial-convert-then-swallow; every header item converts without
           throwing.  The only throw is `_M_manager`'s own body during
           instantiation (triggered from user `main`, not a system path).
         * RESOLVED (this session) via the symbol-table-diff next step: the
           location dependence was a *red herring at the surface*.  Diffing the
           system vs de-systemised runs (ddmin reduced the triggering system set
           to a single header, `bits/hashtable_policy.h`, alongside
           `std_function.h`) showed that de-systemising does NOT make
           `_M_manager` convert -- it makes `std::function` take a path that
           never instantiates `_M_manager` at all (B's "success" is degenerate).
           The real bug is independent of attribution: **`_M_manager`'s body
           throws whenever it is actually instantiated.**  gdb (`catch throw if
           g_mmgr==1`) caught the throw at `cpp_typecheck_resolvet::resolve`,
           inside a switch-case function call; instrumenting the throw sites
           pinned it to the `if(all_templates) throw 0;` heuristic in `resolve`
           (the silent "every remaining candidate is a function template ->
           treat as SFINAE" path -- hence no diagnostic).  The failing call is
           the `__clone_functor` case's `_M_init_functor(__dest,
           *const_cast<const _Functor*>(_M_get_pointer(__source)))`.

         ROOT CAUSE (precise, this session): deducing a function template
         parameter from a **`const`-qualified function-pointer argument** loses
         the `const` while building the deduced *reference* parameter.
         `_M_init_functor` is `template<class _Fn> void(_Any_data&, _Fn&&)`;
         the argument is a `const _Functor` lvalue (`_Functor` a function
         pointer), so per N5008 [temp.deduct.call]/3 `_Fn` deduces to
         `const _Functor&` and the parameter is `const _Functor&`.  The const is
         present immediately after deduction/substitution but is dropped during
         `typecheck_type` of the deduced reference parameter (verified:
         `#constant` count 1 pre-`typecheck_type`, 0 post), so the parameter
         becomes `_Functor&` (a non-const lvalue reference).  A `const`-pointer
         argument cannot bind a non-const lvalue reference, so the sole
         (template) candidate is rejected by overload resolution; during the
         elaboration of an instantiated member body the `all_templates`
         heuristic then silently throws, niling the enclosing body
         (`_M_manager`).  Confirmed minimal trigger matrix: const + (substituted
         class-template-parameter) pointer is required (non-const works; a
         non-pointer `const int` works; a *concrete* `const FP` works -- only the
         deduced/substituted const-pointer-reference parameter loses the const).
         The loss is NOT the reference-collapse step (skipping it does not help)
         -- it is deeper inside `typecheck_type`/`cpp_convert` of the deduced
         const-pointer reference; the exact line is not yet pinned.

         TEST: committed minimal **header-free, non-vacuous** KNOWNBUG
         `regression/cbmc-cpp/cpp11_deduce_const_funptr_member_template` (a
         class-template member calling a function template with a const
         function-pointer argument -> "no body for callee").  Flip to CORE once
         the deduced const-qualified function-pointer reference parameter keeps
         its const.

         FIXED: the dropped `#constant` was in `cpp_convert_typet::read_rec`'s
         `ID_pointer` branch -- re-converting an already-converted pointer pushed
         it to `other` without recording its own top-level cv-qualifiers, so the
         trailing `c_qualifiers.write` (is_constant=false) stripped the const
         ([dcl.ptr], [basic.type.qualifier]).  Recovering the pointer's
         cv-qualifiers there makes the deduced parameter `const _Functor&` keep
         its const, the const argument binds, the candidate is accepted, and the
         body is no longer niled.  `sf.cpp` (single-arg `std::function`) now
         verifies; both regression suites pass.
     `cpp17_functional_basic` / `cpp11_function_basic` (`std::function<int(int,
     int)> f = add; f(3,4)`) are now **non-vacuous KNOWNBUGs**.  They were
     previously CORE but passed only VACUOUSLY -- at baseline the multi-arg
     converting constructor failed to resolve ("found no match for symbol
     'function'") and even a deliberately wrong assertion held.  With layer 1
     fixed the constructor resolves; single-argument `std::function` invokes
     correctly and soundly, but the multi-argument path hits **layer 3**.
  - **Layer 3: multi-argument `_Function_handler<R(A...), F>` handler wiring.**
     Decomposed into two sub-roots:
     - **3a. pack expansion in a member function-pointer type (FIXED, CORE).**
       The `_M_invoker` data member of `function<_Res(_ArgTypes...)>` has type
       `_Res(*)(const _Any_data&, _ArgTypes&&...)`.  `template_mapt::apply`
       recursed into the pointer's pointee but did not expand the class pack
       `_ArgTypes&&...` in its parameter list before substituting, collapsing a
       multi-argument signature's invoker pointer to one parameter; the
       correctly-arity'd `&_Function_handler<_Res(A...),F>::_M_invoke` then could
       not be assigned, so the converting constructor body silently failed to
       elaborate (no body).  Fixed in `apply` (expand_parameter_packs on a
       (frontend_)pointer pointee before substituting), N5008 [temp.variadic]/5.
       CORE `cpp11_variadic_pack_in_member_funptr_type`.
     - **3b. pack-expansion use of a parameter pack in a method body (KNOWNBUG,
       NEXT).** With 3a fixed the converting constructor wires up the invoker
       with the correct arity, but the `operator()` body
       `_M_invoker(_M_functor, std::forward<_ArgTypes>(__args)...)` expands the
       pack to a single argument.  Root: for a member of a partial-spec class
       `C<R(A...)>`, the parameter pack is expanded during instantiation by
       `template_mapt` (struct-body `expand_parameter_packs`), which -- unlike
       the in-class `compound_type` path -- neither renames the replicated
       parameters to `base$k` nor records `#expanded_param_packs`, so the
       method-body drain in `cpp_typecheck_method_bodies` has nothing to drive
       the body-use expansion.  KNOWNBUG `cpp11_variadic_pack_in_method_body_call`
       (header-free, non-vacuous).  Fix direction: have the `template_mapt`
       expansion follow the `base$k` rename + `#expanded_param_packs` recording
       convention (or have the method-body drain derive the counts from the
       deduced class pack).
  The dog-food `make_bvrep` files remain blocked on layer 3b (multi-arg
  `std::function` body pack expansion); single-arg `std::function` construction
  *and invocation* are now sound (layers 1, 2a/2b/2c-i/2c-ii, 3a fixed).

Net: the trailing-return decltype is fully handled across pack shapes -- a
type-pack nested inside a reference, a value-pack with no type-pack reference,
and an empty (N == 0) deduced pack -- via the shared `expand_call_argument_packs`
plus the empty-pack recording in deduction (so the result both elaborates in
deduction and propagates through instantiation).  The unified `expand_pack`
primitive remains a worthwhile *consolidation*.  The remaining `std::function`
work is the two layers above: (1) partial-spec pack deduction in the
disambiguation path (fix identified, gated), and (2) `std::function` internal

Net: the trailing-return decltype is fully handled across pack shapes -- a
type-pack nested inside a reference, a value-pack with no type-pack reference,
and an empty (N == 0) deduced pack -- via the shared `expand_call_argument_packs`
plus the empty-pack recording in deduction (so the result both elaborates in
deduction and propagates through instantiation).  The unified `expand_pack`
primitive remains a worthwhile *consolidation*.  The remaining `std::function`
work is the two layers above: (1) partial-spec pack deduction in the
disambiguation path (fix identified, gated), and (2) `std::function` internal
member-template body propagation to the goto model (the actual `make_bvrep`
blocker).
