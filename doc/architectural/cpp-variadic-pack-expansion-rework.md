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

Phases 1–4 are largely independent; Phase 5 depends on 0+2+3.

---

## 5. Test strategy

Header-free, minimal, one gap per test (already committed):

* KNOWNBUG: `cpp11_variadic_empty_pack_call`, `cpp11_variadic_qualified_id_pack`,
  `cpp11_variadic_sizeof_static_init`, `cpp11_decltype_pack_in_class_template`.
* CORE guard: `cpp11_variadic_pack_expansion_works` (must never regress).
* End-to-end KNOWNBUG: `cpp20_vector_erase_if` (flips at Phase 5).

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
