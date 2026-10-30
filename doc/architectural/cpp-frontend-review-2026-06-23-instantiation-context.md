\file

C++ Front-End Review (2026-06-23): function-template instantiation context — and a same-day correction

# C++ Front-End Review — function-template instantiation context

**Date:** 2026-06-23 (with a same-day correction, see §0)
**Scope:** `src/cpp/` — *when and in what context* a function-template
specialization is instantiated and *bound to a call* during body conversion.
**Parent document:** `doc/architectural/cpp-frontend-review.md` §3.2
([temp.deduct]/8 SFINAE context), §3.3 ([over.match] overload resolution /
target-type), §4.2 ([temp.point] POI).
**Standard anchor:** N5008 [temp.point]/1, [temp.inst]/1/5, [temp.deduct.call]/4.3.

This addendum isolates a single root cause behind a cluster of recently
investigated bugs that share the shape **"a templated construct degrades when
it is resolved while a function body is being converted, but not at the top
level."**

---

## 0. Resolution (2026-06-23, same day) — root cause found and fixed

**The defect is fixed.**  The root cause is *neither* definition instantiation
(the first draft's hypothesis, retracted in §0.1) *nor* a genuine
`main`-specific call-binding exemption (the second hypothesis, also wrong — see
below).  It is a **parameter-list corruption during instantiation**:

> When a function template with a trailing template parameter pack is
> instantiated with that pack **empty**, `instantiate_template`
> (`cpp_instantiate_template.cpp`) removed *every* parameter whose type merely
> **references the empty pack name anywhere** — including nested inside a
> template-argument pack expansion such as `Base<_Head, _Tail...> &__b`.  So
> `get_head<int>` was instantiated with an **empty parameter list**; the body's
> `__b` was then "symbol is unknown", and the call `get_head(__d)` had no
> parameter to bind to and was dropped (the function returned nondet).

Per **N5008 [temp.variadic]/7** ("when N is zero, the instantiation of the
expansion produces an empty list") only a *function parameter pack* — a
parameter declared with a top-level `...`, e.g. `_Tail... args` — expands to an
empty parameter list and is removed.  A parameter whose type merely *contains*
the empty expansion nested in a template-id (`Base<_Head, _Tail...>`,
`tuple<_Tail...>`) is a single parameter: the expansion collapses the argument
list (to `Base<_Head>` / `tuple<>`) but the parameter itself must be kept.

**Fix:** restrict the empty-pack parameter-removal predicate (three sites in
`instantiate_template`: the general function-template block, the constructor
block, and the local-pack block) to genuine function parameter packs (top-level
ellipsis on the declarator), dropping the over-broad "references the pack name
nested anywhere" (`refs_ep`/`has_ep`) test.  The nested empty expansion then
collapses correctly via the existing `template_mapt::apply`, yielding
`get_head<int>(Base<int>&)`.  Verified: the minimal repro
`regression/cbmc-cpp/cpp11_derived_to_base_pack_call_in_body` flips KNOWNBUG →
CORE and passes **non-vacuously** (a deliberately-wrong assertion FAILs); both
the `cbmc-cpp` and `cbmc` regression suites remain green.

### The "`main` exemption" was a vacuity artifact

The second-draft analysis (§3–§5 below) claimed the dropped call occurred for
every enclosing body *except* `main`'s.  That was an **unsound observation**:
the call was *also* dropped in `main`, but because the dropped call
`throw 0`-ed out of `main`'s own body conversion, the `catch(int)` /
`had_template_instantiation` path in `convert_method_body`
(`cpp_typecheck_method_bodies.cpp`) abandoned `main`'s body with `continue` —
**silently deleting `main`'s own `__CPROVER_assert`**, so verification reported
a *vacuous* SUCCESS.  Confirmed by replacing the assertion with a false one
(`a == 999`): it still "passed" before the fix (assertion absent from
`--show-properties`), and correctly FAILs after.  This is exactly the
unsound-vacuous-pass failure mode; it is the reason the apparent `main`
exemption was illusory.  The material below is retained for the record but is
superseded by this section.

---

## 0.1. Correction (2026-06-23, same day)

The first draft of this document (commit `dee203f711`) proposed that the root
cause was function-template *definitions* being instantiated **inline** at the
point of reference (`cpp_instantiate_template.cpp` ~5476 / ~4363), in violation
of the [temp.point]/1 point-of-instantiation model, and recommended routing
those definitions through the deferred `method_bodies` queue.

**That premise was wrong, and was retracted after instrumenting the drain.**
Function-template *definition* bodies are **already deferred**:

* `cpp_declarator_convertert` (`cpp_declarator_converter.cpp:780`) sends a
  non-template, non-`auto`, non-`macro`, non-`friend` function body to
  `add_method_body`.  An instantiated free function template (e.g.
  `std::get<0>`'s `__get_helper<0>`) is exactly such a function, so its body is
  queued, **not** converted inline at `:5476`.  A drain trace confirms the
  instantiated callee body (`helper<signed_int>()`) is processed in
  `typecheck_method_bodies`.
* The only definitions converted inline are `auto`-return ones (return-type
  deduction must precede call sites) and the eager `constexpr` member path
  (`:4363`, needed so a constexpr specialization used as a *constant* — an
  `enable_if` non-type argument, an array bound — folds during the enclosing
  type-check), which already falls back to `add_method_body` on failure.

So the deferred-queue POI approximation **already applies to definitions**, and
"route definitions through the queue" is a no-op.  The corrected analysis
below relocates the cause from *definition instantiation* (§4.2 POI) to *call
resolution / instance binding during body conversion* (parent review §3.2 /
§3.3).  The code annotations in `cpp_instantiate_template.cpp` and
`cpp_typecheck_method_bodies.cpp` were corrected to match.

---

## 1. The recurring shape and its evidence

Four header-free, independently-minimised reproductions from the
`std::tuple<int>` / `std::get<0>` work share one mechanism.  The cleanest is
`regression/cbmc-cpp/cpp11_derived_to_base_pack_call_in_body` (KNOWNBUG):

```cpp
template <typename...> struct Base;
template <typename _Head> struct Base<_Head> { _Head v; };
template <typename _Head, typename... _Tail>
_Head &get_head(Base<_Head, _Tail...> &__b) { return __b.v; }   // trailing pack
template <typename... _Elements> struct Derived : Base<_Elements...> {};
int wrapper(Derived<int> &__d) { return get_head(__d); }        // derived-to-base
```

`get_head(__d)` is a [temp.deduct.call]/4.3 derived-to-base call: `__d` is
`Derived<int>`, whose base `Base<int>` matches `Base<_Head, _Tail...>` with
`_Head = int`, `_Tail` empty.  In `wrapper`, this call is **dropped** — the
callee is instantiated but left unbindable, `wrapper` returns a nondet value.

### The discriminator (minimised `geth*` family + clean A/B/C tests)

| variant | result |
|---|---|
| the call directly in `main`'s body | **works** |
| the same call in *any other* function body (`wrapper`, `get3`, `prime`) | **fails** |
| by-value vs by-reference parameter | no effect (both fail outside `main`) |
| definition/queue drain order (`wrapper` before/after `main`) | no effect |
| add a **direct** call to the callee in `main`'s body | the other body's call then **works** |

Net: **the first instantiation of the callee via a derived-to-base call binds
correctly only when the referencing body is `main`'s; from any other body the
instance is left unbindable and the call is dropped.**  A direct reference to
the callee from `main` produces a correct, reusable instance, after which every
other body's call binds.  The `main`-specific exemption is the key open clue.

---

## 2. What the standard requires (for orientation)

* [temp.point]/1 / [temp.inst]/1: a *reference* needs only the *declaration*
  instantiated; the *definition* is instantiated at the POI.
* [temp.inst]/5: the definition is instantiated when referenced in a context
  requiring it.
* [temp.deduct.call]/4.3: when P is a class template-id and A is a derived
  class, the arguments are deduced from the base of A that is a specialization
  of P.

CBMC's `typecheck_method_bodies` deferred drain is a sound approximation of
the "POI at end of translation unit" model and is used for **both** member and
free function-template definitions (see §0).  The defect is therefore *not*
where definitions are instantiated.

---

## 3. What CBMC actually does (corrected)

1. **Definitions are deferred correctly.**  `instantiate_template` registers
   the specialization's declaration and queues its body; the drain converts it
   in a clean top-level context.  Verified by the drain trace.
2. **Call resolution happens *during* a body's drain.**  When `wrapper`'s body
   is drained, `get_head(__d)` is resolved there: overload resolution +
   [temp.deduct.call]/4.3 base-walk (`cpp_typecheck_resolve.cpp` ~4929) deduce
   `get_head<int>`, the callee declaration is instantiated, and the call
   expression is built and bound to it.
3. **The binding step is where it degrades.**  Outside `main`, the built call
   is discarded (the callee ends up unreferenced and is removed by clean-up)
   and the enclosing function returns nondet.  Inside `main`, the identical
   resolution binds.  The deduction itself succeeds in both (confirmed by an
   earlier base-deduction trace); what differs is whether the *call* is
   committed to the instantiated callee.

This places the defect in the parent review's §3.2 (immediate-context /
error-suppression state active during the drain) and §3.3 (overload-resolution
/ argument-conversion binding), **not** §4.2 (POI).  The `main` exemption
strongly suggests a difference in the suppression / scope / instantiation
state present while `main`'s body is drained versus another body's — e.g. a
`sfinae_contextt` or `suppress_elaborate` flag, or a `template_map` / scope
left active by the caller, that causes the freshly-built call to be treated as
a discardable probe rather than a committed call.

---

## 4. Which rules are implemented / violated / unimplemented (corrected)

| rule | status | site |
|---|---|---|
| [temp.point]/1, [temp.inst]/1/5 POI / deferred definition | **implemented** (approx.) for member **and** free fn templates | `typecheck_method_bodies`; `add_method_body` |
| inline definition only for `auto`/`constexpr` | implemented (with deferral fallback) | `cpp_declarator_converter.cpp:780`; `cpp_instantiate_template.cpp:4363` |
| [temp.deduct.call]/4.3 derived-to-base deduction | **implemented** (deduction succeeds) | `cpp_typecheck_resolve.cpp:~4929` |
| committing the *call* after a successful derived-to-base deduction during a (non-`main`) body drain | **violated** — call dropped / instance unbindable | call-resolution path under `typecheck_method_bodies` |
| [temp.deduct]/8 immediate-context delineation during body drain | suspect — suppression state appears to leak across the call build (parent §3.2) | resolve / conversion paths |

---

## 5. Recommendation (corrected)

Do **not** re-plumb definition instantiation (already deferred).  Instead:

1. **Find the `main`-specific difference in the drain/resolution state.**  The
   A/B/C and `geth*` tests reduce it to: "first derived-to-base instantiation
   of a callee with a trailing parameter pack, triggered from a non-`main`
   body, leaves the call unbound."  Instrument the call-build/commit step
   (`typecheck_side_effect_function_call` → resolve → the function_call
   construction) for the failing body and compare the active
   `sfinae_contextt` / `suppress_elaborate` / scope / `template_map` state to
   `main`'s.  The most likely culprit is an error/elaboration-suppression flag
   that is *not* lifted for non-`main` body drains, so the built call is
   silently dropped.
2. **Fix the binding, not the definition.**  Once the leaking flag/state is
   identified, the fix is local (lift the suppression for the committed call,
   or stop discarding a successfully-built call).
3. This connects to parent review §3.2 (formal SFINAE-context propagation):
   the recurring guards' "immediate context" is not being lifted when the body
   drain commits a real call.

### Definition of done

* `cpp11_derived_to_base_pack_call_in_body` flips KNOWNBUG → CORE.
* `std::tuple<int>` + `std::get<0>` verify non-vacuously.
* Both regression suites green; dog-food not regressed.

---

## 6. Status

This document is now an accurate map of the defect's *location* (call binding
during body drain, `main`-exempt) and an explicit retraction of the
definition-instantiation hypothesis.  The `main`-specific exemption is the next
concrete lead; it is reproduced minimally and header-free by
`cpp11_derived_to_base_pack_call_in_body` and the `geth*` / A-B-C tests in the
investigation log.
