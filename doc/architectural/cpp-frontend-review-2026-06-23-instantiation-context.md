\file

C++ Front-End Review (2026-06-23): function-template instantiation context / point of instantiation

# C++ Front-End Review — function-template instantiation context

**Date:** 2026-06-23
**Scope:** `src/cpp/` — *when and in what context* a function-template
specialization's **definition** is implicitly instantiated.
**Parent document:** `doc/architectural/cpp-frontend-review.md` §4.2
(point-of-instantiation, marked "ad hoc / long term").
**Standard anchor:** N5008 [temp.point]/1, [temp.point]/8, [temp.inst]/5,
[temp.deduct.call]/4.

This is a focused addendum to the May-13 architectural review.  It
isolates a *single* root cause behind a cluster of recently-investigated
bugs that all share the shape **"a templated construct resolved while
converting a function body behaves differently (degraded) than the same
construct resolved at the top level."**  The May review names this axis
(§4.2 POI) but defers it to long-term work; the evidence below argues it
is the proximate cause of the current `std::tuple` blockers and is worth
promoting.

---

## 1. The recurring shape

Four independently-minimised, header-free reproductions, all from the
`std::tuple<int>` / `std::get<0>` work, share one mechanism:

| repro / test | symptom | standard rule mis-applied |
|---|---|---|
| `std::tuple<int> t{42}` ctor SFINAE (`cpp11_constexpr_*` arc) | a candidate's constexpr constraint `make_constant`-fails in a *committed* context during overload resolution instead of being a silent substitution failure | [temp.deduct]/8 immediate context, but **reached** via nested instantiation |
| `cpp11_get_bytype_overload_skip` (fixed `20551a9dde`) | a by-type `get<T>(pair)` candidate's kind mismatch aborts the *whole* overload set | [temp.arg]/2, [temp.deduct]/8 |
| `cpp11_derived_to_base_pack_call_in_body` (KNOWNBUG `1b70c07870`) | a derived-to-base call with an empty trailing pack, **first instantiated from within a function body**, drops the call → callee returns nondet | [temp.deduct.call]/4.3 |
| `std::get<0>` body | `get<0>`'s own definition fails to convert (no body) when instantiated inline during `main`'s body conversion | [temp.point]/1, [temp.inst]/5 |

The minimisations established the discriminator precisely (see the
KNOWNBUG test's `geth*` family in the investigation log):

* The same call/instantiation **succeeds** when it is the *first* thing a
  **top-level** function body does (e.g. directly in `main`), and
  **fails** when it is *first* triggered from a **nested, on-demand**
  body conversion (a callee body converted while converting its caller).
* Pre-instantiating the callee with a top-level direct call makes the
  nested call subsequently succeed (the nested path then reuses the
  already-correct instance).

In other words: the *deduction* is correct; what differs is the
**context in which the callee's definition is instantiated**.

---

## 2. What the standard requires

### [temp.point]/1 — point of instantiation (POI)

> For a function template specialization, a member function template
> specialization, or a specialization for a member function or static
> data member of a class template, if the specialization is implicitly
> instantiated because it is referenced from within another template
> specialization, ... the point of instantiation of the enclosing
> specialization.  Otherwise, the point of instantiation for such a
> specialization immediately follows the namespace scope declaration or
> definition that refers to the specialization.

### [temp.point]/8 — instantiation context

> A specialization for a function template ... may have multiple points
> of instantiation within a translation unit ... the instantiation
> context ... is the union of [the definition context and] the
> [context at] every point of instantiation.

### [temp.inst]/5 — when the *definition* is instantiated

> Unless a function template specialization is a declared specialization,
> the function template specialization is implicitly instantiated when
> the specialization is referenced in a context that requires a function
> definition to exist ...

**Net rule:** the *definition* of a function-template specialization is
instantiated **at a point that immediately follows the enclosing
namespace-scope declaration/definition** that referenced it — i.e. at
namespace scope, in the full translation-unit context, **not** spliced
into the middle of the referencing function's body.  A reference from
inside `main`'s body to `std::get<0>` makes `main`'s POI (end of the
namespace-scope definition of `main`) the place where `get<0>`'s
*definition* is instantiated.

---

## 3. What CBMC does

### 3.1 The deferred queue *is* an approximate POI model

`cpp_typecheckt::typecheck()` runs the namespace-scope `convert` loop and
*then* `typecheck_method_bodies()` (`cpp_typecheck.cpp:204`).  The latter
drains `method_bodies` with `while(!method_bodies.empty())`
(`cpp_typecheck_method_bodies.cpp:105`) — so a body added to the queue
while another body is being converted is processed in a *later* iteration
of the same top-level loop, in a clean context.  This is, in effect, a
"POI at end of translation unit" model, and it is **correct**.  Class
member-function template specializations reach it via `add_method_body`.

### 3.2 Function templates bypass the queue and instantiate inline

`cpp_typecheckt::instantiate_template` converts a **free** function
template specialization's *definition* synchronously, inline, via
`convert_non_template_declaration(new_decl)`
(`cpp_instantiate_template.cpp:5476`), and a **constexpr member** function
template specialization's *definition* via an eager `convert_function(ws)`
(`cpp_instantiate_template.cpp:4363`).  Because `instantiate_template` is
itself called from `typecheck_side_effect_function_call` →
`resolve` → `guess_function_template_args` **while converting the
referencing body**, this instantiates the *definition* in a **nested**
context — exactly what [temp.point]/1 says must instead happen at the
enclosing namespace-scope POI.

### 3.3 Why "nested" is degraded

The nested context differs from the top-level POI context in ways that
break the four reproductions:

* **Error/elaboration suppression is active.**  Nested instantiation runs
  under `suppress_elaborate`, `sfinae_contextt`, or the error-count
  save/restore guards (May review §3.2).  A definition-conversion failure
  that should be a hard, attributed error (or simply should not happen in
  this context at all) is instead swallowed, leaving a no-body stub or a
  dropped call (the `cpp11_derived_to_base_pack_call_in_body` symptom).
* **Class/lazy elaboration is partial.**  Per the May review §3.1
  ([temp.inst]/3), member types are resolved on demand; mid-body the
  enclosing instances may be only partially elaborated, so a
  derived-to-base or constraint lookup that the end-of-TU context would
  satisfy fails now.
* **Scope and `template_map` state is the caller's, not the callee's
  POI.**  The nested conversion inherits whatever scope/`template_map` the
  caller's body left active, rather than the clean namespace-scope state a
  real POI would present.

The May review already documents each individual contributor (§3.1 lazy
elaboration, §3.2 SFINAE context, §4.2 POI).  The new observation here is
that they **compound specifically at the function-template definition
instantiation point**, and that routing that instantiation through the
existing deferred queue (§3.1 above) would put it in the one context where
all three are already correct.

---

## 4. Which rules are implemented / violated / unimplemented

| rule | status in CBMC | site |
|---|---|---|
| [temp.point]/1 POI for member-fn-template specializations | **approximated** by the deferred `method_bodies` queue | `cpp_typecheck_method_bodies.cpp:105`, `add_method_body` |
| [temp.point]/1 POI for **free** function-template specializations | **violated** — definition instantiated inline at the reference, not at the enclosing namespace-scope POI | `cpp_instantiate_template.cpp:5476` |
| [temp.point]/1 POI for **constexpr** member-fn-template specializations | **violated** — eager inline `convert_function` at the reference | `cpp_instantiate_template.cpp:4363` |
| [temp.point]/8 instantiation context = union over POIs | **not implemented** — only the immediate nested context is available | (whole-TU notion absent) |
| [temp.inst]/5 definition instantiated when referenced | implemented (the reference triggers it) but **at the wrong point** (§3.2) | as above |
| [temp.inst]/3 lazy member declarations vs definitions | partial; see May review §3.1 lazy-elaboration plan | `typecheck_compound_body` |
| [temp.deduct]/8 immediate context | implemented via `sfinae_contextt`; but **the suppression leaks into definition instantiation** done in the same nested scope (§3.3) | resolve / instantiate paths |
| [temp.deduct.call]/4.3 derived-to-base deduction | implemented (`guess_template_args` base walk, `cpp_typecheck_resolve.cpp:~4929`) but the **call it feeds is built in the degraded nested context** | KNOWNBUG `cpp11_derived_to_base_pack_call_in_body` |

---

## 5. Recommendation

Promote the §4.2 POI item from "long term" to a concrete, bounded change
that is the function-template analogue of the §3.1 lazy class-body work:

**Route every function-template *definition* instantiation through the
deferred `method_bodies` queue, instead of converting it inline.**

* `instantiate_template` should register the specialization's
  *declaration* (signature) eagerly — that is all a *reference* needs
  ([temp.inst]/1) and all overload resolution needs — and `add_method_body`
  the *definition* for the top-level drain, rather than calling
  `convert_non_template_declaration` / `convert_function` inline at
  `cpp_instantiate_template.cpp:5476` / `:4363`.
* The drain loop (`typecheck_method_bodies`) already provides the clean
  end-of-TU POI context; extending it to free and constexpr function
  templates means their bodies convert there, not nested.
* This subsumes the recurring symptoms: the dropped derived-to-base call,
  the no-body `get<0>`, and the committed-context constraint failures all
  stem from converting the definition in the nested context.

### Risks / caveats

* **constexpr needs the value during the enclosing type-check.**  A
  constexpr function-template specialization used as a non-type template
  argument or array bound must be *foldable now*, so its definition cannot
  always be deferred.  The split is: defer the *runtime* definition
  (GOTO body); fold the *constant* value eagerly via the evaluator, which
  already recurses through `typecheck_side_effect_function_call` directly
  (see the `non_constant_expression_contextt` comment in
  `cpp_typecheck.h`).  This is why §3.2's eager `convert_function(ws)` at
  `:4363` exists; the fix must preserve constant-folding while deferring
  the body.
* This is a structural change to a hot path; it must be gated exactly like
  the lazy-elaboration plan (CORE + KNOWNBUG + both regression suites +
  dog-food delta per commit).

### Definition of done

* `cpp11_derived_to_base_pack_call_in_body` flips KNOWNBUG → CORE.
* `std::tuple<int>` + `std::get<0>` verify non-vacuously (a wrong-value
  assertion FAILs).
* No new inline `convert_non_template_declaration` / `convert_function`
  for a function-template *definition* inside `instantiate_template`
  reachable from `guess_function_template_args`.
* Both suites green; dog-food not regressed.

---

## 6. Relationship to existing plans

This does **not** supersede the lazy class-body elaboration plan
(`cpp-frontend-plan-lazy-elaboration.md`); it is its function-template
sibling and shares the same end-state (resolve definitions at a clean
use-point context, attribute failures to the use site).  Both are facets
of giving CBMC a real [temp.point] model.  Sequencing: this change is
smaller and unblocks the `std::tuple` line item, so it is a good first
concrete step toward the §4.2 POI work the May review deferred.
