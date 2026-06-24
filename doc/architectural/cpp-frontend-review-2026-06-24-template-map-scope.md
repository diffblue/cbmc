# C++ Front-End Conformance Review: `template_mapt` and Instantiation Context

Date: 2026-06-24
Scope: `src/cpp/template_map.{h,cpp}` (the template-argument binding map) and its
use as the per-instantiation binding/substitution mechanism in
`cpp_instantiate_template.cpp` and `cpp_typecheck_resolve.cpp`.  Standard
reference: **N5008**.  Bracket tags are the stable `[...]`; parenthesised
numbers are the N5008 section numbers.

This review prepares a **structural change**.  It maps the machinery to the
clauses it is meant to implement, pins the one architectural rule it violates,
and scopes the change with its blast radius and a migration path.  It does not
itself change behaviour.

## The recurring symptom

Across several debugging sessions one failure shape keeps reappearing: a
template parameter (very often a **parameter pack**) of one template
instantiation is bound to a value that belongs to a *different* template
instantiation that happens to be live at the same time.  Recent concrete
instances:

- `std::get<0>(t) = x` (tuple write) fails because `__get_helper<0>`'s trailing
  pack `_Tail` is sized `{int}` instead of empty — the `int` is the enclosing
  `get`'s element pack `_Elements` (regression
  `cpp11_tuple_get_write_reference`, KNOWNBUG).
- The historical `_Tp leaking` and same-named-parameter notes already in the
  code (see Workarounds below).

The common denominator is **parameter identity**.

## How `template_mapt` represents bindings

`template_mapt` (`template_map.h`) is four **flat** maps keyed by `irep_idt`:

```cpp
std::map<irep_idt, typet>              type_map;       // type parameters
std::map<irep_idt, exprt>              expr_map;       // non-type parameters
std::map<irep_idt, std::size_t>        pack_size_map;  // sizeof...(Pack)
std::map<irep_idt, std::vector<typet>> pack_args_map;  // pack elements
```

There is a single process-wide instance (`cpp_typecheck.template_map`).  Nested
and sibling instantiations are handled by `cpp_saved_template_mapt`, which
saves the whole map **by copy** on entry and restores it on exit — so while an
inner instantiation runs, the outer instantiation's entries remain present in
the same flat maps.

## Conformance map

| Clause (N5008) | Rule | Code site | Status |
|---|---|---|---|
| `[basic.scope.temp]`/2 (6.4.9) | Each template-declaration introduces its **own** template parameter scope; *"only template parameters belong to a template parameter scope."*  A parameter's identity is its (scope, name) — same-named parameters of different templates are **distinct entities**. | Keys are `irep_idt`s that are scope-qualified (`template::N::Name`), which *could* encode identity correctly. | **PARTIAL** — the keys encode scope, but resolution does not respect it (next rows). |
| `[basic.scope.temp]`/2 | (as above) | `template_mapt::lookup(id)` — exact-key `std::map::find`. | **IMPLEMENTED** — exact identity. |
| `[basic.scope.temp]`/2 | (as above) | `template_mapt::lookup_by_suffix(suffix)` and ~10 resolution sites in `apply()`/`build()` that match a parameter by its **short name** (`rfind("::")`, `substr(p+2)`) across the whole flat map (e.g. `template_map.cpp` lines 43, 55, 140, 448, 698, 736, 762, 809, 887; `lookup_by_suffix` at 1048). | **VIOLATED** — short-name matching conflates same-named parameters of unrelated templates. See Violation V1. |
| `[temp.point]`/1 (13.8.4.1) | The point of instantiation of a specialization referenced from a dependent context is that of the enclosing specialization; instantiation happens in a definite context. | `cpp_saved_template_mapt` save/restore by copy; one shared flat map. | **PARTIAL** — bindings are not isolated per instantiation; outer/sibling entries coexist and are reachable by the short-name match of V1. See Violation V2. |
| `[temp.variadic]`/5,8 (13.7.4) | A type parameter pack binds an element list; `sizeof...` is its count. | `build()` pack block; `apply()` pack expansion; `pack_args_map`/`pack_size_map`. | **IMPLEMENTED** for the in-scope pack; but the *which-pack* selection uses short-name match (V1). |
| `[temp.arg.explicit]`/4 Note 1 (13.10.2) | A trailing parameter pack not otherwise deduced is the empty sequence. | `build()` `pack_count = nargs - non_pack`. | **PARTIAL** — `build()` is faithful to its input arg count; it is over-fed a spurious trailing argument by the assembly path when V1/V2 let another pack's element through.  (This is the proximate cause of the tuple-write KNOWNBUG.) |
| `[temp.res]` (13.8.3) two-phase | A dependent name's referent is fixed by the parameter's identity, bound at the template's point of definition. | Parameter references in bodies are stored as bare `cpp_name`s and resolved late by short name. | **VIOLATED indirectly** — because references carry only the short name, resolution must guess the scope (V1). |

## Violations

### V1 — Parameter identity by spelling, not scope ([basic.scope.temp]/2) — ROOT

`lookup_by_suffix` and the ~10 `apply()`/`build()` short-name match sites resolve
a parameter reference `Name` by scanning the flat map for **any** entry whose
identifier ends in `::Name`.  Per [basic.scope.temp]/2 a parameter's identity is
its template's scope plus its name; two templates may legitimately each have a
parameter spelled `_Tp` (or `_Tail`, `_Elements`, …) and they are different
entities.  Short-name matching cannot tell them apart, so when two
instantiations are live (V2) it can bind a reference in template A to template
B's value.

The code already **documents** this and patches it twice:

- `apply()` `#tmpl_param_shadow` marker (`template_map.cpp` ~253–298): *"`apply`'s
  short-name matching would bind the top-level body reference to an unrelated
  enclosing parameter of the same name (e.g. `std::decay<_Tp>`'s `_Tp` leaking
  into `std::__conditional<C>::type`)."*
- `build()` shadow-removal loop (`template_map.cpp` ~1133–1184): *"`apply`'s
  short-name suffix-match can return the outer binding when an inner same-named
  parameter exists … wrong substitutions for nested instantiations of unrelated
  class templates that happen to share parameter names."*

These are **symptom patches** (hide same-named outer entries while an inner
instantiation runs); they do not establish scope identity, and they do not
cover cross-template bleed where the names differ but the assembly still routes
one pack's element into another's slot (the tuple-write case).

### V2 — No per-instantiation isolation ([temp.point]/1)

One flat map shared across all live instantiations, saved/restored by copy,
means an inner instantiation sees the outer's entries.  Combined with V1's
short-name resolution, the outer entries are reachable and substitutable.  A
conforming model gives each instantiation its own parameter frame; lookups
resolve only within the current frame (and explicitly captured enclosing
class-template arguments, per [temp.point]/1), never by scanning all live
bindings.

## Scoped structural change

Goal: make parameter identity **scope-exact** and bindings **per-instantiation
isolated**, so V1/V2 are eliminated by construction and the shadow workarounds
can be deleted.

1. **Resolve only by full scope-qualified identifier.**  Every parameter
   reference in a template body/type must carry its full identifier
   (`template::N::Name`) by the time it reaches `template_mapt`.  This is the
   [temp.res] two-phase guarantee: the referent is fixed at definition time.
   Where references currently arrive as bare short-name `cpp_name`s, attach the
   scoped identifier during type-checking of the template definition (the
   parser/`cpp_scopes` already assign scoped ids to the parameters themselves).

2. **Delete `lookup_by_suffix` and the ~10 short-name match sites**; replace
   with exact-key `lookup`.  Once (1) holds, the suffix fallbacks are dead and
   unsound and can be removed, along with the `#tmpl_param_shadow` marker and
   the `build()` shadow-removal loop.

3. **Isolate per-instantiation bindings.**  Replace the single shared flat map
   (saved/restored by copy) with a **stack of frames**, one per active
   instantiation, each holding only that instantiation's parameters plus an
   explicit link to the enclosing class-template arguments it legitimately
   depends on ([temp.point]/1).  `lookup` searches the current frame (then the
   explicit enclosing link), never the union of all live bindings.

### Blast radius and migration

- High: `template_mapt` is used by essentially every template instantiation and
  substitution path (`cpp_instantiate_template.cpp`, `cpp_typecheck_resolve.cpp`,
  `cpp_typecheck_expr.cpp`, conversions).  The four maps and `apply()`/`build()`
  are load-bearing for all of `regression/cbmc-cpp`.
- Migration is best done in dependency order and gated at each step against
  both suites (`cbmc-cpp -X libcxx`, `cbmc`):
  1. Ensure parameter references carry full scoped ids (additive; assert in a
     debug build that every key looked up by suffix is also found by exact id —
     this *measures* how often the suffix fallback actually fires before
     removing it).
  2. Switch each short-name site to exact-id lookup, one at a time, gating.
  3. Remove `lookup_by_suffix` and the shadow workarounds.
  4. Replace the shared map with the frame stack; convert
     `cpp_saved_template_mapt` users to push/pop frames.
- A useful intermediate safety net: keep `lookup_by_suffix` but make it
  `INVARIANT`-check that the suffix match is unique among live bindings; any
  ambiguity is exactly a V1 bleed and pinpoints the remaining sites that still
  rely on short names.

### Why this fixes the recurring bug

The tuple-write KNOWNBUG is *related* to V1/V2 (a trailing pack acquiring an
element it should not have), but **migration step 1's measurement corrected the
mechanism** — see the next section.

## Migration step 1 result (2026-06-24): measure suffix reliance

Step 1 (measure how often short-name resolution actually fires, before removing
it) was executed on the flagship reproducer
`cpp11_tuple_get_write_reference`.  Result, with instrumentation on the V1
sites:

- **`lookup_by_suffix` is never called** during the reproducer.
- The bleed does **not** flow through a short-name/suffix resolution at all.

Tracing the actual mechanism (gdb backtrace + per-stage instrumentation):

1. In `get<0>`'s body the call `__get_helper<__i>(__t)` has **one** explicit
   template argument (`<__i>`).
2. `typecheck_template_args` turns it into **two** arguments
   `[__i=0, _Tail=unassigned]` — it materialises the trailing parameter pack as
   a single **unassigned placeholder** rather than the **empty sequence**
   required by [temp.arg.explicit]/4 Note 1.
3. Across the defer/finalise path for this (variadic) function template
   (`guess_function_template_args` eagerly instantiates variadic templates,
   unlike the deferred non-variadic path), that placeholder is finalised to
   `int`, so `template_mapt::build` receives `[0,int]`, computes
   `pack_count = nargs - non_pack = 1`, and sizes `_Tail = {int}`.
4. `__get_helper<0>`'s parameter therefore becomes the **primary**
   `_Tuple_impl<0,int,int>` (no `_Head_base` base) instead of the partial
   specialization `_Tuple_impl<0,int>`, so the inherited `_M_head`
   derived-to-base call fails and `get<0>` is left bodyless.

**Conclusion / scope correction.**  The scope-identity migration (V1/V2) is a
genuine and worthwhile conformance fix — the documented `_Tp leaking` bleeds DO
flow through short-name resolution — but it would **not** by itself fix the
tuple-write bug, whose root is a distinct **[temp.arg.explicit]/4 violation**: a
trailing parameter pack that is neither explicitly specified nor deduced must be
the empty sequence, and the representation of "empty trailing pack" is lost
between `typecheck_template_args` and the variadic instantiate/finalise path
(the `variadic_pack_empty` truncation at `cpp_typecheck_resolve.cpp` ~6260 fixes
this for the *signature* path but not for the arguments passed to
`instantiate_template`).  This is a separate, narrower fix than the migration
and should be scoped as its own task: make a trailing pack with no
explicit/deduced argument the empty sequence on the instantiate path too (mirror
the existing signature-side truncation, or represent the empty pack explicitly
so `build` sizes it 0).

## Migration progress

### Increment 1 (2026-06-24): suite-wide suffix measurement + nearest-scope disambiguation — DONE (commit `b958b5fe73`)

Measurement across the whole `cbmc-cpp` suite (instrumenting `lookup_by_suffix`):

- **47322** calls (each after an exact scope-qualified `lookup` had already
  failed) — the suffix fallback is heavily load-bearing.
- **2326** of them are **ambiguous** (`nhits>1`): several live bindings share
  the short name, e.g. `std::__detail::template::1805::_Tp` vs
  `std::template::1837::_Tp`.  These are the latent Violation-V1 bleeds.
- The reference ids that fail exact lookup are themselves scope-qualified (e.g.
  `std::template::1335::_Tp`); they fail because the **same parameter is
  registered under a different instantiation scope-number**.  So the root that
  forces the fallback is a **scope-number inconsistency** between a parameter's
  declaration id and its use-site id ([temp.res] two-phase / [temp.point]).

Change made: `lookup_by_suffix` now takes the reference's full id and resolves
ambiguity to the **nearest enclosing scope** ([basic.scope.temp]/2) — the
candidate sharing the longest leading `::`-component path — instead of the
arbitrary first map entry.  Both suites pass.  This makes the 2326 ambiguous
cases conforming without removing the fallback.

### Prerequisite for removing the fallback (Increment 2, not yet done)

The 47322 exact-lookup failures must be eliminated first: a template
parameter's identifier at its **use site** (in a body/type) must equal its
identifier as **registered** in the map.  Today they differ by instantiation
scope-number, so exact `lookup` misses and the suffix bridge is taken.  Closing
this is the real V1 removal step and is a deeper change to template-parameter
scope-id assignment ([temp.res]); it has no failing regression test driving it
(the suite passes via the bridge), so it should be undertaken deliberately with
the debug-build uniqueness invariant (below) to catch any remaining ambiguity as
it is removed.

## How to use this map

Before changing any short-name match site, find its row/Violation above; a
change that moves a site from short-name to exact-id resolution is progress
toward V1's removal.  Do not add new short-name fallbacks; if a reference cannot
be resolved by exact id, the fix is to attach the scoped id upstream
([temp.res]), not to scan by spelling.
