# C++ Front-End Conformance Review: Template Argument Deduction & Instantiation

Date: 2026-06-23
Scope: the template **argument-deduction**, **parameter-pack**, and
**instantiation** subsystem of `src/cpp/` — the part of the front-end that has
proven most regression-prone. Standard reference: **N5008** (working draft).
Clause tags below are the stable `[bracket.tags]`; the parenthesised section
numbers are the N5008 numbering.

## Why this review exists

Most of the deduction/instantiation code grew empirically: a branch handles the
cases that were observed to fail, with no recorded mapping to the rule it is
meant to implement. That makes change risky — when a branch is altered to fix
one case, there is no way to tell whether the change corrects a genuine
deviation from the standard or breaks an unstated invariant another clause
relies on. This document records, for the load-bearing sites, **which clause
each block implements** and **where the implementation deviates from or omits a
rule**, so that future changes can be checked against the standard rather than
only against the regression suite.

Status legend: **IMPLEMENTED** / **PARTIAL** / **MISSING** / **VIOLATED**.

## Re-investigation update (2026-06-23, later)

The gap claims below (G1, G2, G3) were first derived from a single fragile,
cvise-reduced reproducer (`cpp11_nested_function_template_no_body`).  A
follow-up investigation built minimal, header-free, single-feature reproducers
for each and validated them against g++.  The results **revise** the original
claims and are authoritative:

- **G1 (trailing pack → empty): NOT an independently-reproducible defect.**
  Every clean reproducer of "a trailing parameter pack not otherwise deduced"
  verifies correctly in CBMC — including `sizeof...(EmptyPack) == 0`, and a
  pack used in a qualified-id body (`Impl<I,int,Tail...>::member`).  The
  truncation in `guess_function_template_args` (`variadic_pack_empty`,
  `args.resize(i)`) already implements [temp.arg.explicit]/4.  The `_Tail`
  mis-sizing seen in the fragile reproducer arises only from its specific
  multi-feature confluence (two overloads + SFINAE + dependent return type),
  not from a general trailing-pack defect.
- **G2 (empty pack expansion in a body qualified-id): NOT independently
  reproducible** either — the same clean reproducer above exercises exactly
  this and passes.
- **G3 (concept subsumption): the substring heuristic is genuinely unsound,
  but it is NOT the operative cause of wrong concept-overload selection.**  A
  minimal reproducer (`cpp11_concept_more_constrained_overload`, g++ returns 1,
  CBMC returns 2) shows the real defect is one level earlier: two
  concept-constrained overloads with otherwise-identical signatures collide on
  a single instance symbol, so only one candidate ever reaches disambiguation
  and the subsumption *ordering* code never runs.  A correct fix needs both
  (a) such overloads forming a proper overload set, and (b) real subsumption
  ordering per [temp.constr.order]/1 (prescribed in G3 below).

Net: the deduction subsystem is more conformant than the original single-repro
review implied; the remaining concrete, reproducible defect is concept-overload
set formation + ordering (G3').

## Conformance map

| Clause (N5008) | Rule (paraphrase) | Code site | Status |
|---|---|---|---|
| `[temp.deduct]`/2 (13.10.3) | Deduction starts from a clean slate: parameters being deduced have no prior assignment. | `template_mapt::build_unassigned` (`template_map.cpp`) — sets each param `ID_unassigned` and erases `pack_args_map`/`pack_size_map`. | **IMPLEMENTED** (annotated) |
| `[temp.deduct.type]`/3,8–11,14 (13.10.3.6) | Structural deduction by decomposing `T&`, `T*`, `T[N]`, function types, `A<T>`, cv-qualified types. | `guess_template_args` (`cpp_typecheck_resolve.cpp` ~4684). | **IMPLEMENTED** (well-annotated, one decomposition case per branch) |
| `[temp.arg]`/2 + `[temp.deduct]`/8 | A kind mismatch (value supplied for a type parameter, etc.) when applying explicit args to an unrelated overload is a SFINAE failure removing only that candidate. | `apply_template_args` (`cpp_typecheck_resolve.cpp` ~81), `template_arg_kind_mismatch_exceptiont`. | **IMPLEMENTED** (annotated) |
| `[temp.deduct]`/3,8 | Substitution failure while deducing a candidate is SFINAE (discard candidate, no error). | `guess_function_template_args` per-candidate loop, `sfinae_contextt`. | **IMPLEMENTED** (annotated) |
| `[temp.func.order]` + `[temp.deduct.partial]` (13.7.7.3 / 13.10.3.5) | Partial ordering of function templates by deduction. | `cpp_typecheck_resolve.cpp` ~1304–1496. | **IMPLEMENTED** (annotated) |
| `[temp.variadic]`/5,8 (13.7.4) | A type parameter pack binds an element *list*; `sizeof...` yields the element count. | `template_mapt::build` pack block (`template_map.cpp` ~1220–1265): `pack_args_map`/`pack_size_map`, plus a `type_map` convenience entry for 1-element packs. | **IMPLEMENTED** |
| `[temp.variadic]`/10 (13.7.4) | When `N == 0`, instantiating a pack expansion produces an empty list and does not change the enclosing construct. | Base-specifier arg lists: `cpp_typecheck_bases.cpp` (empty-pack base drop); and the `variadic_pack_empty` truncation in `guess_function_template_args`. | **IMPLEMENTED** (revised) — clean reproducers of an empty pack expansion in a body qualified-id verify correctly; see Re-investigation update (was provisionally G2). |
| `[temp.arg.explicit]`/4, Note 1 (13.10.2) | A **trailing** template parameter pack **not otherwise deduced** is deduced as an **empty sequence**. | `guess_function_template_args` (`variadic_pack_empty` truncation) + `build_unassigned` clean slate. | **IMPLEMENTED** (revised) — clean reproducers verify correctly; not an independent defect.  See Re-investigation update (was provisionally G1). |
| `[temp.constr.order]` (13.5.4) / `[temp.constr.*]` | Constraint subsumption determines the more-constrained candidate. | `guess_function_template_args` concept filter; overload set formation/instantiation. | **VIOLATED** (revised) — but the operative defect is concept-overload **set formation** (colliding instances), not the subsumption test alone.  See Gap G3' and `cpp11_concept_more_constrained_overload`. |

## Gaps and deviations

### G1 — `[temp.arg.explicit]`/4 Note 1: trailing pack → empty (REVISED: not an independent defect)

> **Revised:** see the Re-investigation update above.  Clean, header-free
> reproducers of this rule verify correctly; the mechanism (`variadic_pack_empty`
> truncation) is in place.  The text below documents the rule and the fragile
> reproducer in which a `_Tail` mis-sizing was *originally* observed, which is now
> attributed to that reproducer's multi-feature confluence rather than to a
> general trailing-pack defect.

Normative text (N5008 [temp.arg.explicit]/4, Note 1):

> *A trailing template parameter pack (13.7.4) not otherwise deduced will be
> deduced as an empty sequence of template arguments.*

The standard's own Example 2 is the exact shape that breaks here:

```cpp
template<class X, class Y, class ... Z> X g(Y);
int k = g<int>(5.6);   // Y deduced as double; Z deduced as an empty sequence
```

CBMC reproduces this as `__get_helper`:

```cpp
template <int __i, typename... _Tail>
int &__get_helper(_Tuple_impl<__i, int> __t)        // _Tail occurs ONLY in the body
{ return _Tuple_impl<__i, int, _Tail...>::_M_head(__t); }
```

For `__get_helper<0>` (`__i` explicit, `_Tail` neither specified nor deducible
from the parameter), `_Tail` must be the empty sequence. `build_unassigned`
clears `_Tail` from the pack maps, so the empty default is only **implicit** —
it holds only if nothing later supplies an argument for `_Tail`. When this call
is resolved from *within* an enclosing instantiated body (`get<0>`, whose own
element pack has size 1), the assembled argument list passed to
`template_mapt::build` carries one **spurious** trailing element, so
`build` computes `pack_count = nargs - non_pack = 1` and records
`pack_size_map[_Tail] = 1` with a phantom element in `pack_args_map[_Tail]`.

`build` itself is faithful to its input — the defect is **upstream**, in the
assembly of the explicit+deduced argument list: a trailing pack left
unassigned after deduction is not pinned to the empty sequence before the count
is taken.

Downstream effect: resolving the body qualifier `_Tuple_impl<__i, int,
_Tail...>` then tries to expand a one-element `_Tail...` that has no bound
element type; resolution throws, the deferred method-body drain silently nil's
the body, and the callee is left bodyless (`no body for callee
__get_helper<0>`) and returns a nondet reference — an **unsound** vacuous pass.

- Regression: `regression/cbmc-cpp/cpp11_nested_function_template_no_body`
  (KNOWNBUG, commit `8bc5643c44`).
- Fix locus: the function-template argument assembly that feeds
  `template_mapt::build` (in `guess_function_template_args` /
  `instantiate_template`) must force any **trailing** parameter pack that
  remains `ID_unassigned` after deduction to a zero-length sequence
  *before* the argument count is taken, so an enclosing instantiation's pack
  cannot bleed in an extra element.

### G2 — `[temp.variadic]`/10: empty pack expansion in a body qualified-id (REVISED: not an independent defect)

> **Revised:** see the Re-investigation update above.  A clean, header-free
> reproducer of an empty pack expansion in a body qualified-id
> (`Impl<I,int,Tail...>::member` with `Tail` empty) verifies correctly, so this
> is not an independent defect.  The note below is retained for context.

The `N == 0` collapse is implemented for **base-specifier** argument lists and,
for a function body's qualified-id, via the `variadic_pack_empty` truncation in
`guess_function_template_args` (which removes the empty pack before the
qualifier is built).  A clean reproducer of `C<..., Pack...>::member` with an
empty `Pack` verifies correctly.  A localised attempt to *additionally* drop
such arguments during `typecheck_expr_cpp_name` was found to be confounded by
same-named packs across distinct templates (the short-name suffix match cannot
disambiguate `X::Pack` from `Y::Pack`); since the existing truncation already
handles the clean cases, that extra collapse is unnecessary and was not added.

### G3' — concept-overload selection: set formation + subsumption ordering (VIOLATED, reproducible)

Reproducer: `regression/cbmc-cpp/cpp11_concept_more_constrained_overload`
(header-free; g++ returns 1, CBMC returns 2).

```cpp
template <typename T> concept Cheap = sizeof(T) >= 1;
template <typename T> concept Rare = sizeof(T) >= 1000;
template <typename T> concept CheapOrRare = Cheap<T> || Rare<T>;
template <Cheap T>       int f(T) { return 1; } // more constrained
template <CheapOrRare T> int f(T) { return 2; } // less constrained
// f(0): Cheap subsumes Cheap||Rare, so f<Cheap> must win -> 1.
```

Two related issues, in order of operative importance:

1. **Overload-set formation (the operative defect).**  The two overloads have
   otherwise-identical signatures `f(T) -> int` and their `int` instantiations
   collide on a single instance symbol `f<signed_int>(signed_int)`.
   Instrumentation shows only **one** candidate ever reaches
   `disambiguate_functions` (`in=1`), so no ordering decision is made — CBMC
   simply uses whichever overload survived.  Fixing this requires
   concept-constrained overloads with the same signature to form a proper
   overload set (e.g. carry the constraint into the instance identity, as
   `function_template_identifier` already does for the *template* symbol).

2. **Subsumption ordering (the textual heuristic).**  Even once a set forms,
   the ordering used `string containment` of constraint names:

   ```cpp
   if(id2string(cj).find(id2string(ci)) != std::string::npos && ci != cj)
     subsumed[i] = true;
   ```

   This is unsound and incomplete vs [temp.constr.order]/1.  The correct
   algorithm (verified by hand on the reproducer) is: normalise each constraint
   to atomic constraints by expanding nested concept references through
   `&&`/`||`; `P subsumes Q` iff every disjunctive clause of `DNF(P)` shares an
   identical atomic with every conjunctive clause of `CNF(Q)`
   ([temp.constr.atomic]).  Then candidate `i` is dominated by `j` iff
   `constraint(j)` subsumes `constraint(i)` but not vice versa.  Worked example:
   `DNF(Cheap)={{Cheap}}`, `CNF(Cheap||Rare)={{Cheap,Rare}}` → `Cheap` subsumes
   `Cheap||Rare`; the converse fails on the `{Rare}` clause, so `Cheap` is
   strictly more constrained and `f<Cheap>` wins.

   A prototype of this ordering (a `constraint_subsumes` helper plus a
   subsumption pass in `disambiguate_functions`) was implemented and validated
   in isolation, but **shelved** because issue (1) prevents both candidates from
   reaching the ordering step; landing the ordering alone would be dead code.
   Both halves are required to flip the KNOWNBUG to CORE.

## Notes on sites that are already conformant

- `guess_template_args` ([temp.deduct.type]) is the strongest-annotated area:
  each decomposition branch already names its sub-clause. No change needed.
- `build_unassigned` correctly implements the [temp.deduct]/2 clean-slate rule
  *including* clearing the pack maps, which is what prevents a recursive
  variadic partial specialization (`And<B1, Bn...> : ... && And<Bn...>`) from
  inheriting the enclosing instance's pack. This is load-bearing — do not
  remove the pack-map erase.
- The `#ifdef DEBUG std::cout` in `guess_template_args` is compile-time gated
  and is not a diagnostic leak.

## How to use this map when changing the deduction code

1. Before editing a branch, find its row above and read the cited clause in
   N5008. If the branch has no row, add one (clause + status) as part of the
   change.
2. Prefer fixes that make a **named** rule hold (e.g. G1: enforce
   [temp.arg.explicit]/4) over fixes that patch a single observed symptom.
3. After the change, re-confirm the IMPLEMENTED rows still hold via the
   regression suite; a regression there usually means a load-bearing invariant
   (like the [temp.deduct]/2 pack-map erase) was disturbed.
