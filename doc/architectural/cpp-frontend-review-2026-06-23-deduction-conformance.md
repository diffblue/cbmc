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

## Conformance map

| Clause (N5008) | Rule (paraphrase) | Code site | Status |
|---|---|---|---|
| `[temp.deduct]`/2 (13.10.3) | Deduction starts from a clean slate: parameters being deduced have no prior assignment. | `template_mapt::build_unassigned` (`template_map.cpp`) — sets each param `ID_unassigned` and erases `pack_args_map`/`pack_size_map`. | **IMPLEMENTED** (annotated) |
| `[temp.deduct.type]`/3,8–11,14 (13.10.3.6) | Structural deduction by decomposing `T&`, `T*`, `T[N]`, function types, `A<T>`, cv-qualified types. | `guess_template_args` (`cpp_typecheck_resolve.cpp` ~4684). | **IMPLEMENTED** (well-annotated, one decomposition case per branch) |
| `[temp.arg]`/2 + `[temp.deduct]`/8 | A kind mismatch (value supplied for a type parameter, etc.) when applying explicit args to an unrelated overload is a SFINAE failure removing only that candidate. | `apply_template_args` (`cpp_typecheck_resolve.cpp` ~81), `template_arg_kind_mismatch_exceptiont`. | **IMPLEMENTED** (annotated) |
| `[temp.deduct]`/3,8 | Substitution failure while deducing a candidate is SFINAE (discard candidate, no error). | `guess_function_template_args` per-candidate loop, `sfinae_contextt`. | **IMPLEMENTED** (annotated) |
| `[temp.func.order]` + `[temp.deduct.partial]` (13.7.7.3 / 13.10.3.5) | Partial ordering of function templates by deduction. | `cpp_typecheck_resolve.cpp` ~1304–1496. | **IMPLEMENTED** (annotated) |
| `[temp.variadic]`/5,8 (13.7.4) | A type parameter pack binds an element *list*; `sizeof...` yields the element count. | `template_mapt::build` pack block (`template_map.cpp` ~1220–1265): `pack_args_map`/`pack_size_map`, plus a `type_map` convenience entry for 1-element packs. | **IMPLEMENTED** |
| `[temp.variadic]`/10 (13.7.4) | When `N == 0`, instantiating a pack expansion produces an empty list and does not change the enclosing construct. | Base-specifier arg lists: `cpp_typecheck_bases.cpp` (empty-pack base drop). | **PARTIAL** — handled for base-specifier argument lists; **not** handled for an empty pack expansion appearing in a **qualified-id's template-argument list inside a function body** (e.g. `_Tuple_impl<__i, int, _Tail...>::_M_head`). See Gap G2. |
| `[temp.arg.explicit]`/4, Note 1 (13.10.2) | A **trailing** template parameter pack **not otherwise deduced** is deduced as an **empty sequence**. | The argument list assembled for an explicitly-but-partially specialized function template before `template_mapt::build`. | **VIOLATED** — see Gap G1. |
| `[temp.constr.order]` (13.5.4) / `[temp.constr.*]` | Constraint subsumption determines the more-constrained candidate. | `guess_function_template_args` concept filter (`cpp_typecheck_resolve.cpp` ~150–175). | **PARTIAL / APPROXIMATED** — see Gap G3. |

## Gaps and deviations

### G1 — `[temp.arg.explicit]`/4 Note 1: trailing pack not forced to empty (VIOLATED)

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

### G2 — `[temp.variadic]`/10: empty pack expansion in a body qualified-id (PARTIAL)

The `N == 0` collapse is implemented for **base-specifier** argument lists but
not for an empty pack expansion that appears in a **qualified-id's
template-argument list inside a function body** (`C<..., Pack...>::member`).
Once G1 is fixed so `_Tail` is correctly empty, the qualifier should collapse
to `_Tuple_impl<__i, int>` per [temp.variadic]/10; a general collapse of
empty-pack expansion arguments during name resolution (not only at base
specifiers) would make this robust. A localised attempt to drop such arguments
during `typecheck_expr_cpp_name` was found to be confounded by same-named packs
across distinct templates (the short-name suffix match cannot disambiguate
`X::Pack` from `Y::Pack`), which is itself a symptom of G1 mis-sizing the pack —
so G2 should be revisited only after G1 is corrected.

### G3 — `[temp.constr.order]`: concept subsumption is a textual approximation (PARTIAL)

The C++20 "prefer the more-constrained candidate" filter compares constraints by
**string containment**:

```cpp
if(id2string(cj).find(id2string(ci)) != std::string::npos && ci != cj)
  subsumed[i] = true;
```

This is a heuristic, not the normative subsumption of [temp.constr.order] (which
decomposes constraints into atomic constraints and tests implication). It
happens to order simple cases where one constraint's identifier is a substring
of another, but it is neither sound nor complete: unrelated constraints whose
spellings share a substring would be wrongly ordered, and genuinely subsuming
constraints with different spellings would not be. Marked as a known
approximation; a faithful implementation requires normalising constraints to
atomic-constraint form and testing implication.

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
