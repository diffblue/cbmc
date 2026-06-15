# C++20 requires-expression / concept-evaluation support

Scope and implementation plan for evaluating C++20 `requires`-expressions and
concept-ids in CBMC's C++ front end, grounded in N5008.

## 1. Motivation

At `-std=c++20`/`c++23`, `std::string` does not work: `basic_string<char>`
elaborates to a *truncated* struct containing only its member typedefs (no data
members, no constructors), so every string operation fails overload resolution
(`invalid implicit conversion from 'char [3]' to 'struct basic_string'`), and a
BMC run can diverge.

Root cause (established by a goto-/symbol-table diff — see
`cpp-extern-template-member-instantiation.md` §13): `basic_string`'s
`reverse_iterator` / `const_reverse_iterator` member typedefs name
`std::reverse_iterator<iterator>`, whose C++20 definition
(`bits/stl_iterator.h:166`) is

```cpp
using iterator_concept
  = __conditional_t<random_access_iterator<_Iterator>,
                    random_access_iterator_tag,
                    bidirectional_iterator_tag>;
```

Forming `iterator_concept` requires evaluating the **concept-id**
`random_access_iterator<_Iterator>` to a constant `bool`. That concept (in
`bits/iterator_concepts.h`) is defined in terms of **`requires`-expressions**,
which CBMC does not evaluate. The evaluation throws, the failure is swallowed
by the system-header guards, and the throw abandons the rest of
`basic_string`'s class body.

Because the libstdc++ machinery is selected by the `__cpp_concepts` feature
macro, a tempting shortcut is to `-U__cpp_concepts` so the library falls back
to its pre-C++20 SFINAE/`void_t` detection idioms. This was tried and
**rejected**: it regresses existing C++20 concept tests (e.g.
`cpp20_array_basic`, `cpp20_compare_header` — 100 `--cpp20` + 21 `--cpp23`
tests exist) and, even with the front end unblocked, `std::string` still timed
out in BMC (see §7). The correct fix is to actually evaluate the concepts.

## 2. Standard grounding (N5008)

- **[expr.prim.req.general]/2** — "A requires-expression is a prvalue of type
  `bool` whose value is described below."
- **[expr.prim.req.general]/5** — substitution of template arguments into a
  requires-expression that forms invalid types/expressions *in the immediate
  context* of its requirements makes the requires-expression **evaluate to
  `false`**; it is *not* ill-formed. "Substitution and semantic constraint
  checking proceeds in **lexical order** and **stops** when a condition that
  determines the result is encountered." → maps directly to an SFINAE-guarded,
  short-circuiting conjunction.
- **[expr.prim.req.general]/4** — local parameters of a requires-expression
  (the requirement-parameter-list) have no linkage/storage/lifetime; they are
  notation only.
- **[expr.prim.req.simple/type/compound/nested]** — the four requirement kinds
  and their satisfaction:
  - simple `expr;` — satisfied iff `expr` is a valid expression.
  - type `typename T;` — satisfied iff the type-id is valid.
  - compound `{ expr } noexcept(opt) -> type-constraint;` — `expr` valid (and
    `noexcept` if requested), and `decltype((expr))` satisfies the
    type-constraint.
  - nested `requires constraint-expression;` — satisfied iff the
    constraint-expression is satisfied.
- **[temp.names]/9** — "A concept-id ... is a prvalue of type `bool` ...
  evaluates to `true` if the concept's normalized constraint-expression
  (13.5.3) is satisfied by the specified template arguments and `false`
  otherwise."
- **[temp.constr.constr]** — conjunction (`/2`), disjunction (`/3`), atomic
  constraints (`/13.5.2.3`); satisfaction is checked left-to-right with
  short-circuiting.
- **[temp.constr.atomic]/3** — substitution failure forming an atomic
  constraint's expression makes the constraint **not satisfied** (a soft
  failure), not an error.

The throughline: concept/`requires` evaluation is *exactly* SFINAE
well-formedness checking combined into a short-circuiting boolean. CBMC already
has the SFINAE primitive (`sfinae_contextt`).

## 3. Current state in CBMC

### Parser (`src/cpp/parse.cpp`)
- **requires-expression** (`rPrimaryExpr`, `case TOK_REQUIRES`, ~9880–10160):
  parses the optional requirement-parameter-list into a `#requires_params`
  sub-irep and builds an `and_exprt` chain of requirement nodes —
  `type_requirement` (with `ID_type_arg`), `simple_requirement`,
  `compound_requirement` (with `#constraint` naming the return-type concept),
  and nested `requires` expressions. Functional but **ad hoc**: several
  hand-rolled `lex.Save/Restore` branches and a final "skip unknown
  requirement" fallback that silently drops requirements it cannot parse.
- **concept definition** (~1388): `template<...> concept Name = constraint;` is
  parsed as `constexpr bool Name = constraint;` (constraint via `rExpression`,
  so a requires-expression body is parsed by the case above).
- **requires-clause** in a template-head (~1418): if the constraint parses as a
  conditional-expression followed by a declaration-start token it is stored as
  `ID_C_requires_clause`; **otherwise the fallback skips the tokens and stores
  only a constraint *count*** — so requires-expressions used directly in a
  requires-clause (`template<class T> requires requires(T x){ x+x; }`) are not
  evaluated.

### Evaluator (`src/cpp/cpp_instantiate_template.cpp`, ~1283–1540)
A reasonably complete, SFINAE-guarded, standard-cited requirement evaluator
already exists, but **only inside partial-specialization selection**:
- evaluates a specialization's `ID_C_requires_clause` via `typecheck_expr`
  under `sfinae_contextt` + `simplify`, treating a `false` result as
  "specialization not viable" ([temp.constr.atomic]/3);
- evaluates per-parameter `#C_concept_constraint`s by looking up the concept,
  building a `template_mapt` for the concept's parameter, materialising
  `requires_param::<name>` symbols for the requirement-parameter-list, and
  `visit_pre`-evaluating `type_requirement` / `simple_requirement` /
  `compound_requirement` nodes and nested concept-ids — each guarded by
  `sfinae_contextt`.

### The gap
There is **no general, reusable routine** that, given a concept-id `C<Args>` or
a requires-expression, returns a constant `bool`, callable wherever a
concept-id appears as a **value**:
- as a non-type (`bool`) **template argument** — the `__conditional_t<
  random_access_iterator<_It>, …>` case that breaks `basic_string` (primary
  target);
- in `static_assert` (confirmed today: `static_assert(HasPlus<int>)` with a
  `requires`-based concept ⇒ CONVERSION ERROR);
- in `if constexpr`;
- in a requires-clause that the parser currently skips.

## 4. Design

Introduce one reusable evaluator and call it from the value contexts above.

```
std::optional<bool>
cpp_typecheckt::evaluate_constraint(const exprt &constraint,
                                    const template_mapt &arg_map);
```

- `constraint` is either a concept-id reference, a requires-expression
  (`and_exprt` of requirement nodes with `#requires_params`), or a boolean
  combination thereof.
- The routine substitutes `arg_map`, then evaluates **left-to-right with
  short-circuiting** ([expr.prim.req.general]/5, [temp.constr.constr]):
  - conjunction/disjunction → recurse with short-circuit;
  - atomic boolean expression → `typecheck_expr` + `simplify` under
    `sfinae_contextt`; on substitution failure ⇒ `false` (not error);
  - `type_requirement` / `simple_requirement` / `compound_requirement` /
    nested → exactly the existing per-kind checks, lifted out of the
    specialization-selection code into this routine;
  - concept-id `C<Args>` → look up the concept, build its `template_mapt`,
    recurse on its constraint-expression ([temp.names]/9).
- Returns `std::nullopt` only when the constraint is genuinely
  non-templated-and-invalid (→ ill-formed per [expr.prim.req.general]/5 Note 1);
  callers in templated contexts treat that as `false`.

This is a refactor-and-generalise of existing code, not a green-field
implementation; the per-requirement semantics are already written and cited.

## 5. Implementation steps (each gated by the full `cbmc-cpp` suite)

1. **Extract** the requirement-kind evaluation from
   `cpp_instantiate_template.cpp` into `evaluate_constraint` (+ a
   `requires_param::` symbol-scope RAII helper). Re-point the existing
   specialization-selection call sites at it. Expected: no behavioural change;
   full suite stays green. (Pure refactor — safest first step.)
2. **Evaluate concept-ids / requires-expressions as constant `bool` values.**
   In the constant-expression / non-type-template-argument path
   (`cpp_typecheck_expr.cpp` constant folding, and template-argument
   typechecking in `cpp_typecheck_template.cpp`), when the operand is a
   concept-id or requires-expression, call `evaluate_constraint` and replace it
   with the resulting `bool` constant. This is the step that lets
   `__conditional_t<random_access_iterator<_It>, …>` form, unblocking
   `basic_string`'s `reverse_iterator` typedefs. Add `static_assert` and
   `if constexpr` as additional call sites.
3. **Harden the parser** for the requirement forms actually used by
   `bits/iterator_concepts.h` (compound requirements with `noexcept` and
   nested `same_as`/`convertible_to` return-type constraints, parameter packs
   in the requirement-parameter-list). Replace the "skip unknown requirement"
   fallback with a hard parse error under a debug flag so unhandled forms are
   visible rather than silently dropped.
4. **requires-clause evaluation:** parse the full constraint-expression in the
   template-head (not just count it) and feed it to `evaluate_constraint` for
   constraint checking and (later) subsumption-based partial ordering
   ([temp.constr.order]).
5. **Validation** (see §6): bottom-up concept tests, then the iterator concept
   chain, then `std::string` at cpp20/23.

## 6. Validation strategy

- **Unit-style regression tests** (STL-independent, user-level concepts),
  bottom-up so failures localise:
  - each requirement kind (`simple`/`type`/`compound` with and without
    `noexcept` and return-type constraint / `nested`);
  - concept-id as: `static_assert`, `if constexpr` condition, non-type
    (`bool`) template argument to a `__conditional_t`-like alias, and
    requires-clause;
  - short-circuit / substitution-failure-is-`false` behaviour
    ([expr.prim.req.general]/5): a requirement that would be ill-formed for the
    argument must yield `false`, not an error;
  - a hand-written `random_access_iterator`-shaped concept chain over a pointer
    and over a class iterator.
- **Library milestone:** `std::reverse_iterator<std::string::iterator>` and the
  `basic_string<char>` reverse-iterator typedefs elaborate; `basic_string<char>`
  regains its data members and constructors at cpp20/23 (check the symbol
  table has constructor components, not just typedefs).
- **String milestone:** `std::string s("ab")`, `s = "ab"`, fill `(n,c)`,
  element access at cpp20/23 — first that the **front end** succeeds
  (no CONVERSION ERROR), then that BMC verifies (subject to §7).
- **No regressions:** full `cbmc-cpp` suite (`-X libcxx`) across
  cpp11/14/17/20/23; the 100 `--cpp20` + 21 `--cpp23` tests must stay green;
  cpp11–17 unaffected. `git-clang-format --binary clang-format-15` clean.

## 7. Risks and the BMC-performance caveat

- **Front end necessary but maybe not sufficient.** When the front end was
  unblocked experimentally (`-U__cpp_concepts`), `basic_string<char>`
  elaborated fully (≈315 goto functions) but even `std::string s;` then
  **timed out in BMC**. The C++20 libstdc++ string is `constexpr`-heavy and its
  member bodies (e.g. `_S_allocate` with `std::__is_constant_evaluated()` /
  `std::construct_at`, `if constexpr` branches) appear to stress symex. So a
  separate **symex / `constexpr`-modelling** work item is likely required for
  cpp20/23 `std::string` to actually *verify*, even after concepts work. This
  plan should be sequenced expecting that follow-on.
- **Performance of evaluation.** Concept evaluation is recursive and can fan out
  (the iterator concept chain is deep). Memoise concept-id results per
  (concept, arguments) to avoid re-evaluation; bound recursion defensively.
- **Parser fragility.** The current hand-rolled requires-expression parser is
  the most likely source of silent wrongness; step 3's "no silent skip" change
  is important to surface gaps during development.
- **Soundness over convenience.** Treating an unevaluable constraint as
  satisfied (the current `catch(...) ⇒ satisfied` backward-compat behaviour in
  one path) can mask real `false` results and select wrong specializations;
  `evaluate_constraint` should distinguish "soft `false`" from "cannot model"
  and prefer the standard-mandated `false` in templated contexts.

## 8. Out of scope (separate items)

- Subsumption-based partial ordering of constraints ([temp.constr.order]) beyond
  the existing primary-template-level comparison.
- Concept template-template parameters ([temp.arg.template]/3.3).
- `std::ranges` / `<ranges>` (depends on far more of the concepts and the
  range adaptors).
- The cpp20/23 `std::string` BMC-performance work (§7), which is downstream and
  independent of the front-end concept evaluation delivered here.
