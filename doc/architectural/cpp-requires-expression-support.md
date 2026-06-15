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

---

## 9. Implementation findings (2026-06, first pass)

A first implementation pass refined the gap analysis and is recorded here so
the next pass starts from facts rather than re-derivation. No source change was
kept (the tree is at the §-8 baseline); the findings below are the deliverable
of this pass.

### What already works vs. fails (clean baseline, `--cpp20`)

Minimal user-level probes (no STL):

| probe | construct | result |
|---|---|---|
| type requirement | `requires { typename T::inner; }` via `static_assert` | **works** |
| simple requirement | `requires(T a){ a + a; }` via `static_assert` | fails: `symbol 'a' is unknown` |
| compound requirement | `requires(T a){ { ++a } -> SameAs<T&>; }` | fails: `symbol 'a' is unknown` |
| concept-id as bool template arg | `cond<HasPlus<T>, …>` | fails: `symbol 'a' is unknown` |

So `type_requirement` (no requirement-parameters) is fine; **every requirement
that references a requirement-parameter fails uniformly with `symbol '<param>'
is unknown`**, in *all* value contexts (`static_assert`, non-type bool template
argument, etc.). The earlier belief that the template-argument context "worked"
was a stale-binary reading; it does not.

### Precise root cause

The error is raised **while instantiating the concept** (the diagnostic is
`instantiating 'HasPlus' with <signed int> … symbol 'a' is unknown`). A concept
is a `constexpr bool` **variable template**; evaluating `HasPlus<int>`
instantiates that variable template and type-checks its initializer (the
requires-expression). At that point the requirement-parameter-list
(`#requires_params`, e.g. `a`) is **not materialised into a scope/symbol**, so
the requirement expressions that mention `a` fail name lookup.

The existing requirement evaluator in `cpp_instantiate_template.cpp` (the
partial-specialization-selection path) *does* materialise `#requires_params`
before evaluating, which is why constraints attached to partial specializations
work — but the **variable-template-body evaluation path does not**, and that is
the path used for a concept-id used as a value.

### What was tried, and the confirmed-working approach

1. Added `simple_requirement` / `compound_requirement` handlers to
   `typecheck_expr_main` (mirroring the existing `type_requirement` handler and
   the partial-spec compound logic, SFINAE-guarded per [expr.prim.req.*]).
   Necessary, but not sufficient alone: the parameters must first be in scope.
2. Materialising `#requires_params` at the top of `typecheck_expr_main` did
   **not** work — the parameters must be bound in the scope in which the
   requirement sub-expressions are resolved during *variable-template
   instantiation*, not the scope current at the requires-expression node.
3. **Working approach (confirmed):** materialise `#requires_params` at the
   **variable-template instantiation site** — binding each parameter as a
   `requires_param::<name>` symbol in the instantiation `current_scope()`
   immediately before `convert_non_template_declaration(new_decl)` converts the
   concept body (the "Force elaboration during variable template body
   processing" block in `cpp_instantiate_template.cpp`) — **combined with** the
   `simple_requirement` handler from (1). With this, the user-level probes
   behaved as:

   | probe | result with (3) |
   |---|---|
   | `type_requirement` (`t_type`) | ✅ SUCCESSFUL |
   | `simple_requirement` (`t_simple`) | ✅ SUCCESSFUL (was `symbol 'a' unknown`) |
   | concept-id as bool template arg (`t_condarg`) | ✅ SUCCESSFUL |
   | `compound_requirement` `{++a}->SameAs<T&>` (`t_compound`) | ❌ wrongly `false` |
   | concept that must be **false** (`t_false`) | ❌ CONVERSION ERROR (should be `false`) |

   So simple requirements, type requirements, and concept-ids-as-values now
   evaluate correctly. **Two correctness bugs remain and are load-bearing for
   the iterator concepts:**
   - **Compound requirements** with a return-type-requirement mis-evaluate (the
     `{ E } -> C` return-type check returns `false` for a case that should be
     `true`). The iterator concepts are full of these
     (`{ i += n } -> same_as<I&>`), so this must be correct.
   - **A requirement that is invalid for the argument must make the concept
     evaluate to `false`, not raise an error.** `requires(int a){ a.foo(); }`
     produced `member operator requires struct/union type … got 'signed int'`
     (CONVERSION ERROR) instead of `false`. The SFINAE guard suppressed the
     *message* in some paths but this member-access error escaped — the soft-
     failure conversion of [expr.prim.req.general]/5 is not yet uniform.

4. **A partial landing is unsafe.** Building with (3) regressed exactly one
   existing test, `cpp20_ranges_basic`, from passing to an **invariant
   violation / core dump**: once concept evaluation is switched on, ranges'
   deep concept chain reaches a path the partial implementation does not handle
   and trips a CBMC invariant. The change was therefore **reverted** — concept
   evaluation must be completed end-to-end (correct compound requirements,
   uniform soft-failure, and robustness across the full concept chain) before
   it can land without regressing.

### Recommended next step (precise)

Land approach (3) but only together with the two fixes it exposed, validated
bottom-up:
- **Uniform soft-failure:** ensure *every* requirement-evaluation path converts
  a substitution/semantic failure to `false` ([expr.prim.req.general]/5). The
  `member operator requires struct/union type` error indicates a typecheck path
  that emits/escapes rather than throwing-and-being-suppressed under
  `sfinae_contextt`; route it (and similar member/operator-resolution errors)
  through the SFINAE soft-failure path, or wrap the whole requires-expression
  evaluation so any escape becomes `false`.
- **Compound requirement return-type check:** debug the `{ E } -> C` path so
  `decltype((E))` is formed correctly (value vs. lvalue → reference per
  [expr.prim.req.compound]/1) and `C<decltype((E)), …>` is evaluated through the
  same recursive concept evaluator (so nested `same_as`/`convertible_to`
  resolve), rather than the ad-hoc inline check.
- **Robustness:** guard the evaluator so an unhandled node/shape yields `false`
  (or a clean soft failure) rather than tripping an invariant — this is what
  `cpp20_ranges_basic` needs.

Validate against the four probes, a hand-written `random_access_iterator`-shaped
chain, and the full `cbmc-cpp` suite (especially `cpp20_*`) before touching the
libstdc++ headers.

### Standing caveat (unchanged)

Even once concept evaluation works, the C++20 `constexpr`-heavy libstdc++
`std::string` still timed out in BMC in the earlier experiment (§7). Front-end
concept support is necessary but likely not sufficient for cpp20/23
`std::string` to *verify*; budget the separate symex/`constexpr` work item.

---

## 10. Landed (2026-06, second pass)

The second pass **landed** the value-context concept evaluation for the
tractable requirement kinds, with no regressions (full `cbmc-cpp` suite green):

- **Requirement-parameter materialisation** at the variable-template
  instantiation site (`cpp_instantiate_template.cpp`, before
  `convert_non_template_declaration` converts the concept body), per
  [expr.prim.req.general]/4 — fixes the `symbol '<p>' is unknown` failure.
- **`simple_requirement` / `compound_requirement` handlers** in
  `typecheck_expr_main` (alongside the existing `type_requirement`), with
  `requirement_expression_is_valid` / `compound_requirement_is_satisfied`
  converting failures to a soft `false` ([expr.prim.req.general]/5) and
  restoring the error count (so a non-throwing diagnostic does not fail the TU).
- **Robustness guard** against a malformed (non-unary) requirement node, so an
  unmodelled requirement form no longer trips the `to_unary_expr` invariant —
  this is what previously **aborted `cpp20_ranges_basic`**; it now passes.

Now working: simple-requirements, type-requirements, and concept-ids used as
values (`static_assert`, non-type bool template argument, `if constexpr`).
Guarded by the CORE test `cpp20_concept_requires_eval`.

### Remaining blockers (precise)

1. **Compound-requirement return-type check** — **resolved** (commit:
   "pre-increment/decrement of arithmetic/pointer lvalue is an lvalue (C++)").
   `decltype((++a))` is now an lvalue-reference per [expr.pre.incr]/1, so
   `{ ++a } -> same_as<T&>` evaluates correctly (CORE test
   `cpp20_concept_compound_requirement`). The value-category fix currently
   covers pre-increment/decrement of arithmetic/pointer operands; other
   lvalue-yielding forms over **builtin** types (`i += n`, `j[n]`) should be
   audited similarly if a concept needs them, but `same_as<decltype((E)), …>`
   for the common forms now resolves.

2. **Class-type operator / member-call requirements soft-fail to `false`** —
   **resolved** (commit: "soft-fail invalid requirement expressions on
   class/member operations"; CORE test
   `cpp20_concept_requirement_soft_failure`). Root cause: the requirement-node
   handlers in `typecheck_expr_main` ran *after* the generic operand recursion
   in `cpp_typecheckt::typecheck_expr`, which type-checked the requirement's
   sub-expression (e.g. `a + a` on a class without `operator+`, or `a.foo()` on
   a non-class type) as ordinary code and emitted a hard diagnostic *before* the
   handler could soften it ([expr.prim.req.general]/5). Fix: intercept
   `simple_/compound_/type_requirement` nodes in the `typecheck_expr` dispatcher
   and route them straight to `typecheck_expr_main`, skipping the operand
   recursion, so the sub-expression is checked only under the SFINAE-guarded
   handler. With this, `Addable<NoPlus>` / `HasFoo<int>` correctly evaluate
   `false` instead of erroring, and the libstdc++ iterator-concept chain over
   `__normal_iterator` now progresses well past the previous truncation point
   (see (3)).

3. **Deep concept chain over class iterators** — **resolved** for the concept
   evaluation itself (commit: "bind requires-expression parameters for conjoined
   requires-expressions"; CORE tests `cpp20_concept_conjunction_requires_params`
   and `cpp20_concept_iterator_chain`). Root cause: a requires-expression that
   is only a *conjunct* of a larger constraint-expression — the shape of
   `std::assignable_from`, `std::movable`, `std::copyable`
   (`<concept-id> && requires(params){...}`) — carries its `#requires_params`
   on an inner node, but the instantiation-site materialisation only read the
   *top-level* value, so the parameters were never bound and the
   requires-expression evaluated to a spurious `false`
   ([expr.prim.req.general]/2). Fix: materialise the parameter-list of *every*
   requires-expression in the constraint-expression (visit the body), not just
   one at the top. With this, `assignable_from` / `movable` / `copyable`,
   `swappable`, and the full iterator hierarchy
   (`input_or_output`/`input`/`forward`/`bidirectional`/`random_access_iterator`)
   evaluate correctly over a user-defined class iterator — verified both true
   and false. Confirmed working over: a hand-written random-access class
   iterator; a faithful `__normal_iterator` mimic (namespace-scoped template
   wrapping a pointer, with the `enable_if` SFINAE converting constructor and
   `iterator_category` from `iterator_traits`); the `reverse_iterator<It>`
   adaptor; and the incomplete-container member-typedef pattern
   (`reverse_iterator<normal_iter<C*, Self>>` formed while `Self` is still being
   defined, as in `basic_string`). A constrained `operator()` with a
   *disjunctive* requires-clause (`requires A || B`, the `_Swap` CPO shape) also
   evaluates correctly (true and false). So the deep concept chain is no longer
   the blocker.

4. **Real cpp20/23 `std::string` still fails — but not due to a remaining
   concept-evaluation gap.** `std::string s("ab")` still ends with
   `invalid implicit conversion from 'char [3]' to 'struct basic_string'`,
   i.e. `basic_string<char>` does not acquire its `const char*` constructor.
   The instantiation trace runs the iterator-concept chain over
   `__normal_iterator` (driven additionally by the eagerly-processed
   `operator""s` literal operators for `char16_t`/`char32_t`) and reaches
   `swappable` → `std::ranges::swap` → `__adl_swap` before the conversion error.
   However, **none of the increasingly faithful standalone mimics reproduce the
   failure** — `random_access_iterator` and `reverse_iterator` over a
   namespace-scoped `__normal_iterator`-shaped template, the incomplete-container
   member typedef, the SFINAE converting constructor, and the disjunctive
   `operator()` requires-clause all evaluate correctly. This indicates the
   remaining failure is an *emergent interaction* in the full libstdc++
   `basic_string` elaboration (many headers, the explicit `char16/char32`
   instantiations, the complete instantiation graph), not an isolable
   front-end concept-evaluation bug. Reducing it needs a delta-debugged
   reduction from the actual headers rather than further bottom-up mimics.

5. **requires-clauses** (step 5 of §5) are still only counted in some contexts;
   constrained `operator()` requires-clauses (incl. disjunctions) *are* now
   evaluated for viability inside a requires-expression (see (3)).

## 11. Delta-debugged reduction from `<string>` (2026-06, fourth pass)

Rather than more bottom-up mimics (§10(4)), the cpp20 `std::string` failure was
attacked by delta-debugging the preprocessed `<string>` translation unit with
`cvise`, gated by an interestingness test that (a) requires `g++ -std=c++20
-fsyntax-only` to *accept* the file — so every reduction step stays valid C++
that g++ compiles but CBMC rejects — and (b) bans anonymous namespaces, which
`clang_delta` introduces by stripping the `std` name and which expose an
*unrelated* bug (CBMC fails to resolve a name declared in an unnamed namespace
at the enclosing scope, `namespace { class A; } A a;` → "symbol 'A' is unknown",
contrary to [namespace.unnamed]/1 — recorded here as a separate finding).

This produced a 13-line g++-valid repro and pinned down a precise, faithful
front-end bug, now **fixed** (commit "parse a qualified concept name as a
template type-constraint"; CORE test `cpp20_concept_qualified_constraint`):

   ```c++
   namespace std {
   namespace __detail { template<class _Tp> concept __dereferenceable = true; }
   template<__detail::__dereferenceable _Tp> using iter_reference_t = _Tp;
   template<class> struct basic_string {
     iter_reference_t<int> m; basic_string(wchar_t*, long); };
   basic_string<wchar_t> to_wstring();          // prior, declaration-context inst.
   }
   void op(){ std::basic_string<wchar_t>{&g_str, g_len}; }
   ```

   Root cause: a **qualified** concept name used as a type-constraint
   (`__detail::__dereferenceable _Tp`, the libstdc++ `iter_reference_t` shape,
   [temp.param]/4) was mis-parsed as a non-type parameter, because the parser
   only fell back to the type-constraint path via a fragile heuristic (parameter
   name reused as a type immediately after `>`), which fails for an alias
   template. Instantiating the alias then failed ("expected expression, but got
   type"); when the enclosing class was first instantiated in a
   *declaration context* (a function signature), the failure truncated the
   class and the truncated form was cached, so a later brace-construction fell
   back to aggregate initialisation and went out of bounds. Fix: track concept
   names and recognise a qualified concept constraint directly. Two essential
   ingredients were confirmed by bisection (qualified-vs-unqualified concept;
   with-vs-without the prior instantiation).

   The fix removes the `expected expression, but got type` diagnostics from the
   real `<string>` and is faithful to libstdc++ (`iter_reference_t` does use
   `__detail::__dereferenceable`).

### `std::string` is a multi-bug situation (current status)

The qualified-constraint fix did **not** fully unblock `std::string`:
`std::string s("ab")` still ends with the `char[3]` → `basic_string` conversion
error, and the g++-preprocessed TU still shows `member designator index 13 out
of bounds (struct has 13 components)` in the `char16_t`/`char32_t`
`operator""s`. These are **distinct** remaining causes that share the
truncation/aggregate-fallback symptom: brace-/paren-construction of
`basic_string<...>` is treated as aggregate initialisation rather than resolving
the `(const CharT*, size_type)` constructor (a class with user-declared
constructors is not an aggregate, [dcl.init.aggr]/1), when that constructor is
missing/unmatched. A simple base-class + constructor brace-init probe works, so
the trigger is more specific (template instance, constexpr constructor, or
list-init constructor matching) and needs its own delta-debugged reduction.
Each remaining manifestation is a separate reduction+fix unit.

## 12. Reduction campaign, second cause: partial-spec member access (open)

Continuing the campaign, the `member designator index N out of bounds` (the
`char16_t`/`char32_t` `operator""s`) manifestation was delta-debugged with the
same `cvise` + g++-validity pipeline to a minimal **g++-valid** repro, then
hand-minimised and bisected to a 7-line root cause (not cpp20-specific):

   ```c++
   template <typename> struct holder {};
   template <typename> struct base;                       // primary: declared
   template <typename T> struct base<holder<T>> { using cp = T; };   // partial spec
   typedef base<holder<int>>::cp X;   // CBMC: "symbol 'X' is unknown"; g++: OK
   X gv;
   ```

   This is the libstdc++ `allocator_traits<allocator<T>>` shape (a class-template
   partial specialization keyed on a **nested class-template-id**).  CBMC fails
   to use the partial specialization for `base<holder<int>>`, so the member
   typedef `cp` is not found.  In `std::string` this is reached via
   `__alloc_traits<...>::const_pointer` (the `const_iterator` member type): the
   typedef fails to resolve, which truncates `basic_string`, drops its
   constructor, makes it look like a POD/aggregate, and routes
   `basic_string{ptr, len}` to aggregate initialisation → member-designator OOB.

   **Mechanism, traced precisely** (`elaborate_class_template` /
   `cpp_instantiate_template.cpp`):
   1. Template-argument deduction for the partial specialization **succeeds** —
      `holder<T>` is matched against `holder<int>`, `T = int`
      (`guessed_args.has_unassigned()` is false).
   2. The subsequent **verification re-typecheck** of the partial-spec argument
      pattern — `typecheck_template_args(primary, [holder<T>])` — **throws**
      (`sfinae_failed`), so the specialization is rejected (`continue`) and
      `base<holder<int>>` silently falls back to the **incomplete primary**
      template, which has no `cp`.  The throw occurs whether or not
      `suppress_elaborate` is set, and even forcing `best_match` to the
      specialization on `sfinae_failed` did not produce `cp`, so the failure is
      deeper than the verification gate alone (the instantiation of the matched
      specialization for a nested-template-id key is itself not completing).
   This is grounded in [temp.class.spec.match]/2 (a partial specialization is
   used when its arguments can be deduced) — CBMC deduces but does not apply it.

   **Status: open.** The fix touches partial-specialization selection /
   instantiation (used pervasively), so it must be done carefully and gated on
   the full suite; a too-broad change to the verification regresses other
   partial-spec tests.  Minimal repros saved under `/tmp/red` during
   investigation: `m3e.cpp` (the 7-line core above), `mdB.cpp` (a 36-line
   `basic_string`-shaped reproduction through `__alloc_traits`/`rebind`).  When
   fixed, both become CORE regression tests (the qualified-constraint cause
   above is already guarded by `cpp20_concept_qualified_constraint`).

   **Deeper findings (2026-06, fix attempt).** The failure is
   *context-dependent*, which narrows it from "partial-spec matching is broken"
   to "instantiation during qualified-name resolution is broken":
   - `base<holder<int>> obj; obj.field;` (object), `base<holder<int>>::cp x;`
     inside a function body, and forcing a prior `base<holder<int>>` variable
     all **work** — the partial specialization is selected and instantiated
     (`ncomp` correct).  Only the namespace-scope qualified-name form
     `typedef base<holder<int>>::cp X;` fails.
   - Traced in `elaborate_class_template` (`cpp_instantiate_template.cpp`): in
     the working contexts the partial-spec **verification re-typecheck**
     (`typecheck_template_args` of the spec's argument pattern) succeeds; in the
     failing context it throws a silent `throw 0` (deduction itself has already
     succeeded — `guessed_args.has_unassigned()` is false).
   - Even making the verification throw non-fatal (selecting the spec on the
     successful deduction, per [temp.class.spec.match]/2) does **not** fix it:
     the subsequent `instantiate_template(spec)` is entered with no unassigned
     arguments but **also throws** while elaborating the specialization body,
     leaving `base<holder<int>>` complete-but-empty (cached), so the member
     typedef is still absent.
   - So *two* layers throw in the qualified-name-resolution context that do not
     throw when the same type is named in a declaration; the root is how
     instantiation is driven during qualified-name resolution for a
     nested-template-id key, not the partial-spec matcher.  Three targeted
     attempts (substitute the deduced args into the pattern before
     verification; instantiate the class-template-id actual arguments up front;
     trust the successful deduction) were each insufficient on their own and
     were reverted.  The next step is to make qualified-name resolution of
     `T<args>::member` instantiate `T<args>` the same way a declaration of the
     type does (a fuller instantiation than the current
     `elaborate_class_template` call in `cpp_typecheck_resolve.cpp`), rather
     than patching the verification.

### Landed this pass (commits)

- `cpp: evaluate C++20 requires-expressions and concept-ids as constexpr bool`
  (materialisation + simple/compound handlers + robustness guard).
- `cpp: pre-increment/decrement of arithmetic/pointer lvalue is an lvalue (C++)`
  (compound return-type value-category).
- `cpp: soft-fail invalid requirement expressions on class/member operations`
  (intercept requirement nodes before operand recursion; class-operator and
  member-call requirements now evaluate `false` instead of erroring).
- `cpp: bind requires-expression parameters for conjoined requires-expressions`
  (materialise params for every requires-expression in the constraint, not just
  the top-level — fixes assignable_from/movable/copyable and the iterator chain).
- CORE tests `cpp20_concept_requires_eval`, `cpp20_concept_compound_requirement`,
  `cpp20_concept_requirement_soft_failure`,
  `cpp20_concept_conjunction_requires_params`, `cpp20_concept_iterator_chain`.

All gated by a green full `cbmc-cpp` suite (cpp20_ranges_basic no longer
crashes).

### Standing caveat (unchanged)

Even with full concept evaluation, the C++20 `constexpr`-heavy libstdc++
`std::string` still timed out in BMC (§7); a separate symex/`constexpr` work
item is expected before cpp20/23 `std::string` *verifies*.
