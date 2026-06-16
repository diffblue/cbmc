# C++20 class-template instantiation correctness — fresh plan (2026-06)

This is a fresh, code-review-grounded plan for the `std::string s("ab")` /
iterator-concept truncation family of failures in CBMC's C++ front end at
`--cpp20`/`--cpp23`.  It supersedes the incremental notes in §13 of
`cpp-requires-expression-support.md`: a structured review plus minimal
self-contained experiments reduced the whole family to **one** standard
divergence, with everything around it confirmed correct.

All probes are self-contained (no libstdc++), accepted by `g++ -std=c++20`, and
run with `cbmc --cpp20`.  They live as regression tests under
`regression/cbmc-cpp/` (see "Regression tests" below).

## 1. Scope and goal

Goal: `std::string s("ab")` (and `s(p)` for `const char *p`, and
copy-assignment) type-check at `--cpp20` and reach BMC, by making CBMC's
class-template instantiation conform to N5008 in the one place it currently
diverges.  (BMC may still hit the standing symex/`constexpr` resource caveat;
that is out of scope here — this plan is about the front end.)

## 2. What is already correct (locked in as CORE tests)

The review confirmed CBMC is conforming for the surrounding machinery:

- **[temp.inst]/1 lazy member-function definitions.** A member function with an
  ill-formed-if-instantiated body that is never ODR-used does not break the
  class. (probe P1)
- **Member typedefs / member functions naming a class-template-id**
  ([temp.inst]/2): a member typedef aliasing `W<T>`, a member typedef that is a
  pointer to a forward-declared `Fwd<T>`, and a member function *declared* to
  return `R<T>` all work. (probes P2, P3, P4)
- **Namespace-scope qualified-name member typedef** `S<int>::type`. (probe P5)
- **`void_t` partial-specialization SFINAE** — both the classic
  `void_t<typename T::mem>` member-type probe and the
  `void_t<decltype(declval<T>().foo())>` expression-`decltype` probe — selects
  the specialization when well-formed and rejects it (falling back to the
  primary) otherwise, **including when the specialization is a member of a
  class template**. (probe P8/P9 → test `cpp_partial_spec_void_t_sfinae`)
- **`requires`-expression containment** ([temp.deduct]/8): a requires-expression
  whose body contains an ill-formed conditional evaluates the concept to
  `false` rather than erroring. (probe P6)
- **Conditional-operator SFINAE in a function body**: a partial spec gated on
  `void_t<decltype(false ? declval<A>() : declval<B>())>` is correctly selected
  / rejected for function-body locals. (probe P10 → test
  `cpp20_partial_spec_conditional_sfinae`)

## 3. The single divergence (KNOWNBUG)

> A class-template partial specialization whose argument-list SFINAE check is a
> **conditional-operator `decltype`** —
> `void_t<decltype(false ? declval<A>() : declval<B>())>` — is mis-handled when
> the specialization is instantiated as a **member of a class template**.

Test: `regression/cbmc-cpp/cpp20_partial_spec_conditional_sfinae_member`
(KNOWNBUG; flip to CORE when fixed).  For `cref<int, int*>` (no common type → the
`?:` is ill-formed → the specialization must be rejected and the primary used,
`tag == 1`), CBMC instead leaves the member's value **uninitialized
(nondeterministic)** and leaks a `types are incompatible` diagnostic.  The
identical construct as a function-body local (P10) is correct, so this is
*context-dependent* to class-member instantiation, and it is specific to the
**conditional operator** (`void_t` with member-type or expression probes, P8/P9,
is correct in the same member context).

This is the minimal essence of libstdc++'s C++20 `common_reference` machinery:
`std::__common_ref_impl<_Xp&, _Yp&, void_t<__condres_cvref<_Xp, _Yp>>>` is exactly
this shape, reached through the iterator concepts when a `reverse_iterator`
member of `std::basic_string` / `std::vector` is instantiated.  The mis-handled
SFINAE there is what truncates `basic_string` (drops its constructors → POD
misclassification → `char[]`/`const char*` → `basic_string` CONVERSION ERROR).

### Standard grounding (N5008)

- **[expr.cond]/4**: `E1 ? E2 : E3` with no common type for `E2`/`E3` (and no
  other applicable bullet) is ill-formed.
- **[temp.deduct]/8**: an invalid type/expression in the *immediate context* of
  the substitution is a deduction failure (SFINAE), not a hard error.  A
  `void_t<decltype(?: )>` partial-specialization argument is such an immediate
  context.
- **[temp.spec.partial.match]/2**: a partial specialization matches iff its
  arguments can be deduced *and* the deduced arguments are well-formed; an
  ill-formed SFINAE argument removes the specialization (the primary is used).

So the conditional-operator failure must be a contained substitution failure in
this context, and it must produce the *same* result regardless of whether the
specialization is instantiated as a function-body local or as a class member
([temp.point], one consistent instantiation per [temp.spec.general]/7).

## 4. Root, as far as localised by the review

There are **two** partial-specialization selection mechanisms with **separate**
SFINAE verifications:

1. `cpp_typecheck_resolvet::disambiguate_template_classes`
   (`cpp_typecheck_resolve.cpp` ~2680) — used for *named* resolution; verifies by
   `typecheck_template_args` in a try/catch; does **not** set
   `suppress_elaborate`.
2. `cpp_typecheckt::elaborate_class_template`'s partial-spec loop
   (`cpp_instantiate_template.cpp` ~1586–1656) — used when an instance created
   from the primary is (re-)elaborated; verifies by `typecheck_template_args`
   in a try/catch but first sets **`suppress_elaborate = true`** ("avoid
   instantiating unused branches e.g. `conditional_t`'s false branch").

For the member `cref<int,int*>` both verifications report `sfinae_failed = 1`
(reject the spec) in tracing, yet the instantiated member is still
uninitialized and the `?:` throw leaks — so the rejection is not fully honoured
*or* the chosen primary's NSDMI/body is dropped during member instantiation.
The conditional-operator typecheck itself is
`typecheck_expr_trinary` (`cpp_typecheck_expr.cpp` ~1078–1125): when neither
operand converts to the other it does `error() << "types are incompatible"; throw 0;`.
The `error()` is emitted even when the `throw 0` is later caught as SFINAE
(observed as the P10 leak), and `suppress_elaborate = true` in mechanism (2) is
the prime suspect for the wrong *result* (it can suppress the very
conditional-`decltype` evaluation that determines well-formedness, so the
verification does not see the ill-formedness).

## 5. Prioritised fix sequence

Each step is independently testable; acceptance criteria reference the tests.

1. **Make the conditional-operator substitution failure a clean, silent SFINAE
   signal.** *(DONE — commits `f661171ad8` + `f008f35e65`.)* A substitution
   failure while type-checking a candidate partial specialization's argument
   list is a deduction failure, not a diagnosable error ([temp.deduct]/8).
   `disambiguate_template_classes`' verification previously used only an error
   *count* save/restore (which rolls back the count but does not unsend the
   emitted message), leaking `types are incompatible` for an ill-formed
   `void_t<decltype(false ? a : b)>` SFINAE argument; it now runs under an
   `sfinae_contextt` (null handler), mirroring the `elaborate_class_template`
   verification.  Acceptance met: `cpp20_partial_spec_conditional_sfinae` is
   still CORE and now forbids the `types are incompatible` line; full
   `cbmc-cpp` suite green.

2. **Reconcile the two partial-spec SFINAE verifications.** *(DONE, but turned
   out to be a different root — commit `11725a980c`.)*  The actual divergence the
   member KNOWNBUG isolated was not the SFINAE *decision* (both verifications
   correctly reject the spec for `cref<int,int*>`) but the *timing* of the
   primary fallback's elaboration: the primary `cref<int,int*>` was still
   incomplete at the enclosing class's constructor-synthesis time, so the
   default-ctor member-init loop saw no NSDMI and dropped the member's
   initialisation (it read uninitialised), whereas the cleanly-matched spec
   member `cref<int,int>` was already complete.  Fixed by elaborating a member's
   class-template-instance type before deciding whether its default construction
   is non-trivial ([class.default.ctor]/3 + [temp.inst]/2), in
   `cpp_typecheck_constructor.cpp`.  Acceptance met:
   `cpp20_partial_spec_conditional_sfinae_member` is now CORE.

   **However**, this did *not* fix `std::string s("ab")`.  The synthetic member
   test no longer reproduces the real libstdc++ failure, so the plan's premise
   that the whole family reduces to that one divergence was incomplete.  The
   remaining real-case divergence is captured by a new KNOWNBUG,
   `cpp20_vector_iterator_namespace_typedef`: a **namespace-scope** typedef of
   `std::vector<int>::iterator` fails (`symbol ... is unknown` / `CONVERSION
   ERROR`) while the same use inside a function body, and a namespace-scope
   `std::vector<int>` variable, both succeed.  Naming the member instantiates
   `vector<int>`, whose `reverse_iterator` member drives the C++20
   iterator-concept / `std::ranges::swap` CPO chain for `__normal_iterator`, and
   in the namespace-scope qualified-name resolution context that evaluation
   raises an *uncontained* failure that aborts resolution.  A self-contained
   reproduction was not found: faithful hand mimics of `__normal_iterator`
   (Container param + `iterator_traits` indirection + converting constructor) do
   *not* trigger it, so it depends on some further detail of the real type.

   **Next divergence to fix (was step 2's tail, now the live one):** contain the
   `swappable` / `ranges::swap` CPO concept evaluation reached during
   namespace-scope qualified-name elaboration of a class-template instance, so a
   substitution failure there is an immediate-context SFINAE failure
   ([temp.deduct]/8, [temp.constr.atomic]) rather than an escaping throw -- the
   same containment that already holds in the function-body / variable contexts.
   Acceptance: `cpp20_vector_iterator_namespace_typedef` flips to CORE.

3. **Re-test the libstdc++ chain.** With (1)+(2), confirm `std::vector<int>`'s
   `reverse_iterator` member and `std::basic_string`'s `const_reverse_iterator`
   member instantiate without truncation (basic_string regains its
   constructors, `cpp_is_pod` is false), so `std::string s("ab")` /
   `std::string s(p)` reach BMC with no CONVERSION ERROR.  Gate on the full
   `cbmc-cpp` suite (`-X libcxx`).  Add a CORE regression test for the
   `std::string` construction once the front end elaborates it (BMC resource
   limits permitting; otherwise a front-end-only `goto-cc`/typecheck check).

4. **Watch for the two-selection-mechanism design smell.** If reconciling (2) is
   fragile, consider unifying the two partial-spec SFINAE verifications behind a
   single helper so they cannot diverge again; this is the structural fix and
   the cleanest guard against regressions in this pervasive code.

## 6. Regression tests (this plan)

| test | level | what it pins |
|------|-------|--------------|
| `cpp20_partial_spec_conditional_sfinae_member` | CORE *(was KNOWNBUG; fixed by step 2)* | the member-NSDMI / primary-fallback elaboration divergence |
| `cpp20_partial_spec_conditional_sfinae` | CORE | conditional SFINAE in a function body works (step 1 contrast) |
| `cpp_partial_spec_void_t_sfinae` | CORE | `void_t` member-type / expression SFINAE works in member context (pins the divergence to the conditional operator) |
| `cpp20_vector_iterator_namespace_typedef` | KNOWNBUG | the remaining real-case divergence: namespace-scope typedef of `std::vector<int>::iterator` (the `swappable`/`ranges::swap` CPO chain truncates in that context) |

## 7. Already landed (related, this branch)

- `cpp: match reference qualifier in template-argument deduction`
  (`98f8ab2094`) + test `template_partial_spec_reference_qualifier`
  (`531cd661b8`) — fixed a *different* root in the same family (the
  reference-qualifier-keyed `__common_ref_impl<_Xp&, _Yp&&>` self-inheritance);
  necessary but not sufficient for `std::string`.
- `cpp: elaborate nested class-template-id arguments before partial-spec
  matching` (`8c5aa75ca5`) + test `template_partial_spec_nested_template_id` —
  fixed the `allocator_traits<allocator<T>>` nested-template-id shape (§12).
