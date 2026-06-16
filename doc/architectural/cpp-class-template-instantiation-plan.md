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

### Terminology and prioritisation

Following a deliberate distinction:

- **conformance / conformant** — the *front end* matches what N5008 mandates
  (type-checking, name lookup, instantiation, POD/triviality classification,
  overload resolution).  This is the **first-tier** goal.
- **correct / correctness** — CBMC reaches the *right verification result*.
  Together with verification *performance* (does BMC complete within resources)
  this is **second-tier**: pursued only after conformance is established.

Concretely: a fix that makes the front end conformant is preferred even if it
regresses verification performance; conversely a change that merely "makes a
test pass" via a non-conformant front end (e.g. relying on a truncated class
plus library models) is *not* a conformance fix.  The `cpp20_erase_if` /
`cpp20_apple_libcxx_basic` CORE tests, for instance, pass today with a
*non-conformant* (truncated) `std::vector`; that is a verification result
standing on a conformance gap.

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

   **Course-correction (2026-06, investigated):** the
   `cpp20_vector_iterator_namespace_typedef` divergence, on closer analysis, is
   **orthogonal to the `std::string s("ab")` goal**.  gdb/instrumentation shows
   the namespace alias `It` is created with a *deferred* underlying type;
   `vector<int>` is instantiated only when `It` is *used* (`sizeof(It)` in
   `main`, attributed to line 3), and the failure is specific to resolving a
   *namespace-scope* type alias's underlying type at its point of use (the
   identical alias declared *locally* in a function resolves eagerly and works).
   The goal, by contrast, fails at line 2 in `main` (a function context): naming
   `std::string s("ab")` instantiates `basic_string<char>`, whose **body**
   elaboration truncates at the `const_reverse_iterator` member typedef
   (`reverse_iterator<const_iterator>`, the member after `const_iterator`; 13
   components, 0 constructors), so `cpp_is_pod(basic_string)` is wrongly true and
   the `(const char*)` constructor is gone.  (`std::string s;` only "works"
   *vacuously* -- the truncated POD is default-initialised to garbage.)

   So the **goal-critical divergence is the class-member truncation**: a member
   typedef aliasing a class-template-id whose eager definition-instantiation
   throws (the `reverse_iterator`/iterator-concept chain) must not abort the
   enclosing class's body ([temp.inst]/1-2: a member *declaration* does not
   require the aliased template's *definition*).  A prior member-elaboration
   containment attempt in `typecheck_compound_body` lifted basic_string from 13
   to 65 components but did not restore the constructors, because a
   class-template instance's member *functions* are populated through a
   different instantiation route than the body-loop declarator path.  Both this
   and the namespace-alias divergence share the `reverse_iterator<__normal_iterator>`
   concept-chain root and resist self-contained reproduction (faithful
   `__normal_iterator` mimics verify cleanly), so the remaining work is a
   focused, dedicated effort on either (a) not eagerly instantiating
   `reverse_iterator`'s definition for a member-typedef declaration, or
   (b) containing the iterator-concept/CPO substitution failure at its source so
   the chain never throws uncontained.

3. **Re-test the libstdc++ chain.** With (1)+(2), confirm `std::vector<int>`'s
   `reverse_iterator` member and `std::basic_string`'s `const_reverse_iterator`
   member instantiate without truncation (basic_string regains its
   constructors, `cpp_is_pod` is false), so `std::string s("ab")` /
   `std::string s(p)` reach BMC with no CONVERSION ERROR.  Gate on the full
   `cbmc-cpp` suite (`-X libcxx`).  Add a CORE regression test for the
   `std::string` construction once the front end elaborates it (BMC resource
   limits permitting; otherwise a front-end-only `goto-cc`/typecheck check).

   **Major finding (2026-06, route mapped + front-end fix demonstrated, then
   reverted).** The route that populates a class-template instance's members is
   `typecheck_compound_body`'s member loop, run via `convert_non_template_declaration`
   inside `instantiate_template`.  It has *two* passes over the body: the first
   adds typedefs / data members / non-constructor methods (and **skips**
   constructors, `if(declaration.is_constructor()) { found_ctor=true; continue; }`),
   the second (clearly labelled "We now deal with the constructors") adds the
   constructors.  For `basic_string<char>` the first pass aborts at member [26],
   the `const_reverse_iterator` typedef (`reverse_iterator<const_iterator>`,
   immediately after `const_iterator`): its eager `typecheck_type` drives the
   C++20 iterator-concept chain and throws, so the loop never reaches the
   *second* (constructor) pass -> 13 components, 0 constructors -> `cpp_is_pod`
   wrongly true -> `char[3]`/`const char*` -> `basic_string` CONVERSION ERROR.

   Containing that throw works, but **must lazily register the alias, not skip
   it**: a plain skip leaves later members that name it (e.g.
   `const_reverse_iterator rbegin() const;`, member [108]) dangling, which throws
   again and re-aborts the first pass.  Keeping the unresolved cpp_name (the
   `kept_unresolved_cpp_name` lazy-typedef path) lets the first pass complete,
   the second pass run, and the constructors register.  With this, **the goal's
   front end is fixed**: `std::string s("ab")` and `std::string s(p)` no longer
   produce CONVERSION ERROR -- they reach Bounded Model Checking (then hit the
   standing BMC resource limit: "Out of memory").

   **But it was reverted because it regresses the vector tests via BMC timeout.**
   The containment fires for `std::vector<int>` too (its `const_reverse_iterator`),
   *un-truncating* vector.  `cpp20_erase_if` / `cpp20_apple_libcxx_basic`
   previously passed *because* the truncated vector + CBMC's compiled library
   models were lightweight; the full header `vector` inlines heavy iterator code
   and the BMC blows up (front end still completes fast and reaches "Starting
   Bounded Model Checking" -- the timeout is purely in symex/SAT).  This exposes
   a **conformance vs verification-performance tension**: un-truncating the
   iterator-heavy classes is *conformant* (they have user-declared constructors
   and are not PODs) and is necessary for `std::string` construction, but it
   makes the model-backed container tests intractable.

   **Scope of the performance impact (2026-06, measured):** it is **not** limited
   to those two tests.  With the blanket lazy un-truncation the full `cbmc-cpp`
   suite no longer completes (timed out mid-run at `cpp20_map_basic`): every
   container test whose class has a `reverse_iterator` member typedef
   un-truncates and its full header machinery is symexed.

   **Resolved: the un-truncation is correct and was re-landed** (commits
   `976bf25ea4` + `81cae27a21`).  A per-test-timeout suite run identified the
   *exact* set affected -- only **4** tests (`cpp20_vector_basic`,
   `cpp20_map_basic`, `cpp20_erase_if`, `cpp20_apple_libcxx_basic`), not the
   whole suite (the earlier "untestable" impression was an artifact of running
   with no per-test timeout, so one hung test blocked the rest).  Crucially, all
   four were **unsound** before: with the truncated container symex executed
   **zero** instructions of the real container, so the properties were vacuous --
   `cpp20_erase_if` reports VERIFICATION SUCCESSFUL even for
   `__CPROVER_assert(v.size() == 999)`.  And the now-executed code is exactly
   what `g++ -O0` emits for the same program (diffed: the 99 `vector`/iterator/
   allocator/algorithm template instantiations).  So un-truncation is both
   **conformant** *and* **restores soundness**; the four tests were reclassified
   to KNOWNBUG as a second-tier **verification-performance** matter (they return
   to CORE once symex is tractable on real libstdc++ containers), and the suite
   is green again.

   **Why symex diverges on the real containers (measured, not loops).** With
   `--unwind 1` the affected test still does not finish, and `--verbosity 10`
   shows symex never reaches the equation/SAT phase: it is stuck *inside* symex.
   "depth N" in the trace is the symex *step* count, and it is only ~495 after
   90s -- i.e. ~5 steps/second.  So it is **pathologically slow per step**, not
   loop-unwinding, recursion, or function-pointer fan-out (the only
   function-pointer sites resolve to 0 targets).  The steps are genuine
   libstdc++ code (`stl_vector.h`, `vector.tcc`, `stl_algobase.h`,
   `stl_iterator.h`).  Finding and fixing that per-step cost is the second-tier
   work item (profiling under way).

   **(Historical) Conformant-AND-tractable approach considered.** Per [temp.inst]/2,
   implicitly instantiating a class template instantiates its member
   *declarations*, not the *definitions* of the entities they name (definitions
   are instantiated on ODR-use).  The conformant front end therefore needs the
   class to carry all its member *declarations* (so it is non-POD with its
   constructors -- the conformance property `std::string s("ab")` needs) while
   keeping member-function *definitions* lazy, so BMC continues to use CBMC's
   compiled library models / does not inline the heavy header bodies.  The
   blanket lazy un-truncation over-instantiates (it pulls in the member-function
   bodies via the `ID_template_methods` pass), which is what makes BMC
   intractable.  The next step is to split these: keep the member-declaration
   completion (conformance, the first-tier goal) but not the eager body
   instantiation (which is the second-tier performance cost).

   Two earlier-considered framings (superseded by the above):
   - (A) **Narrower front-end fix:** route `basic_string`'s `(const char*)`
     construction correctly *without* un-truncating -- i.e. stop misclassifying a
     truncated, model-backed `basic_string` as a POD in `cpp_constructor`
     (`cpp_is_pod` / the assignment fallback) so the construction uses the
     constructor / library model instead of an `implicit_typecast`.  This avoids
     touching vector's elaboration entirely.
   - (B) **BMC-tractability:** keep the (correct) un-truncation but provide
     lighter models/stubs for the inlined iterator machinery so the vector tests
     stay tractable (the same class of work as the `cpp11_map_insert` KNOWNBUG).

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
