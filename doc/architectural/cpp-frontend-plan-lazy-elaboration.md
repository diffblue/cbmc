\file

Detailed plan: lazy class-body elaboration per [temp.inst]/3

# Detailed plan: lazy class-body elaboration

**Owner:** — (to be assigned)
**Status:** Proposed
**Parent document:** `doc/architectural/cpp-frontend-review.md` §3.1, §6 (medium term, lazy class-body elaboration)
**Standard anchor:** N5008 [temp.inst]/3:

> The implicit instantiation of a class template specialization causes
> the implicit instantiation of the declarations, but not of the
> definitions, of the non-deleted class member functions, member
> classes, scoped member enumerations, static data members, member
> templates, and friends …

In CBMC terms: during `typecheck_compound_body`, the class should be
produced with all member *names* registered, but the full *type* of
each member should only be resolved at the point where it is used.

## 1. Motivation from measured data

From `ci-failures-2026-05-13.md` and the dog-food expansion:

- Dog-food `--expand` on `src/util/` is at 10 OK_CLEAN / 4 OK_NOISY /
  103 FAIL / 0 CRASH (8.5% clean).
- The dominant FAIL categories:

  | count | category |
  |-------|----------|
  |   58  | `symbol 'X' is unknown` in member-function bodies |
  |   17  | `instantiating 'std::…'` cascade |
  |   11  | `found no match for symbol 'swap'` (templates-only overload set) |
  |    3  | `symbol 'id' is unknown` |
  |    2  | range-based for requires an array type |
  |    … | misc |

- The top two categories together (75 of 103 FAILs) share a
  root cause: class elaboration abandons the member-declaration
  loop on the first throw from `typecheck_type` /
  `typecheck_compound_declarator`, losing *subsequent* members.
  Later method bodies referencing those lost members produce the
  `symbol 'X' is unknown` diagnostics.

Closing this root cause is projected to move the dog-food `--expand`
pass rate from ~12% to ~50%+.  The 2026-05-13 incremental attempt
confirmed the underlying theory (the string_containert minimal
reproduction went from FAIL to OK with partial-class tolerance) but
also demonstrated that the approach *must* be holistic — the
naive "catch and skip" lost other OK cases because their success
depended on the loop exiting early.

## 2. Existing mitigations to retire

The codebase has accumulated narrow patches that will become no-ops
once the lazy refactor lands:

1. `cpp_typecheck_compound_type.cpp:1318` — `instantiation_stack.empty()
   && type_is_tpl_cpp_name` branch: "keep unresolved cpp_name" on
   top-level template-args member types.  Added to let typedef
   declarators survive instantiation failures.
2. `cpp_typecheck_compound_type.cpp:~1337` — `!instantiation_stack.empty()
   && type_is_tpl_cpp_name && is_self_reference` branch: skip
   self-referential `common_type_t<SelfClass>`-style members during
   class-template instantiation (commit `a437aacd7d`, generalized
   from the earlier duration-specific `2e8e74f8ed`).
3. `cpp_typecheck_expr.cpp` — `deduce_function_address_args_from_target`
   probe-and-retry helper for [temp.deduct.funcaddr] (commits
   `d612fe6dac` + refactor `a5a4b9f156`).  Not strictly a class-body
   issue, but becomes redundant once target-type threading lands
   alongside lazy elaboration.
4. `resolve_template_alias` thread-local active-set cycle break
   (`09e5625681`).  Becomes a proper cache once class members are
   reliably elaborated under stable scopes.

Each of these has a comment tying it back to the standard clause it
is approximating; after lazy elaboration lands each one becomes a
single commit: "retire X mitigation, now subsumed by lazy
elaboration".

## 3. Current state (what changes)

### 3.1 `typecheck_compound_body` flow

```
for each cpp_declaration in body:                         ← eager
  typecheck_type(declaration.type())                      ← may throw
  for each declarator in declaration:
    typecheck_compound_declarator(…)                       ← may throw
```

On any throw, the enclosing loop exits.  Everything after the
throwing declaration is never processed.

### 3.2 Readers of `components()`

There are 36 reads of `struct_union_typet::components()` in
`src/cpp/` (measured 2026-05-13).  Classified by what they do with
the returned component:

| count | pattern | depends on complete type? |
|-------|---------|--------------------------|
|  ~12 | iterate to find by base_name | no (base_name only) |
|  ~10 | iterate to find by type.id()==ID_code (method) | yes |
|  ~6 | read `component.type()` for construction / copy | yes |
|  ~5 | vtable / aggregate init | yes |
|  ~3 | printing / inspection | partial |

The "no" sites can stay as is.  The "yes" sites need to go through
a completion helper.

## 4. Target state

### 4.1 The primitive: `ensure_member_complete`

```cpp
// Declared in cpp_typecheck.h.

/// Resolve the type of a lazily-registered class-scope member per
/// [temp.inst]/3.  Idempotent: a call on an already-complete
/// component is a cheap no-op.
///
/// \param struct_type the class whose member is being completed.
///        Must be mutable because completion updates the component
///        in place.
/// \param base_name the unqualified name of the member to complete.
/// \return pointer to the (now-complete) component, or nullptr if
///         the member genuinely cannot be resolved (an error has
///         been emitted at the use site via the caller's context).
struct_union_typet::componentt *ensure_member_complete(
  struct_union_typet &struct_type,
  const irep_idt &base_name);
```

Implementation sketch:

```cpp
auto *comp = find(struct_type.components(), base_name);
if(comp == nullptr)
  return nullptr;
if(!comp->get_bool(ID_C_lazy_member_type))
  return comp;  // already complete

const irept &source = comp->find(ID_lazy_type_source);
// source is the original `cpp_declaration` / `cpp_declarator` pair.

try
{
  sfinae_contextt guard{*this};  // [temp.deduct]/8-adjacent
  typet resolved = resolve_lazy_source(source, /*scope=*/struct_type);
  comp->type() = std::move(resolved);
  comp->remove(ID_C_lazy_member_type);
  comp->remove(ID_lazy_type_source);
  return comp;
}
catch(...)
{
  // Resolution genuinely failed — leave the component in lazy form
  // so a later (possibly better-scoped) retry can proceed, and the
  // caller gets nullptr to produce a proper use-site diagnostic.
  return nullptr;
}
```

The guard is important: completion is semantically a substitution
step ([temp.inst]/4-5 defer to the deduction/substitution rules,
and [temp.deduct]/8's "immediate context" applies).

### 4.2 New irep attributes

Add to `src/util/irep_ids.def`:
- `ID_C_lazy_member_type` → `"#lazy_member_type"` (bool marker)
- `ID_lazy_type_source` → `"lazy_type_source"` (subtree carrying the
  original source declaration)

### 4.3 `typecheck_compound_body` becomes bimodal

```cpp
for each op in body:
  if(op.id() != ID_cpp_declaration) { …handle access/friend/static_assert… }
  else if(use_lazy_elaboration_for(symbol))
    add_lazy_components(type, to_cpp_declaration(op), access, …);
  else
    typecheck_eager(type, to_cpp_declaration(op), access, …);  // current path
```

`use_lazy_elaboration_for(symbol)` is a small predicate.  For the
first phased enablement it only returns `true` for
`!instantiation_stack.empty()` (i.e. class-template instances); later
it expands.

`add_lazy_components` is minimal:

```cpp
void add_lazy_components(
  struct_union_typet &type,
  const cpp_declarationt &decl,
  const irep_idt access,
  bool is_static, bool is_typedef, bool is_mutable)
{
  for(const auto &d : decl.declarators())
  {
    const irep_idt &base_name = d.name().get_sub().empty()
      ? irep_idt()  // operator / special
      : d.name().get_sub().front().get(ID_identifier);
    struct_union_typet::componentt comp(base_name, typet{});
    comp.set_base_name(base_name);
    comp.set(ID_access, access);
    if(is_static) comp.set(ID_is_static, true);
    if(is_typedef) comp.set(ID_is_type, true);
    if(is_mutable) comp.set(ID_is_mutable, true);
    comp.set(ID_C_lazy_member_type, true);
    irept source(ID_lazy_type_source);
    source.get_sub().push_back(static_cast<const irept &>(decl));
    source.get_sub().push_back(static_cast<const irept &>(d));
    comp.add(ID_lazy_type_source) = source;
    type.components().push_back(std::move(comp));
  }
}
```

The key property: `add_lazy_components` **cannot throw**.  It
extracts a name + stores the source subtree.  Everything that might
throw (resolve cpp_name, instantiate template, convert declarator)
is deferred to `ensure_member_complete` where it runs inside a
sfinae guard.

### 4.4 Caller audit — the 10 "yes, needs complete type" sites

Each site is a one-file change that inserts an
`ensure_member_complete` call before reading `component.type()`.  A
helper `iterate_complete(struct_type)` returns an iterator range
that completes on access; most sites can switch to it.

The specific sites (paths + approximate line numbers as of
`bf79ab84e3`):

1. `cpp_typecheck_expr.cpp:~1800` — `typecheck_expr_member` direct
   access
2. `cpp_typecheck_expr.cpp:~1950` — `typecheck_expr_ptrmember`
   (delegate to member after `add_implicit_dereference`)
3. `cpp_typecheck_resolve.cpp:~1080` — struct-type identifier
   expansion into constructor candidates
4. `cpp_typecheck_resolve.cpp:~3690` — destructor synthesis fallback
   (commit `5e7efee580`)
5. `cpp_typecheck_conversions.cpp:~980` — user-defined conversion
   operator candidates
6. `cpp_typecheck_compound_type.cpp:~640` — virtual table base-class
   walk
7. `cpp_typecheck_compound_type.cpp:~800` — vtable entry generation
8. `cpp_typecheck_compound_type.cpp:~1110` — aggregate-init designated
   initializers
9. `cpp_constructor.cpp:~370` — constructor lookup
10. `cpp_destructor.cpp:~80` — destructor lookup

## 5. Phased migration

### Phase 1 — infrastructure, no behaviour change (1 day)

- Commit A: add `ID_C_lazy_member_type` + `ID_lazy_type_source`.
- Commit B: declare + define `ensure_member_complete` as a no-op
  when the marker is absent.  Unit test that confirms idempotence
  on a non-lazy component.
- Commit C: define `add_lazy_components` producer helper and unit
  test it directly.  Nothing in the tree calls it yet.

Regression: bit-identical behaviour, 26/26 MSVC, dog-food 10/4/103/0
unchanged.  If any of these three commits moves any number, that's
a latent bug we caught early.

**2026-05-16 status.** Phases 1A (`5444441ce2`) and 2A
(`c9aa0a996c`) landed:

* Phase 1A — `ID_C_lazy_member_type` + `ID_lazy_type_source` ireps;
  `ensure_member_complete(struct, base_name)` primitive declared and
  stub-implemented.
* Phase 2A — added `const`-overload of `ensure_member_complete` for
  read-only iteration sites, plus `complete_all_components(struct)`
  for bulk pre-iteration completion.  Both are no-ops in Phase 1.

Both commits are bit-identical behaviour changes (no caller marks
components lazy yet); regression suite green; dog-food unchanged at
10/4/103/0.

### Phase 2 — caller audit (~1 week)

- One commit per call site (so each can be reverted independently
  if it surfaces an issue).  Each inserts the `ensure_member_complete`
  call and — if the site has an iteration — switches to
  `iterate_complete`.
- After each commit, run: full CORE + KNOWNBUG + MSVC 26 + dog-food.
  Expected: all green, dog-food unchanged (no producer yet).

### Phase 3 — narrow producer opt-in (~1 week)

- Commit N: add the `use_lazy_elaboration_for(symbol)` predicate,
  returning `true` only when `!instantiation_stack.empty()` AND
  the member's declared type is `type_is_tpl_cpp_name`.
- Commit N+1..N+k: iterate based on dog-food and regression
  feedback.  Each iteration either:
  - Expands the predicate (e.g. to cover non-tpl cpp_name types that
    fail within instantiation), or
  - Fixes a caller that missed `ensure_member_complete` (visible as a
    new diagnostic referring to an incomplete type).
- Expected dog-food: step up from 12% to ~25–35% OK_CLEAN as the
  top-level template-class-instance failures stop cascading.

**2026-05-16 attempt notes (second attempt, after Phase 1A/2A).**
A targeted producer was tried: when `typecheck_compound_body`'s
existing `kept_unresolved_cpp_name` mitigation fires (top-level
class member of the form `template<…> m;` whose template
instantiation cannot complete), and the subsequent
`typecheck_compound_declarator` then throws, register the
component lazily (mark `ID_C_lazy_member_type`, keep
`declaration.type()` as the unresolved cpp_name placeholder).

Result: dog-food regressed from 10 OK_CLEAN to 8 OK_CLEAN —
`validate_expressions.cpp` and `validate_types.cpp` went from OK
to FAIL.  Identical to the May-13 finding: registering the member
*name* without resolving the *type* surfaces previously-suppressed
"member of incomplete type" diagnostics in sibling method bodies
that previously bailed out at the original throw.

**2026-05-16 follow-up (third attempt, working).**  The
above analysis turned out to be slightly misleading: the
regression was caused specifically by **typedef** declarators,
not data members.  Tracing showed the catch handler ran on
`typedef std::unordered_map<…> hash_tablet;` declarators —
where the type couldn't elaborate eagerly, the throw escaped
`typecheck_compound_declarator`, and the lazy fallback added
the typedef as a struct **component** but never as a class-
scope **typedef symbol**.  Subsequent declarators that
referenced the typedef (`hash_tablet hash_table;`) then
failed with `symbol 'hash_tablet' is unknown`, which leaked
through the error suppression because it occurred *outside*
the catch.

The fix has two parts, landed as `77307e32b2` (Phase 3
producer) and `41e614892c` (Phase 4 on-demand resolution):

* **Phase 3 producer** (commit `77307e32b2`).  When the
  declarator throws under `kept_unresolved_cpp_name` and the
  declarator is a typedef, register a typedef *symbol* in the
  class scope (the way `cpp_declarator_convertert` would,
  with `is_type=true, is_macro=true`, put_into_scope as
  `cpp_idt::id_classt::TYPEDEF`) — the symbol's aliased type
  is the unresolved cpp_name, marked `ID_C_lazy_member_type`.
  Sibling lookups by name find the symbol; users of the
  resolved type fail at the use site only.  For non-typedef
  data-member declarators, the lazy struct component is
  still registered as before.

  Dog-food: 10/4/103/0 → **14/5/98/0** — four files newly
  OK_CLEAN (`dstring.cpp`, `irep_ids.cpp`, `options.cpp`,
  `string_container.cpp`), one newly OK_NOISY
  (`xml_irep.cpp`), zero regressions, cbmc-cpp regression
  675/0/83.

* **Phase 4 on-demand resolution** (commit `41e614892c`).
  `try_resolve_lazy_member` does the real work:

    1. Read the class-scope identifier from
       `ID_lazy_type_source` (stamped by Phase 3's producer).
    2. `cpp_save_scopet`, then
       `cpp_scopes.go_to(class_scope)` so member-typedef
       lookups inside the placeholder work.
    3. Run `typecheck_type` on a scrubbed copy of the type,
       under `sfinae_contextt` ([temp.deduct]/8), so failure
       is silently absorbed.
    4. On success, replace `component.type()` with the
       resolved type — markers gone, component now normal.
    5. On failure, leave the placeholder + marker; later
       calls or different scopes can retry.

  No dog-food change yet because no caller of
  `ensure_member_complete` exists in the tree.  Phase 2
  caller-audit is now the unblock to expose more files to
  the resolution capability; the helper itself is correct
  and ready.

The original lesson still stands: lazy registration without
typedef-symbol registration is harmful.  The amended fix
matches the lesson exactly — Phase 3's producer registers
both the symbol and the component, and Phase 4 wires up
on-demand resolution so the symbol's type can actually be
completed when something looks at it.

### Phase 4 — wider opt-in (~1–2 weeks)

- Expand the predicate to top-level classes whose eager elaboration
  currently fails.  Requires the "keep unresolved cpp_name" branch
  to be rewritten against lazy elaboration rather than via the
  saved_type dance.
- Each expansion is a commit with its own dog-food + regression run.
- Expected dog-food: step up to target ≥ 50% OK_CLEAN.

### Phase 5 — retire mitigations (~2–3 days)

Commit-per-retirement, each testable with a single ctest run:
- Remove "keep unresolved cpp_name" branch (subsumed by lazy path).
- Remove P3a self-reference skip (same).
- Remove `deduce_function_address_args_from_target` probe-retry
  (subsumed by target-type threading from the sibling plan; keep
  the helper's comment as a docstring on the lazy-path equivalent).
- Remove the `sfinae_contextt` error-count-save/restore pattern in
  `typecheck_compound_body`'s inner typecheck_type try/catch
  (eager path gone).

## 6. Testing strategy

### Regression gates

- **CORE:** `ctest -L CORE` on all platforms (local Linux always;
  CI gates the rest) — must stay 100% green at every commit.
- **KNOWNBUG:** `ctest -L KNOWNBUG` — must stay green (the
  inverted-match tests might legitimately move to CORE as the refactor
  fixes their underlying issue; that's a separate test.desc update
  per phase).
- **MSVC preprocessed headers:** all 26/26 must stay green on every
  commit.  The minimum is re-running the MSVC pass rate script at
  each commit.
- **Dog-food `--expand`:** record the delta per commit.  Regressions
  on previously-OK_CLEAN files are the leading indicator that a
  caller missed `ensure_member_complete`.

### New tests to add

- `regression/cbmc-cpp/cpp11_string_container_style/` — minimal
  repro of the string_containert pattern (typedef of
  `unordered_map<...>` before an unrelated member method that
  references a later-declared member).  CORE (`VERIFICATION
  SUCCESSFUL`).
- `regression/cbmc-cpp/cpp11_lazy_member_ordering/` — class body
  with forward-declared member types and method bodies that
  reference later-declared members.  Ensures [basic.scope.class]/1
  class-scope lookup continues to work.
- `regression/cbmc-cpp/cpp11_lazy_member_fails_gracefully/` —
  class body where a member's type truly cannot be resolved (e.g.
  undefined template).  Use sites of that member must produce a
  use-site diagnostic (not a parse-time loop-abandonment).

### Unit tests

- `unit/cpp/ensure_member_complete.cpp`:
  - Idempotence.
  - Completion of a lazy member resolves its type correctly.
  - Completion of a member whose source declaration fails returns
    nullptr and leaves the component in lazy form for later retry.
  - Completion honours scope (the source is re-resolved against
    `struct_type`'s scope, not the caller's current scope).

## 7. Risks

| risk | probability | severity | mitigation |
|------|-------------|----------|------------|
| A caller reads `components()[i].type()` without completing first, silently operating on an empty type | high (many call sites) | high (wrong verification) | Start with a DATA_INVARIANT in `componentt::type()` that fires when the lazy marker is still set.  Convert to a softer warning during migration if too noisy, tighten back at end of Phase 2. |
| Lazy source subtree holds a stale scope reference, resolving to a different symbol than the eager path would have | medium | medium | Capture the scope explicitly at lazy registration (store `scope_identifier` in `lazy_type_source`).  Compare to eager path in Phase 2 audits. |
| A completion failure inside a destructor/vtable iteration leaves the class in a broken state downstream | medium | high | `ensure_member_complete` never partially updates: either the component fully resolves or stays lazy.  Downstream code sees a well-known "incomplete" type rather than a half-initialised one. |
| Phase 3 producer trips a previously-implicit ordering assumption in `typecheck_method_bodies` (method bodies iterate in registration order) | medium | low | Method-body iteration sees the same components in the same order; only the type-completion point changes. |
| Dog-food regresses on some file between phases | medium | low | Revert the last commit; each phase is a sequence of small commits.  The learning captured in `doc/architectural/cpp-frontend-review.md` §6 already warns us about the "errors emitted" anti-monotonicity — the lazy path should fix that because errors now come from use sites, not elaboration sites. |

## 8. Success criteria (definition of done)

1. `typecheck_compound_body`'s `instantiation_stack.empty() &&
   type_is_tpl_cpp_name` "keep unresolved cpp_name" branch is
   deleted — lazy elaboration subsumes it.
2. The P3a `is_self_reference` skip is deleted.
3. `deduce_function_address_args_from_target` probe-retry is either
   deleted (target-type-threading plan landed) or documented as the
   only remaining such helper.
4. Dog-food `--expand` OK_CLEAN ≥ 50% on `src/util/`.
5. `grep "components()\[" src/cpp/ | …` finds zero occurrences of a
   direct `.type()` read without a prior `ensure_member_complete` or
   `iterate_complete`.
6. MSVC preprocessed headers: 26/26 (today).
7. All CORE + KNOWNBUG regressions: green.

## 9. Non-goals

- **Not** implementing full two-phase name lookup per [temp.res.general].
  That is the long-term item §4.3 of the architectural review and
  remains future work; lazy elaboration is orthogonal to it.  Two-phase
  lookup would expand on the lazy elaboration's scope capture by
  distinguishing dependent vs non-dependent names at parse time.
- **Not** reshaping resolver return types to `std::optional<exprt>`
  (§3.2 second half of the roadmap).  Can follow after lazy
  elaboration if still worthwhile — the lazy refactor itself retires
  several of the sites where the outcome type would matter.
- **Not** retiring `sfinae_contextt` — it remains the primitive for
  immediate-context substitution.  `ensure_member_complete` uses it
  internally.

## 10. Dependencies and ordering

- Depends on: `sfinae_contextt` (landed, commit `7160102bc3`).
- Independent of: target-type threading (sibling plan).  Can proceed
  in parallel if two people are working; a single person should do
  target-type threading first since it is mechanical and unblocks
  retiring Phase 5's `deduce_function_address_args_from_target`
  helper.
- Blocks: long-term two-phase lookup / POI tracking work.
